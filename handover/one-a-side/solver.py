#!/usr/bin/env python3
"""Synthesize a Lean Represents circuit using a SAT table on the oneEach promise."""

import argparse
from dataclasses import dataclass
from itertools import combinations
import json
from math import isfinite
from pathlib import Path
import re
from threading import Timer
from time import perf_counter

from pysat.solvers import Glucose3


OPS = {"ao": ("and", "or"), "aon": ("and", "or", "not")}
FALSE_WIRE = None
CORPUS_GATES = [
    ("or", [9, 0]),
    ("or", [6, 4]),
    ("or", [2, 10]),
    ("or", [5, 11]),
    ("or", [3, 13]),
    ("or", [10, 14]),
    ("and", [12, 14]),
    ("not", [16]),
    ("and", [15, 17]),
]
# The same circuit with gates 0/1 and 2/3 swapped, wire IDs remapped, and operands sorted.
CORPUS_ORDERED_GATES = [
    ("or", [4, 6]),
    ("or", [0, 9]),
    ("or", [5, 10]),
    ("or", [2, 11]),
    ("or", [3, 12]),
    ("or", [11, 14]),
    ("and", [13, 14]),
    ("not", [16]),
    ("and", [15, 17]),
]


@dataclass(frozen=True)
class Instance:
    rows: int
    cols: int
    mask: int
    ops: str
    bound: int

    @property
    def input_count(self):
        return self.rows + self.cols


@dataclass(frozen=True)
class PromiseRow:
    u: int
    v: int
    inputs: tuple[bool, ...]
    target: bool


def truth_table(instance):
    return [
        PromiseRow(
            u,
            v,
            tuple(wire in (u, instance.rows + v) for wire in range(instance.input_count)),
            bool((instance.mask >> (instance.cols * u + v)) & 1),
        )
        for u in range(instance.rows)
        for v in range(instance.cols)
    ]


def evaluate(gates, output, inputs):
    """Replay Lean's fold over gates, including its default-false wire reads."""
    wires = list(inputs)
    for op, predecessors in gates:
        values = [wires[wire] if 0 <= wire < len(wires) else False for wire in predecessors]
        if op == "and":
            wires.append(all(values))
        elif op == "or":
            wires.append(any(values))
        elif op == "not":
            wires.append(not (values[0] if values else False))
        else:
            raise ValueError(f"unsupported gate op {op!r}")
    return wires[output] if 0 <= output < len(wires) else False


def replay(gates, output, table):
    correct = 0
    for row in table:
        actual = evaluate(gates, output, row.inputs)
        if actual == row.target:
            correct += 1
        else:
            print(
                f"REPLAY MISMATCH u={row.u} v={row.v} "
                f"expected={int(row.target)} actual={int(actual)}",
                flush=True,
            )
    return correct


@dataclass(frozen=True)
class GateVars:
    ops: dict[str, int]
    active: tuple[int, int]
    slots: tuple[dict[int | None, int], dict[int | None, int]]
    values: list[tuple[int, int, int]]


class Encoding:
    def __init__(self, instance, table, nosym):
        self.variables = 0
        self.clauses = []
        self.gates = []

        input_count = instance.input_count
        for index in range(instance.bound):
            self.gates.append(
                GateVars(
                    {op: self.new_var() for op in OPS[instance.ops]},
                    (self.new_var(), self.new_var()),
                    (self.wire_selectors(input_count + index),
                     self.wire_selectors(input_count + index)),
                    [(self.new_var(), self.new_var(), self.new_var()) for _ in table],
                )
            )
        self.output = self.wire_selectors(input_count + instance.bound)

        for index, gate in enumerate(self.gates):
            self.exactly_one(gate.ops.values())
            first_active, second_active = gate.active
            self.add(-second_active, first_active)
            if "not" in gate.ops:
                # Lean's NOT ignores any second input, so we can always omit it.
                self.add(-gate.ops["not"], -second_active)
            for active, selectors in zip(gate.active, gate.slots):
                self.exactly_one(selectors.values())
                if not nosym:
                    self.add(active, selectors[FALSE_WIRE])
            if not nosym:
                self.order_gate_inputs(index, gate)

            for row_index, row in enumerate(table):
                x, y, z = gate.values[row_index]
                for selectors, slot_value in zip(gate.slots, (x, y)):
                    for wire, selector in selectors.items():
                        tag, value = self.wire_value(wire, row, row_index)
                        if tag == "c":
                            self.add(-selector, slot_value if value else -slot_value)
                        else:
                            self.add(-selector, -slot_value, value)
                            self.add(-selector, slot_value, -value)
                self.gate_evaluation(gate, x, y, z)

        self.exactly_one(self.output.values())
        for row_index, row in enumerate(table):
            for wire, selector in self.output.items():
                tag, value = self.wire_value(wire, row, row_index)
                if tag == "v":
                    self.add(-selector, value if row.target else -value)
                elif value != row.target:
                    self.add(-selector)

        if not nosym and len({row.target for row in table}) == 2:
            self.normalize_nonconstant_circuit(input_count, table)

    def new_var(self):
        self.variables += 1
        return self.variables

    def add(self, *literals):
        self.clauses.append(list(literals))

    def exactly_one(self, selectors):
        self.add(*selectors)
        for first, second in combinations(selectors, 2):
            self.add(-first, -second)

    def wire_selectors(self, real_wire_count):
        selectors = {wire: self.new_var() for wire in range(real_wire_count)}
        selectors[FALSE_WIRE] = self.new_var()
        return selectors

    def wire_value(self, wire, row, row_index):
        # Constants and SAT variable IDs occupy separate namespaces.
        if wire is FALSE_WIRE:
            return "c", False
        if wire < len(row.inputs):
            return "c", row.inputs[wire]
        return "v", self.gates[wire - len(row.inputs)].values[row_index][2]

    def order_gate_inputs(self, index, gate):
        first, second = gate.slots
        second_active = gate.active[1]
        # Slot 2 can only be active on a two-input AND or OR.
        for earlier_wire, later_wire in combinations(range(len(first) - 1), 2):
            self.add(-second_active, -first[later_wire], -second[earlier_wire])

        if index == 0:
            return
        previous = self.gates[index - 1]
        previous_second = previous.slots[1]
        # A circuit can normalize binary FALSE inputs away. Then any adjacent
        # inversion of the two max predecessors can be swapped without a dependency.
        for before, before_selector in previous_second.items():
            later_choices = range(len(second) - 1) if before is FALSE_WIRE else range(before)
            for after in later_choices:
                self.add(-previous.active[1], -second_active, -before_selector, -second[after])

    def normalize_nonconstant_circuit(self, input_count, table):
        # Propagate constant wires through their consumers, bypass copies and
        # repeated operands, and discard gates outside the output's dependency
        # cone. A nonconstant output then needs only real, active operands.
        # Pack these gates first and fill the remaining budget with empty ORs.
        for index, gate in enumerate(self.gates):
            wire = input_count + index
            first_active, second_active = gate.active
            first, second = gate.slots
            self.add(first_active, gate.ops["or"])
            self.add(-first_active, -first[FALSE_WIRE])
            self.add(-second_active, -second[FALSE_WIRE])
            for op in ("and", "or"):
                self.add(-gate.ops[op], -first_active, second_active)
            for predecessor in range(wire):
                self.add(-second_active, -first[predecessor], -second[predecessor])

            self.add(-self.output[wire], first_active)
            if index > 0:
                self.add(-first_active, self.gates[index - 1].active[0])
            later_uses = [slot[wire] for later in self.gates[index + 1:] for slot in later.slots]
            self.add(-first_active, self.output[wire], *later_uses)

            outputs = [z for _, _, z in gate.values]
            self.add(-first_active, *outputs)
            self.add(-first_active, *(-z for z in outputs))
            for primary in range(input_count):
                differs = [-z if row.inputs[primary] else z for row, z in zip(table, outputs)]
                self.add(-first_active, *differs)

    def gate_evaluation(self, gate, x, y, z):
        first_active, second_active = gate.active
        and_op, or_op = gate.ops["and"], gate.ops["or"]
        # Arity zero gives the identity of the op. Arity one copies slot 1.
        self.add(-and_op, first_active, z)
        self.add(-or_op, first_active, -z)
        for op in (and_op, or_op):
            self.add(-op, -first_active, second_active, -x, z)
            self.add(-op, -first_active, second_active, x, -z)

        self.add(-and_op, -second_active, -x, -y, z)
        self.add(-and_op, -second_active, x, -z)
        self.add(-and_op, -second_active, y, -z)
        self.add(-or_op, -second_active, x, y, -z)
        self.add(-or_op, -second_active, -x, z)
        self.add(-or_op, -second_active, -y, z)

        if "not" in gate.ops:
            not_op = gate.ops["not"]
            self.add(-not_op, first_active, z)
            self.add(-not_op, -first_active, x, z)
            self.add(-not_op, -first_active, -x, -z)

    def extract(self, model, missing_wire):
        def selected(selectors):
            wire = next(wire for wire, selector in selectors.items() if selector in model)
            return missing_wire if wire is FALSE_WIRE else wire

        gates = [
            (
                next(op for op, selector in gate.ops.items() if selector in model),
                [selected(slot) for active, slot in zip(gate.active, gate.slots) if active in model],
            )
            for gate in self.gates
        ]
        return gates, selected(self.output)


def solve(encoding, timeout, phases=()):
    with Glucose3(bootstrap_with=encoding.clauses) as solver:
        if phases:
            solver.set_phases(phases)
        start = perf_counter()
        if timeout is None:
            sat = solver.solve()
            elapsed = perf_counter() - start
        else:
            timer = Timer(timeout, solver.interrupt)
            timer.start()
            try:
                sat = solver.solve_limited(expect_interrupt=True)
                elapsed = perf_counter() - start
            finally:
                # Ensure the callback cannot race with deletion of the native solver.
                timer.cancel()
                timer.join()
            if elapsed >= timeout:
                sat = None
        return sat, elapsed, set(solver.get_model()) if sat else None


def lean_proof(identifier, instance, gates, output):
    name = identifier if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*", identifier) else f"«{identifier}»"
    predicate = "Monotone2" if instance.ops == "ao" else "FanInTwo"
    circuit = "PEqualNP.CircuitLowerBounds.Circuit"
    gate_op = "PEqualNP.CircuitLowerBounds.GateOp"
    gate_list = ",\n      ".join(
        f"{{ op := {gate_op}.{op}, inputs := {inputs} }}" for op, inputs in gates
    )
    fan_in = "    simp only [List.not_mem_nil] at hg\n"
    if gates:
        # The singleton membership simplification already leaves a single equality.
        cases = " | ".join(["rfl"] * len(gates))
        fan_in = (
            "    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg\n"
            f"    rcases hg with {cases} <;> simp\n"
        )
    return (
        "import PEqualNP.Defs\n\n"
        f"theorem PEqualNP.Outside.{name} : ∃ C : {circuit},\n"
        f"    PEqualNP.MetaComplexity.{predicate} C ∧ C.size ≤ {instance.bound} ∧\n"
        "    PEqualNP.Represents.Represents\n"
        f"      (fun (u : Fin {instance.rows}) (v : Fin {instance.cols}) =>\n"
        f"        ({instance.mask} : Nat).testBit ({instance.cols} * u.val + v.val)) C := by\n"
        f"  refine ⟨({{ gates := [{gate_list}], output := {output} }} : {circuit}), "
        "?_, by decide, ?_⟩\n"
        "  · intro g hg\n"
        f"{fan_in}"
        "  · decide +kernel\n"
    )


def run(instance, out, identifier, nosym, timeout, hint=None):
    table = truth_table(instance)
    encoding = Encoding(instance, table, nosym)
    phases = ()
    if hint is not None:
        # Prefer the accepted witness during validation without fixing a SAT literal.
        gates, output = hint
        positive = {encoding.output[output]}
        for index, ((op, inputs), gate) in enumerate(zip(gates, encoding.gates)):
            positive.add(gate.ops[op])
            for slot, (active, selectors) in enumerate(zip(gate.active, gate.slots)):
                if slot < len(inputs):
                    positive.update((active, selectors[inputs[slot]]))
                else:
                    positive.add(selectors[FALSE_WIRE])
            for row, (x, y, z) in zip(table, gate.values):
                for wire, var in zip(inputs, (x, y)):
                    if evaluate(gates[:index], wire, row.inputs):
                        positive.add(var)
                if evaluate(gates[:index + 1], instance.input_count + index, row.inputs):
                    positive.add(z)
        phases = [var if var in positive else -var for var in range(1, encoding.variables + 1)]
    sat, elapsed, model = solve(encoding, timeout, phases)
    verdict = "TIMEOUT" if sat is None else "SAT" if sat else "UNSAT"
    summary = (
        f"rows={instance.rows} cols={instance.cols} mask={instance.mask} "
        f"ops={instance.ops} bound={instance.bound} verdict={verdict} "
        f"solve_seconds={elapsed:.6f} vars={encoding.variables} clauses={len(encoding.clauses)}"
    )
    if sat is None:
        print(f"{summary} replay=NA", flush=True)
        return 2
    if not sat:
        summary += " replay=NA"
        out.mkdir(parents=True, exist_ok=True)
        (out / f"{identifier}.verdict.txt").write_text(summary + "\n", encoding="utf-8")
        print(summary, flush=True)
        return 0

    # Use the usual sentinel, or a higher missing wire if 9999 would exist.
    missing_wire = max(9999, instance.input_count + instance.bound)
    gates, output = encoding.extract(model, missing_wire)
    correct = replay(gates, output, table)
    if correct != len(table):
        print(f"{summary} replay=FAILED({correct}/{len(table)})", flush=True)
        return 1

    witness = {
        "rows": instance.rows,
        "cols": instance.cols,
        "mask": instance.mask,
        "ops": instance.ops,
        "bound": instance.bound,
        "gates": [{"op": op, "inputs": inputs} for op, inputs in gates],
        "output": output,
        "solve_seconds": elapsed,
        "vars": encoding.variables,
        "clauses": len(encoding.clauses),
    }
    lean = lean_proof(identifier, instance, gates, output)
    out.mkdir(parents=True, exist_ok=True)
    (out / f"{identifier}.witness.json").write_text(json.dumps(witness, indent=2) + "\n", encoding="utf-8")
    (out / f"{identifier}.lean").write_text(lean, encoding="utf-8")
    print(f"{summary} replay=OK({correct}/{len(table)})", flush=True)
    return 0


def validate_19356(out, nosym, timeout):
    aon = Instance(5, 5, 16237180, "aon", 9)
    ao = Instance(5, 5, 16237180, "ao", 9)
    table = truth_table(aon)
    correct = replay(CORPUS_GATES, 18, table)
    print(f"L-meta-19356 corpus replay={correct}/{len(table)}", flush=True)
    if correct != 25 or len(table) != 25:
        return 1
    aon_status = run(aon, out, "L_meta_19356_aon", nosym, timeout, (CORPUS_ORDERED_GATES, 18))
    ao_status = run(ao, out, "L_meta_19356_ao", nosym, timeout)
    return 1 if 1 in (aon_status, ao_status) else max(aon_status, ao_status)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows", type=int)
    parser.add_argument("--cols", type=int)
    parser.add_argument("--mask", type=int)
    parser.add_argument("--ops", choices=OPS)
    parser.add_argument("--bound", type=int)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--id", help="filename stem and Lean theorem name component")
    parser.add_argument("--nosym", action="store_true")
    parser.add_argument(
        "--timeout", type=float, metavar="SECONDS",
        help="wall-clock solve budget (validation defaults to 600 seconds per solve)",
    )
    parser.add_argument("--validate-19356", action="store_true")
    args = parser.parse_args()

    if args.timeout is not None and (not isfinite(args.timeout) or args.timeout <= 0):
        parser.error("--timeout must be finite and positive")
    instance_args = (args.rows, args.cols, args.mask, args.ops, args.bound)
    if args.validate_19356:
        if any(value is not None for value in (*instance_args, args.id)):
            parser.error("--validate-19356 uses its own instance and IDs")
        out = args.out if args.out is not None else Path("validation")
        timeout = args.timeout if args.timeout is not None else 600
        return validate_19356(out, args.nosym, timeout)

    if any(value is None for value in (*instance_args, args.out)):
        parser.error("--rows, --cols, --mask, --ops, --bound, and --out are required")
    if min(args.rows, args.cols, args.mask, args.bound) < 0:
        parser.error("--rows, --cols, --mask, and --bound must be nonnegative")
    if args.id is not None and (
        not args.id or not args.id.isprintable() or any(char in args.id for char in "/\\«»")
    ):
        parser.error("--id must be a nonempty printable filename component without /, \\, «, or »")
    instance = Instance(*instance_args)
    identifier = args.id or f"mask{args.mask}_{args.rows}x{args.cols}_{args.ops}_k{args.bound}"
    return run(instance, args.out, identifier, args.nosym, args.timeout)


if __name__ == "__main__":
    raise SystemExit(main())
