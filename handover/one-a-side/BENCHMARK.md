# One-a-side promise SAT benchmarks

## Corpus semantics

For a `rows × cols` instance, the graph is `A : Fin rows → Fin cols → Bool`, with
`A u v = (mask : Nat).testBit (cols * u.val + v.val)`. Each promise input has
`rows + cols` wires. Exactly the left wire `u.val` and right wire `rows + v.val`
are true. The encoding constrains exactly those `rows * cols` inputs. The
rectangular `col_reader` example in the corpus uses `Fin 4`, `Fin 5`, and a stride
of `5`. [L_meta_9410.lean](../../lean/PEqualNP/Outside/L_meta_9410.lean#L501)

`oneEach` and `Represents` are defined as follows. [Represents.lean](../../lean/PEqualNP/Defs/Represents.lean)

```lean
def oneEach {n m : ℕ} (u : Fin n) (v : Fin m) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i = u)) ++ List.ofFn (fun j : Fin m => decide (j = v))

def Represents {n m : ℕ} (A : Fin n → Fin m → Bool) (C : Circuit) : Prop :=
  ∀ (u : Fin n) (v : Fin m), C.eval (oneEach u v) = A u v
```

Gate `j` produces wire `rows + cols + j`. An unavailable wire reads `false` at
the time of the read, including at output selection. The relevant cases of
`GateOp.eval` and the circuit definitions are below. In particular, empty AND is
true, empty OR is false, and NOT uses its first input with an empty-list default
of false. [CircuitLowerBounds.lean](../../lean/PEqualNP/Defs/CircuitLowerBounds.lean)

```lean
def GateOp.eval : GateOp → List Bool → Bool
  | GateOp.and, l => l.all id
  | GateOp.or, l => l.any id
  | GateOp.not, l => !(l.headD false)

def Circuit.wires (C : Circuit) (x : List Bool) : List Bool :=
  C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def Circuit.eval (C : Circuit) (x : List Bool) : Bool :=
  (C.wires x).getD C.output false

def Circuit.size (C : Circuit) : ℕ :=
  C.gates.length
```

`--ops aon` uses `FanInTwo`. [MetaComplexity.lean](../../lean/PEqualNP/Defs/MetaComplexity.lean)

```lean
def FanInTwo (C : PEqualNP.CircuitLowerBounds.Circuit) : Prop :=
  ∀ g ∈ C.gates,
    g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
    g.inputs.length ≤ 2
```

`--ops ao` uses `Monotone2`. [MetaComplexityLgpMono.lean](../../lean/PEqualNP/Defs/MetaComplexityLgpMono.lean)

```lean
def Monotone2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
```

The encoding allocates exactly `K` gates, with selectable output among all real
wires and the `FALSE` pseudo-wire. A smaller circuit can keep its output while
appending empty OR gates. Removing a NOT's ignored second input preserves its
value. Operands have exactly-one selectors, and arity flags determine which
selected operands a gate evaluates. A missing wire is emitted as `9999` for all
runs here. When `9999` can be a real wire, extraction uses `rows + cols + K` so the
emitted index still reads false. All SAT circuits are replayed in list order on
every promise row before their JSON and Lean files are written.

## Symmetry and orientation

With symmetry enabled, inactive selectors choose `FALSE` and two active real
operands are ordered by wire index. The slot 2 indices of consecutive binary
gates are nondecreasing, treating `FALSE` as greater than any real wire. Both
requested orderings are sound. Binary AND/OR gates that read `FALSE` can first
become an empty OR or a copy. For two adjacent binary gates with real operands,
the larger operand index is in slot 2. If those indices are inverted, the later
gate cannot read the earlier gate's output, whose index exceeds both operands of
the earlier gate. Swapping the gates and remapping their output wire references
decreases the slot 2 sequence lexicographically. Repeating this step yields the
required order.

For nonconstant tables, symmetry mode also uses a compact circuit. On the
promise, constant gate results can be propagated into consumers, copies and
primary-equivalent gates can be bypassed, and unused gates can be discarded.
AND/OR gates with duplicate operands become copies. The remaining gates can be
ordered as above and padded at the end with empty OR gates. `--nosym` disables
both the ordering and these canonical choices.

The corpus specifies the stride once the left and right dimensions are known.
The benchmark label “4 by 5” could assign those dimensions in either order. The
primary runs use four left vertices and five right vertices. A `TRANSPOSED` run
would reinterpret the same integer with five left vertices, four right vertices
and stride four, keeping the numeric mask fixed.

## Validation

The accepted L-meta-19356 circuit replayed **25/25** with its original gate
order, inputs, and output wire `18`. Its validation SAT run uses the same witness
reordered for symmetry as Glucose3 phase preferences. These preferences leave
all CNF variables free. The `ao` validation run and benchmark searches use the
solver's default phases. [L_meta_19356.lean](../../lean/PEqualNP/Outside/L_meta_19356.lean)

| Gate basis | Bound | Verdict | Solve seconds | Vars | Clauses | Replay | Witness |
| --- | ---: | --- | ---: | ---: | ---: | --- | --- |
| `aon` | 9 | SAT | 0.000958 | 1,010 | 16,502 | 25/25 | [JSON](validation/L_meta_19356_aon.witness.json), [Lean](validation/L_meta_19356_aon.lean) |
| `ao` | 9 | TIMEOUT | 120.482297 | 1,001 | 15,800 | — | — |

The validation command used `--timeout 120` for each of its two SAT calls.

Independent enumeration also agreed with Glucose3 for each of the 16 `2×2`
masks under each gate basis, at bounds 1 and 2, in both symmetry modes. The
same comparison at bound 2 covered all 64 masks in each orientation of `2×3`.

An independent bitset evaluator confirmed all three saved JSON witnesses.
Lean 4.36.0 kernel-checked all three theorem bodies in a temporary file with
`import PEqualNP.Defs.Represents`. The emitted files use the requested
`import PEqualNP.Defs`. Local checks with that broader import timed out.

## Benchmark method

Runs use Glucose3 from the repository's `search-venv` (`python-sat 1.9.dev25`).
Times are wall seconds inside the solve call and exclude CNF construction,
solver initialization, and witness replay. Variable and clause counts are for
the emitted CNF before Glucose3 simplifies it. Up to four benchmark solves run
concurrently. Each benchmark solve has a 600-second wall-clock budget.
On expiry, the timer interrupts Glucose3. Reported TIMEOUT times include the
delay until the native solver returns control to Python.

Reproduce the first primary run from this directory with the following command.

```sh
../../search-venv/bin/python solver.py --rows 4 --cols 5 --mask 39737 \
  --ops ao --bound 8 --out witnesses --id L_meta_20920_ao --timeout 600
```

## Benchmark results

| Instance | Run | Dimensions | Mask | Ops | Bound | Verdict | Solve seconds | Vars | Clauses | Artifact |
| --- | --- | --- | ---: | --- | ---: | --- | ---: | ---: | ---: | --- |
| L-meta-20920 | Primary | 4×5 | 39737 | `ao` | 8 | UNSAT | 105.557420 | 746 | 10,630 | [Verdict](witnesses/L_meta_20920_ao.verdict.txt) |
| L-meta-20920 | Primary `--nosym` | 4×5 | 39737 | `ao` | 8 | TIMEOUT | 600.027599 | 746 | 9,200 | — |
| L-meta-20920 | Secondary | 4×5 | 39737 | `aon` | 8 | SAT, 8 gates | 3.165133 | 754 | 11,134 | [JSON](witnesses/L_meta_20920_aon.witness.json), [Lean](witnesses/L_meta_20920_aon.lean) |
| L-meta-20920 | TRANSPOSED | 5×4 | 39737 | `ao` | 8 | SAT, 8 gates | 4.122023 | 746 | 10,630 | [JSON](witnesses/L_meta_20920_ao_5x4_transposed.witness.json), [Lean](witnesses/L_meta_20920_ao_5x4_transposed.lean) |
| L-meta-21143 | Primary | 4×5 | 39288 | `ao` | 10 | TIMEOUT | 601.312512 | 950 | 14,656 | — |
| L-meta-19638 | Primary | 5×5 | 12059857 | `aon` | 9 | TIMEOUT | 600.096438 | 1,010 | 16,460 | — |
| L-meta-21127 | Primary | 4×5 | 36247 | `ao` | 10 | TIMEOUT | 618.913354 | 950 | 14,662 | — |

Both L-meta-20920 SAT witnesses replayed **20/20**. Its `--nosym` confirmation
was inconclusive within the timeout. The other three secondary runs were
skipped because their primary solves exceeded 300 seconds. The swapped-dimension
check was triggered only for L-meta-20920.
