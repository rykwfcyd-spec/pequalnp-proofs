#!/usr/bin/env python3
"""Res(2) for PHP(4,3): exact checker per PEqualNP/Defs/ProofComplexityResK.lean,
plus an extractor for the L_pcx_191 proof.

Representation:
- literal: (i, j, pol) with i in 0..3 (pigeon), j in 0..2 (hole), pol True/False.
  Lean literal is ((i, j), pol).
- term: frozenset of literals (conjunction). Line: frozenset of terms (disjunction).
- axiom lines: for each PHP clause C, the line { {l} : l in C }.
Rules (each step appends ONE line; premises are earlier lines):
- ax: line in AXIOMS, all terms card <= 2.
- weak: from line C in pi, new D with C subset D, all terms card <= 2.
- andIntro: from C, D: choose T1 in C, T2 in D; R = (C-{T1}) | (D-{T2}) | {T1|T2}; all terms <= 2.
- andElim: from C: choose T in C, nonempty T' subset T; R = (C-{T}) | {T'}.
- cut: from C, D: choose nonempty T in C such that for every l in T, {neg l} in D;
  R = (C-{T}) | (D - { {neg l} : l in T }).
Refutation: some line is the empty line (no terms). Length = number of lines.
"""
import re, sys

def lit(i, j, pol): return (i, j, pol)
def neg(l): return (l[0], l[1], not l[2])

# PHP(4,3) clauses
def php_clauses():
    cls = []
    for i in range(4):
        cls.append(frozenset(lit(i, j, True) for j in range(3)))
    for j in range(3):
        for i in range(4):
            for i2 in range(i+1, 4):
                cls.append(frozenset({lit(i, j, False), lit(i2, j, False)}))
    return cls

AXIOMS = [frozenset(frozenset({l}) for l in c) for c in php_clauses()]
AXIOM_SET = set(AXIOMS)

def term_ok(line, k=2):
    return all(len(t) <= k for t in line)

def check_proof(steps):
    """steps: list of (rule, result_line, premises...) in derivation order.
    Each step is a tuple:
      ('ax', line)
      ('weak', line, src_idx)
      ('andIntro', line, c_idx, d_idx, T1, T2)
      ('andElim', line, c_idx, T, Tp)
      ('cut', line, c_idx, d_idx, T)
    Returns (ok, message)."""
    lines = []
    for n, st in enumerate(steps):
        rule = st[0]
        if rule == 'ax':
            line = st[1]
            if line not in AXIOM_SET: return False, f"step {n}: ax line not an axiom"
            if not term_ok(line): return False, f"step {n}: ax term too big"
        elif rule == 'weak':
            _, line, ci = st
            if not (lines[ci] <= line): return False, f"step {n}: weak not a superset"
            if not term_ok(line): return False, f"step {n}: weak term too big"
        elif rule == 'andIntro':
            _, line, ci, di, T1, T2 = st
            C, D = lines[ci], lines[di]
            if T1 not in C or T2 not in D: return False, f"step {n}: andIntro term missing"
            R = (C - {T1}) | (D - {T2}) | {T1 | T2}
            if R != line: return False, f"step {n}: andIntro result mismatch"
            if not term_ok(line): return False, f"step {n}: andIntro term too big"
        elif rule == 'andElim':
            _, line, ci, T, Tp = st
            C = lines[ci]
            if T not in C or not Tp or not (Tp <= T): return False, f"step {n}: andElim bad"
            R = (C - {T}) | {Tp}
            if R != line: return False, f"step {n}: andElim result mismatch"
        elif rule == 'cut':
            _, line, ci, di, T = st
            C, D = lines[ci], lines[di]
            if T not in C or not T: return False, f"step {n}: cut term missing/empty"
            negs = frozenset(frozenset({neg(l)}) for l in T)
            if not all(frozenset({neg(l)}) in D for l in T):
                return False, f"step {n}: cut negations missing in D"
            R = (C - {T}) | (D - negs)
            if R != line: return False, f"step {n}: cut result mismatch"
        else:
            return False, f"step {n}: unknown rule {rule}"
        lines.append(line)
    if frozenset() not in lines: return False, "no empty line derived"
    return True, f"PASS: {len(lines)} lines, empty line at index {lines.index(frozenset())}"

def fmt_lit(l):
    return ("x" if l[2] else "~x") + f"{l[0]}{l[1]}"
def fmt_term(t):
    if not t: return "TRUE"
    return "(" + "&".join(sorted(fmt_lit(l) for l in t)) + ")" if len(t) > 1 else fmt_lit(next(iter(t)))
def fmt_line(line):
    if not line: return "EMPTY"
    return " | ".join(sorted(fmt_term(t) for t in line))

# ---------- extraction of L_pcx_191 ----------
LIT_RE = re.compile(r"\(\((\d), (\d)\), (true|false)\)")

def parse_clause(s):
    return frozenset((int(a), int(b), c == 'true') for a, b, c in LIT_RE.findall(s))

def parse_kterm(s):
    return frozenset((int(a), int(b), c == 'true') for a, b, c in LIT_RE.findall(s))

def extract_191(path):
    src = open(path).read()
    clauses = {}
    for m in re.finditer(r"def c(\d+) : Clause VV := \(\{(.*?)\} : Clause VV\)", src, re.S):
        clauses[int(m.group(1))] = parse_clause(m.group(2))
    for m in re.finditer(r"def c(\d+) : Clause VV := \(∅ : Clause VV\)", src):
        clauses[int(m.group(1))] = frozenset()
    klines = {}
    for m in re.finditer(r"def k(\d+) : KLine VV := kLineOfClause c(\d+)", src):
        c = clauses[int(m.group(2))]
        klines[int(m.group(1))] = frozenset(frozenset({l}) for l in c)
    for m in re.finditer(r"def k(\d+) : KLine VV := \(\{(.*?)\} : KLine VV\)", src, re.S):
        body = m.group(2)
        terms = re.findall(r"\(\{(.*?)\} : KTerm VV\)", body, re.S)
        klines[int(m.group(1))] = frozenset(parse_kterm(t) for t in terms)
    steps = []
    for m in re.finditer(r"IsResKDerivation\.(ax|weak|andIntro|andElim|cut) \(C := k(\d+)\)(?: \(D := k(\d+)\))? \(R := k(\d+)\)", src):
        steps.append(m)
    return clauses, klines, src

if __name__ == '__main__':
    clauses, klines, src = extract_191('/home/hatch/workspace/pequalnp-verify/attack/pcx189/L_pcx_191.lean')
    print("clauses:", len(clauses), "klines:", len(klines))
    for i in sorted(klines):
        print(f"k{i:2d} = {fmt_line(klines[i])}")
