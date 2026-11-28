#!/usr/bin/env python3
"""Positional SAT search for a short Res(2) refutation (v2 encoding).

Positions 1..T hold DERIVED lines; axioms are free premises.
- x[p][i]: position p holds pool line i
- A[p][i]: pool line i available before position p
- s[(i,h)]: hyperedge h is the chosen justification of pool line i
Hyperedge: (kind, p1, p2): kind in {'un','sym','cut'}; p1/p2 are pool indices
or -1 (axiom). 'un': unary (andElim) with premise p1. 'sym': andIntro with
premises {p1,p2}. 'cut': ordered (owner p1, other p2).
"""
import sys, itertools
sys.path.insert(0, '.')
from resk import AXIOM_SET, neg
from pysat.solvers import Glucose3
from pysat.card import CardEnc, EncType

AX_LIST = sorted(AXIOM_SET, key=repr)

def build_hyperedges(pool):
    index = {L: i for i, L in enumerate(pool)}
    def ref(L):
        if L in index: return index[L]
        if L in AXIOM_SET: return -1
        return None
    edges = {}
    def add(R, h):
        r = ref(R)
        if r is None or r < 0: return
        edges.setdefault(r, set()).add(h)
    sources = [(L, ref(L)) for L in pool] + [(L, -1) for L in AX_LIST]
    for C, rc in sources:
        for T in C:
            if len(T) < 2: continue
            for r in range(1, len(T)):
                for s in itertools.combinations(T, r):
                    add((C - {T}) | {frozenset(s)}, ('un', rc, -1))
    varset = {id(L): {l[0:2] for t in L for l in t} for L, _ in sources}
    n = len(sources)
    for si in range(n):
        C, rc = sources[si]
        for sj in range(si, n):
            D, rd = sources[sj]
            if not (varset[id(C)] & varset[id(D)]): continue
            if C & D:
                for T1 in C:
                    for T2 in D:
                        U = T1 | T2
                        if len(U) > 2 or len(U) < max(len(T1), len(T2)): continue
                        add((C - {T1}) | (D - {T2}) | {U}, ('sym', min(rc, rd), max(rc, rd)))
            for (A, B, ra, rb) in ((C, D, rc, rd), (D, C, rd, rc)):
                if A is B: continue
                for T in A:
                    if not T: continue
                    if all(frozenset({neg(l)}) in B for l in T):
                        negs = frozenset(frozenset({neg(l)}) for l in T)
                        R = (A - {T}) | (B - negs)
                        if len(R) <= max(len(A), len(B)) + 1:
                            add(R, ('cut', ra, rb))
    return {k: sorted(v) for k, v in edges.items()}

def solve(pool, targets, T, edges):
    index = {L: i for i, L in enumerate(pool)}
    n = len(pool)
    NXT = [1]
    def newvar():
        v = NXT[0]; NXT[0] += 1; return v
    X = [[newvar() for _ in range(n)] for _ in range(T)]
    A = [[newvar() for _ in range(n)] for _ in range(T + 1)]
    clauses = []
    for i in range(n): clauses.append([-A[0][i]])
    for p in range(T):
        enc = CardEnc.atmost(lits=[X[p][i] for i in range(n)], bound=1,
                             top_id=NXT[0] - 1, encoding=EncType.seqcounter)
        clauses += enc.clauses; NXT[0] = enc.nv + 1
        clauses.append([X[p][i] for i in range(n)])
        for i in range(n):
            clauses.append([-A[p][i], A[p + 1][i]])
            clauses.append([-X[p][i], A[p + 1][i]])
            clauses.append([-A[p + 1][i], A[p][i], X[p][i]])
    # support vars and justification
    for i in range(n):
        es = edges.get(i, [])
        if not es:
            for p in range(T): clauses.append([-X[p][i]])
            continue
        svars = []
        for h in es:
            s = newvar(); svars.append(s)
            kind, p1, p2 = h
            prems = []
            if kind == 'un': prems = [p1]
            elif kind == 'sym': prems = [p1, p2]
            else: prems = [p1, p2]
            prems = [q for q in prems if q >= 0]
            for p in range(T):
                for q in prems:
                    clauses.append([-X[p][i], -s, A[p][q]])
        for p in range(T):
            clauses.append([-X[p][i]] + svars)
    for t in targets:
        ti = index[t]
        clauses.append([X[p][ti] for p in range(T)])
    print(f"vars {NXT[0]-1} clauses {len(clauses)}", flush=True)
    with Glucose3(bootstrap_with=clauses) as s:
        sat = s.solve()
        if not sat: return None
        model = set(s.get_model())
        return [next(i for i in range(n) if X[p][i] in model) for p in range(T)]
