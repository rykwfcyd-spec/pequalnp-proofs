#!/usr/bin/env python3
import sys, pickle, itertools, json, time
sys.path.insert(0, '.')
from resk import *
from segment_sat import build_hyperedges, solve, AX_LIST
from resk import AXIOM_SET as _AXS
def build_pool(lines):
    return sorted({L for L in lines if L not in _AXS}, key=repr)

def cline(clause): return frozenset(frozenset({l}) for l in clause)

def perm_line(L, pp, ph):
    # pp: pigeon perm (tuple of 4), ph: hole perm (tuple of 3)
    return frozenset(frozenset((pp[l[0]], ph[l[1]], l[2]) for l in t) for t in L)

def main():
    depth = pickle.load(open('closure_depth.pkl', 'rb'))
    clauses191, klines, src = extract_191('L_pcx_191.lean')
    lines191 = [klines[i] for i in range(22, 55)]
    pool_lines = set(lines191)
    # symmetry orbit of 191 lines (full S4 x S3)
    for pp in itertools.permutations(range(4)):
        for ph in itertools.permutations(range(3)):
            for L in lines191:
                pool_lines.add(perm_line(L, pp, ph))
    print("after orbit:", len(pool_lines), flush=True)
    # closure clauses: width<=3 & depth<=5 & (negs<=1 or all-neg); width4 & depth<=3 & negs<=1; all width<=2
    def negs(c): return sum(1 for l in c if not l[2])
    def allneg(c): return all(not l[2] for l in c)
    for c, d in depth.items():
        if len(c) <= 2 or (len(c) <= 3 and d <= 5 and (negs(c) <= 1 or allneg(c))) or \
           (len(c) == 4 and d <= 3 and negs(c) <= 1):
            pool_lines.add(cline(c))
    pool_lines.add(frozenset())
    print("after closure:", len(pool_lines), flush=True)
    # andIntro products of axiom pairs (<=6 terms)
    axs = AX_LIST
    for i, C in enumerate(axs):
        for D in axs[i:]:
            for T1 in C:
                for T2 in D:
                    U = T1 | T2
                    if len(U) > 2: continue
                    R = (C - {T1}) | (D - {T2}) | {U}
                    if len(R) <= 5: pool_lines.add(R)
    print("after axiom andIntro:", len(pool_lines), flush=True)
    # andElim closure (one step) of pool lines
    extra = set()
    for L in pool_lines:
        for T in L:
            if len(T) == 2:
                for l in T:
                    extra.add((L - {T}) | {frozenset({l})})
    pool_lines |= extra
    print("after andElim closure:", len(pool_lines), flush=True)
    pool = build_pool(pool_lines)
    print("pool size:", len(pool), flush=True)
    pickle.dump(pool, open('pool.pkl', 'wb'))
    t0 = time.time()
    edges = build_hyperedges(pool)
    print("hyperedges:", sum(len(v) for v in edges.values()), "for", len(edges), "results; build", round(time.time()-t0), "s", flush=True)
    pickle.dump(edges, open('edges.pkl', 'wb'))
    targets = [frozenset()]
    for T in [int(x) for x in sys.argv[1:]] or [28]:
        t0 = time.time()
        res = solve(pool, targets, T, edges)
        print(f"T={T}: {'SAT' if res else 'UNSAT'} in {round(time.time()-t0)}s", flush=True)
        if res:
            seq = [pool[i] for i in res]
            json.dump([[sorted([list(l) for l in t]) for t in L] for L in seq],
                      open(f'solution_T{T}.json', 'w'))
            for p, L in enumerate(seq):
                print(f"  {p+23:3d}. {fmt_line(L)}")
            break

if __name__ == '__main__':
    main()
