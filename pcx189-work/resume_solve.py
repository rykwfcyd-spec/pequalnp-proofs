import sys, itertools, json, time
sys.path.insert(0, '.')
from resk import *
from segment_sat import build_hyperedges, solve, AX_LIST
from resk import AXIOM_SET as _AXS
def build_pool(lines): return sorted({L for L in lines if L not in _AXS}, key=repr)
def cline(clause): return frozenset(frozenset({l}) for l in clause)
def perm_line(L, pp, ph):
    return frozenset(frozenset((pp[l[0]], ph[l[1]], l[2]) for l in t) for t in L)

import pickle
depth = pickle.load(open('closure_depth.pkl', 'rb'))
_, klines, _ = extract_191('L_pcx_191.lean')
lines191 = [klines[i] for i in range(22, 55)]
pool_lines = set(lines191)
for pp in itertools.permutations(range(4)):
    for ph in itertools.permutations(range(3)):
        for L in lines191: pool_lines.add(perm_line(L, pp, ph))
def negs(c): return sum(1 for l in c if not l[2])
def allneg(c): return all(not l[2] for l in c)
for c, d in depth.items():
    if len(c) <= 2 or (len(c) <= 3 and d <= 4 and (negs(c) <= 1 or allneg(c))) or \
       (len(c) == 4 and d <= 2 and negs(c) <= 1):
        pool_lines.add(cline(c))
pool_lines.add(frozenset())
axs = AX_LIST
for i, C in enumerate(axs):
    for D in axs[i:]:
        if not (C & D): continue
        for T1 in C:
            for T2 in D:
                U = T1 | T2
                if len(U) > 2: continue
                R = (C - {T1}) | (D - {T2}) | {U}
                if len(R) <= 5: pool_lines.add(R)
pool = build_pool(pool_lines)
print("pool size:", len(pool), flush=True)
edges = build_hyperedges(pool)
print("hyperedges:", sum(len(v) for v in edges.values()), flush=True)
targets = [frozenset({frozenset({(0, j, False)})}) for j in range(3)]
for T in [25, 26, 27, 24, 23]:
    t0 = time.time()
    res = solve(pool, targets, T, edges)
    msg = f"T={T}: {'SAT' if res else 'UNSAT'} in {round(time.time()-t0)}s"
    print(msg, flush=True)
    with open('segment_results.txt', 'a') as f: f.write(msg + "\n")
    if res:
        seq = [pool[i] for i in res]
        json.dump([[sorted([list(l) for l in t]) for t in L] for L in seq],
                  open(f'segment_T{T}.json', 'w'))
        for p, L in enumerate(seq): print(f"  seg{p+1:3d}. {fmt_line(L)}", flush=True)
        break
