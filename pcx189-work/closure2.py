import sys, pickle
sys.path.insert(0, '.')
from resk import php_clauses, neg
from collections import defaultdict

depth = {}
for c in php_clauses(): depth[c] = 0
by_lit = defaultdict(set)
for c in depth: 
    for l in c: by_lit[l].add(c)
frontier = list(depth)
d = 0
while frontier and d < 8:
    d += 1
    new = {}
    for c in frontier:
        for l in c:
            for c2 in by_lit[neg(l)]:
                if c2 is c: continue
                r = (c - {l}) | (c2 - {neg(l)})
                if len(r) > 5: continue
                if any(neg(x) in r for x in r): continue
                if r in depth or r in new: continue
                # subsumption: skip if an existing clause is a proper subset
                if any(o < r for o in depth): continue
                new[r] = d
    for r in new:
        depth[r] = d
        for l in r: by_lit[l].add(r)
    frontier = list(new)
    print(f"depth {d}: +{len(new)} total {len(depth)}", flush=True)
pickle.dump(depth, open('closure_depth.pkl','wb'))
from collections import Counter
print(Counter(depth.values()))
print("width dist:", Counter(len(c) for c in depth))
