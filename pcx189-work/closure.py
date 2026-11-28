import sys
sys.path.insert(0, '.')
from resk import php_clauses, neg

def resolvents(c1, c2):
    out = []
    for l in c1:
        if neg(l) in c2:
            r = (c1 - {l}) | (c2 - {neg(l)})
            if any(neg(x) in r for x in r): continue  # tautology
            out.append(frozenset(r))
    return out

cls = set(php_clauses())
print("axioms:", len(cls))
changed = True
rounds = 0
while changed:
    changed = False; rounds += 1
    cur = list(cls)
    new = set()
    for i in range(len(cur)):
        for j in range(i+1, len(cur)):
            for r in resolvents(cur[i], cur[j]):
                if len(r) <= 6 and r not in cls: new.add(r)
    # subsumption: drop clauses subsumed by another (keep minimal)
    new = {r for r in new if not any(o < r for o in cls)}
    if new:
        cls |= new; changed = True
    print(f"round {rounds}: total {len(cls)}")
from collections import Counter
print(Counter(len(c) for c in cls))
import pickle
pickle.dump(cls, open('closure.pkl','wb'))
