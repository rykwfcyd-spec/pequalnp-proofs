import re, sys
sys.path.insert(0, '.')
from resk import *

clauses, klines, src = extract_191('L_pcx_191.lean')
# steps in order: d0..d54 add k0..k54
raw = re.findall(r"IsResKDerivation\.(ax|andIntro|cut) \(C := k(\d+)\)(?: \(D := k(\d+)\))? \(R := k(\d+)\)", src)
raw_ax = len(re.findall(r"IsResKDerivation\.ax ", src))
print("ax steps:", raw_ax, "rule steps with C/D/R:", len(raw))
steps = []
lines = []  # lines[i] = kline at position i
for i in range(22):
    steps.append(('ax', klines[i])); lines.append(klines[i])
assert len(lines) == 22
for rule, ci, di, ri in raw:
    ci, ri = int(ci), int(ri); di = int(di) if di else None
    R = klines[ri]
    assert ri == len(lines), (ri, len(lines))
    if rule == 'andIntro':
        C, D = lines[ci], lines[di]
        found = None
        for T1 in C:
            for T2 in D:
                if (C - {T1}) | (D - {T2}) | {T1 | T2} == R: found = (T1, T2)
        assert found, f"andIntro k{ri} no witness"
        steps.append(('andIntro', R, ci, di, found[0], found[1]))
    elif rule == 'cut':
        C, D = lines[ci], lines[di]
        found = None
        for T in C:
            if not T: continue
            if all(frozenset({neg(l)}) in D for l in T):
                negs = frozenset(frozenset({neg(l)}) for l in T)
                if (C - {T}) | (D - negs) == R: found = T
        assert found, f"cut k{ri} no witness"
        steps.append(('cut', R, ci, di, found))
    lines.append(R)
ok, msg = check_proof(steps)
print(msg)
assert ok
import json
def enc_line(line): return sorted([sorted([list(l) for l in t]) for t in line])
json.dump({'n': len(steps)}, open('verify191.json','w'))
print("191 proof replayed and verified: 55 lines")
