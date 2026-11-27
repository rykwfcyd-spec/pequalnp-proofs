#!/usr/bin/env python3
"""Exact AON fan-in-2 circuit synthesis for a fixed Boolean function given
as a truth table over n input bits. Selector encoding in the style of the
two-lit family solver: per gate, exactly-one selectors for operand A and B
over (inputs + earlier gates + FALSE pseudo-wire) and an op selector over
{AND, OR, NOT}. Wire values are per-row SAT variables tied to the selected
operands' row values. SAT result is replay-verified in plain Python before
anything is emitted."""
import sys, json, itertools, time
sys.path.insert(0, '/home/hatch/workspace/pequalnp-verify/search-venv/lib/python3.13/site-packages')
from pysat.solvers import Glucose3

def build(n_in, table, K):
    # wires: 0..n_in-1 inputs, n_in..n_in+K-1 gates, FALSE = n_in+K (const 0)
    NW = n_in + K + 1
    FALSE_W = n_in + K
    rows = list(itertools.product([0,1], repeat=n_in))
    assert len(rows) == len(table)
    top = 0
    def var():
        nonlocal top; top += 1; return top
    # selectors: selA[g][w], selB[g][w], op[g][0=AND,1=OR,2=NOT]
    selA = [[var() for _ in range(NW)] for _ in range(K)]
    selB = [[var() for _ in range(NW)] for _ in range(K)]
    opv = [[var() for _ in range(3)] for _ in range(K)]
    # wire value vars: wv[g][r]
    wv = [[var() for _ in rows] for _ in range(K)]
    out_sel = [var() for _ in range(NW)]
    clauses = []
    def exactly_one(lits):
        clauses.append(list(lits))
        for a, b in itertools.combinations(lits, 2):
            clauses.append([-a, -b])
    for g in range(K):
        avail = list(range(0, n_in + g)) + [FALSE_W]
        for w in range(NW):
            if w not in avail:
                clauses.append([-selA[g][w]]); clauses.append([-selB[g][w]])
        exactly_one([selA[g][w] for w in avail])
        exactly_one([selB[g][w] for w in avail])
        exactly_one(opv[g])
    exactly_one(out_sel)
    # operand value vars: av[g][r], bv[g][r]
    def row_wire_val(w, r):
        if w < n_in: return ('c', rows[r][w])
        if w == FALSE_W: return ('c', 0)
        return ('v', wv[w - n_in][r])
    def tie(sel, g, r, out_lit):
        # out_lit (a fresh var) equals the value of the selected operand on row r
        for w in range(NW):
            tag, v = row_wire_val(w, r)
            s = sel[g][w]
            if tag == 'c':
                if v == 1: clauses.append([-s, out_lit])
                else: clauses.append([-s, -out_lit])
            else:
                clauses.append([-s, -v, out_lit]); clauses.append([-s, v, -out_lit])
    for g in range(K):
        for r in range(len(rows)):
            av = var(); bv = var()
            tie(selA, g, r, av); tie(selB, g, r, bv)
            o = wv[g][r]
            a_, o_, n_ = opv[g]
            # AND: o <-> av & bv ; OR: o <-> av | bv ; NOT: o <-> ~av
            clauses += [[-a_, -av, -bv, o], [-a_, av, -o], [-a_, bv, -o]]
            clauses += [[-o_, av, bv, -o], [-o_, -av, o], [-o_, -bv, o]]
            clauses += [[-n_, av, o], [-n_, -av, -o]]
    # output constraint
    for r in range(len(rows)):
        t = table[r]
        for w in range(NW):
            tag, v = row_wire_val(w, r)
            s = out_sel[w]
            if tag == 'c':
                if v != t: clauses.append([-s])
            else:
                if t == 1: clauses.append([-s, v])
                else: clauses.append([-s, -v])
    meta = dict(selA=selA, selB=selB, opv=opv, wv=wv, out_sel=out_sel, FALSE_W=FALSE_W)
    return clauses, meta, rows

def extract(model, meta, n_in, K):
    m = set(model)
    gates = []
    for g in range(K):
        a = next(w for w in range(len(meta['selA'][g])) if meta['selA'][g][w] in m)
        b = next(w for w in range(len(meta['selB'][g])) if meta['selB'][g][w] in m)
        o = next(i for i in range(3) if meta['opv'][g][i] in m)
        gates.append((['and','or','not'][o], a, b))
    out = next(w for w in range(len(meta['out_sel'])) if meta['out_sel'][w] in m)
    return gates, out

def replay(n_in, table, gates, out):
    rows = list(itertools.product([0,1], repeat=n_in))
    FW = n_in + len(gates)
    for r, row in enumerate(rows):
        wires = list(row) + [0]*len(gates)
        for g, (op, a, b) in enumerate(gates):
            va = wires[a] if a < len(wires) else 0
            vb = wires[b] if b < len(wires) else 0
            if a == FW: va = 0
            if b == FW: vb = 0
            wires[n_in+g] = (va & vb) if op=='and' else (va | vb) if op=='or' else (1-va)
        val = wires[out] if out < len(wires) else 0
        if out == FW: val = 0
        if val != table[r]: return False
    return True

def solve(n_in, table, K, timeout_s=1200):
    clauses, meta, rows = build(n_in, table, K)
    print(f"vars~{meta['wv'][-1][-1]} clauses={len(clauses)} rows={len(rows)} K={K}", flush=True)
    s = Glucose3(bootstrap_with=clauses)
    t0 = time.time()
    res = s.solve()
    dt = time.time() - t0
    if not res:
        print(f"UNSAT solve_seconds={dt:.2f}"); return None
    gates, out = extract(s.get_model(), meta, n_in, K)
    ok = replay(n_in, table, gates, out)
    print(f"SAT solve_seconds={dt:.2f} replay={'OK' if ok else 'FAIL'}")
    if not ok: sys.exit(1)
    return gates, out

def colour3_table(nv):
    edges = [(i, j) for i in range(nv) for j in range(i+1, nv)]
    table = []
    for bits in itertools.product([0,1], repeat=len(edges)):
        E = [edges[k] for k in range(len(edges)) if bits[k]]
        ok = False
        for col in itertools.product(range(3), repeat=nv):
            if all(col[i] != col[j] for i, j in E): ok = True; break
        table.append(1 if ok else 0)
    return len(edges), table

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'selftest':
        ne, table = colour3_table(4)
        print("4-vertex 3-colourability: edge bits", ne, "positives", sum(table))
        for K in range(1, 12):
            r = solve(ne, table, K)
            if r: print("min gates (4v):", K); break
    elif mode == 'solve5':
        K = int(sys.argv[2])
        ne, table = colour3_table(5)
        print("5-vertex 3-colourability: edge bits", ne, "positives", sum(table), "target K", K, flush=True)
        r = solve(ne, table, K)
        if r:
            gates, out = r
            json.dump({'gates': gates, 'output': out, 'n_in': ne, 'K': K},
                      open('/home/hatch/workspace/pequalnp-verify/attack/17732/witness.json', 'w'), indent=1)
            print("witness saved")
