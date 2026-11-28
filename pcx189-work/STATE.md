# L-pcx-189 work state (muse, started 2026-11-28 14:55 JST, deadline 19:30 JST)
Task (Claude via Issue #39 comment 7234912598): Res(2) refutation of PHP(4 pigeons, 3 holes) in <= 50 lines.
Rules: PEqualNP/Defs/ProofComplexityResK.lean (ax/weak/andIntro/andElim/cut, terms <= 2 literals).
Known: L_pcx_191 accepted (55-line ordinary resolution, bound 57). L_pcx_188 accepted (<=43 impossible).
astra: 53 lines, shrinking from above. Muse: build from below using 188's forced structure. No desk access.
Deliverable: line sequence (rule + premise line numbers) + own checker PASS, posted to Issue #39. Checkpoints pushed to fork branch muse/pcx189-work.
## Progress
- [ ] fetch upstream main; read ProofComplexityResK.lean, PHP def, L_pcx_188, L_pcx_191
- [ ] write independent Res(2) checker (python)
- [ ] extract 188's structural constraints
- [ ] search for <=50-line refutation
- [ ] verify + post to Issue #39

## Baseline verified (2026-11-28 15:0x JST)
- Rules extracted exactly from ProofComplexityResK.lean; PHP(4,3): 22 clauses (4 pigeon + 18 hole), vars (i,j) in Fin4 x Fin3.
- L_pcx_191 extracted mechanically (55 lines: 22 ax + 3 andIntro + 30 cut) and replayed in my own checker resk.py: PASS (verify191.py).
- 191 cost map: axioms 22 (all necessary: dropping any PHP clause makes it SAT), andIntro A_j = ((~x1j&~x3j)|~x2j) x3, middle game 18 lines -> sums S_j = x1j|x2j|x3j (k32/k38/k42), strip 3/hole -> units ~x00,~x01,~x02, final 3 cuts vs k0 -> empty.
- L_pcx_188: counting bound over 22 assignment groups (4 pigeon pts + 18 hole-pair pts); every axiom misses <= 1 point. Minimum 44. Target <= 50 = save >= 5 derived lines vs 191.
- astra at 53 (top-down). Muse lane: bottom-up restructure.

## Search design (15:3x)
- Full-proof SAT v1 OOM'd: pool 3191, 364k hyperedges, 24.2M clauses.
- v2: segment SAT (axioms -> units ~x00,~x01,~x02), tighter pool (~1.6k), pruned hyperedges
  (andIntro only when premises share a term; cut result <= max premise terms + 1).
  Segment budget 25 -> total 22 + 25 + 3 final = 50.
