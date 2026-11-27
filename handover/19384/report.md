# L-meta-19384 report

**Verdict for the unrestricted reading** — reduced-to-one-lemma. The proof covers all 512 graphs at `n = 3`, in the budget and minimum-size forms for both gate conventions. The sole admitted declaration, `complement_sizeAtMost_ge_four`, asks for the `2n - 4` construction for arbitrary `n ≥ 4` in the `Monotone2` model.

Direct De Morgan dualization needs to supply the missing input polarities. The prefix and suffix construction gives an overhead of `6n - 12`, while the target allows `2n - 4`. The corpus theorem `L_meta_19123` gives a sharp example for every `n ≥ 3`: the single edge needs one gate, and its complement needs exactly `2n - 3`. The unrestricted bound has no proof or counterexample in this package.

**Desk match** — nearby bipartite graph statements support `Monotone2`. Confidence is low on the precise scope of “Small cases only” because the title supplies no cutoff or circuit-size restriction. If the desk restricts to `n = 3`, both gate conventions are covered. If it requires all `n ≥ 3`, the named lemma remains open. The statement notes also give a paper proof for arbitrary `n ≥ 3` when the complement takes at most two gates.

## Verification

Lean 4.36.0 compiled the scratch module against the project's existing Lake cache. The project source directory is mounted read-only, so the module was compiled from a temporary `PEqualNP/Outside/Scratch19384.lean` copy with its output outside the project. This sandbox also required a temporary process-path shim for Lean to resolve its own executable through `/proc/self/exe`. The scratch compilation exited successfully in about 5 minutes 38 seconds. The exact-two minimum-size theorem was compiled separately against the resulting scratch module.

All four `n = 3` declarations report only `propext`, `Classical.choice`, and `Quot.sound`. The two unrestricted declarations additionally report `sorryAx` through `complement_sizeAtMost_ge_four`. An independent truth-table replay checked all 512 witness circuits and the five small-budget cases.

From the project directory on a standard installation, the deliverable can be checked with `lake env lean --root=.. ../attack/19384/proof_attempt.lean`.
