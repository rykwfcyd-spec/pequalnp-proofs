# L-meta-19384

## Candidate statements and guesses

The unrestricted reading of the title gives the following two equivalent targets. The cast in the first target makes the subtraction a natural-number subtraction.

```lean
open PEqualNP.Represents

theorem complement_repSize {n : ℕ} (hn : 3 ≤ n) (A : Fin n → Fin n → Bool) :
    repSize A ≤ repSize (fun u v => !A u v) + ((2 * n - 4 : ℕ) : ℕ∞)

theorem complement_sizeAtMost {n s : ℕ} (hn : 3 ≤ n) (A : Fin n → Fin n → Bool)
    (h : RepSizeAtMost (fun u v => !A u v) s) :
    RepSizeAtMost A (s + (2 * n - 4))
```

- **Scope guess.** The formulas quantify over every square graph and every natural `n ≥ 3`. “Small cases only” may impose an upper limit on `n`, restrict the graph family, or limit the size of the complement circuit. The title gives no particular cutoff or restriction.
- **Model guess.** These candidates use `Monotone2` via `RepSizeAtMost` and `repSize`. This follows the bipartite siblings `L_meta_19123`, `L_meta_19155`, and `L_lib_370`. The exact-two `RepSize2AtMost` and `repSize2` remain plausible. They use `TopForm.IsAO2` and require each gate to read two earlier wires.
- **Statement-form guess.** The desk could state a circuit-budget implication, an inequality of minima, or a direct existential. The proof package uses the circuit-budget form for the construction, then derives the minimum-size inequality.
- **Arithmetic guess.** The proposed inequality casts the natural gate budget into `ℕ∞`. The lower bound on `n` removes truncation issues for this finite term.
- **Naming guess.** The scratch name and theorem names are local. The desk declaration and binders are unavailable.

## Gate count on paper

Let the input wires be `x_i` and `y_j`. On the promise, the negations of `x_i` and `y_j` are the ORs of the other wires on their own sides. De Morgan duality works gate by gate after these negated inputs are available. At `n = 3` the six negated input masks are all distinct and each needs a new wire if the transform materializes all six. The proposed surcharge is two. This shows where the direct dualization strategy exceeds the budget.

The two `(n - 2)`-gate chains do suffice when only one specified input from each side needs to be negated. For the complement of the single edge `(i,j)`, form the two exclusion ORs and join them by OR. This gives `2n - 3` gates against the one AND gate for the edge. With no gates the output is a row, a column, or zero, so the single edge needs at least one gate. The corpus theorem `L_meta_19123` proves the `2n - 3` count is exact. For the complement of a row–column union, the same chains joined by AND give the rectangle with both the row and column removed. The corpus theorem `L_meta_19155` gives the exact same count for that rectangle. These cases attain the requested gap.

## The 3 by 3 check

Encode each wire by its nine-bit truth table over the ordered pairs. A binary gate appends the intersection or union of two available masks. Unary gates copy an existing mask, empty gates supply zero or all ones, and missing reads supply zero. For positive budgets, including both constant masks in the initial search state is a sound overapproximation. At budget zero, check only the six input masks and zero.

The finite proof uses a verified upper-bound circuit for each mask. All such circuits have size at most seven. For each budget from zero through four, exhaustively check that the complement of every reachable output has a witness of size at most the budget plus two. At larger budgets, seven gates suffice. In this search the complete state retains previously computed masks, so both common subexpressions and unrestricted fan-out are covered.

For the diagonal, three edge ANDs and two ORs give five gates. For the off-diagonal, put `z_i = x_i OR y_i` using three gates. The output `(z_0 AND z_1) OR ((z_0 OR z_1) AND z_2)` uses four more gates. The promise makes two distinct `z_i` true exactly when the selected row and column differ. This gives the budget checks `7 ≤ 5 + 2` and `5 ≤ 7 + 2`.

The all-`n` statement requires a further argument beyond these checks. The construction for the sharp examples does not produce the full complement of an arbitrary circuit.

The search checks the closure under pairs of available masks. After a fresh mask is appended, only pairs involving that mask need to be checked again. Each upper certificate uses exactly two earlier input wires per gate. The complete graph uses two ORs on its three row inputs. The resulting finite proof therefore also applies to the exact-two model, and even produces an exact-two circuit from an at-most-two circuit for the complement. The checked minimum-size forms are

```lean
theorem complement_repSize_three (A : Fin 3 → Fin 3 → Bool) :
    repSize A ≤ repSize (fun u v => !A u v) + 2

theorem complement_repSize2_three (A : Fin 3 → Fin 3 → Bool) :
    repSize2 A ≤ repSize2 (fun u v => !A u v) + 2
```

As a comparison, a general construction gives an overhead of `6n - 12` in the at-most-two model. On each side build all proper prefixes and suffixes needed for exclusions in `2(n - 2)` OR gates. An interior exclusion takes one OR of its prefix and suffix, and there are `n - 2` interior exclusions. For each original gate, discard missing operands from an OR and replace an AND with a missing operand by a nullary OR. After this normalization, dualize the gates, including nullary gates, and remap the inputs. A missing output represents false, whose complement has a one-gate constant circuit. This construction handles the corpus default for missing wires and leaves the stronger budget open.

A further paper-only check covers arbitrary `n ≥ 3` when the complement has at most two gates. After simplifying constants, unary gates and repeated operands, its output is constant, a single input, one binary operation, or a two-operation formula on three distinct inputs. The first three cases use at most one exclusion OR per side, or a single side's exclusion for multiple inputs on that side. For the last case with all three inputs on one side, the promise reduces the output to a subset of that side. With two inputs on one side (`x₁,x₂`) and one on the other (`y`), formulas with the same operation at both gates simplify by associativity. An inner gate on `x₁,x₂` either gives false or combines them into one group, whose complement costs `n - 3` OR gates. The mixed formulas involving an inner gate on opposite sides reduce as follows:

- `(x₁ OR y) AND x₂ = y AND x₂`, since `x₁ AND x₂` is always false.
- The complement of `(x₁ AND y) OR x₂` is `r OR (x₁ AND ¬y)`, where `r` is the OR of the `n - 2` other row inputs. This uses `(n - 3) + (n - 2) + 2 = 2n - 3` gates, within the two-gate case's budget `2n - 2`.

These checks also handle transposition, as swapping the two input blocks changes only wire labels.
