import PEqualNP.Defs.ProofComplexity

/-!
# Definitions of the proof complexity program: k-DNF resolution Res(k)

The system Res(k) of Krajicek (Fund. Math. 170, 2001), in the form of Segerlind, Buss and
Impagliazzo (SIAM J. Comput. 33, 2004): lines are k-DNFs, that is, disjunctions of conjunctions
of at most `k` literals. Rules: weakening (add terms), and-introduction, and-elimination, and
cut of a conjunction against the negations of its literals. All rules are syntactic. It is here
as a yardstick: Res(k, ⊕) of `Defs/ProofComplexityLinK.lean` is meant to contain it.
-/

namespace PEqualNP.ProofComplexity

/-- A term of a k-DNF: a finite set of literals, read as their conjunction. -/
abbrev KTerm (V : Type) : Type := Finset (Literal V)

/-- A line of Res(k): a finite set of terms, read as their disjunction. -/
abbrev KLine (V : Type) : Type := Finset (KTerm V)

/-- The assignment `a` satisfies the line `L`: it makes every literal of some term true. -/
def KLineSat {V : Type} (a : V → Bool) (L : KLine V) : Prop :=
  ∃ T ∈ L, ∀ l ∈ T, a l.1 = l.2

/-- A clause as a line: one one-literal term for each literal. -/
def kLineOfClause {V : Type} [DecidableEq V] (C : Clause V) : KLine V :=
  C.image (fun l => ({l} : KTerm V))

/-- Weakening: `M` holds every term of `L`. -/
def IsResKWeakening {V : Type} (L M : KLine V) : Prop := L ⊆ M

/-- And-introduction: from `C` holding `T₁` and `D` holding `T₂`, the rest of both together
with the term `T₁ ∪ T₂`. -/
def IsResKAndIntro {V : Type} [DecidableEq V] (C D R : KLine V) : Prop :=
  ∃ T₁ T₂ : KTerm V, T₁ ∈ C ∧ T₂ ∈ D ∧ R = (C.erase T₁ ∪ D.erase T₂) ∪ {T₁ ∪ T₂}

/-- And-elimination: a term `T` of `C` is replaced by a nonempty part `T'` of it. -/
def IsResKAndElim {V : Type} [DecidableEq V] (C R : KLine V) : Prop :=
  ∃ T T' : KTerm V, T ∈ C ∧ T' ⊆ T ∧ T'.Nonempty ∧ R = C.erase T ∪ {T'}

/-- Cut: `C` holds the term `T`, `D` holds the one-literal term of the negation of every
literal of `T`, and `R` is the rest of `C` together with the rest of `D`. -/
def IsResKCut {V : Type} [DecidableEq V] (C D R : KLine V) : Prop :=
  ∃ T : KTerm V, T ∈ C ∧ T.Nonempty ∧ (∀ l ∈ T, ({(l.1, !l.2)} : KTerm V) ∈ D) ∧
    R = C.erase T ∪ (D \ T.image (fun l => ({(l.1, !l.2)} : KTerm V)))

/-- `IsResKDerivation k F π`: the list `π`, NEWEST LINE FIRST, is a Res(k) derivation from the
lines `F`; every term of every line has at most `k` literals. The number of lines is
`π.length`. -/
inductive IsResKDerivation {V : Type} [DecidableEq V] (k : ℕ) (F : Set (KLine V)) :
    List (KLine V) → Prop
  | nil : IsResKDerivation k F []
  | ax {π : List (KLine V)} {C : KLine V} :
      IsResKDerivation k F π → C ∈ F → (∀ T ∈ C, T.card ≤ k) → IsResKDerivation k F (C :: π)
  | weak {π : List (KLine V)} {C D : KLine V} :
      IsResKDerivation k F π → C ∈ π → IsResKWeakening C D → (∀ T ∈ D, T.card ≤ k) →
      IsResKDerivation k F (D :: π)
  | andIntro {π : List (KLine V)} {C D R : KLine V} :
      IsResKDerivation k F π → C ∈ π → D ∈ π → IsResKAndIntro C D R → (∀ T ∈ R, T.card ≤ k) →
      IsResKDerivation k F (R :: π)
  | andElim {π : List (KLine V)} {C R : KLine V} :
      IsResKDerivation k F π → C ∈ π → IsResKAndElim C R → IsResKDerivation k F (R :: π)
  | cut {π : List (KLine V)} {C D R : KLine V} :
      IsResKDerivation k F π → C ∈ π → D ∈ π → IsResKCut C D R → IsResKDerivation k F (R :: π)

/-- A Res(k) refutation of the CNF formula `F`: a derivation from the clauses of `F`, read as
lines, that contains the empty line. -/
def IsResKRefutation {V : Type} [DecidableEq V] (k : ℕ) (F : Set (Clause V))
    (π : List (KLine V)) : Prop :=
  IsResKDerivation k ((fun C => kLineOfClause C) '' F) π ∧ (∅ : KLine V) ∈ π

end PEqualNP.ProofComplexity
