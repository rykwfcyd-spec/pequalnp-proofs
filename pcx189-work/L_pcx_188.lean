import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_188

open PEqualNP.ProofComplexity

theorem and_intro_sound {V : Type} [DecidableEq V] {C D R : KLine V}
    (h : IsResKAndIntro C D R) (a : V → Bool) (hC : KLineSat a C) (hD : KLineSat a D) :
    KLineSat a R := by
  obtain ⟨T, U, _, _, rfl⟩ := h
  obtain ⟨P, hP, hp⟩ := hC
  obtain ⟨Q, hQ, hq⟩ := hD
  by_cases e : P = T
  · subst P
    by_cases f : Q = U
    · subst Q
      refine ⟨T ∪ U, by simp, ?_⟩
      intro l hl
      rcases Finset.mem_union.mp hl with h | h
      · exact hp l h
      · exact hq l h
    · exact ⟨Q, Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨f,hQ⟩)), hq⟩
  · exact ⟨P, Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hP⟩)), hp⟩

theorem and_elim_sound {V : Type} [DecidableEq V] {C R : KLine V}
    (h : IsResKAndElim C R) (a : V → Bool) (hC : KLineSat a C) : KLineSat a R := by
  obtain ⟨T, U, _, hUT, _, rfl⟩ := h
  obtain ⟨P, hP, hp⟩ := hC
  by_cases e : P = T
  · subst P
    exact ⟨U, by simp, fun l hl => hp l (hUT hl)⟩
  · exact ⟨P, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hP⟩), hp⟩

theorem cut_sound {V : Type} [DecidableEq V] {C D R : KLine V}
    (h : IsResKCut C D R) (a : V → Bool) (hC : KLineSat a C) (hD : KLineSat a D) : KLineSat a R := by
  obtain ⟨T, _, _, _, rfl⟩ := h
  obtain ⟨P, hP, hp⟩ := hC
  obtain ⟨Q, hQ, hq⟩ := hD
  by_cases e : P = T
  · subst P
    refine ⟨Q, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hQ,?_⟩), hq⟩
    intro hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
    have h1 := hp l hl
    have h2 := hq (l.1, !l.2) (Finset.mem_singleton_self _)
    simp only at h2
    rw [h1] at h2
    revert h2
    cases l.2 <;> decide
  · exact ⟨P, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hP⟩), hp⟩

def Good {V : Type} (F : Set (KLine V)) : List (KLine V) → Prop
  | [] => True
  | R :: π => Good F π ∧ (R ∈ F ∨ ∃ C ∈ π, ∃ D ∈ π, ∀ a, ¬ KLineSat a R → ¬ KLineSat a C ∨ ¬ KLineSat a D)

theorem good {V : Type} [DecidableEq V] {F : Set (KLine V)} {π : List (KLine V)}
    (h : IsResKDerivation 2 F π) : Good F π := by
  induction h with
  | nil => trivial
  | ax _ hC _ ih => exact ⟨ih, .inl hC⟩
  | weak _ hm hw _ ih =>
    refine ⟨ih, .inr ⟨_, hm, _, hm, ?_⟩⟩
    intro a hD
    exact .inl (fun ⟨T,hT,hs⟩ => hD ⟨T,hw hT,hs⟩)
  | @andIntro π C D R _ hC hD hr _ ih =>
    refine ⟨ih, .inr ⟨_,hC,_,hD,?_⟩⟩
    intro a hR
    by_cases h : KLineSat a C
    · exact .inr (fun h' => hR (and_intro_sound hr a h h'))
    · exact .inl h
  | andElim _ hC hr ih =>
    exact ⟨ih, .inr ⟨_,hC,_,hC,fun a hR => .inl (fun h => hR (and_elim_sound hr a h))⟩⟩
  | @cut π C D R _ hC hD hr ih =>
    refine ⟨ih, .inr ⟨_,hC,_,hD,?_⟩⟩
    intro a hR
    by_cases h : KLineSat a C
    · exact .inr (fun h' => hR (cut_sound hr a h h'))
    · exact .inl h

theorem resK_lines_card {V : Type} [DecidableEq V] {k : ℕ} {F : Set (KLine V)} {π : List (KLine V)}
    (h : IsResKDerivation k F π) : ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil => intro L hL; simp at hL
  | ax _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | weak _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | andIntro _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | @andElim π C R _ hC hel ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hLR | hL
    · obtain ⟨T, T', hT, hsub, -, hR⟩ := hel
      rw [hLR, hR]
      intro S hS
      rcases Finset.mem_union.mp hS with hS | hS
      · exact ih C hC S (Finset.mem_of_mem_erase hS)
      · rw [Finset.mem_singleton.mp hS]
        exact (Finset.card_le_card hsub).trans (ih C hC T hT)
    · exact ih L hL
  | @cut π C D R _ hC hD hcut ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hLR | hL
    · obtain ⟨T, -, -, -, hR⟩ := hcut
      rw [hLR, hR]
      intro S hS
      rcases Finset.mem_union.mp hS with hS | hS
      · exact ih C hC S (Finset.mem_of_mem_erase hS)
      · exact ih D hD S (Finset.mem_sdiff.mp hS).1
    · exact ih L hL

section gen
variable {V : Type} [DecidableEq V] {ι : Type} [DecidableEq ι] (F : Set (KLine V)) (Pt : ι → (V → Bool) → Prop)
  (H : ∀ R ∈ F, ∃ k0 : ι, ∀ k, k ≠ k0 → ∀ a, Pt k a → KLineSat a R)

def Hit (K : Finset ι) (N : Finset (KLine V)) : Prop := ∀ k ∈ K, ∃ a, Pt k a ∧ ∃ R ∈ N, ¬ KLineSat a R

theorem hit_step {K : Finset ι} {N Q : Finset (KLine V)} {R : KLine V} (h : Hit Pt K N)
    (hq : ∀ a, ¬ KLineSat a R → ∃ D ∈ Q, ¬ KLineSat a D) : Hit Pt K (N.erase R ∪ Q) := by
  intro k hk
  obtain ⟨a, ha, M, hM, hs⟩ := h k hk
  by_cases e : M = R
  · subst e
    obtain ⟨D, hD, hd⟩ := hq a hs
    exact ⟨a, ha, D, Finset.mem_union_right _ hD, hd⟩
  · exact ⟨a, ha, M, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨e, hM⟩), hs⟩

theorem hit_ax {K : Finset ι} {N : Finset (KLine V)} {R : KLine V} (h : Hit Pt K N) (k0 : ι)
    (hk0 : ∀ k, k ≠ k0 → ∀ a, Pt k a → KLineSat a R) : Hit Pt (K.erase k0) (N.erase R) := by
  intro k hk
  obtain ⟨hne, hk⟩ := Finset.mem_erase.1 hk
  obtain ⟨a, ha, M, hM, hs⟩ := h k hk
  refine ⟨a, ha, M, Finset.mem_erase.2 ⟨?_, hM⟩, hs⟩
  rintro rfl
  exact hs (hk0 k hne a ha)

theorem card_step (N Q : Finset (KLine V)) (R : KLine V) (hR : R ∈ N) : (N.erase R ∪ Q).card + 1 ≤ N.card + Q.card := by
  have h1 := Finset.card_union_le (N.erase R) Q
  have h2 := Finset.card_erase_of_mem hR
  have h3 := Finset.card_pos.2 ⟨R, hR⟩
  omega

theorem tl {N : Finset (KLine V)} {R : KLine V} {π : List (KLine V)} (h : ∀ M ∈ N, M ∈ R :: π) : ∀ M ∈ N.erase R, M ∈ π := by
  intro M hM
  obtain ⟨h1, h2⟩ := Finset.mem_erase.1 hM
  rcases List.mem_cons.1 (h M h2) with e | e
  · exact absurd e h1
  · exact e

theorem tln {N : Finset (KLine V)} {R : KLine V} {π : List (KLine V)} (h : ∀ M ∈ N, M ∈ R :: π) (hR : R ∉ N) : ∀ M ∈ N, M ∈ π := by
  intro M hM
  rcases List.mem_cons.1 (h M hM) with e | e
  · subst e; exact absurd hM hR
  · exact e

include H in
theorem plain {π : List (KLine V)} (hπ : Good F π) : ∀ (N : Finset (KLine V)) (K : Finset ι),
    (∀ M ∈ N, M ∈ π) → Hit Pt K N → 2 * K.card ≤ π.length + N.card := by
  induction π with
  | nil =>
    intro N K hN hK
    have : K = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk
      obtain ⟨_, _, M, hM, _⟩ := hK k hk
      have := hN M hM
      simp at this
    simp [this]
  | cons R π ih =>
    obtain ⟨hπ, hrule⟩ := hπ
    have ih := ih hπ
    rcases hrule with hC | ⟨C,hC,D,hD,hr⟩
    · intro N K hN hK
      by_cases hR : R ∈ N
      · obtain ⟨k0, hk0⟩ := H R hC
        have := ih (N.erase R) (K.erase k0) (tl hN) (hit_ax Pt hK k0 hk0)
        have h2 := Finset.card_erase_of_mem hR
        have h3 := Finset.card_pos.2 ⟨R, hR⟩
        have h4 := Finset.pred_card_le_card_erase (s := K) (a := k0)
        rw [List.length_cons]
        omega
      · have := ih N K (tln hN hR) hK
        rw [List.length_cons]; omega
    · intro N K hN hK
      by_cases hR : R ∈ N
      · have hh := hit_step Pt (Q := {C, D}) hK (R := R) (fun a ha => by
          rcases hr a ha with h | h
          · exact ⟨C, by simp, h⟩
          · exact ⟨D, by simp, h⟩)
        have := ih _ K (fun M hM => by
          rcases Finset.mem_union.1 hM with h | h
          · exact tl hN M h
          · simp only [Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with rfl | rfl <;> assumption) hh
        have h2 := card_step N {C, D} R hR
        have h3 : ({C, D} : Finset (KLine V)).card ≤ 2 := Finset.card_le_two
        rw [List.length_cons]; omega
      · have := ih N K (tln hN hR) hK
        rw [List.length_cons]; omega

include H in
theorem split (i : ι) (p p' : V → Bool) (hp : Pt i p) (hp' : Pt i p') {π : List (KLine V)} (hπ : Good F π) :
    ∀ (A B : Finset (KLine V)) (K : Finset ι), Disjoint A B → (∀ M ∈ A ∪ B, M ∈ π) → Hit Pt K (A ∪ B) →
      (∃ M ∈ A, ¬ KLineSat p M) → (∃ M ∈ B, ¬ KLineSat p' M) → 2 * K.card + 1 ≤ π.length + (A ∪ B).card := by
  -- one step on the part that holds the head
  have stepR : ∀ {π : List (KLine V)} (hπ : Good F π) (R : KLine V) (Q A B : Finset (KLine V)) (K : Finset ι) (r : V → Bool),
      Q.card ≤ 2 → (∀ M ∈ Q, M ∈ π) → (∀ a, ¬ KLineSat a R → ∃ D ∈ Q, ¬ KLineSat a D) → R ∈ A → Disjoint A B →
      (∀ M ∈ A ∪ B, M ∈ R :: π) → Hit Pt K (A ∪ B) → (∃ M ∈ A, ¬ KLineSat r M) →
      ((∀ (A' : Finset (KLine V)), Disjoint A' B → (∀ M ∈ A' ∪ B, M ∈ π) → Hit Pt K (A' ∪ B) → (∃ M ∈ A', ¬ KLineSat r M) →
        2 * K.card + 1 ≤ π.length + (A' ∪ B).card)) → 2 * K.card + 1 ≤ (R :: π).length + (A ∪ B).card := by
    intro π hπ R Q A B K r hQ hQm hq hRA hd hN hK hA ih
    have hRN : R ∈ A ∪ B := Finset.mem_union_left _ hRA
    have hRB : R ∉ B := fun h => (Finset.disjoint_left.1 hd hRA) h
    have hh := hit_step Pt hK hq
    have hmem : ∀ M ∈ (A ∪ B).erase R ∪ Q, M ∈ π := by
      intro M hM
      rcases Finset.mem_union.1 hM with h | h
      · exact tl hN M h
      · exact hQm M h
    have hcs := card_step (A ∪ B) Q R hRN
    rw [List.length_cons]
    by_cases hQB : Disjoint Q B
    · have e : (A ∪ B).erase R ∪ Q = (A.erase R ∪ Q) ∪ B := by
        rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hRB]
        ext x; simp only [Finset.mem_union]; tauto
      rw [e] at hh hmem hcs
      have hd' : Disjoint (A.erase R ∪ Q) B := by
        rw [Finset.disjoint_union_left]
        exact ⟨hd.mono_left (Finset.erase_subset _ _), hQB⟩
      have hA' : ∃ M ∈ A.erase R ∪ Q, ¬ KLineSat r M := by
        obtain ⟨M, hM, hs⟩ := hA
        by_cases eM : M = R
        · subst eM
          obtain ⟨D, hD, hdd⟩ := hq r hs
          exact ⟨D, Finset.mem_union_right _ hD, hdd⟩
        · exact ⟨M, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨eM, hM⟩), hs⟩
      have := ih _ hd' hmem hh hA'
      omega
    · have h1 := plain F Pt H hπ _ K hmem hh
      obtain ⟨x, hxQ, hxB⟩ := Finset.not_disjoint_iff.1 hQB
      have hxN : x ∈ (A ∪ B).erase R := Finset.mem_erase.2 ⟨by rintro rfl; exact hRB hxB, Finset.mem_union_right _ hxB⟩
      have h2 : ((A ∪ B).erase R ∪ Q).card + 1 ≤ ((A ∪ B).erase R).card + Q.card := by
        have hi := Finset.card_union_add_card_inter ((A ∪ B).erase R) Q
        have : 0 < ((A ∪ B).erase R ∩ Q).card := Finset.card_pos.2 ⟨x, Finset.mem_inter.2 ⟨hxN, hxQ⟩⟩
        omega
      have h3 := Finset.card_erase_of_mem hRN
      have h4 := Finset.card_pos.2 ⟨R, hRN⟩
      omega
  have stepA : ∀ {π : List (KLine V)} (hπ : Good F π) (R : KLine V) (A B : Finset (KLine V)) (K : Finset ι) (r r' : V → Bool),
      Pt i r → Pt i r' → R ∈ F → R ∈ A → Disjoint A B → (∀ M ∈ A ∪ B, M ∈ R :: π) → Hit Pt K (A ∪ B) → (∃ M ∈ A, ¬ KLineSat r M) → (∃ M ∈ B, ¬ KLineSat r' M) →
      (∀ (A' : Finset (KLine V)) (K' : Finset ι), Disjoint A' B → (∀ M ∈ A' ∪ B, M ∈ π) → Hit Pt K' (A' ∪ B) → (∃ M ∈ A', ¬ KLineSat r M) →
        2 * K'.card + 1 ≤ π.length + (A' ∪ B).card) → 2 * K.card + 1 ≤ (R :: π).length + (A ∪ B).card := by
    intro π hπ R A B K r r' hr hr' hRF hRA hd hN hK hA hB ih
    obtain ⟨k0, hk0⟩ := H R hRF
    have hRN : R ∈ A ∪ B := Finset.mem_union_left _ hRA
    have hRB : R ∉ B := fun h => (Finset.disjoint_left.1 hd hRA) h
    have h3 := Finset.card_erase_of_mem hRN
    have h4 := Finset.card_pos.2 ⟨R, hRN⟩
    rw [List.length_cons]
    by_cases hi : k0 = i
    · subst hi
      have hh : Hit Pt K ((A ∪ B).erase R) := by
        intro k hk
        by_cases hkk : k = k0
        · subst hkk
          obtain ⟨M, hM, hs⟩ := hB
          exact ⟨r', hr', M, Finset.mem_erase.2 ⟨by rintro rfl; exact hRB hM, Finset.mem_union_right _ hM⟩, hs⟩
        · exact hit_ax Pt hK k0 hk0 k (Finset.mem_erase.2 ⟨hkk, hk⟩)
      have := plain F Pt H hπ _ K (tl hN) hh
      omega
    · have e : (A ∪ B).erase R = A.erase R ∪ B := by
        rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hRB]
      have hh := hit_ax Pt hK k0 hk0
      have hmem := tl hN
      rw [e] at hh hmem h3
      have hA' : ∃ M ∈ A.erase R, ¬ KLineSat r M := by
        obtain ⟨M, hM, hs⟩ := hA
        exact ⟨M, Finset.mem_erase.2 ⟨by rintro rfl; exact hs (hk0 i (Ne.symm hi) r hr), hM⟩, hs⟩
      have := ih _ _ (hd.mono_left (Finset.erase_subset _ _)) hmem hh hA'
      have h5 := Finset.pred_card_le_card_erase (s := K) (a := k0)
      omega
  induction π with
  | nil =>
    rintro A B K _ hN _ ⟨M, hM, _⟩ _
    have := hN M (Finset.mem_union_left _ hM)
    simp at this
  | cons R π ih =>
    obtain ⟨hπ, hrule⟩ := hπ
    have ih := ih hπ
    rcases hrule with hC | ⟨C,hC,D,hD,hr⟩
    · intro A B K hd hN hK hA hB
      by_cases hRA : R ∈ A
      · exact stepA hπ R A B K p p' hp hp' hC hRA hd hN hK hA hB (fun A' K' h1 h2 h3 h4 => ih A' B K' h1 h2 h3 h4 hB)
      · by_cases hRB : R ∈ B
        · rw [Finset.union_comm]
          rw [Finset.union_comm] at hN hK
          refine stepA hπ R B A K p' p hp' hp hC hRB hd.symm hN hK hB hA (fun A' K' h1 h2 h3 h4 => ?_)
          rw [Finset.union_comm] at h2 h3 ⊢
          exact ih A A' K' h1.symm h2 h3 hA h4
        · have := ih A B K hd (tln hN (by simp [hRA, hRB])) hK hA hB
          rw [List.length_cons]; omega
    · intro A B K hd hN hK hA hB
      have q1 : ({C, D} : Finset (KLine V)).card ≤ 2 := Finset.card_le_two
      have q2 : ∀ M ∈ ({C, D} : Finset (KLine V)), M ∈ π := by
        intro M h
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl <;> assumption
      have q3 : ∀ a, ¬ KLineSat a R → ∃ E ∈ ({C, D} : Finset (KLine V)), ¬ KLineSat a E := by
        intro a ha
        rcases hr a ha with h | h
        · exact ⟨C, by simp, h⟩
        · exact ⟨D, by simp, h⟩
      by_cases hRA : R ∈ A
      · exact stepR hπ R _ A B K p q1 q2 q3 hRA hd hN hK hA (fun A' h1 h2 h3 h4 => ih A' B K h1 h2 h3 h4 hB)
      · by_cases hRB : R ∈ B
        · rw [Finset.union_comm]
          rw [Finset.union_comm] at hN hK
          refine stepR hπ R _ B A K p' q1 q2 q3 hRB hd.symm hN hK hB (fun A' h1 h2 h3 h4 => ?_)
          rw [Finset.union_comm] at h2 h3 ⊢
          exact ih A A' K h1.symm h2 h3 hA h4
        · have := ih A B K hd (tln hN (by simp [hRA, hRB])) hK hA hB
          rw [List.length_cons]; omega

end gen

def Marked {V : Type} (C D R : KLine V) : Prop :=
  C = D ∨ (∀ a, KLineSat a R) ∨
    (∃ l : Literal V, ∀ a, ¬ KLineSat a R → KLineSat a C → a l.1 = l.2) ∨
    (∃ l : Literal V, ∀ a, ¬ KLineSat a R → KLineSat a D → a l.1 = l.2)

theorem surviving {V : Type} [DecidableEq V] {C R : KLine V} {T : KTerm V} {a : V → Bool}
    (her : ∀ T' ∈ C.erase T, T' ∈ R) (hn : ¬ KLineSat a R) (ok : KLineSat a C) :
    ∀ l ∈ T, a l.1 = l.2 := by
  obtain ⟨Q,hQ,sat⟩ := ok
  by_cases eq : Q = T
  · exact eq ▸ sat
  · exact False.elim (hn ⟨Q,her _ (Finset.mem_erase.mpr ⟨eq,hQ⟩),sat⟩)

theorem marked_cut {V : Type} [DecidableEq V] {C D R : KLine V} (h : IsResKCut C D R) : Marked C D R := by
  obtain ⟨T,_,hne,_,rfl⟩ := h
  obtain ⟨l,hl⟩ := hne
  exact .inr (.inr (.inl ⟨l,fun _ hn hs => surviving (fun _ ht => Finset.mem_union_left _ ht) hn hs l hl⟩))

theorem marked_intro {V : Type} [DecidableEq V] {C D R : KLine V}
    (h : IsResKAndIntro C D R) : Marked C D R := by
  obtain ⟨T,U,_,_,rfl⟩ := h
  by_cases ht : T.Nonempty
  · obtain ⟨l,hl⟩ := ht
    exact .inr (.inr (.inl ⟨l,fun _ hn hs =>
      surviving (fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)) hn hs l hl⟩))
  by_cases hu : U.Nonempty
  · obtain ⟨l,hl⟩ := hu
    exact .inr (.inr (.inr ⟨l,fun _ hn hs =>
      surviving (fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h)) hn hs l hl⟩))
  · have e1 := Finset.not_nonempty_iff_eq_empty.mp ht
    have e2 := Finset.not_nonempty_iff_eq_empty.mp hu
    subst T
    subst U
    exact .inr (.inl (fun _ => ⟨∅,by simp,by simp⟩))

def Strong {V : Type} (F : Set (KLine V)) : List (KLine V) → Prop
  | [] => True
  | R :: π => Strong F π ∧ (R ∈ F ∨ ∃ C ∈ π, ∃ D ∈ π,
    (∀ a, ¬ KLineSat a R → ¬ KLineSat a C ∨ ¬ KLineSat a D) ∧ Marked C D R)

theorem forget {V : Type} {F : Set (KLine V)} {π : List (KLine V)} (hp : Strong F π) : Good F π := by
  induction π with
  | nil => trivial
  | cons R π ih =>
    obtain ⟨h,ax | ⟨C,hC,D,hD,snd,_⟩⟩ := hp
    · exact ⟨ih h,.inl ax⟩
    · exact ⟨ih h,.inr ⟨C,hC,D,hD,snd⟩⟩

theorem strong {V : Type} [DecidableEq V] {F : Set (KLine V)} {π : List (KLine V)}
    (h : IsResKDerivation 2 F π) : Strong F π := by
  induction h with
  | nil => trivial
  | ax _ hC _ ih => exact ⟨ih,.inl hC⟩
  | weak _ hm hw _ ih =>
    refine ⟨ih, .inr ⟨_,hm,_,hm,?_,.inl rfl⟩⟩
    intro a hD
    exact .inl (fun ⟨T,hT,hs⟩ => hD ⟨T,hw hT,hs⟩)
  | @andIntro _ C _ _ _ hC hD hr _ ih =>
    refine ⟨ih,.inr ⟨_,hC,_,hD,?_,marked_intro hr⟩⟩
    intro a hR
    by_cases h : KLineSat a C
    · exact .inr (fun h' => hR (and_intro_sound hr a h h'))
    · exact .inl h
  | andElim _ hC hr ih =>
    exact ⟨ih,.inr ⟨_,hC,_,hC,fun a hR => .inl (fun h => hR (and_elim_sound hr a h)),.inl rfl⟩⟩
  | @cut _ C _ _ _ hC hD hr ih =>
    refine ⟨ih,.inr ⟨_,hC,_,hD,?_,marked_cut hr⟩⟩
    intro a hR
    by_cases h : KLineSat a C
    · exact .inr (fun h' => hR (cut_sound hr a h h'))
    · exact .inl h

def Big {V : Type} (S : Fin 4 → (V → Bool) → Prop) (R : KLine V) : Prop :=
  ∀ i a, S i a → ¬ KLineSat a R

theorem walk {V : Type} [DecidableEq V] {ι : Type} [DecidableEq ι]
    (F : Set (KLine V)) (Pt : ι → (V → Bool) → Prop)
    (H : ∀ R ∈ F, ∃ k0 : ι, ∀ k, k ≠ k0 → ∀ a, Pt k a → KLineSat a R)
    (S : Fin 4 → (V → Bool) → Prop) (tag : Fin 4 → ι)
    (track : ∀ i a, S i a → Pt (tag i) a)
    (smallAx : ∀ R ∈ F, ¬ Big S R)
    (overlap : ∀ C D R : KLine V, (∀ T ∈ C, T.card ≤ 2) → (∀ T ∈ D, T.card ≤ 2) →
      Marked C D R → (∀ a, ¬ KLineSat a R → ¬ KLineSat a C ∨ ¬ KLineSat a D) →
      Big S R → ¬ Big S C → ¬ Big S D →
      D ≠ C ∧ ∃ i a b, S i a ∧ S i b ∧ ¬ KLineSat a D ∧ ¬ KLineSat b C)
    {π : List (KLine V)} (hπ : Strong F π) (hw : ∀ C ∈ π, ∀ T ∈ C, T.card ≤ 2) :
    ∀ (N : Finset (KLine V)) (K : Finset ι), (∀ M ∈ N, M ∈ π) → Hit Pt K N →
      (∃ M ∈ N, Big S M) → 2 * K.card + 1 ≤ π.length + N.card := by
  classical
  induction π with
  | nil =>
    rintro N K hn _ ⟨M, hm, _⟩
    have := hn M hm
    simp at this
  | cons R π ih =>
    obtain ⟨hπ, rule⟩ := hπ
    have hwt : ∀ C ∈ π, ∀ T ∈ C, T.card ≤ 2 := fun C h => hw C (List.mem_cons_of_mem R h)
    have ih := ih hπ hwt
    rintro N K hn hit ⟨M,hM,big⟩
    by_cases hR : R ∈ N
    · rcases rule with ax | ⟨C,hC,D,hD,hrule,mark⟩
      · obtain ⟨k0,h0⟩ := H R ax
        have ne : M ≠ R := by rintro rfl; exact smallAx M ax big
        have h1 := ih (N.erase R) (K.erase k0) (tl hn) (hit_ax Pt hit k0 h0)
          ⟨M, Finset.mem_erase.mpr ⟨ne,hM⟩, big⟩
        have := Finset.card_erase_of_mem hR
        have := Finset.card_pos.mpr ⟨R,hR⟩
        have := Finset.pred_card_le_card_erase (s := K) (a := k0)
        rw [List.length_cons]
        omega
      · let Q : Finset (KLine V) := {C,D}
        let F' := N.erase R ∪ Q
        have hCQ : C ∈ Q := by simp [Q]
        have hDQ : D ∈ Q := by simp [Q]
        have hc' : C ∈ F' := Finset.mem_union_right _ hCQ
        have hd' : D ∈ F' := Finset.mem_union_right _ hDQ
        have qfail : ∀ a, ¬ KLineSat a R → ∃ E ∈ Q, ¬ KLineSat a E := by
          intro a ha
          rcases hrule a ha with hc | hd
          · exact ⟨C,hCQ,hc⟩
          · exact ⟨D,hDQ,hd⟩
        have hhit : Hit Pt K F' := hit_step Pt hit qfail
        have hmem : ∀ E ∈ F', E ∈ π := by
          intro E he
          rcases Finset.mem_union.mp he with e | e
          · exact tl hn _ e
          · simp only [Q, Finset.mem_insert, Finset.mem_singleton] at e
            rcases e with rfl | rfl <;> assumption
        have cards : F'.card + 1 ≤ N.card + Q.card := card_step N Q R hR
        have two : Q.card ≤ 2 := Finset.card_le_two
        suffices hgoal : 2 * K.card + 1 ≤ π.length + F'.card by
          rw [List.length_cons]
          omega
        by_cases e : M = R
        · subst M
          by_cases bc : Big S C
          · exact ih F' K hmem hhit ⟨C,hc',bc⟩
          by_cases bd : Big S D
          · exact ih F' K hmem hhit ⟨D,hd',bd⟩
          obtain ⟨ne,i,a,b,ha,hb,na,nb⟩ :=
            overlap C D R (hwt _ hC) (hwt _ hD) mark hrule big bc bd
          let A : Finset (KLine V) := {C}
          let B := F'.erase C
          have hAB : A ∪ B = F' := by
            ext L
            by_cases e : L = C <;> simp_all [A,B]
          have dj : Disjoint A B := by simp [A,B]
          have hret := split F Pt H (tag i) b a (track i b hb) (track i a ha) (forget hπ) A B K dj
            (by rwa [hAB]) (by rwa [hAB]) ⟨C,by simp [A],nb⟩
            ⟨D,Finset.mem_erase.mpr ⟨ne,hd'⟩,na⟩
          rwa [hAB] at hret
        · exact ih F' K hmem hhit
            ⟨M,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hM⟩),big⟩
    · have := ih N K (tln hn hR) hit ⟨M,hM,big⟩
      rw [List.length_cons]
      omega

abbrev W := Fin 4 × Fin 3

def asg (m : ℕ) : W → Bool := fun v => m.testBit (3 * v.1.val + v.2.val)

def groups : List (List ℕ) := [[2184, 1288, 2128, 784, 1120, 672], [2177, 1281, 2114, 770, 1092, 644], [2065, 1057, 2058, 546, 1036, 532], [273, 161, 266, 98, 140, 84], [2185], [2130], [1124], [2129], [2186], [1292], [2122], [2193], [1313], [785], [1290], [2188], [778], [1297], [2209], [610], [1185], [2321]]

def pts (k : Fin 22) : List ℕ := groups.getD k.val []

def Pt (k : Fin 22) (a : W → Bool) : Prop := ∃ m ∈ pts k, a = asg m

def kP (i : Fin 4) : Fin 22 := ⟨i.val, by omega⟩

def kH (i j : Fin 4) (h : Fin 3) : Fin 22 :=
  ⟨(4 + 3 * (max i.val j.val * (max i.val j.val - 1) / 2 + min i.val j.val) + h.val) % 22,
    Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 12000 in
theorem factP : ∀ (i : Fin 4) (k : Fin 22), k ≠ kP i → ∀ m ∈ pts k,
    ∃ j : Fin 3, asg m (i,j) = true := by decide +kernel

set_option maxRecDepth 12000 in
theorem factH : ∀ (i j : Fin 4) (h : Fin 3), i ≠ j → ∀ k : Fin 22, k ≠ kH i j h →
    ∀ m ∈ pts k, asg m (i,h) = false ∨ asg m (j,h) = false := by decide +kernel

theorem inhabitedPts : ∀ k : Fin 22, pts k ≠ [] := by decide +kernel

def FF : Set (KLine W) := (fun C => kLineOfClause C) '' PHP 4 3

theorem liftSat {C : Clause W} {a : W → Bool} (h : ClauseSat a C) : KLineSat a (kLineOfClause C) := by
  obtain ⟨l,hl,hs⟩ := h
  exact ⟨{l}, Finset.mem_image_of_mem _ hl, fun x hx => (Finset.mem_singleton.mp hx) ▸ hs⟩

theorem HH : ∀ R ∈ FF, ∃ k0 : Fin 22, ∀ k, k ≠ k0 → ∀ a, Pt k a → KLineSat a R := by
  rintro R ⟨C,hC,rfl⟩
  rcases hC with ⟨i,rfl⟩ | ⟨i,j,h,hij,rfl⟩
  · refine ⟨kP i, ?_⟩
    rintro k hk _ ⟨m,hm,rfl⟩
    obtain ⟨j,hj⟩ := factP i k hk m hm
    exact liftSat ⟨((i,j),true), Finset.mem_image_of_mem _ (Finset.mem_univ j), hj⟩
  · refine ⟨kH i j h, ?_⟩
    rintro k hk _ ⟨m,hm,rfl⟩
    rcases factH i j h hij k hk m hm with q | q
    · exact liftSat ⟨((i,h),false), by simp, q⟩
    · exact liftSat ⟨((j,h),false), by simp, q⟩

def S (i : Fin 4) := Pt (kP i)

def admits (T : KTerm W) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => (pts (kP i)).any (fun m => decide (∀ l ∈ T, asg m l.1 = l.2)) = true)

def owner (m : ℕ) (h : Fin 3) : Fin 4 :=
  if asg m (0,h) then 0 else if asg m (1,h) then 1 else if asg m (2,h) then 2 else 3

def moved (i : Fin 4) (m : ℕ) (h : Fin 3) : ℕ :=
  m ^^^ 2 ^ (3*i.val + h.val) ^^^ 2 ^ (3*(owner m h).val + h.val)

set_option maxRecDepth 12000 in
theorem swapOK : ∀ i : Fin 4, ∀ m ∈ pts (kP i), ∀ h : Fin 3,
    moved i m h ∈ pts (kP (owner m h)) ∧ owner m h ≠ i ∧
    (∀ t : Fin 3, owner m t = owner m h → t = h) := by decide +kernel

theorem offColumn (i : Fin 4) (m : ℕ) (h : Fin 3) (v : W) (hv : v.2 ≠ h) :
    asg (moved i m h) v = asg m v := by
  have hne : v.2.val ≠ h.val := fun he => hv (Fin.ext he)
  have b1 := v.2.isLt
  have b2 := h.isLt
  have d1 : 3*i.val + h.val ≠ 3*v.1.val + v.2.val := by omega
  have d2 : 3*(owner m h).val + h.val ≠ 3*v.1.val + v.2.val := by omega
  simp [asg,moved,Nat.testBit_xor,Nat.testBit_two_pow,d1,d2]

theorem largeTerm {T : KTerm W} (h : T.card ≤ 2) (ne : (admits T).Nonempty) : 2 ≤ (admits T).card := by
  classical
  obtain ⟨i,hi⟩ := ne
  obtain ⟨m,hm,hs⟩ := List.any_eq_true.mp (Finset.mem_filter.mp hi).2
  have goodm : ∀ l ∈ T, asg m l.1 = l.2 := of_decide_eq_true hs
  let used := T.image (fun l : Literal W => l.1.2)
  let free := Finset.univ \ used
  have hsze : used.card ≤ 2 := le_trans Finset.card_image_le h
  have hfree : 1 ≤ free.card := by
    have z : free.card = 3 - used.card := by
      simpa [free] using Finset.card_sdiff_of_subset (Finset.subset_univ used)
    omega
  let dest := free.image (owner m)
  have inj : Function.Injective (owner m) := fun a b he => (swapOK i m hm b).2.2 a he
  have dc : dest.card = free.card := Finset.card_image_of_injective _ inj
  have ni : i ∉ dest := by
    rintro mem
    obtain ⟨t,_,eq⟩ := Finset.mem_image.mp mem
    exact (swapOK i m hm t).2.1 eq
  have sub : insert i dest ⊆ admits T := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    obtain ⟨t,ft,rfl⟩ := Finset.mem_image.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,List.any_eq_true.mpr
      ⟨moved i m t,(swapOK i m hm t).1,decide_eq_true ?_⟩⟩
    intro l hl
    have hv : l.1.2 ≠ t := by
      rintro rfl
      exact (Finset.mem_sdiff.mp ft).2 (Finset.mem_image_of_mem _ hl)
    rw [offColumn _ _ _ _ hv]
    exact goodm l hl
  have z := Finset.card_le_card sub
  rw [Finset.card_insert_of_notMem ni,dc] at z
  omega

theorem termMem {T : KTerm W} {i : Fin 4} {a : W → Bool} (ha : S i a)
    (sat : ∀ l ∈ T, a l.1 = l.2) : i ∈ admits T := by
  obtain ⟨m,hm,rfl⟩ := ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, List.any_eq_true.mpr ⟨m,hm,decide_eq_true sat⟩⟩

theorem getWitness {C : KLine W} {T : KTerm W} {i : Fin 4}
    (h : i ∈ admits T) (hT : T ∈ C) : ∃ a, S i a ∧ KLineSat a C := by
  have hh := (Finset.mem_filter.mp h).2
  obtain ⟨m,hm,hs⟩ := List.any_eq_true.mp hh
  exact ⟨asg m,⟨m,hm,rfl⟩,T,hT,of_decide_eq_true hs⟩

def varies (l : Literal W) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => (pts (kP i)).any (fun m => decide (asg m l.1 ≠ l.2)) = true)

theorem threeVary : ∀ l : Literal W, 3 ≤ (varies l).card := by decide +kernel

theorem mixed {C : KLine W} (wC : ∀ T ∈ C, T.card ≤ 2) (nc : ¬ Big S C) (l : Literal W)
    (fixed : ∀ i a, S i a → KLineSat a C → a l.1 = l.2) :
    ∃ i a b, S i a ∧ S i b ∧ KLineSat a C ∧ ¬ KLineSat b C := by
  classical
  unfold Big at nc
  push Not at nc
  obtain ⟨i,a,ha,T,hT,hs⟩ := nc
  have t2 := largeTerm (wC T hT) ⟨i, termMem ha hs⟩
  have v3 := threeVary l
  have inter : ¬ Disjoint (admits T) (varies l) := by
    intro hd
    have hcard := Finset.card_union_of_disjoint hd
    have bound : (admits T ∪ varies l).card ≤ 4 := by
      simpa using Finset.card_le_univ (admits T ∪ varies l)
    omega
  obtain ⟨k,ht,hv⟩ := Finset.not_disjoint_iff.mp inter
  obtain ⟨p,hp,cp⟩ := getWitness ht hT
  obtain ⟨n,hn,no⟩ := List.any_eq_true.mp (Finset.mem_filter.mp hv).2
  have hn' : S k (asg n) := ⟨n,hn,rfl⟩
  exact ⟨k,p,asg n,hp,hn',cp,fun hc => of_decide_eq_true no (fixed k (asg n) hn' hc)⟩

theorem overlap (C D R : KLine W) (wC : ∀ T ∈ C, T.card ≤ 2) (wD : ∀ T ∈ D, T.card ≤ 2)
    (mark : Marked C D R) (snd : ∀ a, ¬ KLineSat a R → ¬ KLineSat a C ∨ ¬ KLineSat a D)
    (big : Big S R) (nc : ¬ Big S C) (nd : ¬ Big S D) :
    D ≠ C ∧ ∃ i a b, S i a ∧ S i b ∧ ¬ KLineSat a D ∧ ¬ KLineSat b C := by
  classical
  have ne : D ≠ C := by
    rintro rfl
    apply nc
    exact fun i a ha => (snd a (big i a ha)).elim id id
  refine ⟨ne, ?_⟩
  rcases mark with eq | allR | ⟨l,hl⟩ | ⟨l,hl⟩
  · exact (ne eq.symm).elim
  · obtain ⟨m,hm⟩ := List.exists_mem_of_ne_nil (pts (kP 0)) (inhabitedPts (kP 0))
    exact (big 0 (asg m) ⟨m,hm,rfl⟩ (allR _)).elim
  · obtain ⟨i,a,b,ha,hb,sa,nb⟩ := mixed wC nc l (fun i a ha => hl a (big i a ha))
    exact ⟨i,a,b,ha,hb,(snd a (big i a ha)).resolve_left (not_not_intro sa),nb⟩
  · obtain ⟨i,a,b,ha,hb,sa,nb⟩ := mixed wD nd l (fun i a ha => hl a (big i a ha))
    exact ⟨i,b,a,hb,ha,nb,(snd a (big i a ha)).resolve_right (not_not_intro sa)⟩

theorem present (k : Fin 22) : ∃ a, Pt k a := by
  obtain ⟨m,hm⟩ := List.exists_mem_of_ne_nil (pts k) (inhabitedPts k)
  exact ⟨asg m,m,hm,rfl⟩

theorem smallAx : ∀ R ∈ FF, ¬ Big S R := by
  intro R hr big
  obtain ⟨k,h⟩ := HH R hr
  have hx : ∃ i : Fin 4, kP i ≠ k := by
    by_cases z : kP 0 = k
    · exact ⟨1,z ▸ (by decide : kP 1 ≠ kP 0)⟩
    · exact ⟨0,z⟩
  obtain ⟨i,hi⟩ := hx
  obtain ⟨a,ha⟩ := present (kP i)
  exact big i a ha (h _ hi _ ha)

theorem bound {π : List (KLine W)} (h : IsResKRefutation 2 (PHP 4 3) π) : 44 ≤ π.length := by
  obtain ⟨hd,hem⟩ := h
  have noSat : ∀ a : W → Bool, ¬ KLineSat a ∅ := by
    rintro a ⟨T,hT,_⟩
    exact Finset.notMem_empty _ hT
  have hit : Hit Pt Finset.univ ({∅} : Finset (KLine W)) := by
    intro k _
    obtain ⟨a,ha⟩ := present k
    exact ⟨a,ha,∅,by simp,noSat a⟩
  have hret := walk FF Pt HH S kP (fun _ _ x => x) smallAx overlap (strong hd) (resK_lines_card hd)
    {∅} Finset.univ (fun _ hm => (Finset.mem_singleton.mp hm) ▸ hem) hit
      ⟨∅,by simp,fun _ a _ => noSat a⟩
  simp only [Finset.card_univ,Fintype.card_fin, Finset.card_singleton] at hret
  omega

end PEqualNP.Outside.L_pcx_188

theorem PEqualNP.Outside.L_pcx_188 : ¬ (∃ π : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsResKRefutation 2 (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 43) := by
  rintro ⟨π,hπ,hlen⟩
  have := PEqualNP.Outside.L_pcx_188.bound hπ
  omega
