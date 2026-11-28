import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_191

open PEqualNP.ProofComplexity

abbrev VV : Type := Fin 4 × Fin 3


theorem kline_inj {V : Type} [DecidableEq V] :
    Function.Injective (fun l : Literal V => ({l} : KTerm V)) :=
  fun _ _ h => Finset.singleton_injective h

theorem unitc {V : Type} [DecidableEq V] (C : Clause V) : ∀ T ∈ kLineOfClause C, T.card ≤ 2 := by
  intro T hT
  simp only [kLineOfClause, Finset.mem_image] at hT
  obtain ⟨l, _, rfl⟩ := hT
  simp

theorem liftRes {V : Type} [DecidableEq V] {C D R : Clause V} (hR : IsResolvent C D R) :
    IsResKCut (kLineOfClause C) (kLineOfClause D) (kLineOfClause R) := by
  obtain ⟨v, hv1, hv2, rfl⟩ := hR
  refine ⟨{(v, true)}, ?_, Finset.singleton_nonempty _, ?_, ?_⟩
  · exact Finset.mem_image_of_mem _ hv1
  · intro l hl
    rw [Finset.mem_singleton] at hl
    subst hl
    exact Finset.mem_image_of_mem _ hv2
  · simp only [kLineOfClause, Finset.image_union, Finset.image_singleton]
    rw [Finset.image_erase kline_inj, Finset.image_erase kline_inj,
      Finset.sdiff_singleton_eq_erase]
    all_goals rfl

theorem liftResN {V : Type} [DecidableEq V] {C D R : Clause V} (hR : IsResolvent D C R) :
    IsResKCut (kLineOfClause C) (kLineOfClause D) (kLineOfClause R) := by
  obtain ⟨v, hv1, hv2, rfl⟩ := hR
  refine ⟨{(v, false)}, ?_, Finset.singleton_nonempty _, ?_, ?_⟩
  · exact Finset.mem_image_of_mem _ hv2
  · intro l hl
    rw [Finset.mem_singleton] at hl
    subst hl
    exact Finset.mem_image_of_mem _ hv1
  · simp only [kLineOfClause, Finset.image_union, Finset.image_singleton]
    rw [Finset.image_erase kline_inj, Finset.image_erase kline_inj,
      Finset.sdiff_singleton_eq_erase, Finset.union_comm]
    all_goals rfl

theorem cutQ {V : Type} [DecidableEq V] (x a b : Literal V) (C R : Clause V)
    (hab : a ≠ b) (ha : (a.1, !a.2) ∈ C) (hb : (b.1, !b.2) ∈ C)
    (hR : R = insert x ((C.erase (a.1, !a.2)).erase (b.1, !b.2))) :
    IsResKCut ({{x}, {a, b}} : KLine V) (kLineOfClause C) (kLineOfClause R) := by
  subst hR
  have hne : ({x} : KTerm V) ≠ {a, b} := by
    intro h
    have h1 : a ∈ ({x} : KTerm V) := by rw [h]; simp
    have h2 : b ∈ ({x} : KTerm V) := by rw [h]; simp
    rw [Finset.mem_singleton] at h1 h2
    exact hab (h1.trans h2.symm)
  refine ⟨{a, b}, by simp, ⟨a, by simp⟩, ?_, ?_⟩
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact Finset.mem_image_of_mem _ ha
    · exact Finset.mem_image_of_mem _ hb
  · ext T
    simp only [kLineOfClause, Finset.mem_union, Finset.mem_erase, Finset.mem_sdiff,
      Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨l, rfl | ⟨hlb, hla, hl⟩, rfl⟩
      · exact Or.inl ⟨hne, Or.inl rfl⟩
      · refine Or.inr ⟨⟨l, hl, rfl⟩, ?_⟩
        rintro ⟨m, rfl | rfl, hm⟩
        · exact hla (Finset.singleton_injective hm).symm
        · exact hlb (Finset.singleton_injective hm).symm
    · rintro (⟨hT, rfl | rfl⟩ | ⟨⟨l, hl, rfl⟩, hn⟩)
      · exact ⟨x, Or.inl rfl, rfl⟩
      · exact absurd rfl hT
      · refine ⟨l, Or.inr ⟨?_, ?_, hl⟩, rfl⟩
        · rintro rfl
          exact hn ⟨b, Or.inr rfl, rfl⟩
        · rintro rfl
          exact hn ⟨a, Or.inl rfl, rfl⟩
theorem andQ {V : Type} [DecidableEq V] (x a b : Literal V) (hxa : x ≠ a) (hxb : x ≠ b) :
    IsResKAndIntro (kLineOfClause ({a, x} : Clause V)) (kLineOfClause ({x, b} : Clause V))
      ({{x}, {a, b}} : KLine V) := by
  have h1 : kLineOfClause ({a, x} : Clause V) = {{a}, {x}} := by simp [kLineOfClause]
  have h2 : kLineOfClause ({x, b} : Clause V) = {{x}, {b}} := by simp [kLineOfClause]
  rw [h1, h2]
  have hxa' : ({x} : KTerm V) ≠ {a} := fun h => hxa (Finset.singleton_injective h)
  have hxb' : ({x} : KTerm V) ≠ {b} := fun h => hxb (Finset.singleton_injective h)
  refine ⟨{a}, {b}, by simp, by simp, ?_⟩
  ext T
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
    ← Finset.insert_eq]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl (Or.inl ⟨hxa', Or.inr rfl⟩)
    · exact Or.inr rfl
  · rintro ((⟨h, rfl | rfl⟩ | ⟨h, rfl | rfl⟩) | rfl)
    · exact absurd rfl h
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact absurd rfl h
    · exact Or.inr rfl

theorem cardQ {V : Type} [DecidableEq V] (x a b : Literal V) :
    ∀ T ∈ ({{x}, {a, b}} : KLine V), T.card ≤ 2 := by
  intro T hT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl
  · simp
  · exact (Finset.card_insert_le _ _).trans (by simp)

def c0 : Clause VV := ({((0, 0), true), ((0, 1), true), ((0, 2), true)} : Clause VV)

def k0 : KLine VV := kLineOfClause c0

def c1 : Clause VV := ({((1, 0), true), ((1, 1), true), ((1, 2), true)} : Clause VV)

def k1 : KLine VV := kLineOfClause c1

def c2 : Clause VV := ({((2, 0), true), ((2, 1), true), ((2, 2), true)} : Clause VV)

def k2 : KLine VV := kLineOfClause c2

def c3 : Clause VV := ({((3, 0), true), ((3, 1), true), ((3, 2), true)} : Clause VV)

def k3 : KLine VV := kLineOfClause c3

def c4 : Clause VV := ({((0, 0), false), ((1, 0), false)} : Clause VV)

def k4 : KLine VV := kLineOfClause c4

def c5 : Clause VV := ({((0, 0), false), ((2, 0), false)} : Clause VV)

def k5 : KLine VV := kLineOfClause c5

def c6 : Clause VV := ({((0, 0), false), ((3, 0), false)} : Clause VV)

def k6 : KLine VV := kLineOfClause c6

def c7 : Clause VV := ({((1, 0), false), ((2, 0), false)} : Clause VV)

def k7 : KLine VV := kLineOfClause c7

def c8 : Clause VV := ({((1, 0), false), ((3, 0), false)} : Clause VV)

def k8 : KLine VV := kLineOfClause c8

def c9 : Clause VV := ({((2, 0), false), ((3, 0), false)} : Clause VV)

def k9 : KLine VV := kLineOfClause c9

def c10 : Clause VV := ({((0, 1), false), ((1, 1), false)} : Clause VV)

def k10 : KLine VV := kLineOfClause c10

def c11 : Clause VV := ({((0, 1), false), ((2, 1), false)} : Clause VV)

def k11 : KLine VV := kLineOfClause c11

def c12 : Clause VV := ({((0, 1), false), ((3, 1), false)} : Clause VV)

def k12 : KLine VV := kLineOfClause c12

def c13 : Clause VV := ({((1, 1), false), ((2, 1), false)} : Clause VV)

def k13 : KLine VV := kLineOfClause c13

def c14 : Clause VV := ({((1, 1), false), ((3, 1), false)} : Clause VV)

def k14 : KLine VV := kLineOfClause c14

def c15 : Clause VV := ({((2, 1), false), ((3, 1), false)} : Clause VV)

def k15 : KLine VV := kLineOfClause c15

def c16 : Clause VV := ({((0, 2), false), ((1, 2), false)} : Clause VV)

def k16 : KLine VV := kLineOfClause c16

def c17 : Clause VV := ({((0, 2), false), ((2, 2), false)} : Clause VV)

def k17 : KLine VV := kLineOfClause c17

def c18 : Clause VV := ({((0, 2), false), ((3, 2), false)} : Clause VV)

def k18 : KLine VV := kLineOfClause c18

def c19 : Clause VV := ({((1, 2), false), ((2, 2), false)} : Clause VV)

def k19 : KLine VV := kLineOfClause c19

def c20 : Clause VV := ({((1, 2), false), ((3, 2), false)} : Clause VV)

def k20 : KLine VV := kLineOfClause c20

def c21 : Clause VV := ({((2, 2), false), ((3, 2), false)} : Clause VV)

def k21 : KLine VV := kLineOfClause c21

def k22 : KLine VV := ({({((2, 0), false)} : KTerm VV), ({((1, 0), false), ((3, 0), false)} : KTerm VV)} : KLine VV)

def k23 : KLine VV := ({({((2, 1), false)} : KTerm VV), ({((1, 1), false), ((3, 1), false)} : KTerm VV)} : KLine VV)

def k24 : KLine VV := ({({((2, 2), false)} : KTerm VV), ({((1, 2), false), ((3, 2), false)} : KTerm VV)} : KLine VV)

def c25 : Clause VV := ({((1, 0), true), ((1, 2), true), ((3, 1), false)} : Clause VV)

def k25 : KLine VV := kLineOfClause c25

def c26 : Clause VV := ({((1, 2), false), ((3, 0), true), ((3, 1), true)} : Clause VV)

def k26 : KLine VV := kLineOfClause c26

def c27 : Clause VV := ({((1, 0), true), ((1, 2), true), ((3, 0), true), ((3, 2), true)} : Clause VV)

def k27 : KLine VV := kLineOfClause c27

def c28 : Clause VV := ({((1, 0), true), ((2, 2), false), ((3, 0), true)} : Clause VV)

def k28 : KLine VV := kLineOfClause c28

def c29 : Clause VV := ({((1, 0), true), ((1, 1), true), ((3, 0), true), ((3, 1), true)} : Clause VV)

def k29 : KLine VV := kLineOfClause c29

def c30 : Clause VV := ({((1, 0), true), ((2, 1), false), ((3, 0), true)} : Clause VV)

def k30 : KLine VV := kLineOfClause c30

def c31 : Clause VV := ({((1, 0), true), ((2, 0), true), ((2, 1), true), ((3, 0), true)} : Clause VV)

def k31 : KLine VV := kLineOfClause c31

def c32 : Clause VV := ({((1, 0), true), ((2, 0), true), ((3, 0), true)} : Clause VV)

def k32 : KLine VV := kLineOfClause c32

def c33 : Clause VV := ({((1, 0), false), ((3, 1), true), ((3, 2), true)} : Clause VV)

def k33 : KLine VV := kLineOfClause c33

def c34 : Clause VV := ({((1, 1), true), ((2, 0), false), ((3, 1), true)} : Clause VV)

def k34 : KLine VV := kLineOfClause c34

def c35 : Clause VV := ({((1, 1), true), ((1, 2), true), ((3, 1), true), ((3, 2), true)} : Clause VV)

def k35 : KLine VV := kLineOfClause c35

def c36 : Clause VV := ({((1, 1), true), ((2, 2), false), ((3, 1), true)} : Clause VV)

def k36 : KLine VV := kLineOfClause c36

def c37 : Clause VV := ({((1, 1), true), ((2, 1), true), ((2, 2), true), ((3, 1), true)} : Clause VV)

def k37 : KLine VV := kLineOfClause c37

def c38 : Clause VV := ({((1, 1), true), ((2, 1), true), ((3, 1), true)} : Clause VV)

def k38 : KLine VV := kLineOfClause c38

def c39 : Clause VV := ({((1, 2), true), ((2, 0), false), ((3, 2), true)} : Clause VV)

def k39 : KLine VV := kLineOfClause c39

def c40 : Clause VV := ({((1, 2), true), ((2, 1), false), ((3, 2), true)} : Clause VV)

def k40 : KLine VV := kLineOfClause c40

def c41 : Clause VV := ({((1, 2), true), ((2, 1), true), ((2, 2), true), ((3, 2), true)} : Clause VV)

def k41 : KLine VV := kLineOfClause c41

def c42 : Clause VV := ({((1, 2), true), ((2, 2), true), ((3, 2), true)} : Clause VV)

def k42 : KLine VV := kLineOfClause c42

def c43 : Clause VV := ({((0, 0), false), ((2, 0), true), ((3, 0), true)} : Clause VV)

def k43 : KLine VV := kLineOfClause c43

def c44 : Clause VV := ({((0, 0), false), ((3, 0), true)} : Clause VV)

def k44 : KLine VV := kLineOfClause c44

def c45 : Clause VV := ({((0, 0), false)} : Clause VV)

def k45 : KLine VV := kLineOfClause c45

def c46 : Clause VV := ({((0, 1), false), ((2, 1), true), ((3, 1), true)} : Clause VV)

def k46 : KLine VV := kLineOfClause c46

def c47 : Clause VV := ({((0, 1), false), ((3, 1), true)} : Clause VV)

def k47 : KLine VV := kLineOfClause c47

def c48 : Clause VV := ({((0, 1), false)} : Clause VV)

def k48 : KLine VV := kLineOfClause c48

def c49 : Clause VV := ({((0, 2), false), ((2, 2), true), ((3, 2), true)} : Clause VV)

def k49 : KLine VV := kLineOfClause c49

def c50 : Clause VV := ({((0, 2), false), ((3, 2), true)} : Clause VV)

def k50 : KLine VV := kLineOfClause c50

def c51 : Clause VV := ({((0, 2), false)} : Clause VV)

def k51 : KLine VV := kLineOfClause c51

def c52 : Clause VV := ({((0, 1), true), ((0, 2), true)} : Clause VV)

def k52 : KLine VV := kLineOfClause c52

def c53 : Clause VV := ({((0, 2), true)} : Clause VV)

def k53 : KLine VV := kLineOfClause c53

def c54 : Clause VV := (∅ : Clause VV)

def k54 : KLine VV := kLineOfClause c54

def p0 : List (KLine VV) := [k0]

def p1 : List (KLine VV) := k1 :: p0

def p2 : List (KLine VV) := k2 :: p1

def p3 : List (KLine VV) := k3 :: p2

def p4 : List (KLine VV) := k4 :: p3

def p5 : List (KLine VV) := k5 :: p4

def p6 : List (KLine VV) := k6 :: p5

def p7 : List (KLine VV) := k7 :: p6

def p8 : List (KLine VV) := k8 :: p7

def p9 : List (KLine VV) := k9 :: p8

def p10 : List (KLine VV) := k10 :: p9

def p11 : List (KLine VV) := k11 :: p10

def p12 : List (KLine VV) := k12 :: p11

def p13 : List (KLine VV) := k13 :: p12

def p14 : List (KLine VV) := k14 :: p13

def p15 : List (KLine VV) := k15 :: p14

def p16 : List (KLine VV) := k16 :: p15

def p17 : List (KLine VV) := k17 :: p16

def p18 : List (KLine VV) := k18 :: p17

def p19 : List (KLine VV) := k19 :: p18

def p20 : List (KLine VV) := k20 :: p19

def p21 : List (KLine VV) := k21 :: p20

def p22 : List (KLine VV) := k22 :: p21

def p23 : List (KLine VV) := k23 :: p22

def p24 : List (KLine VV) := k24 :: p23

def p25 : List (KLine VV) := k25 :: p24

def p26 : List (KLine VV) := k26 :: p25

def p27 : List (KLine VV) := k27 :: p26

def p28 : List (KLine VV) := k28 :: p27

def p29 : List (KLine VV) := k29 :: p28

def p30 : List (KLine VV) := k30 :: p29

def p31 : List (KLine VV) := k31 :: p30

def p32 : List (KLine VV) := k32 :: p31

def p33 : List (KLine VV) := k33 :: p32

def p34 : List (KLine VV) := k34 :: p33

def p35 : List (KLine VV) := k35 :: p34

def p36 : List (KLine VV) := k36 :: p35

def p37 : List (KLine VV) := k37 :: p36

def p38 : List (KLine VV) := k38 :: p37

def p39 : List (KLine VV) := k39 :: p38

def p40 : List (KLine VV) := k40 :: p39

def p41 : List (KLine VV) := k41 :: p40

def p42 : List (KLine VV) := k42 :: p41

def p43 : List (KLine VV) := k43 :: p42

def p44 : List (KLine VV) := k44 :: p43

def p45 : List (KLine VV) := k45 :: p44

def p46 : List (KLine VV) := k46 :: p45

def p47 : List (KLine VV) := k47 :: p46

def p48 : List (KLine VV) := k48 :: p47

def p49 : List (KLine VV) := k49 :: p48

def p50 : List (KLine VV) := k50 :: p49

def p51 : List (KLine VV) := k51 :: p50

def p52 : List (KLine VV) := k52 :: p51

def p53 : List (KLine VV) := k53 :: p52

def p54 : List (KLine VV) := k54 :: p53

set_option maxRecDepth 100000 in
theorem d0 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p0 :=
  IsResKDerivation.ax IsResKDerivation.nil ⟨c0, Set.mem_union_left _ ⟨0, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d1 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p1 :=
  IsResKDerivation.ax d0 ⟨c1, Set.mem_union_left _ ⟨1, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d2 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p2 :=
  IsResKDerivation.ax d1 ⟨c2, Set.mem_union_left _ ⟨2, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d3 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p3 :=
  IsResKDerivation.ax d2 ⟨c3, Set.mem_union_left _ ⟨3, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d4 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p4 :=
  IsResKDerivation.ax d3 ⟨c4, Set.mem_union_right _ ⟨0, 1, 0, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d5 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p5 :=
  IsResKDerivation.ax d4 ⟨c5, Set.mem_union_right _ ⟨0, 2, 0, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d6 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p6 :=
  IsResKDerivation.ax d5 ⟨c6, Set.mem_union_right _ ⟨0, 3, 0, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d7 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p7 :=
  IsResKDerivation.ax d6 ⟨c7, Set.mem_union_right _ ⟨1, 2, 0, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d8 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p8 :=
  IsResKDerivation.ax d7 ⟨c8, Set.mem_union_right _ ⟨1, 3, 0, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d9 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p9 :=
  IsResKDerivation.ax d8 ⟨c9, Set.mem_union_right _ ⟨2, 3, 0, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d10 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p10 :=
  IsResKDerivation.ax d9 ⟨c10, Set.mem_union_right _ ⟨0, 1, 1, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d11 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p11 :=
  IsResKDerivation.ax d10 ⟨c11, Set.mem_union_right _ ⟨0, 2, 1, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d12 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p12 :=
  IsResKDerivation.ax d11 ⟨c12, Set.mem_union_right _ ⟨0, 3, 1, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d13 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p13 :=
  IsResKDerivation.ax d12 ⟨c13, Set.mem_union_right _ ⟨1, 2, 1, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d14 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p14 :=
  IsResKDerivation.ax d13 ⟨c14, Set.mem_union_right _ ⟨1, 3, 1, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d15 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p15 :=
  IsResKDerivation.ax d14 ⟨c15, Set.mem_union_right _ ⟨2, 3, 1, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d16 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p16 :=
  IsResKDerivation.ax d15 ⟨c16, Set.mem_union_right _ ⟨0, 1, 2, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d17 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p17 :=
  IsResKDerivation.ax d16 ⟨c17, Set.mem_union_right _ ⟨0, 2, 2, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d18 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p18 :=
  IsResKDerivation.ax d17 ⟨c18, Set.mem_union_right _ ⟨0, 3, 2, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d19 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p19 :=
  IsResKDerivation.ax d18 ⟨c19, Set.mem_union_right _ ⟨1, 2, 2, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d20 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p20 :=
  IsResKDerivation.ax d19 ⟨c20, Set.mem_union_right _ ⟨1, 3, 2, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d21 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p21 :=
  IsResKDerivation.ax d20 ⟨c21, Set.mem_union_right _ ⟨2, 3, 2, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

set_option maxRecDepth 100000 in
theorem d22 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p22 :=
  IsResKDerivation.andIntro (C := k7) (D := k9) (R := k22) d21 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))) (andQ (V := VV) (((2, 0), false) : Literal VV) (((1, 0), false) : Literal VV) (((3, 0), false) : Literal VV) (by decide) (by decide)) (cardQ (V := VV) (((2, 0), false) : Literal VV) (((1, 0), false) : Literal VV) (((3, 0), false) : Literal VV))

set_option maxRecDepth 100000 in
theorem d23 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p23 :=
  IsResKDerivation.andIntro (C := k13) (D := k15) (R := k23) d22 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) (andQ (V := VV) (((2, 1), false) : Literal VV) (((1, 1), false) : Literal VV) (((3, 1), false) : Literal VV) (by decide) (by decide)) (cardQ (V := VV) (((2, 1), false) : Literal VV) (((1, 1), false) : Literal VV) (((3, 1), false) : Literal VV))

set_option maxRecDepth 100000 in
theorem d24 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p24 :=
  IsResKDerivation.andIntro (C := k19) (D := k21) (R := k24) d23 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (andQ (V := VV) (((2, 2), false) : Literal VV) (((1, 2), false) : Literal VV) (((3, 2), false) : Literal VV) (by decide) (by decide)) (cardQ (V := VV) (((2, 2), false) : Literal VV) (((1, 2), false) : Literal VV) (((3, 2), false) : Literal VV))

set_option maxRecDepth 100000 in
theorem d25 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p25 :=
  IsResKDerivation.cut (C := k1) (D := k14) (R := k25) d24 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))) (liftRes (C := c1) (D := c14) (R := c25) ⟨(1, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d26 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p26 :=
  IsResKDerivation.cut (C := k3) (D := k20) (R := k26) d25 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) (liftRes (C := c3) (D := c20) (R := c26) ⟨(3, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d27 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p27 :=
  IsResKDerivation.cut (C := k3) (D := k25) (R := k27) d26 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.head _)) (liftRes (C := c3) (D := c25) (R := c27) ⟨(3, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d28 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p28 :=
  IsResKDerivation.cut (C := k24) (D := k27) (R := k28) d27 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _) (cutQ (V := VV) (((2, 2), false) : Literal VV) (((1, 2), false) : Literal VV) (((3, 2), false) : Literal VV) c27 c28 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d29 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p29 :=
  IsResKDerivation.cut (C := k1) (D := k26) (R := k29) d28 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (liftRes (C := c1) (D := c26) (R := c29) ⟨(1, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d30 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p30 :=
  IsResKDerivation.cut (C := k23) (D := k29) (R := k30) d29 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.head _) (cutQ (V := VV) (((2, 1), false) : Literal VV) (((1, 1), false) : Literal VV) (((3, 1), false) : Literal VV) c29 c30 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d31 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p31 :=
  IsResKDerivation.cut (C := k2) (D := k28) (R := k31) d30 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (liftRes (C := c2) (D := c28) (R := c31) ⟨(2, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d32 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p32 :=
  IsResKDerivation.cut (C := k31) (D := k30) (R := k32) d31 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) (liftRes (C := c31) (D := c30) (R := c32) ⟨(2, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d33 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p33 :=
  IsResKDerivation.cut (C := k3) (D := k8) (R := k33) d32 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))) (liftRes (C := c3) (D := c8) (R := c33) ⟨(3, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d34 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p34 :=
  IsResKDerivation.cut (C := k22) (D := k29) (R := k34) d33 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (cutQ (V := VV) (((2, 0), false) : Literal VV) (((1, 0), false) : Literal VV) (((3, 0), false) : Literal VV) c29 c34 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d35 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p35 :=
  IsResKDerivation.cut (C := k1) (D := k33) (R := k35) d34 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.head _)) (liftRes (C := c1) (D := c33) (R := c35) ⟨(1, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d36 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p36 :=
  IsResKDerivation.cut (C := k24) (D := k35) (R := k36) d35 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))) (List.Mem.head _) (cutQ (V := VV) (((2, 2), false) : Literal VV) (((1, 2), false) : Literal VV) (((3, 2), false) : Literal VV) c35 c36 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d37 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p37 :=
  IsResKDerivation.cut (C := k2) (D := k34) (R := k37) d36 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (liftRes (C := c2) (D := c34) (R := c37) ⟨(2, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d38 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p38 :=
  IsResKDerivation.cut (C := k37) (D := k36) (R := k38) d37 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) (liftRes (C := c37) (D := c36) (R := c38) ⟨(2, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d39 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p39 :=
  IsResKDerivation.cut (C := k22) (D := k27) (R := k39) d38 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))) (cutQ (V := VV) (((2, 0), false) : Literal VV) (((1, 0), false) : Literal VV) (((3, 0), false) : Literal VV) c27 c39 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d40 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p40 :=
  IsResKDerivation.cut (C := k23) (D := k35) (R := k40) d39 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (cutQ (V := VV) (((2, 1), false) : Literal VV) (((1, 1), false) : Literal VV) (((3, 1), false) : Literal VV) c35 c40 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel))

set_option maxRecDepth 100000 in
theorem d41 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p41 :=
  IsResKDerivation.cut (C := k2) (D := k39) (R := k41) d40 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.head _)) (liftRes (C := c2) (D := c39) (R := c41) ⟨(2, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d42 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p42 :=
  IsResKDerivation.cut (C := k41) (D := k40) (R := k42) d41 (List.Mem.head _) (List.Mem.tail _ (List.Mem.head _)) (liftRes (C := c41) (D := c40) (R := c42) ⟨(2, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d43 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p43 :=
  IsResKDerivation.cut (C := k32) (D := k4) (R := k43) d42 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))) (liftRes (C := c32) (D := c4) (R := c43) ⟨(1, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d44 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p44 :=
  IsResKDerivation.cut (C := k43) (D := k5) (R := k44) d43 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))) (liftRes (C := c43) (D := c5) (R := c44) ⟨(2, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d45 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p45 :=
  IsResKDerivation.cut (C := k44) (D := k6) (R := k45) d44 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))))))))) (liftRes (C := c44) (D := c6) (R := c45) ⟨(3, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d46 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p46 :=
  IsResKDerivation.cut (C := k38) (D := k10) (R := k46) d45 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) (liftRes (C := c38) (D := c10) (R := c46) ⟨(1, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d47 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p47 :=
  IsResKDerivation.cut (C := k46) (D := k11) (R := k47) d46 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) (liftRes (C := c46) (D := c11) (R := c47) ⟨(2, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d48 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p48 :=
  IsResKDerivation.cut (C := k47) (D := k12) (R := k48) d47 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))) (liftRes (C := c47) (D := c12) (R := c48) ⟨(3, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d49 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p49 :=
  IsResKDerivation.cut (C := k42) (D := k16) (R := k49) d48 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))) (liftRes (C := c42) (D := c16) (R := c49) ⟨(1, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d50 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p50 :=
  IsResKDerivation.cut (C := k49) (D := k17) (R := k50) d49 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))) (liftRes (C := c49) (D := c17) (R := c50) ⟨(2, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d51 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p51 :=
  IsResKDerivation.cut (C := k50) (D := k18) (R := k51) d50 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))) (liftRes (C := c50) (D := c18) (R := c51) ⟨(3, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d52 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p52 :=
  IsResKDerivation.cut (C := k0) (D := k45) (R := k52) d51 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))) (liftRes (C := c0) (D := c45) (R := c52) ⟨(0, 0), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d53 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p53 :=
  IsResKDerivation.cut (C := k52) (D := k48) (R := k53) d52 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (liftRes (C := c52) (D := c48) (R := c53) ⟨(0, 1), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem d54 : IsResKDerivation 2 ((fun C => kLineOfClause C) '' PHP 4 3) p54 :=
  IsResKDerivation.cut (C := k53) (D := k51) (R := k54) d53 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (liftRes (C := c53) (D := c51) (R := c54) ⟨(0, 2), by decide +kernel, by decide +kernel, by decide +kernel⟩)

set_option maxRecDepth 100000 in
theorem main_aux : ∃ π : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsResKRefutation 2 (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 57 := by
  have hm : k54 ∈ p54 := List.Mem.head _
  have e0 : k54 = ∅ := by simp [k54, c54, kLineOfClause]
  rw [e0] at hm
  exact ⟨p54, ⟨d54, hm⟩, by decide +kernel⟩

end PEqualNP.Outside.L_pcx_191

theorem PEqualNP.Outside.L_pcx_191 : ∃ π : List (PEqualNP.ProofComplexity.KLine (Fin 4 × Fin 3)), PEqualNP.ProofComplexity.IsResKRefutation 2 (PEqualNP.ProofComplexity.PHP 4 3) π ∧ π.length ≤ 57 :=
  PEqualNP.Outside.L_pcx_191.main_aux
