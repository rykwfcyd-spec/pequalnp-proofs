import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20920_aon : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧
    PEqualNP.Represents.Represents
      (fun (u : Fin 4) (v : Fin 5) =>
        (39737 : Nat).testBit (5 * u.val + v.val)) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 6] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 9] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 10] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [11] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 10] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 14] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 15] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
