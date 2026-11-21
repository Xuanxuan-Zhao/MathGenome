import MathGenome.Internal.AlgebraCore.Specs.P103.Ch03.Semisimple

/-! Simple and semisimple modules, paper.tex, Theorem 3.1.
All results apply to right modules by substituting the opposite scalar ring.
No commutativity, finite generation, or nonzero scalar-ring assumption is used.
-/

namespace P103.Ch03.Semisimple

open P103.Specs.Ch03.Semisimple

theorem simple_iff : simple_iffType := by
  intro R M _ _ _
  constructor
  · intro h
    exact ⟨IsSimpleModule.nontrivial R M, fun U => eq_bot_or_eq_top U⟩
  · rintro ⟨hM, h⟩
    haveI := hM
    exact (isSimpleModule_iff R M).mpr ⟨h⟩

theorem schur : schurType := by
  intro R M N _ _ _ _ _ _ _ f hf
  exact ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf), rfl⟩

noncomputable def endomorphismDivisionRing : endomorphismDivisionRingType :=
  endomorphismDivisionRingValue

theorem endomorphism_ring_compatible : endomorphism_ring_compatibleType := by
  intro R M _ _ _ _
  rfl

theorem semisimple_iff_directSum : semisimple_iff_directSumType := by
  intro R M _ _ _
  exact isSemisimpleModule_iff_exists_linearEquiv_dfinsupp

theorem semisimple_iff_sum : semisimple_iff_sumType := by
  intro R M _ _ _
  exact sSup_simples_eq_top_iff_isSemisimpleModule.symm

theorem semisimple_iff_summand : semisimple_iff_summandType := by
  intro R M _ _ _
  rw [isSemisimpleModule_iff, complementedLattice_iff]

theorem internal_decomposition : internal_decompositionType := by
  intro R M _ _ _ _
  exact IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top R M

theorem submodule : submoduleType := by
  intro R M _ _ _ _ U
  infer_instance

theorem quotient : quotientType := by
  intro R M _ _ _ _ U
  infer_instance

theorem arbitrary_directSum : arbitrary_directSumType := by
  intro R ι S _ _ _ _
  infer_instance

theorem zero : zeroType := by
  intro R M _ _ _ _
  haveI : Subsingleton (Submodule R M) := (Submodule.subsingleton_iff R).mpr inferInstance
  exact (isSemisimpleModule_iff R M).mpr Subsingleton.instComplementedLattice

end P103.Ch03.Semisimple
