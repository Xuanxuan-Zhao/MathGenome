import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.CartanQuotient
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.MinimalRealization
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.Center

/-! The center of the canonical contragredient Lie algebra. -/

namespace LieNotes.Contragredient.Center

open CartanQuotient

universe u v

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H]

/-- A central element has weight zero. In the Cartan, vanishing of the root evaluations
is equivalent to commuting with the generators, hence with the whole quotient. -/
theorem center_eq_map_common_kernel [Finite I] (R : Realization A H) :
    (LieAlgebra.center ℂ (Algebra R)).toSubmodule =
      (⨅ i, LinearMap.ker (R.α i)).map (cartan R) := by
  apply le_antisymm
  · intro x hx
    have hcentral : ∀ y : Algebra R, ⁅y, x⁆ = 0 := hx
    have hgrade : x ∈ grade R 0 :=
      (mem_grade R).mpr fun h => by simp [hcentral]
    rw [grade_zero] at hgrade
    obtain ⟨h, rfl⟩ := hgrade
    refine ⟨h, (Submodule.mem_iInf _).mpr (fun i => LinearMap.mem_ker.mpr ?_), rfl⟩
    have he : ⁅cartan R h, e R i⁆ = 0 := by rw [← lie_skew, hcentral, neg_zero]
    rw [(definingRelations R).cartan_e] at he
    exact (smul_eq_zero.mp he).resolve_right (e_ne_zero R i)
  · rintro _ ⟨h, hh, rfl⟩
    have hroot (i : I) : R.α i h = 0 :=
      LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hh i)
    have hrel := definingRelations R
    intro x
    rw [← lie_skew, neg_eq_zero]
    have hx : x ∈ LieSubalgebra.lieSpan ℂ (Algebra R)
        (Set.range (cartan R) ∪ Set.range (e R) ∪ Set.range (f R)) := by
      rw [generated R]
      exact LieSubalgebra.mem_top x
    induction hx using LieSubalgebra.lieSpan_induction with
    | mem x hx =>
        rcases hx with (⟨k, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
        · exact hrel.cartan_cartan h k
        · rw [hrel.cartan_e, hroot, zero_smul]
        · rw [hrel.cartan_f, hroot, zero_smul, neg_zero]
    | zero => exact lie_zero _
    | add x y _ _ hx hy => rw [lie_add, hx, hy, zero_add]
    | smul t x _ hx => rw [lie_smul, hx, smul_zero]
    | lie x y _ _ hx hy => rw [leibniz_lie, hx, hy, zero_lie, lie_zero, zero_add]

/-- The embedded common kernel has the dimension computed by rank-nullity in the realization. -/
theorem minimal_realization_center_finrank [Fintype I] (R : Realization A H) (hR : R.IsMinimal) :
    Module.finrank ℂ (LieAlgebra.center ℂ (Algebra R)) =
      Fintype.card I - (A.map fun a : ℤ => (a : ℂ)).rank := by
  change Module.finrank ℂ ↥(LieAlgebra.center ℂ (Algebra R)).toSubmodule = _
  rw [center_eq_map_common_kernel]
  exact (Submodule.equivMapOfInjective (cartan R) (cartan_injective R) _).finrank_eq.symm.trans
    (minimal_realization_common_kernel_finrank R hR)

/-- The Cartan-disjoint ideal theorem, including the center of the same canonical quotient. -/
theorem cartan_disjoint_ideal_and_center :
    Specs.LieNotes.Contragredient.Center.CartanDisjointIdealAndCenter.{u, v} :=
  ⟨@cartanDisjointIdeal_isGreatest, @cartan_injective, @triangularAdd_bijective, @grade_eq_map,
    @grade_isInternal, @lie_mem_grade, @grade_zero, @iSup_negative_grade, @iSup_positive_grade,
    @center_eq_map_common_kernel, @minimal_realization_center_finrank, @eq_bot_of_disjoint_cartan⟩

end LieNotes.Contragredient.Center
