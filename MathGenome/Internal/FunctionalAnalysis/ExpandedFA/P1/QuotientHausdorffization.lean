import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.QuotientHausdorffization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C02QuotientMap
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.SeminormNullQuotient

/-! Hausdorffization of the distance-seminorm quotient, paper.tex lines 397–400. -/

noncomputable section

namespace ExpandedFA.P1.QuotientHausdorffization

/-- A null coset is represented precisely by a vector in the closure of `M`. -/
theorem quotient_null_subspace_identification :
    Spec.NullSubspaceIdentification := by
  intro 𝕜 E _ _ _ M
  ext z
  obtain ⟨x, rfl⟩ := M.mkQ_surjective z
  constructor
  · intro hx
    exact ⟨x, (C02QuotientMap.quotient_null_cosets 𝕜 E M x).mp hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    change ‖M.mkQ x‖ = 0
    rw [← hxy]
    exact (C02QuotientMap.quotient_null_cosets 𝕜 E M y).mpr hy

/-- Apply the isometric third isomorphism theorem after identifying the null space.
The computation on representatives fixes the intended canonical map. -/
theorem quotient_hausdorff_isometry :
    Spec.HausdorffIsometry := by
  intro 𝕜 E _ _ _ M
  let e := (Submodule.quotLIEOfEq (nullSpace M)
    (M.topologicalClosure.map M.mkQ)
    (quotient_null_subspace_identification 𝕜 E M)).trans
    (M.quotientQuotientLIEQuotient M.topologicalClosure M.le_topologicalClosure)
  refine ⟨e, ?_⟩
  intro x
  rfl

/-- Quotienting by zero-seminorm vectors leaves the seminorm value unchanged.
Comparison with the closed quotient proves definiteness of this exact value. -/
theorem quotient_hausdorff_norm : Spec.HausdorffNorm := by
  intro 𝕜 E _ _ _ M
  have hnorm : ∀ z : E ⧸ M, ‖(nullSpace M).mkQ z‖ = ‖z‖ := by
    intro z
    apply le_antisymm (Submodule.Quotient.norm_mk_le _ z)
    apply QuotientAddGroup.le_norm_iff.mpr
    intro y hy
    have hnull : ‖y - z‖ = 0 :=
      (Submodule.Quotient.eq (nullSpace M)).mp hy
    have hle := norm_sub_norm_le z y
    rw [norm_sub_rev, hnull] at hle
    exact sub_nonpos.mp hle
  refine ⟨hnorm, ?_, ?_⟩
  · intro w
    obtain ⟨z, rfl⟩ := (nullSpace M).mkQ_surjective w
    rw [hnorm]
    exact (SeminormNullQuotient.seminorm_null_quotient_value 𝕜 (E ⧸ M)
      (C02QuotientNorm.Spec.distanceSeminormValue 𝕜 E M) z).symm
  · obtain ⟨e, _⟩ := quotient_hausdorff_isometry 𝕜 E M
    refine ⟨C01Norm.canonical_seminorm_axioms 𝕜 (Space M), ?_⟩
    intro w
    let : IsClosed (M.topologicalClosure : Set E) := M.isClosed_topologicalClosure
    rw [← e.norm_map, norm_eq_zero]
    exact ⟨fun h => e.injective (h.trans e.map_zero.symm), fun h => h ▸ e.map_zero⟩

/-- Density kills every seminorm value; properness preserves nonzero algebraic cosets. -/
theorem dense_proper_quotient : Spec.DenseProperQuotient := by
  intro 𝕜 E _ _ _ M hd hp
  refine ⟨Submodule.Quotient.nontrivial_iff.mpr hp, ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := M.mkQ_surjective z
  exact (C02QuotientMap.quotient_null_cosets 𝕜 E M x).mpr (hd x)

end ExpandedFA.P1.QuotientHausdorffization
