import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05Restriction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04DualMaps

/-! Restriction as an isometric quotient (paper.tex 992–1014).
Hahn–Banach supplies norm-minimizing representatives of each restriction
fiber. The distance quotient norm is consequently exactly the restriction norm.
The annihilator is closed even when the original subspace is not closed. -/

noncomputable section

namespace ExpandedFA.P1.C05Restriction

universe u v

/-- The kernel computation does not use closedness or Hahn–Banach. -/
theorem dualRestriction_ker (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M : Submodule 𝕜 E) :
    (C04DualMaps.dualRestriction 𝕜 E M).ker = C04Annihilators.annihilator 𝕜 E (M : Set E) := by
  ext f
  constructor
  · intro hf m hm
    have h := congrArg (fun g : M →L[𝕜] 𝕜 => g ⟨m, hm⟩) hf
    exact h
  · intro hf
    apply ContinuousLinearMap.ext
    intro m
    exact hf m.val m.property

/-- Every restriction fiber has a representative attaining its least norm. -/
theorem dualRestriction_extension (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (g : M →L[𝕜] 𝕜) :
    ∃ f : E →L[𝕜] 𝕜, C04DualMaps.dualRestriction 𝕜 E M f = g ∧ ‖f‖ = ‖g‖ := by
  obtain ⟨f, hf, hn⟩ := C05NormExtension.norm_preserving_extension 𝕜 E M g
  exact ⟨f, ContinuousLinearMap.ext hf, hn⟩

theorem restriction_properties : Spec.RestrictionProperties.{u, v} := by
  intro 𝕜 E _ _ _ M
  refine ⟨C04DualMaps.dualRestriction_norm_le 𝕜 E M, ?_, dualRestriction_ker 𝕜 E M,
    dualRestriction_extension 𝕜 E M⟩
  intro g
  obtain ⟨f, hf, _⟩ := dualRestriction_extension 𝕜 E M g
  exact ⟨f, hf⟩

/-- Restriction factors to a surjective linear isometry on the distance quotient.
Contractivity gives the lower bound for the quotient norm, and a Hahn–Banach
extension in the same coset gives the upper bound. -/
theorem restriction_quotient_isometry :
    Spec.RestrictionQuotientIsometry.{u, v} := by
  intro 𝕜 E _ _ _ M
  let N := C04Annihilators.annihilator 𝕜 E (M : Set E)
  have hN : IsClosed (N : Set (E →L[𝕜] 𝕜)) := C04DualMaps.annihilator_isClosed 𝕜 E (M : Set E)
  refine ⟨hN, ?_⟩
  let : IsClosed (N : Set (E →L[𝕜] 𝕜)) := hN
  let := C02QuotientNorm.Spec.quotientNormedGroupValue 𝕜 (E →L[𝕜] 𝕜) N hN
  let r := C04DualMaps.dualRestriction 𝕜 E M
  have hker : N ≤ r.ker := (dualRestriction_ker 𝕜 E M).ge
  let L : ((E →L[𝕜] 𝕜) ⧸ N) →ₗ[𝕜] (M →L[𝕜] 𝕜) := N.liftQ r.toLinearMap hker
  have hL (f : E →L[𝕜] 𝕜) : L (N.mkQ f) = r f := rfl
  have hnorm (z : (E →L[𝕜] 𝕜) ⧸ N) : ‖L z‖ = ‖z‖ := by
    apply le_antisymm
    · exact (QuotientFactorization.quotient_lift_bound N r hker z).trans
        ((mul_le_mul_of_nonneg_right (C04DualMaps.dualRestriction_norm_le 𝕜 E M)
          (norm_nonneg z)).trans_eq (one_mul _))
    · obtain ⟨f, rfl⟩ := N.mkQ_surjective z
      obtain ⟨F, hF, hn⟩ := dualRestriction_extension 𝕜 E M (r f)
      have heq : N.mkQ F = N.mkQ f := by
        apply (Submodule.Quotient.eq N).mpr
        change F - f ∈ C04Annihilators.annihilator 𝕜 E (M : Set E)
        rw [← dualRestriction_ker 𝕜 E M]
        change r (F - f) = 0
        rw [map_sub, hF, sub_self]
      calc
        ‖N.mkQ f‖ = ‖N.mkQ F‖ := congrArg norm heq.symm
        _ ≤ ‖F‖ := Submodule.Quotient.norm_mk_le N F
        _ = ‖r f‖ := hn
        _ = ‖L (N.mkQ f)‖ := rfl
  let I : ((E →L[𝕜] 𝕜) ⧸ N) →ₗᵢ[𝕜] (M →L[𝕜] 𝕜) :=
    { L with norm_map' := hnorm }
  have hsurj : Function.Surjective I := by
    intro g
    obtain ⟨f, hf, _⟩ := dualRestriction_extension 𝕜 E M g
    exact ⟨N.mkQ f, hf⟩
  have hinj : Function.Injective L := by
    intro x y h
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [← hnorm, map_sub, h, sub_self, norm_zero]
  let e : ((E →L[𝕜] 𝕜) ⧸ N) ≃ₗᵢ[𝕜] (M →L[𝕜] 𝕜) :=
    { toLinearEquiv := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
      norm_map' := hnorm }
  exact ⟨e, hL⟩

/-- Retain the closed-subspace quotient-dual identification by composition with q. -/
theorem restriction_closed_quotient_dual_isometry :
    Spec.ClosedQuotientDualIsometry.{u, v} :=
  C04DualMaps.quotient_dual_isometry

end ExpandedFA.P1.C05Restriction
