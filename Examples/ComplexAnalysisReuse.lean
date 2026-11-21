import Examples.ComplexAnalysisReuseSpecs
import Mathlib.Tactic.Ring

/-! Six downstream applications of the public complex-analysis chapter entries.
No proof is a copied upstream module or an assumed conclusion. -/

noncomputable section
open Set

namespace Examples.GenomeComplexProbe

theorem realJacobianPositive :
    Examples.GenomeComplexProbeSpecs.realJacobianPositive := by
  intro f c a hderiv hc
  obtain ⟨hintrinsic, hmatrix⟩ := D12Complex.realDifferential_det f c a hderiv
  have hpositive : 0 < ‖c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
  exact ⟨hintrinsic.symm ▸ hpositive, hmatrix.symm ▸ hpositive⟩

theorem omittedValuesDerivativesVanish :
    Examples.GenomeComplexProbeSpecs.omittedValuesDerivativesVanish := by
  intro f a b hf hab ha hb
  obtain ⟨c, hc⟩ := D12Complex.LittlePicard.omits_two_constant f a b hf hab ha hb
  have hconstant : f = fun _ : ℂ => c := funext hc
  intro z
  rw [hconstant]
  simp

theorem schwarzEqualityPreservesDistances :
    Examples.GenomeComplexProbeSpecs.schwarzEqualityPreservesDistances := by
  intro f hf hmaps hzero heq
  obtain ⟨c, hc, hrotation⟩ :=
    D12Complex.Schwarz.rotation_of_norm_deriv_eq_one f hf hmaps hzero heq
  intro z hz w hw
  rw [hrotation z hz, hrotation w hw]
  simp only [dist_eq_norm, ← mul_sub, norm_mul, hc, one_mul]

theorem zeroPeriodsRectifiablePrimitive :
    Examples.GenomeComplexProbeSpecs.zeroPeriodsRectifiablePrimitive := by
  intro Ω f hΩ hf hperiods
  have hendpoint :=
    (D12Complex.Primitives.endpointIndependent_iff_zeroPeriods Ω f hf).mpr hperiods
  obtain ⟨F, hF⟩ :=
    D12Complex.Primitives.exists_primitive_of_endpointIndependent Ω f hΩ hf hendpoint
  exact ⟨F, hF, fun γ hrect htrace =>
    D12Complex.Primitives.rectifiable_endpoint Ω f F hf hF γ hrect htrace⟩

theorem normalizedPrimitiveUnique :
    Examples.GenomeComplexProbeSpecs.normalizedPrimitiveUnique := by
  intro Ω f F G a hΩ ha hF hG hbase
  obtain ⟨c, hc⟩ := D12Complex.Primitives.primitive_unique Ω f F G hΩ hF hG
  have hc0 : c = 0 := by
    calc
      c = (G a + c) - G a := by ring
      _ = F a - G a := by rw [hc a ha]
      _ = 0 := sub_eq_zero.mpr hbase
  intro z hz
  simpa only [hc0, add_zero] using hc z hz

theorem componentAndFullGermCountability :
    Examples.GenomeComplexProbeSpecs.componentAndFullGermCountability := by
  intro Ω hΩ p
  obtain ⟨S, _, _⟩ := D12Complex.ContinuationSurface.continuation_surface Ω hΩ p
  exact ⟨S.secondCountable,
    D12Complex.GermSpaceCountability.fullSpace_not_secondCountable⟩

end Examples.GenomeComplexProbe
