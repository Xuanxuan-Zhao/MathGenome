import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Differential.Definitions

open scoped Topology Asymptotics ContDiff

namespace ExpandedFA.Differential

/-- The domain's Fréchet derivative is Mathlib's native chosen derivative. -/
noncomputable def frechetDerivative : Spec.FrechetDerivativeType :=
  fun 𝕜 _ _ _ _ _ _ _ _ _ Ω f x => fderivWithin 𝕜 f Ω x

/-- The manuscript's small-o definition, using Mathlib's native derivative. -/
theorem frechet_derivative_iff_smallO : Spec.FrechetDerivativeSmallO := by
  intro 𝕜 E F _ _ _ _ _ _ _ Ω hΩ f x hx A
  rw [Asymptotics.isLittleO_norm_norm, ← hasFDerivAt_iff_isLittleO_nhds_zero]
  exact ⟨fun h => h.hasFDerivAt (hΩ.mem_nhds hx), fun h => h.hasFDerivWithinAt⟩

/-- The native chosen derivative realizes every small-o candidate. -/
theorem frechetDerivative_eq_of_smallO : Spec.CanonicalDerivativeIdentification := by
  intro 𝕜 E F _ _ _ _ _ _ _ Ω hΩ f x hx A hA
  exact ((frechet_derivative_iff_smallO 𝕜 E F Ω hΩ f x hx A).mpr hA).fderivWithin
    (hΩ.uniqueDiffOn x hx)

/-- Uniqueness follows from the two small-o hypotheses, not from any
assumed derivative or certificate. Mathlib's uniqueness theorem compares the
rescaled increments along tangent vectors. -/
theorem smallO_derivative_unique : Spec.SmallOUniqueness := by
  intro 𝕜 E F _ _ _ _ _ _ _ f x A B hA hB
  exact (hasFDerivAt_iff_isLittleO_nhds_zero.mpr hA.of_norm_norm).unique
    (hasFDerivAt_iff_isLittleO_nhds_zero.mpr hB.of_norm_norm)

/-- C¹ is existence everywhere and operator-norm continuity of the derivative. -/
theorem c1_iff_continuous_derivative_field : Spec.C1DerivativeField := by
  intro 𝕜 E F _ _ _ _ _ _ _ Ω hΩ f
  simpa [contDiffOn_zero] using
    (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (𝕜 := 𝕜) (f := f) (n := 0) hΩ.uniqueDiffOn)

/-- In this characterization the derivative can be the canonical `fderiv`. -/
theorem c1_iff_continuous_fderiv : Spec.C1CanonicalDerivative := by
  intro 𝕜 E F _ _ _ _ _ _ _ Ω hΩ f
  simpa [contDiffOn_zero] using
    (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := 𝕜) (f := f) (n := 0) hΩ)

end ExpandedFA.Differential
