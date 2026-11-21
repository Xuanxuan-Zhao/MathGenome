import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.MomentIdentities

/-!
# Finite second moments, variance, and covariance

This formalizes the definitions and identities in paper.tex 925–939. We use
Mathlib's canonical variance (the real value of its extended variance) and
covariance. The L² assumptions ensure that every displayed integrand is
integrable. Hölder's inequality gives integrability of products; centering
preserves L² because a probability measure is finite.
-/

open MeasureTheory

namespace P205.Probability.MomentIdentities

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X Y : Ω → ℝ}

/-- An L² real random variable on a probability space has an integrable mean. -/
theorem first_moment_integrable (hX : MemLp X 2 μ) : Integrable X μ :=
  hX.integrable (by simp)

/-- The second moment is integrable. -/
theorem square_integrable (hX : MemLp X 2 μ) : Integrable (fun ω ↦ X ω ^ 2) μ :=
  hX.integrable_sq

/-- Subtracting the mean preserves L². -/
theorem centered_memLp (hX : MemLp X 2 μ) :
    MemLp (fun ω ↦ X ω - ∫ x, X x ∂μ) 2 μ :=
  hX.sub (memLp_const _)

/-- Hölder's inequality makes the product of two L² variables integrable. -/
theorem product_integrable (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω ↦ X ω * Y ω) μ :=
  hX.integrable_mul hY

/-- The squared centered variable is integrable. -/
theorem centered_square_integrable (hX : MemLp X 2 μ) :
    Integrable (fun ω ↦ (X ω - ∫ x, X x ∂μ) ^ 2) μ :=
  (centered_memLp hX).integrable_sq

/-- The centered product defining covariance is integrable. -/
theorem centered_product_integrable (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω ↦ (X ω - ∫ x, X x ∂μ) * (Y ω - ∫ x, Y x ∂μ)) μ :=
  (centered_memLp hX).integrable_mul (centered_memLp hY)

/-- The canonical variance is the expected squared deviation from the mean. -/
theorem variance_eq_centered (hX : MemLp X 2 μ) :
    ProbabilityTheory.variance X μ = ∫ ω, (X ω - ∫ x, X x ∂μ) ^ 2 ∂μ :=
  ProbabilityTheory.variance_eq_integral hX.aemeasurable

/-- The canonical covariance is the expected product of centered variables. -/
theorem covariance_eq_centered (_hX : MemLp X 2 μ) (_hY : MemLp Y 2 μ) :
    ProbabilityTheory.covariance X Y μ =
      ∫ ω, (X ω - ∫ x, X x ∂μ) * (Y ω - ∫ x, Y x ∂μ) ∂μ :=
  rfl

/-- Variance is the second moment minus the squared mean. -/
theorem variance_eq_second_moment (hX : MemLp X 2 μ) :
    ProbabilityTheory.variance X μ = (∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2 :=
  ProbabilityTheory.variance_eq_sub hX

/-- Covariance is the product moment minus the product of means. -/
theorem covariance_eq_product_moment (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ProbabilityTheory.covariance X Y μ =
      (∫ ω, X ω * Y ω ∂μ) - (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ) :=
  ProbabilityTheory.covariance_eq_sub hX hY

end P205.Probability.MomentIdentities
