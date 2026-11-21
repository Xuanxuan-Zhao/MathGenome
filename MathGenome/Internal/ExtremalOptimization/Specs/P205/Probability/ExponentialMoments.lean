import Mathlib.Probability.Moments.Basic

/-!
The unnumbered facts in paper.tex, section "Exponential moments".
We reuse `ProbabilityTheory.mgf X μ lam`, defined as `∫ ω, exp (lam * X ω) ∂μ`.
Bounds are only almost everywhere. A `Fintype` index permits the empty family.
Measurability of each test function is required with respect to the law of X;
this includes measurable test functions defined on the essential range, with
arbitrary extensions off that range. The test-function bound is expressed
on its composition with X, so no global bound on the extension is required.
-/

open MeasureTheory ProbabilityTheory

namespace Specs.P205.Probability

/-- Exponentials of bounded measurable random variables are integrable for every real lam. -/
def BoundedExponentialIntegrable : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ), Measurable X → (∃ B : ℝ, ∀ᵐ ω ∂μ, |X ω| ≤ B) →
    ∀ lam : ℝ, Integrable (fun ω => Real.exp (lam * X ω)) μ

/-- Factorization, together with the integrability of all the expectations involved. -/
def IndependentProduct : Prop :=
  ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (f : ι → ℝ → ℝ),
    (∀ i, Measurable (X i)) →
    (∀ i, ∃ B : ℝ, ∀ᵐ ω ∂μ, |X i ω| ≤ B) → iIndepFun X μ →
    (∀ i, AEStronglyMeasurable (f i) (μ.map (X i))) →
    (∀ i, ∃ C : ℝ, ∀ᵐ ω ∂μ, |f i (X i ω)| ≤ C) →
    (∀ i, Integrable (fun ω => f i (X i ω)) μ) ∧
    Integrable (fun ω => ∏ i, f i (X i ω)) μ ∧
    (∫ ω, ∏ i, f i (X i ω) ∂μ) = ∏ i, ∫ ω, f i (X i ω) ∂μ

/-- All exponential moments exist and the MGF of the sum factors, for every real lam. -/
def IndependentMGFSum : Prop :=
  ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ),
    (∀ i, Measurable (X i)) →
    (∀ i, ∃ B : ℝ, ∀ᵐ ω ∂μ, |X i ω| ≤ B) → iIndepFun X μ →
    ∀ lam : ℝ,
      (∀ i, Integrable (fun ω => Real.exp (lam * X i ω)) μ) ∧
      Integrable (fun ω => Real.exp (lam * ∑ i, X i ω)) μ ∧
      mgf (fun ω => ∑ i, X i ω) μ lam = ∏ i, mgf (X i) μ lam

/-- Inclusive upper tail, with arbitrary real t and positive lam. -/
def ExponentialMarkov : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ), Measurable Y → (∃ B : ℝ, ∀ᵐ ω ∂μ, |Y ω| ≤ B) →
    ∀ t lam : ℝ, 0 < lam →
      μ.real {ω | t ≤ Y ω} ≤ Real.exp (-lam * t) * mgf Y μ lam

end Specs.P205.Probability
