import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.MonotoneReparameterization
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch03.AbsolutelyContinuousContours
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Arclength part of paper.tex:749–806 and rectifiable estimates in 583–616.
Ambient functions denote their restrictions to the specified closed intervals.
No differentiability is asserted for the original rectifiable parametrization.
-/
noncomputable section
open Set MeasureTheory

namespace Specs.D12Complex.Ch03.ArclengthFactorization
open _root_.D12Complex _root_.D12Complex.Stieltjes

def accumulated_type := ComplexPath → ℝ → ℝ
/-- Independent expected value: the original path's accumulated polygonal variation. -/
def accumulated_value : accumulated_type :=
  fun γ t => (totalVariation γ γ.a t).toReal

def accumulated_properties_type : Prop :=
  ∀ γ : ComplexPath, Rectifiable γ →
    ContinuousOn (accumulated_value γ) (Icc γ.a γ.b) ∧
    MonotoneOn (accumulated_value γ) (Icc γ.a γ.b) ∧
    accumulated_value γ γ.a = 0 ∧ accumulated_value γ γ.b = (polygonalLength γ).toReal ∧
    accumulated_value γ '' Icc γ.a γ.b = Icc 0 (polygonalLength γ).toReal

/-- The factor uses the prescribed accumulated variation, including plateaus. -/
def lipschitz_factor_type : Prop :=
  ∀ γ : ComplexPath, Rectifiable γ →
    ∃ σ : ℝ → ℂ,
      LipschitzOnWith 1 σ (Icc 0 (polygonalLength γ).toReal) ∧
      (∀ t ∈ Icc γ.a γ.b, γ t = σ (accumulated_value γ t)) ∧
      σ '' Icc 0 (polygonalLength γ).toReal = γ.trace ∧
      totalVariation σ 0 (polygonalLength γ).toReal = polygonalLength γ

/-- The AC length formula, also for complex paths rather than only coordinates. -/
def ac_length_type : Prop :=
  ∀ {a b : ℝ}, a ≤ b → ∀ σ : ℝ → ℂ,
    AbsolutelyContinuousOnInterval σ a b →
    (totalVariation σ a b).toReal = ∫ v in a..b, ‖deriv σ v‖

/-- Positive length and 1-Lipschitz regularity imply unit speed, with no
unit-speed certificate in the hypotheses. -/
def unit_speed_type : Prop :=
  ∀ {L : ℝ}, 0 < L → ∀ σ : ℝ → ℂ,
    LipschitzOnWith 1 σ (Icc 0 L) → (totalVariation σ 0 L).toReal = L →
    ∀ᵐ v ∂volume.restrict (Icc 0 L), HasDerivAt σ (deriv σ v) v ∧ ‖deriv σ v‖ = 1

/-- The complete positive-length bridge, using the same σ for every integrand. -/
def arclength_factorization_type : Prop :=
  ∀ γ : ComplexPath, Rectifiable γ → 0 < (polygonalLength γ).toReal →
    ∃ σ : ℝ → ℂ,
      LipschitzOnWith 1 σ (Icc 0 (polygonalLength γ).toReal) ∧
      (∀ t ∈ Icc γ.a γ.b, γ t = σ (accumulated_value γ t)) ∧
      σ '' Icc 0 (polygonalLength γ).toReal = γ.trace ∧
      totalVariation σ 0 (polygonalLength γ).toReal = polygonalLength γ ∧
      (∀ᵐ v ∂volume.restrict (Icc 0 (polygonalLength γ).toReal),
        HasDerivAt σ (deriv σ v) v ∧ ‖deriv σ v‖ = 1) ∧
      ∀ f : ℂ → ℂ, ContinuousOn f γ.trace →
        IntervalIntegrable (fun v => f (σ v) * deriv σ v) volume 0
          (polygonalLength γ).toReal ∧
        IntervalIntegrable (fun v => ‖f (σ v)‖ * ‖deriv σ v‖) volume 0
          (polygonalLength γ).toReal ∧
        contourIntegral γ f = ∫ v in (0 : ℝ)..(polygonalLength γ).toReal,
          f (σ v) * deriv σ v ∧
        ‖contourIntegral γ f‖ ≤ ∫ v in (0 : ℝ)..(polygonalLength γ).toReal,
          ‖f (σ v)‖ * ‖deriv σ v‖ ∧
        (∫ v in (0 : ℝ)..(polygonalLength γ).toReal,
          ‖f (σ v)‖ * ‖deriv σ v‖) ≤
          (polygonalLength γ).toReal * sSup ((fun z => ‖f z‖) '' γ.trace)

def zero_length_type : Prop :=
  ∀ γ : ComplexPath, polygonalLength γ = 0 →
    (∀ t ∈ Icc γ.a γ.b, γ t = γ γ.a) ∧ ∀ f : ℂ → ℂ, contourIntegral γ f = 0

/-- Uniform convergence on this fixed trace, without varying parametrizations. -/
def contourIntegral_uniform_limit_type : Prop :=
  ∀ γ : ComplexPath, Rectifiable γ → ∀ (f : ℂ → ℂ) (F : ℕ → ℂ → ℂ),
    ContinuousOn f γ.trace → (∀ n, ContinuousOn (F n) γ.trace) →
    TendstoUniformlyOn F f Filter.atTop γ.trace →
    Filter.Tendsto (fun n => contourIntegral γ (F n)) Filter.atTop
      (nhds (contourIntegral γ f))

end Specs.D12Complex.Ch03.ArclengthFactorization
