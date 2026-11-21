import MathGenome.Internal.LinearPDE.P201Specs.Heat.GaussianSemigroup
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! Independent statements for `pde:heat-lp-smoothing`, paper.tex:2702–2714.
The representatives are the actual Lebesgue convolutions, including at p = ∞.
`p⁻¹.toReal` is the reciprocal exponent, with value zero at infinity.
-/
noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal
namespace P201Specs.Heat

abbrev heatMixedDerivativeType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  MultiIndex n → ℕ → (Space n → 𝕜) → ℝ → Space n → 𝕜

/-- Time differentiation after the shared spatial multi-index differentiation. -/
def heatMixedDerivative : heatMixedDerivativeType := fun α j g t x =>
  iteratedDeriv j (fun s => multiPartial (heatConvolution s g) α x) t

def heatSmoothingExponent {n : ℕ} (α : MultiIndex n) (j : ℕ) (p q : ℝ≥0∞) : ℝ :=
  -(j : ℝ) - (α.card : ℝ) / 2 - (n : ℝ) / 2 * (p⁻¹.toReal - q⁻¹.toReal)

abbrev gaussianMixedDerivativeType := {n : ℕ} → MultiIndex n → ℕ → ℝ → Space n → ℝ

def gaussianMixedDerivative : gaussianMixedDerivativeType := fun {n} α j t x =>
  iteratedDeriv j (fun s => multiPartial (gaussianKernel n s) α x) t

def heatSmoothRepresentativeStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)),
    (∀ t > 0, ∀ x, Integrable
      (fun y => gaussianKernel n t (x - y) • g y) (spatialMeasure n)) ∧
    ContDiffOn ℝ ∞ (fun z : Space n × ℝ => heatConvolution z.2 g z.1)
      {z | 0 < z.2}

/-- The constant is chosen before the initial datum and time. `MemLp` prevents
the totalized `toReal` from hiding an infinite derivative norm. -/
def heatMixedEstimateStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (𝕜 : Type) [RCLike 𝕜] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)], p ≤ q → ∀ (α : MultiIndex n) (j : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) (t : ℝ), 0 < t →
        MemLp (heatMixedDerivative α j g t) q (spatialMeasure n) ∧
        (eLpNorm (heatMixedDerivative α j g t) q (spatialMeasure n)).toReal ≤
          C * t ^ (heatSmoothingExponent α j p q) * ‖g‖

/-- Every time power equals the same power of the positive-sign Laplacian,
also after every spatial derivative. -/
def heatTimeLaplacianStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) (α : MultiIndex n) (j : ℕ)
    (t : ℝ), 0 < t → ∀ x,
      heatMixedDerivative α j g t x =
        (laplacian^[j]) (multiPartial (heatConvolution t g) α) x

def lpSmoothingStatement : Prop :=
  heatSmoothRepresentativeStatement ∧ heatMixedEstimateStatement ∧
    heatTimeLaplacianStatement

/-- Analytic kernel estimate needed for the quantitative part. This is a
proposition to be proved, never a field assumed of the Gaussian definition. -/
def gaussianMixedBoundStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (α : MultiIndex n) (j : ℕ) (r : ℝ≥0∞), 1 ≤ r →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), 0 < t →
      MemLp (gaussianMixedDerivative α j t) r (spatialMeasure n) ∧
      (eLpNorm (gaussianMixedDerivative α j t) r (spatialMeasure n)).toReal ≤
        C * t ^ (-(j : ℝ) - (α.card : ℝ) / 2 - (n : ℝ) / 2 * (1 - r⁻¹.toReal))

def heatDifferentiationUnderIntegralStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) (α : MultiIndex n) (j : ℕ)
    (t : ℝ), 0 < t → ∀ x,
      heatMixedDerivative α j g t x =
        ∫ y, gaussianMixedDerivative α j t (x - y) • g y ∂spatialMeasure n

def heatMixedEstimateAssemblyStatement : Prop :=
  gaussianMixedBoundStatement → heatDifferentiationUnderIntegralStatement →
    heatMixedEstimateStatement

/-! Proved preliminary interfaces, useful independently of the full estimate. -/

def gaussianSpatialSchwartzStatement : Prop :=
  ∀ (n : ℕ) (t : ℝ), 0 < t → ∀ α : MultiIndex n,
    ∃ Φ : SchwartzMap (Space n) ℝ,
      (Φ : Space n → ℝ) = multiPartial (gaussianKernel n t) α

def gaussianSpatialMemLpStatement : Prop :=
  ∀ (n : ℕ) (t : ℝ), 0 < t → ∀ (α : MultiIndex n) (r : ℝ≥0∞),
    MemLp (multiPartial (gaussianKernel n t) α) r (spatialMeasure n)

def heatConvolutionEverywhereStatement : Prop :=
  ∀ (n : ℕ) (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) (t : ℝ), 0 < t → ∀ x,
      Integrable (fun y => gaussianKernel n t (x - y) • g y) (spatialMeasure n)

def heatDiagonalZeroEstimateStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) (t : ℝ), 0 < t →
      MemLp (heatMixedDerivative 0 0 g t) p (spatialMeasure n) ∧
      (eLpNorm (heatMixedDerivative 0 0 g t) p (spatialMeasure n)).toReal ≤ ‖g‖

end P201Specs.Heat
