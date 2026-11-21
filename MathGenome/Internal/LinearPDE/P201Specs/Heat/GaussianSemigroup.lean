import MathGenome.Internal.LinearPDE.P201Specs.Heat.CausalFundamental
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! The full Gaussian theorem, in the shared Euclidean coordinates.
Time is nonnegative; every positive-time action uses the same Lebesgue
convolution. Strong continuity is required only for finite exponents. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace P201Specs.Heat

abbrev heatConvolutionType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  ℝ → (Space n → 𝕜) → Space n → 𝕜

def heatConvolution : heatConvolutionType := fun t f x =>
  ∫ y, gaussianKernel _ t (x - y) • f y ∂spatialMeasure _

abbrev heatFlowType := {n : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  ℝ≥0 → (Space n → 𝕜) → Space n → 𝕜

/-- Time zero is the identity on the given pointwise representative. -/
def heatFlow : heatFlowType := fun t f =>
  if t = 0 then f else heatConvolution t f

def kernelPropertiesStatement : Prop :=
  gaussianNonnegativeStatement ∧ gaussianIntegrableStatement ∧ gaussianMassStatement ∧
  gaussianHeatEquationStatement ∧ gaussianConvolutionStatement ∧
  causalLocallyIntegrableStatement ∧ causalFundamentalStatement

/-- The action is by bounded scalar-linear maps, with the original pointwise
convolution as representative. This includes the semigroup law at p = ∞. -/
def lpSemigroupStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)],
  ∃ S : ℝ≥0 → MeasureTheory.Lp 𝕜 p (spatialMeasure n) →L[𝕜] MeasureTheory.Lp 𝕜 p (spatialMeasure n),
    S 0 = ContinuousLinearMap.id 𝕜 _ ∧
    (∀ t s, S (t + s) = (S t).comp (S s)) ∧
    (∀ t f, ‖S t f‖ ≤ ‖f‖) ∧
    (∀ t f, (S t f : Space n → 𝕜) =ᵐ[spatialMeasure n] heatFlow t f) ∧
    (∀ (t : ℝ≥0), 0 < t → ∀ f : MeasureTheory.Lp 𝕜 p (spatialMeasure n),
      ∀ᵐ x ∂spatialMeasure n, Integrable
        (fun y => gaussianKernel n t (x - y) • f y) (spatialMeasure n)) ∧
    (p ≠ ∞ → ∀ f, Continuous (fun t => S t f))

def boundedContinuousRecoveryStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ g : Space n → ℝ,
    Continuous g → (∃ M : ℝ, ∀ x, ‖g x‖ ≤ M) →
    (∀ t > 0, ∀ x, Integrable
      (fun y => gaussianKernel n t (x - y) * g y) (spatialMeasure n)) ∧
    ∀ K : Set (Space n), IsCompact K →
      TendstoUniformlyOn (fun t => heatConvolution t g) g (𝓝[>] 0) K

def boundedUniformRecoveryStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ g : Space n → ℝ,
    UniformContinuous g → (∃ M : ℝ, ∀ x, ‖g x‖ ≤ M) →
    (∀ t > 0, ∀ x, Integrable
      (fun y => gaussianKernel n t (x - y) * g y) (spatialMeasure n)) ∧
    TendstoUniformly (fun t => heatConvolution t g) g (𝓝[>] 0)

end P201Specs.Heat
