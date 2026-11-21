import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyMaximalInterfaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.MaximalWeakBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The two kernel estimates in the fixed maximal-function chapter.
The nonnegative integral in `ShiftedAverage` is extended-valued, so the
statement retains locally integrable inputs whose maximal value is infinite.
No measurability assumption on the dominated kernel is needed for this
stronger nonnegative-integral formulation. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ExpandedFA.PartIV.HardyWeightedKernelSpec
open ExpandedFA.Fourier HardyMaximalSpec

def WeightedConvolution : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
  ∀ (u v : Euclidean d → 𝕜), Integrable u → Integrable v →
  weightedNorm u < ∞ → weightedNorm v < ∞ →
  weightedNorm (convolve u v) ≤
    ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) + 1 / 2)) *
      (weightedNorm u * ENNReal.ofReal (∫ x, ‖v x‖) +
        ENNReal.ofReal (∫ x, ‖u x‖) * weightedNorm v)

def ConvolutionAbsolute : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
  ∀ (u v : Euclidean d → 𝕜), Integrable u → Integrable v →
  weightedNorm u < ∞ → weightedNorm v < ∞ →
  ∀ x, Integrable (fun z => u z * v (x - z))

def ShiftedAverage : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (τ C : ℝ), 0 < τ → 0 ≤ C →
  ∃ C' : ℝ, 0 ≤ C' ∧ ∀ {𝕜 : Type} [RCLike 𝕜]
    (K : Euclidean d → 𝕜),
    (∀ z, ‖K z‖ ≤ C * (1 + ‖z‖) ^ (-(d : ℝ) - τ)) →
    ∀ (H : Euclidean d → ℝ), (∀ z, 0 ≤ H z) → LocallyIntegrable H volume →
    ∀ (s : ℝ), 0 < s → ∀ (x y : Euclidean d),
    (∫⁻ z, ENNReal.ofReal (‖dilate s K (y - z)‖ * H z)) ≤
      ENNReal.ofReal (C' * (1 + ‖x - y‖ / s) ^ d) *
        ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec.MaximalValue volume H x

/-- The displayed source inequality for the ordinary integral, embedded into
the extended nonnegative reals used by the maximal function. -/
def ShiftedOrdinaryIntegral : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (τ C : ℝ), 0 < τ → 0 ≤ C →
  ∃ C' : ℝ, 0 ≤ C' ∧ ∀ {𝕜 : Type} [RCLike 𝕜]
    (K : Euclidean d → 𝕜),
    (∀ z, ‖K z‖ ≤ C * (1 + ‖z‖) ^ (-(d : ℝ) - τ)) →
    ∀ (H : Euclidean d → ℝ), (∀ z, 0 ≤ H z) → LocallyIntegrable H volume →
    ∀ (s : ℝ), 0 < s → ∀ (x y : Euclidean d),
    ENNReal.ofReal (∫ z, ‖dilate s K (y - z)‖ * H z) ≤
      ENNReal.ofReal (C' * (1 + ‖x - y‖ / s) ^ d) *
        ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec.MaximalValue volume H x

end ExpandedFA.PartIV.HardyWeightedKernelSpec
