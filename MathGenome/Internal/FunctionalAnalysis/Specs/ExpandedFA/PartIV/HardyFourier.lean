import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.AtomicHardySpace
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.Analysis.Complex.Basic

/-!
The weighted Fourier inequality of `fa2:p4:hardy-fourier`, with the local
20261105-six-boundary-errata, item 3. The space is the accepted completed
atomic quotient, embedded in the actual Lebesgue L¹ space. Fourier transforms
of real inputs use their canonical complex embedding. A nonnegative Lebesgue
integral records divergence faithfully; in particular it cannot become zero
because a Bochner integral was applied to a nonintegrable function.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.PartIV.HardyFourierSpec
open ExpandedFA.Fourier ExpandedFA.Hardy.AtomicHardySpaceSpec

abbrev L1 (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  Lp 𝕜 1 (volume : Measure (Euclidean d))
abbrev Hardy (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  HardyValue (𝕜 := 𝕜) (volume : Measure (Euclidean d))
abbrev Atom (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  AtomValue (𝕜 := 𝕜) (volume : Measure (Euclidean d))

/-- Ordinary 2π-normalized integral Fourier transform, for either scalar field. -/
def fourier {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Euclidean d → 𝕜) : Euclidean d → ℂ :=
  integralFourier (fun x => RCLike.map 𝕜 ℂ (f x))

/-- The value at zero uses the usual conventions `0 ^ 0 = 1` and `a / 0 = 0`;
in positive dimension its value at that one null point does not affect the integral. -/
def weightedIntegral {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Euclidean d → 𝕜) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (‖fourier f ξ‖ / ‖ξ‖ ^ d)

/-- Uniformity is in all radii, centers and members of the completed Hardy space,
with one finite real constant depending only on dimension (both scalar fields). -/
def HardyBound : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (𝕜 : Type) [RCLike 𝕜] (h : Hardy 𝕜 d),
      weightedIntegral (EmbeddingValue volume h : Euclidean d → 𝕜) ≤
        ENNReal.ofReal (C * ‖h‖)

/-- Atom conditions with only cancellation removed. -/
def IsUncancelledAtom {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : L1 𝕜 d) : Prop :=
  ∃ c : Euclidean d, ∃ r : ℝ, 0 < r ∧
    ∀ᵐ x, (x ∉ Metric.ball c r → f x = 0) ∧
      ‖f x‖ ≤ (volume.real (Metric.ball c r))⁻¹

/-- No finite uniform atom bound survives removal of cancellation, only in
positive dimensions as specified by the adopted source amendment. -/
def CancellationNecessary : Prop :=
  ∀ d : ℕ, 0 < d → ∀ C : ℝ, ∃ f : L1 ℝ d,
    IsUncancelledAtom f ∧
      ENNReal.ofReal C < weightedIntegral (f : Euclidean d → ℝ)

/-- A convenient, stronger analytic subproblem; it is not an assumption in
`HardyBound` and will have to be proved before that result is complete. -/
def AtomBound : Prop :=
  ∀ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (𝕜 : Type) [RCLike 𝕜] (a : Atom 𝕜 d),
      weightedIntegral (a.val : Euclidean d → 𝕜) ≤ ENNReal.ofReal C

/-- The retained singleton case, in the actual completed space. -/
def ZeroDimension : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (h : Hardy 𝕜 0), h = 0 ∧
    weightedIntegral (EmbeddingValue volume h : Euclidean 0 → 𝕜) = 0

end ExpandedFA.PartIV.HardyFourierSpec
