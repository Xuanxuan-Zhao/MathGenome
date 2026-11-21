import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.LaplaceL2
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! Endpoint and p≠2 clauses of `fa2:p4:laplace-hankel`,
paper.tex:19598–19649. Interval tests alone already rule out a bounded strong
extension; thus the negative statements apply to any operator compatible with
the positive integral formula on bounded compactly supported inputs. -/
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace ExpandedFA.PartIV.LaplaceEndpointsSpec
open LaplaceL2Spec

abbrev PositiveLp (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) := Lp 𝕜 p halfLine

def intervalTest (𝕜 : Type) [RCLike 𝕜] (a b : ℝ) : ℝ → 𝕜 :=
  (Ioc a b).indicator (fun _ => 1)

def intervalVector (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) (a b : ℝ) :
    PositiveLp 𝕜 p :=
  indicatorConstLp (s := Ioc a b) p measurableSet_Ioc measure_Ioc_lt_top.ne (1 : 𝕜)

/-- Compatibility on all positive interval indicators, in ordinary a.e. classes. -/
def IntervalCompatible {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (F : (ℝ → 𝕜) → ℝ → 𝕜) (T : PositiveLp 𝕜 p →L[𝕜] PositiveLp 𝕜 p) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b →
    (T (intervalVector 𝕜 p a b) : ℝ → 𝕜) =ᵐ[halfLine] F (intervalTest 𝕜 a b)

def CarlemanTail : Prop :=
  (∀ s : ℝ, 2 ≤ s → (2 * s)⁻¹ ≤ carlemanIntegral ((Icc (1 : ℝ) 2).indicator (fun _ => (1 : ℝ))) s) ∧
    ¬ Integrable (carlemanIntegral ((Icc (1 : ℝ) 2).indicator (fun _ => (1 : ℝ)))) halfLine

/-- The logarithmic witness is essentially unbounded: every threshold is
exceeded on an entire positive interval, not just at isolated points. The
source open-interval indicator is retained exactly. -/
def CarlemanLog : Prop :=
  (∀ s : ℝ, 0 < s → carlemanIntegral ((Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) s =
    Real.log ((s + 1) / s)) ∧
  ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ∀ s ∈ Ioo 0 δ, M < carlemanIntegral ((Ioo (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) s

def CarlemanEndpoints : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜],
    (¬ ∃ T : PositiveLp 𝕜 1 →L[𝕜] PositiveLp 𝕜 1,
      IntervalCompatible carlemanIntegral T) ∧
    (¬ ∃ T : PositiveLp 𝕜 ∞ →L[𝕜] PositiveLp 𝕜 ∞,
      IntervalCompatible carlemanIntegral T)

/-- Substitution is valid even when the Bochner integral is defined as zero
for a nonintegrable function. -/
def LaplaceDilation : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (f : ℝ → 𝕜) (a : ℝ), 0 < a →
    ∀ s : ℝ, laplaceIntegral (fun t => f (a * t)) s =
      a⁻¹ • laplaceIntegral f (s / a)

/-- ENNReal exponents include infinity explicitly; no finite-exponent
side condition is imposed. -/
def LaplaceUnbounded : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) (hp : 1 ≤ p) (_hne : p ≠ 2),
    letI : Fact (1 ≤ p) := ⟨hp⟩
    ¬ ∃ T : PositiveLp 𝕜 p →L[𝕜] PositiveLp 𝕜 p,
      IntervalCompatible laplaceIntegral T

end ExpandedFA.PartIV.LaplaceEndpointsSpec
