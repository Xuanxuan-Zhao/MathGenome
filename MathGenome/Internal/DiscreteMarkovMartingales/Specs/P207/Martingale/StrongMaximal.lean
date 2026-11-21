import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.WeakMaximal
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207

/-- The martingale hypotheses only through the indicated finite horizon. -/
def IsMartingaleUpTo {Ω : Type u} [m : MeasurableSpace Ω]
    (M : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m) (μ : Measure Ω) (n : ℕ) : Prop :=
  (∀ k, k ≤ n → Measurable[ℱ k] (M k)) ∧
  (∀ k, k ≤ n → Integrable (M k) μ) ∧
  ∀ k, k < n → μ[M (k + 1) | ℱ k] =ᵐ[μ] M k

namespace StrongMaximalSpec

/-- The real exponent is finite, and the only moment hypothesis is at time `n`.
The conjunction records both membership and the quantitative norm bound. -/
def strong_maximal : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ),
    IsSubmartingaleUpTo X ℱ μ n →
    (∀ k, k ≤ n → 0 ≤ᵐ[μ] X k) →
    ∀ (p : ℝ), 1 < p → MemLp (X n) (ENNReal.ofReal p) μ →
      MemLp (finiteMax X n) (ENNReal.ofReal p) μ ∧
      lpNorm (finiteMax X n) (ENNReal.ofReal p) μ ≤
        (p / (p - 1)) * lpNorm (X n) (ENNReal.ofReal p) μ

/-- The corresponding estimate for the running absolute maximum of a real
martingale, with the same finite-horizon and terminal-moment hypotheses. -/
def strong_maximal_martingale : Prop :=
  ∀ {Ω : Type u} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (n : ℕ),
    IsMartingaleUpTo M ℱ μ n →
    ∀ (p : ℝ), 1 < p → MemLp (M n) (ENNReal.ofReal p) μ →
      MemLp (finiteMax (fun k ω => |M k ω|) n) (ENNReal.ofReal p) μ ∧
      lpNorm (finiteMax (fun k ω => |M k ω|) n) (ENNReal.ofReal p) μ ≤
        (p / (p - 1)) * lpNorm (M n) (ENNReal.ofReal p) μ

end StrongMaximalSpec
end P207
