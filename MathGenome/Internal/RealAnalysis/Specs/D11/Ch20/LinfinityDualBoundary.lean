import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Order.Filter.Ultrafilter.Basic

/-! Independent statements for paper.tex:5803–5810. On the discrete natural
numbers bounded continuous functions are exactly bounded sequences. The
counting-space equivalence below explicitly identifies them with ordinary
(native a.e.) L-infinity. The integral pairing is bilinear, without conjugation.
All scalar assertions apply to both the real and complex fields. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction
namespace Specs.D11.Ch20.LinfinityDualBoundary

/-- The singleton sequence with value one at n. -/
def unitSequence (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) : ℕ →ᵇ 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun j => if j = n then 1 else 0) 1 (by intro j; split_ifs <;> simp)

/-- Counting a.e. equality is pointwise equality, and the essential-supremum
norm is the supremum norm of the bounded sequence. -/
def counting_equivalence : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  ∃ E : (ℕ →ᵇ 𝕜) ≃ₗᵢ[𝕜] Lp 𝕜 ∞ (Measure.count : Measure ℕ),
    ∀ (a : ℕ →ᵇ 𝕜) (n : ℕ), E a n = a n

/-- A single free ultrafilter constructs norm-one scalar-linear functionals.
The two coordinate assertions express positivity on nonnegative real-valued
sequences also in the complex case. All pairings with an L1 density are
integrable, but none represents this functional. -/
def ultrafilter_boundary : Prop :=
  ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ cofinite ∧
    (∀ n : ℕ, ({n} : Set ℕ) ∉ U) ∧
    ∀ (𝕜 : Type) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜],
      ∃ ell : (ℕ →ᵇ 𝕜) →L[𝕜] 𝕜,
        (∀ a : ℕ →ᵇ 𝕜, Tendsto a (U : Filter ℕ) (𝓝 (ell a))) ∧
        ‖ell‖ = 1 ∧
        ell (BoundedContinuousFunction.const ℕ 1) = 1 ∧
        (∀ n, ell (unitSequence 𝕜 n) = 0) ∧
        (∀ a : ℕ →ᵇ 𝕜, (∀ n, 0 ≤ RCLike.re (a n)) → 0 ≤ RCLike.re (ell a)) ∧
        (∀ a : ℕ →ᵇ 𝕜, (∀ n, RCLike.im (a n) = 0) → RCLike.im (ell a) = 0) ∧
        (∀ g : ℕ → 𝕜, Integrable g Measure.count →
          (∀ a : ℕ →ᵇ 𝕜, Integrable (fun n => a n * g n) Measure.count) ∧
          ¬ (∀ a : ℕ →ᵇ 𝕜, ell a = ∫ n, a n * g n ∂Measure.count))

/-- The endpoint failure on the ordinary L-infinity quotient, including the
coordinate-preserving identification, positivity and normalized test values. -/
def counting_dual_boundary : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜],
  ∃ E : (ℕ →ᵇ 𝕜) ≃ₗᵢ[𝕜] Lp 𝕜 ∞ (Measure.count : Measure ℕ),
    (∀ (a : ℕ →ᵇ 𝕜) (n : ℕ), E a n = a n) ∧
    ∃ ell : Lp 𝕜 ∞ (Measure.count : Measure ℕ) →L[𝕜] 𝕜,
      ‖ell‖ = 1 ∧
      ell (E (BoundedContinuousFunction.const ℕ 1)) = 1 ∧
      (∀ n, ell (E (unitSequence 𝕜 n)) = 0) ∧
      (∀ f : Lp 𝕜 ∞ (Measure.count : Measure ℕ), (∀ n, 0 ≤ RCLike.re (f n)) → 0 ≤ RCLike.re (ell f)) ∧
      (∀ f : Lp 𝕜 ∞ (Measure.count : Measure ℕ), (∀ n, RCLike.im (f n) = 0) → RCLike.im (ell f) = 0) ∧
      (∀ g : Lp 𝕜 1 (Measure.count : Measure ℕ),
        (∀ f : Lp 𝕜 ∞ (Measure.count : Measure ℕ),
          Integrable (fun n => f n * g n) Measure.count) ∧
        ¬ (∀ f, ell f = ∫ n, f n * g n ∂Measure.count))

end Specs.D11.Ch20.LinfinityDualBoundary
