import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

open MeasureTheory Filter
open scoped Topology ENNReal

universe u

namespace VariationalNotes.Specs

/-- The bounded variable-coefficient pairing limit.  The measure space is arbitrary
and finite; the Euclidean dimension may be zero.  All coefficient hypotheses are
almost everywhere hypotheses, and no pointwise convergence of `vₙ` is required. -/
def BoundedWeakLpPairing : Prop :=
  ∀ (S : Type u) [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (D : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (_hptop : p < ∞),
    letI : Fact (1 ≤ p) := ⟨hp.le⟩
    ∀ (vₙ : ℕ → Lp (EuclideanSpace ℝ (Fin D)) p μ)
      (v : Lp (EuclideanSpace ℝ (Fin D)) p μ)
      (bₙ : ℕ → S → EuclideanSpace ℝ (Fin D))
      (b : S → EuclideanSpace ℝ (Fin D)),
      Tendsto (fun n ↦ toWeakSpace ℝ _ (vₙ n)) atTop
        (𝓝 (toWeakSpace ℝ _ v)) →
      (∀ n, AEMeasurable (bₙ n) μ) → AEMeasurable b μ →
      (∀ᵐ x ∂μ, Tendsto (fun n ↦ bₙ n x) atTop (𝓝 (b x))) →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂μ, (∀ n, ‖bₙ n x‖ ≤ M) ∧ ‖b x‖ ≤ M) →
      (∀ n, Integrable (fun x ↦ inner ℝ (bₙ n x) (vₙ n x)) μ) ∧
      Integrable (fun x ↦ inner ℝ (b x) (v x)) μ ∧
      Tendsto (fun n ↦ ∫ x, inner ℝ (bₙ n x) (vₙ n x) ∂μ) atTop
        (𝓝 (∫ x, inner ℝ (b x) (v x) ∂μ))

end VariationalNotes.Specs
