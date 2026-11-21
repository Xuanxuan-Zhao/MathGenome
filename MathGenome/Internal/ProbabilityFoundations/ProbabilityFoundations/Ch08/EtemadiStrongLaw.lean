import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.EtemadiStrongLaw
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.IndependenceInterfaces
import Mathlib.Probability.StrongLaw

/-! The forward direction of Theorem 8.3 (`thm:etemadi`). Apply the
pairwise Etemadi law to `Y k = X (k + 1)`, then identify its zero-based
sum with the source's `S n = ∑ k ∈ Icc 1 n, X k`. No hypothesis is
imposed on the unused coordinate `X 0`. -/

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityFoundations.Ch08

universe u

/-- Etemadi's first-moment strong law, with the source's one-based sums. -/
theorem etemadi_strong_law {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ k : ℕ, Measurable (X (k + 1)))
    (hindep : Ch02.PairwiseIndependentRandomElements P (fun k : ℕ => X (k + 1)))
    (hident : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (X (k + 1)) (X 1) P P)
    (hmoment : Integrable (fun ω => |X 1 ω|) P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, X k ω) / (n : ℝ))
      atTop (𝓝 (∫ ω, X 1 ω ∂P)) := by
  have hint : Integrable (X 1) P :=
    (integrable_norm_iff (hX 0).aestronglyMeasurable).mp
      (by simpa only [Real.norm_eq_abs] using hmoment)
  have hi := (Ch02.pairwiseIndependentRandomElements_iff P
    (fun k : ℕ => X (k + 1))).mp hindep
  have h := ProbabilityTheory.strong_law_ae_real
    (fun k : ℕ => X (k + 1)) hint hi hident
  have hsum (n : ℕ) (ω : Ω) :
      (∑ k ∈ Finset.Icc 1 n, X k ω) = ∑ k ∈ Finset.range n, X (k + 1) ω := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm]
  simpa only [hsum] using h

end ProbabilityFoundations.Ch08
