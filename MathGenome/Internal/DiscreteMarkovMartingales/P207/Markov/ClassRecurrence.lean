import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.ClassRecurrence
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.GreenCriterion

open scoped ENNReal
universe u
namespace P207.Markov
noncomputable section

/-- Keeping a single intermediate state in Chapman--Kolmogorov gives a lower bound. -/
theorem power_mul_le_power_add {S : Type u} (P : StochasticMatrix S)
    (m n : ℕ) (i j k : S) :
    power P m i j * power P n j k ≤ power P (m + n) i k := by
  rw [chapman_kolmogorov]
  exact ENNReal.le_tsum (f := fun x => power P m i x * power P n x k) j

/-- A fixed outward path and a fixed return path compare the diagonal Green series. -/
theorem greenSeries_path_comparison {S : Type u} (P : StochasticMatrix S)
    (i j : S) (a b : ℕ) :
    power P a i j * greenSeries P j * power P b j i ≤ greenSeries P i := by
  calc
    power P a i j * greenSeries P j * power P b j i =
        ∑' n : ℕ, power P a i j * power P n j j * power P b j i := by
      simp only [greenSeries, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
    _ ≤ ∑' n : ℕ, power P (a + n + b) i i := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact (mul_le_mul_of_nonneg_right (power_mul_le_power_add P a n i j j)
        (show 0 ≤ power P b j i from zero_le)).trans
        (power_mul_le_power_add P (a + n) b i j i)
    _ ≤ greenSeries P i := by
      exact ENNReal.tsum_comp_le_tsum_of_injective
        (fun n m h => by omega) (fun n => power P n i i)

variable {S : Type u} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- Recurrence is invariant under communication, without whole-space irreducibility. -/
theorem recurrent_iff_of_communicate (P : StochasticMatrix S) {i j : S}
    (h : Communicate P i j) : Recurrent P i ↔ Recurrent P j := by
  have transfer : ∀ {i j : S}, Communicate P i j → Recurrent P j → Recurrent P i := by
    intro i j hij hj
    obtain ⟨a, ha⟩ := hij.1
    obtain ⟨b, hb⟩ := hij.2
    apply (recurrent_iff_greenSeries_eq_top P i).mpr
    have hcomp := greenSeries_path_comparison P i j a b
    rw [(recurrent_iff_greenSeries_eq_top P j).mp hj,
      ENNReal.mul_top ha.ne', ENNReal.top_mul hb.ne'] at hcomp
    exact top_unique hcomp
  exact ⟨transfer ⟨h.2, h.1⟩, transfer h⟩

/-- Transience is invariant under communication for an arbitrary countable chain. -/
theorem transient_iff_of_communicate (P : StochasticMatrix S) {i j : S}
    (h : Communicate P i j) : Transient P i ↔ Transient P j := by
  rw [transient_iff_not_recurrent, transient_iff_not_recurrent,
    recurrent_iff_of_communicate P h]

end
end P207.Markov
