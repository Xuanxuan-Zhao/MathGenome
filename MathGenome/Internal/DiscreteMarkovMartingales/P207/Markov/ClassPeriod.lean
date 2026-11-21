import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.ClassPeriod
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.RecurrenceInterfaces

open scoped ENNReal

universe u
namespace P207.Markov

/-- Concatenating two transitions of positive mass gives a positive transition. -/
theorem power_pos_add {S : Type u} (P : StochasticMatrix S)
    {i j k : S} {m n : ℕ}
    (hm : 0 < power P m i j) (hn : 0 < power P n j k) :
    0 < power P (m + n) i k := by
  rw [chapman_kolmogorov]
  exact (ENNReal.mul_pos_iff.mpr ⟨hm, hn⟩).trans_le
    (ENNReal.le_tsum (f := fun x => power P m i x * power P n x k) j)

private theorem positive_access_length_of_ne {S : Type u} (P : StochasticMatrix S)
    {i j : S} {n : ℕ} (hij : i ≠ j) (hn : 0 < power P n i j) : 1 ≤ n := by
  cases n with
  | zero => simp [power_zero, identity_apply, Ne.symm hij] at hn
  | succ n => exact Nat.succ_le_succ (Nat.zero_le n)

theorem communicate_common_returnLength {S : Type u} (P : StochasticMatrix S)
    {i j : S} (h : Communicate P i j) (hij : i ≠ j) :
    ∃ n, n ∈ returnLengths P i ∧ n ∈ returnLengths P j := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  have hab : 1 ≤ a + b := (positive_access_length_of_ne P hij ha).trans (Nat.le_add_right a b)
  refine ⟨a + b, ⟨hab, power_pos_add P ha hb⟩, hab, ?_⟩
  simpa only [Nat.add_comm] using power_pos_add P hb ha

private theorem period_dvd_of_communicate {S : Type u} (P : StochasticMatrix S)
    {i j : S} (h : Communicate P i j) : period P i ∣ period P j := by
  by_cases hij : i = j
  · subst j
    exact dvd_refl _
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  have hab : 1 ≤ a + b := (positive_access_length_of_ne P hij ha).trans (Nat.le_add_right a b)
  have hdab : period P i ∣ a + b :=
    period_dvd_returnLength P i (a + b) ⟨hab, power_pos_add P ha hb⟩
  apply (dvd_period_iff P j (period P i)).mpr
  intro n hn
  have hlong : a + n + b ∈ returnLengths P i :=
    ⟨by have := hn.1; omega, power_pos_add P (power_pos_add P ha hn.2) hb⟩
  have hdlong : period P i ∣ (a + b) + n := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      period_dvd_returnLength P i (a + n + b) hlong
  exact (Nat.dvd_add_iff_right hdab).mpr hdlong

theorem period_eq_of_communicate {S : Type u} (P : StochasticMatrix S)
    {i j : S} (h : Communicate P i j) : period P i = period P j := by
  exact Nat.dvd_antisymm (period_dvd_of_communicate P h)
    (period_dvd_of_communicate P ⟨h.2, h.1⟩)

end P207.Markov
