import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.RuinMean
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Walk.GamblersRuin
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Markov.MeanHittingTime

open MeasureTheory
open scoped ENNReal

namespace P207.Walk
noncomputable section

/-- The real value of the finite expected entrance time. -/
def ruinMeanReal (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) : ℝ :=
  (Markov.meanHittingTime (ruinKernel N p hp hp1) (ruinBoundary N) i).toReal

private theorem ruinMean_ne_top (N : ℕ) (hN : 1 ≤ N) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (i : RuinState N) :
    Markov.meanHittingTime (ruinKernel N p hp hp1) (ruinBoundary N) i ≠ ⊤ := by
  rw [Markov.meanHittingTime_eq_lintegral]
  exact (ruinTime_finite_mean N hN p hp hp1 i).ne

theorem ruinMeanReal_boundary (N : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (i : RuinState N) (hi : i ∈ ruinBoundary N) : ruinMeanReal N p hp hp1 i = 0 := by
  simp [ruinMeanReal, Markov.meanHittingTime_boundary _ _ i hi]

theorem ruinMeanReal_step (N : ℕ) (hN : 1 ≤ N) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (i : RuinState N) (hi : i ∉ ruinBoundary N) :
    ruinMeanReal N p hp hp1 i = 1 + p * ruinMeanReal N p hp hp1 (ruinRight i) +
      (1 - p) * ruinMeanReal N p hp hp1 (ruinLeft i) := by
  have he := Markov.meanHittingTime_equation (ruinKernel N p hp hp1) (ruinBoundary N) i hi
  rw [ruinKernel_action N p hp hp1 i hi] at he
  have hr := congrArg ENNReal.toReal he
  have hR := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := p))
    (ruinMean_ne_top N hN p hp hp1 (ruinRight i))
  have hL := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 1 - p))
    (ruinMean_ne_top N hN p hp hp1 (ruinLeft i))
  rw [ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.add_ne_top.mpr ⟨hR, hL⟩),
    ENNReal.toReal_one, ENNReal.toReal_add hR hL,
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal (sub_nonneg.mpr hp1.le)] at hr
  simpa only [ruinMeanReal, add_assoc] using hr

/-- A harmonic function on a finite interval that vanishes at both ends is zero. -/
theorem ruin_harmonic_zero (N : ℕ) (hN : 1 ≤ N) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (f : RuinState N → ℝ)
    (h0 : f 0 = 0) (hLast : f (Fin.last N) = 0)
    (hs : ∀ i, i ∉ ruinBoundary N → f i = p * f (ruinRight i) + (1 - p) * f (ruinLeft i))
    (i : RuinState N) : f i = 0 := by
  let c : ℕ → RuinState N := fun k => ⟨min k N, Nat.lt_succ_of_le (min_le_right _ _)⟩
  let u : ℕ → ℝ := fun k => f (c k)
  have hc0 : c 0 = 0 := by apply Fin.ext; simp [c]
  have hcN : c N = Fin.last N := by apply Fin.ext; simp [c]
  have hu0 : u 0 = 0 := by simpa [u, hc0] using h0
  have huN : u N = 0 := by simpa [u, hcN] using hLast
  have hu : ∀ k, 0 < k → k < N → u k = p * u (k + 1) + (1 - p) * u (k - 1) := by
    intro k hk hkN
    have hi : c k ∉ ruinBoundary N := by
      simp only [ruinBoundary, Set.mem_ofPred_eq, c, min_eq_left hkN.le]
      omega
    have hR : ruinRight (c k) = c (k + 1) := by
      apply Fin.ext
      simp [ruinRight, c, min_eq_left hkN.le]
    have hL : ruinLeft (c k) = c (k - 1) := by
      apply Fin.ext
      simp [ruinLeft, c, min_eq_left hkN.le, min_eq_left (show k - 1 ≤ N by omega)]
    simpa only [u, hR, hL] using hs (c k) hi
  have hsum : (∑ j ∈ Finset.range N, ((1 - p) / p) ^ j) ≠ 0 :=
    ne_of_gt (geom_sum_pos (div_nonneg (sub_nonneg.mpr hp1.le) hp.le) (by omega))
  have ht := ruin_recurrence_sum N p hp.ne' u hu0 hu N le_rfl
  rw [huN] at ht
  have hu1 : u 1 = 0 := (mul_eq_zero.mp ht.symm).resolve_right hsum
  have he := ruin_recurrence_sum N p hp.ne' u hu0 hu i.val (Nat.le_of_lt_succ i.isLt)
  rw [hu1, zero_mul] at he
  have hci : c i.val = i := by
    apply Fin.ext
    exact min_eq_left (Nat.le_of_lt_succ i.isLt)
  simpa only [u, hci] using he

/-- Solving the Poisson equation for the actual, finite expectation. -/
theorem ruinMeanReal_formula (N : ℕ) (hN : 1 ≤ N) (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (i : RuinState N) :
    ruinMeanReal N p hp hp1 i =
      if p = 1 - p then (i.val : ℝ) * (N - (i.val : ℝ))
      else ((N : ℝ) * ruinExitProbability N p hp hp1 i - i.val) / (p - (1 - p)) := by
  have hb0 : (0 : RuinState N) ∈ ruinBoundary N := Or.inl rfl
  have hbN : Fin.last N ∈ ruinBoundary N := Or.inr rfl
  by_cases he : p = 1 - p
  · rw [ite_eq_left he]
    let f : RuinState N → ℝ := fun j =>
      ruinMeanReal N p hp hp1 j - (j.val : ℝ) * (N - (j.val : ℝ))
    have hf0 : f 0 = 0 := by
      simp [f, ruinMeanReal_boundary N p hp hp1 0 hb0]
    have hfN : f (Fin.last N) = 0 := by
      simp [f, ruinMeanReal_boundary N p hp hp1 (Fin.last N) hbN]
    have hs : ∀ j, j ∉ ruinBoundary N →
        f j = p * f (ruinRight j) + (1 - p) * f (ruinLeft j) := by
      intro j hj
      have hji := j.isLt
      have hjb : ¬ (j.val = 0 ∨ j.val = N) := hj
      have hR : (ruinRight j).val = j.val + 1 := by
        simp only [ruinRight, min_eq_left (show j.val + 1 ≤ N by omega)]
      have hL : (ruinLeft j).val = j.val - 1 := rfl
      have hx : ((j.val - 1 : ℕ) : ℝ) = (j.val : ℝ) - 1 :=
        by simpa only [Nat.cast_one] using
          (Nat.cast_sub (R := ℝ) (show 1 ≤ j.val by omega))
      have hg := ruinMeanReal_step N hN p hp hp1 j hj
      dsimp [f]
      rw [hR, hL, hx, Nat.cast_add, Nat.cast_one]
      have hpHalf : p = 1 / 2 := by linarith
      generalize ruinMeanReal N p hp hp1 j = a at hg ⊢
      generalize ruinMeanReal N p hp hp1 (ruinRight j) = b at hg ⊢
      generalize ruinMeanReal N p hp hp1 (ruinLeft j) = c at hg ⊢
      rw [hpHalf] at hg ⊢
      nlinarith [hg]
    have hz := ruin_harmonic_zero N hN p hp hp1 f hf0 hfN hs i
    dsimp [f] at hz
    linarith
  · rw [ite_eq_right he]
    let d : ℝ := p - (1 - p)
    let f : RuinState N → ℝ := fun j =>
      d * ruinMeanReal N p hp hp1 j + j.val - N * ruinExitProbability N p hp hp1 j
    have hf0 : f 0 = 0 := by
      simp [f, ruinMeanReal_boundary N p hp hp1 0 hb0, ruinExitProbability_zero N hN p hp hp1]
    have hfN : f (Fin.last N) = 0 := by
      simp [f, ruinMeanReal_boundary N p hp hp1 (Fin.last N) hbN,
        ruinExitProbability_last N hN p hp hp1]
    have hs : ∀ j, j ∉ ruinBoundary N →
        f j = p * f (ruinRight j) + (1 - p) * f (ruinLeft j) := by
      intro j hj
      have hji := j.isLt
      have hjb : ¬ (j.val = 0 ∨ j.val = N) := hj
      have hR : (ruinRight j).val = j.val + 1 := by
        simp only [ruinRight, min_eq_left (show j.val + 1 ≤ N by omega)]
      have hL : (ruinLeft j).val = j.val - 1 := rfl
      have hx : ((j.val - 1 : ℕ) : ℝ) = (j.val : ℝ) - 1 := by simpa only [Nat.cast_one] using
          (Nat.cast_sub (R := ℝ) (show 1 ≤ j.val by omega))
      have hg := ruinMeanReal_step N hN p hp hp1 j hj
      have hh := ruinExitProbability_step N p hp hp1 j hj
      dsimp [f, d]
      rw [hR, hL, hx, Nat.cast_add, Nat.cast_one]
      rw [hg, hh]
      ring
    have hz := ruin_harmonic_zero N hN p hp hp1 f hf0 hfN hs i
    apply (eq_div_iff (sub_ne_zero.mpr he)).mpr
    dsimp [f, d] at hz
    nlinarith [hz]

/-- The finite-interval assertion of the absorption-time theorem. -/
theorem ruin_mean : RuinMeanSpec.ruin_mean := by
  intro N hN p hp hp1 i
  have hfin := ruinMean_ne_top N hN p hp hp1 i
  have hform := ruinMeanReal_formula N hN p hp hp1 i
  change (Markov.meanHittingTime (ruinKernel N p hp hp1) (ruinBoundary N) i).toReal = _ at hform
  simp only [ruinTime]
  rw [← Markov.meanHittingTime_eq_lintegral]
  rw [← ENNReal.ofReal_toReal hfin, hform]

/-- The real-valued expectation equals the stated expression exactly. -/
theorem ruin_mean_real : RuinMeanSpec.ruin_mean_real := by
  intro N hN p hp hp1 i
  simp only [ruinTime]
  rw [← Markov.meanHittingTime_eq_lintegral]
  exact ruinMeanReal_formula N hN p hp hp1 i

end
end P207.Walk
