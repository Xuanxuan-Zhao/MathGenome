import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.IntervalTaylor
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.IntervalCalculus
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Taylor bridges for the closed-interval convention in paper.tex:1812–1815.
The formulas provide the foundations used at 2090–2100, 2391–2401, 2443–2452
and the scalar Newton estimates. The supplied jet is restricted to the closed
hull before applying Mathlib's within-derivative Taylor theorems. -/
namespace NumAnalysis206.Approximation
open Set
open scoped BigOperators

noncomputable abbrev jetTaylorSum := IntervalTaylorSpec.sumValue

variable {a b c x M : ℝ} {r : ℕ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ}

private theorem jet_hull (hD : IntervalJet a b r f D)
    (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) :
    IntervalJet (min c x) (max c x) r f D :=
  jet_restrict (le_min hc.1 hx.1) (max_le hc.2 hx.2) hD

private theorem jetTaylorSum_self (hr : 1 ≤ r) : jetTaylorSum D r c c = D 0 c := by
  classical
  unfold jetTaylorSum IntervalTaylorSpec.sumValue
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    simp [zero_pow hk0]
  · simp [show r ≠ 0 by omega]

private theorem jetTaylorSum_eq (hD : IntervalJet a b (r + 1) f D) (hab : a < b)
    (hc : c ∈ Icc a b) :
    jetTaylorSum D (r + 1) c x = taylorWithinEval f r (Icc a b) c x := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← jet_eq_iterated hab hD k (by simpa using (Finset.mem_range.mp hk).le) hc]
  simp only [smul_eq_mul]
  ring

/-- Taylor's formula with a single real Lagrange remainder point in the closed hull. -/
theorem jet_taylor_lagrange (_hab : a ≤ b) (hr : 1 ≤ r)
    (hD : IntervalJet a b r f D) (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) :
    ∃ ξ ∈ uIcc c x, f x = jetTaylorSum D r c x +
      D r ξ * (x - c) ^ r / (r.factorial : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  by_cases hcx : c = x
  · subst x
    refine ⟨c, by simp, ?_⟩
    rw [jetTaylorSum_self (by omega), hD.1 hc]
    simp
  · have hJ := jet_hull hD hc hx
    have hlt : min c x < max c x := min_lt_max.mpr hcx
    have hF := jet_to_contDiff min_le_max hJ
    have hd : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc c x)) (uIcc c x) :=
      hF.differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self n)
        (uniqueDiffOn_Icc hlt)
    obtain ⟨ξ, hξ, heq⟩ := taylor_mean_remainder_lagrange hcx hF.of_succ
      (hd.mono Ioo_subset_Icc_self)
    have hξ' : ξ ∈ uIcc c x := Ioo_subset_Icc_self hξ
    simp only [uIcc] at heq hξ'
    rw [← jet_eq_iterated hlt hJ (n + 1) le_rfl hξ',
      ← jetTaylorSum_eq hJ hlt (by exact left_mem_uIcc)] at heq
    exact ⟨ξ, hξ', by simpa only [add_comm] using eq_add_of_sub_eq heq⟩

/-- Uniform absolute bound on the Taylor remainder; only the joining hull is used. -/
theorem jet_taylor_bound (hab : a ≤ b) (hr : 1 ≤ r)
    (hD : IntervalJet a b r f D) (hc : c ∈ Icc a b) (hx : x ∈ Icc a b)
    (hM : ∀ t ∈ uIcc c x, |D r t| ≤ M) :
    |f x - jetTaylorSum D r c x| ≤ M * |x - c| ^ r / (r.factorial : ℝ) := by
  obtain ⟨ξ, hξ, heq⟩ := jet_taylor_lagrange hab hr hD hc hx
  have heq' : f x - jetTaylorSum D r c x = D r ξ * (x - c) ^ r / (r.factorial : ℝ) := by
    linarith
  rw [heq', abs_div, abs_mul, abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r.factorial)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hM ξ hξ) (pow_nonneg (abs_nonneg _) _)) (by positivity)

/-- Taylor's integral remainder, with the integral oriented from `c` to `x`. -/
theorem jet_taylor_integral (_hab : a ≤ b) (hr : 1 ≤ r)
    (hD : IntervalJet a b r f D) (hc : c ∈ Icc a b) (hx : x ∈ Icc a b) :
    f x = jetTaylorSum D r c x +
      ∫ t in c..x, D r t * (x - t) ^ (r - 1) / ((r - 1).factorial : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  by_cases hcx : c = x
  · subst x
    rw [jetTaylorSum_self (by omega), hD.1 hc]
    simp
  · have hJ := jet_hull hD hc hx
    have hlt : min c x < max c x := min_lt_max.mpr hcx
    have heq := taylor_integral_remainder (jet_to_contDiff min_le_max hJ)
    simp only [uIcc] at heq
    rw [← jetTaylorSum_eq hJ hlt (by exact left_mem_uIcc)] at heq
    have hint : (∫ t in c..x, ((x - t) ^ n / (n.factorial : ℝ)) •
        iteratedDerivWithin (n + 1) f (uIcc c x) t) =
        ∫ t in c..x, D (n + 1) t * (x - t) ^ n / (n.factorial : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [uIcc] at ht ⊢
      rw [← jet_eq_iterated hlt hJ (n + 1) le_rfl ht]
      simp only [smul_eq_mul]
      ring
    simp only [uIcc] at hint
    rw [hint] at heq
    simpa only [Nat.succ_sub_one, add_comm] using (eq_add_of_sub_eq heq)

/-- The positive-part kernel extends the integral from `[a,x]` to `[a,b]`.
The condition `r ≥ 2` makes the kernel vanish also at `t = x`. -/
theorem jet_taylor_positive_part (hab : a ≤ b) (hr : 2 ≤ r)
    (hD : IntervalJet a b r f D) (hx : x ∈ Icc a b) :
    f x = jetTaylorSum D r a x +
      ∫ t in a..b, D r t * (max (x - t) 0) ^ (r - 1) / ((r - 1).factorial : ℝ) := by
  have hF := jet_taylor_integral hab (by omega) hD (left_mem_Icc.mpr hab) hx
  let K : ℝ → ℝ := fun t =>
    D r t * (max (x - t) 0) ^ (r - 1) / ((r - 1).factorial : ℝ)
  have hK : ContinuousOn K (Icc a b) := by
    have hk : Continuous (fun t : ℝ =>
        (max (x - t) 0) ^ (r - 1)) := by fun_prop
    exact ((hD.2.1 r le_rfl).mul hk.continuousOn).div_const _
  have hKax : IntervalIntegrable K MeasureTheory.volume a x := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx.1]
    exact hK.mono (Icc_subset_Icc le_rfl hx.2)
  have hKxb : IntervalIntegrable K MeasureTheory.volume x b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx.2]
    exact hK.mono (Icc_subset_Icc hx.1 le_rfl)
  have hzero : (∫ t in x..b, K t) = 0 := by
    calc
      (∫ t in x..b, K t) = ∫ t in x..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hx.2] at ht
        simp [K, max_eq_right (sub_nonpos.mpr ht.1), zero_pow (by omega : r - 1 ≠ 0)]
      _ = 0 := intervalIntegral.integral_zero
  have hreplace : (∫ t in a..x, D r t * (x - t) ^ (r - 1) /
      ((r - 1).factorial : ℝ)) = ∫ t in a..x, K t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    dsimp [K]
    rw [max_eq_left (sub_nonneg.mpr ht.2)]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hKax hKxb
  rw [hzero, add_zero] at hsplit
  rw [hreplace, hsplit] at hF
  exact hF

end NumAnalysis206.Approximation
