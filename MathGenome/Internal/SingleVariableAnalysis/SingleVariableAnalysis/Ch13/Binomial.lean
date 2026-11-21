import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.BinomialInterior
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Abel
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Alternating
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Nonnegative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Binomial
import Mathlib.Analysis.PSeries

/-!
# Generalized binomial series at the endpoints

K03.13.binomial, paper.tex:1452–1477. The canonical coefficients and the
interior, finite-polynomial and radius results come from `BinomialInterior`.

For α>0, the magnitude recurrence telescopes to bound every finite absolute
tail. For α>-1, decreasing tail magnitudes have limit zero: a positive limit
would bound a shifted harmonic series by summable telescoping differences.
For -1<α<0 this gives ordinary convergence by the alternating test; for α≤-1
the term test fails. Abel's ordinary endpoint theorem identifies the value at
1, identifies the value at -1 for positive α, and rules out a finite sum at
-1 for negative α by the positive-base power blowup. Natural exponents are
handled by their finite support at every real argument, including the constant
polynomial at α=0. No unconditional summability is imposed on a conditional
series.

Public comparison: McGill MATH 255, Lecture 22, p. 1,
https://www.math.mcgill.ca/labute/courses/255w03/L22.pdf
(retrieved text and observations in `research/` and `proof-work.md`).
The endpoint classifications agree; this proof uses the manuscript's
harmonic/telescoping argument rather than that reference's Raabe/log estimates.
-/

noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped Topology BigOperators

/-- Magnitude recurrence on the tail beyond the exponent. -/
theorem binomial_abs_recurrence (α : ℝ) (n : ℕ) (hn : α ≤ n) :
    (n + 1 : ℝ) * |binomialCoefficient α (n+1)| =
      (n - α) * |binomialCoefficient α n| := by
  have h := congrArg abs (binomialCoefficient_recurrence α n)
  simpa only [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n+1),
    abs_of_nonpos (sub_nonpos.mpr hn), neg_sub] using h

/-- A finite telescoping bound, including its nonnegative boundary term. -/
theorem binomial_abs_tail_bound (α : ℝ) (N : ℕ) (hN : α ≤ N) (k : ℕ) :
    α * (∑ j ∈ Finset.range k, |binomialCoefficient α (j+N)|) +
      (k+N : ℝ) * |binomialCoefficient α (k+N)| =
      (N : ℝ) * |binomialCoefficient α N| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := binomial_abs_recurrence α (k+N)
      (hN.trans (by exact_mod_cast Nat.le_add_left N k))
    rw [Finset.sum_range_succ]
    push_cast at h ⊢
    rw [show k+1+N = (k+N)+1 by omega]
    nlinarith

theorem binomial_abs_summable (α : ℝ) (hα : 0 < α) :
    Summable (fun n => |binomialCoefficient α n|) := by
  obtain ⟨N, hN⟩ := exists_nat_gt α
  apply (summable_nat_add_iff N).mp
  apply summable_of_sum_range_le (fun n => abs_nonneg _) (c :=
    (N : ℝ) * |binomialCoefficient α N| / α)
  intro k
  apply (le_div_iff₀ hα).mpr
  have h := binomial_abs_tail_bound α N hN.le k
  have hnon : 0 ≤ (k+N : ℝ) * |binomialCoefficient α (k+N)| := by positivity
  nlinarith

/-- For α>-1, the tail magnitudes decrease. -/
theorem binomial_abs_tail_antitone (α : ℝ) (hα : -1 < α) (N : ℕ)
    (hN : α ≤ N) : Antitone (fun n => |binomialCoefficient α (n+N)|) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := binomial_abs_recurrence α (n+N)
    (hN.trans (by exact_mod_cast Nat.le_add_left N n))
  have ht := abs_nonneg (binomialCoefficient α (n+N))
  have hd : 0 < (n+N+1 : ℝ) := by positivity
  have hc : |binomialCoefficient α (n+1+N)| =
      |binomialCoefficient α ((n+N)+1)| := by congr 2; omega
  rw [hc]
  push_cast at h
  nlinarith

/-- Decay of magnitudes for -1<α. A positive decreasing limit would make the
harmonic series summable by comparison with telescoping differences. -/
theorem binomial_abs_tendsto_zero (α : ℝ) (hα : -1 < α) :
    Tendsto (fun n => |binomialCoefficient α n|) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt α
  let t : ℕ → ℝ := fun n => |binomialCoefficient α (n+N)|
  have ht : ∀ n, 0 ≤ t n := fun n => abs_nonneg _
  have hm : Antitone t := binomial_abs_tail_antitone α hα N hN.le
  have hb : BddBelow (Set.range t) := ⟨0, by rintro _ ⟨n,rfl⟩; exact ht n⟩
  have hl := tendsto_atTop_ciInf hm hb
  have hl0 : 0 ≤ iInf t := le_ciInf (fun n => ht n)
  have hd : Summable (fun n => t n - t (n+1)) := by
    apply summable_of_sum_range_le (fun n => sub_nonneg.mpr (hm (Nat.le_succ n)))
      (c := t 0)
    intro k
    have he : ∑ n ∈ Finset.range k, (t n - t (n+1)) = t 0 - t k := by
      induction k with
      | zero => simp
      | succ k ih => rw [Finset.sum_range_succ, ih]; ring
    rw [he]
    linarith [ht k]
  have hz : iInf t = 0 := by
    by_contra hn
    have hp : 0 < iInf t := lt_of_le_of_ne hl0 (Ne.symm hn)
    have hc : 0 < (α+1) * iInf t := mul_pos (by linarith) hp
    have hcomp : Summable (fun n : ℕ => 1 / (n+N+1 : ℝ)) := by
      apply (hd.div_const ((α+1)*iInf t)).of_nonneg_of_le (fun n => by positivity)
      intro n
      apply (le_div_iff₀ hc).mpr
      have hr := binomial_abs_recurrence α (n+N)
        (hN.le.trans (by exact_mod_cast Nat.le_add_left N n))
      have hi : iInf t ≤ t n := ciInf_le hb n
      have hnt : t (n+1) = |binomialCoefficient α ((n+N)+1)| := by
        dsimp [t]; congr 2; omega
      have hnpos : (0 : ℝ) < n+N+1 := by positivity
      have he : (n+N+1 : ℝ) * (t n - t (n+1)) = (α+1)*t n := by
        dsimp [t] at *
        push_cast at hr ⊢
        rw [hnt]
        nlinarith
      rw [div_mul_eq_mul_div, one_mul]
      apply (div_le_iff₀ hnpos).mpr
      nlinarith
    have hh : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
      apply (summable_nat_add_iff (N+1)).mp
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hcomp
    exact Real.not_summable_one_div_natCast hh
  have hz' : Tendsto t atTop (𝓝 0) := hz ▸ hl
  exact (tendsto_add_atTop_iff_nat N).mp hz'

/-- The signed coefficients are nonnegative for nonpositive exponents. -/
theorem binomial_signed_nonneg (α : ℝ) (hα : α ≤ 0) (n : ℕ) :
    0 ≤ (-1 : ℝ)^n * binomialCoefficient α n := by
  induction n with
  | zero => simp [binomialCoefficient_zero]
  | succ n ih =>
    have hr := binomialCoefficient_recurrence α n
    have he : (n+1 : ℝ) * ((-1 : ℝ)^(n+1) * binomialCoefficient α (n+1)) =
        (n-α) * ((-1 : ℝ)^n * binomialCoefficient α n) := by
      rw [pow_succ]
      calc
        _ = -((-1 : ℝ)^n) * ((n+1 : ℝ) * binomialCoefficient α (n+1)) := by ring
        _ = _ := by rw [hr]; ring
    have hn : (0 : ℝ) ≤ n-α := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hp := mul_nonneg hn ih
    have hd : (0 : ℝ) < n+1 := by positivity
    nlinarith

theorem binomial_signed_abs (α : ℝ) (hα : α ≤ 0) (n : ℕ) :
    (-1 : ℝ)^n * binomialCoefficient α n = |binomialCoefficient α n| := by
  have h := abs_of_nonneg (binomial_signed_nonneg α hα n)
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using h.symm

private theorem ordinary_of_summable {a : ℕ → ℝ} (h : Summable a) :
    RealSeriesConverges a :=
  ⟨_, PowerSeriesDifferentiation.real_hasSum_of_hasSum h.hasSum⟩

/-- Ordinary endpoint convergence at 1, before identifying its value. -/
theorem binomial_one_converges (α : ℝ) (hα : -1 < α) :
    RealSeriesConverges (binomialCoefficient α) := by
  by_cases hp : 0 < α
  · apply ordinary_of_summable (a := binomialCoefficient α)
    exact (summable_norm_iff).mp (by
      simpa only [Real.norm_eq_abs] using binomial_abs_summable α hp)
  by_cases hz : α = 0
  · subst α
    apply ordinary_of_summable
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hn0 : n ≠ 0 := by simpa using hn
    simpa only [Nat.cast_zero] using binomialCoefficient_termination 0 n (by omega)
  have hn : α < 0 := lt_of_le_of_ne (not_lt.mp hp) hz
  have ha := alternating_series_converges (fun n => |binomialCoefficient α n|)
    (fun n => abs_nonneg _) (fun n =>
      (binomial_abs_tail_antitone α hα 0 (by linarith)) (Nat.le_succ n))
    ((realSequenceConverges_iff _ _).mpr (binomial_abs_tendsto_zero α hα))
  have he : (fun n => (-1 : ℝ)^n * |binomialCoefficient α n|) =
      binomialCoefficient α := by
    funext n
    rw [← binomial_signed_abs α hn.le n, ← mul_assoc, ← mul_pow]
    norm_num
  rwa [he] at ha

/-- For α≤-1 the magnitudes never fall below c₀=1, so the term test fails. -/
theorem binomial_one_diverges (α : ℝ) (hα : α ≤ -1) :
    ¬ RealSeriesConverges (binomialCoefficient α) := by
  have hb : ∀ n, 1 ≤ |binomialCoefficient α n| := by
    intro n
    induction n with
    | zero => simp [binomialCoefficient_zero]
    | succ n ih =>
      have hr := binomial_abs_recurrence α n (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      have hd : (0 : ℝ) < n+1 := by positivity
      have ht := abs_nonneg (binomialCoefficient α n)
      nlinarith
  intro h
  obtain ⟨N,hN⟩ := real_series_term_limit _ h 1 (by norm_num)
  have := hN N le_rfl
  simp only [sub_zero] at this
  linarith [hb N]

/-- Interior `tsum` values are used only where the series is absolutely summable. -/
theorem binomial_tsum_interior (α x : ℝ) (hx : |x| < 1) :
    (∑' n, binomialCoefficient α n * x^n) = realPower (1+x) α := by
  have hs := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := α)).hasSum
    (y := x) (by simpa [Metric.mem_eball, edist_dist, Real.dist_eq] using hx)
  have hb : 0 < 1+x := by have := (abs_lt.mp hx).1; linarith
  rw [realPower_eq_rpow _ hb]
  exact (show HasSum (fun n => binomialCoefficient α n * x^n) ((1+x)^α) by
    simpa [binomialSeries, binomialCoefficient_eq_choose, mul_comm] using hs).tsum_eq

/-- Identification of any ordinary sum at 1 by Abel and continuity at base 2. -/
theorem binomial_one_value (α S : ℝ) (hS : RealSeriesHasSum (binomialCoefficient α) S) :
    S = realPower 2 α := by
  have ha := real_abel_endpoint _ S hS
  have hb : Tendsto (fun x : ℝ => realPower (1+x) α) (𝓝[<] 1)
      (𝓝 (realPower 2 α)) := by
    have hc := (realPower_continuous_base α) 2 (by norm_num : (2 : ℝ) ∈ Set.Ioi 0)
    -- Continuity on positive bases at 2 is continuity at this interior point.
    have hct : ContinuousAt (fun y => realPower y α) 2 :=
      hc.continuousAt (isOpen_Ioi.mem_nhds (by norm_num))
    apply hct.tendsto.comp
    convert ((tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1))) using 1 <;> norm_num
  apply tendsto_nhds_unique ha
  apply hb.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with x hx
  exact (binomial_tsum_interior α x (abs_lt.mpr hx)).symm

private theorem binomial_base_zero_approach :
    Tendsto (fun x : ℝ => 1+x) (𝓝[>] (-1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert ((tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun x : ℝ => x) (𝓝[>] (-1 : ℝ)) (𝓝 (-1)))) using 1 <;> norm_num
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < 1+x
    have : (-1 : ℝ) < x := hx
    linarith

private theorem binomial_interior_near_neg_one (α : ℝ) :
    (fun x : ℝ => ∑' n, binomialCoefficient α n * x^n) =ᶠ[𝓝[>] (-1 : ℝ)]
      (fun x => realPower (1+x) α) := by
  filter_upwards [Ioo_mem_nhdsGT (show (-1 : ℝ) < 1 by norm_num)] with x hx
  exact binomial_tsum_interior α x (abs_lt.mpr hx)

/-- A finite ordinary sum at -1 would contradict the negative-power blowup. -/
theorem binomial_neg_one_diverges (α : ℝ) (hα : α < 0) :
    ¬ RealSeriesConverges (fun n => (-1 : ℝ)^n * binomialCoefficient α n) := by
  rintro ⟨S,hS⟩
  have ha := (real_abel_negative_endpoint (binomialCoefficient α) S hS).2
  have hd := (realPower_neg_tendsto_zero_right α hα).comp binomial_base_zero_approach
  have ha' : Tendsto (fun x : ℝ => realPower (1+x) α) (𝓝[>] (-1 : ℝ)) (𝓝 S) :=
    ha.congr' (binomial_interior_near_neg_one α)
  exact not_tendsto_nhds_of_tendsto_atTop hd S ha'

/-- A positive exponent gives absolute ordinary convergence at both endpoints. -/
theorem binomial_endpoints_absolute (α : ℝ) (hα : 0 < α) :
    RealPowerSeriesAbsolutelyConverges (binomialCoefficient α) 0 1 ∧
    RealPowerSeriesAbsolutelyConverges (binomialCoefficient α) 0 (-1) := by
  have ha := ordinary_of_summable (binomial_abs_summable α hα)
  constructor <;>
    simpa only [RealPowerSeriesAbsolutelyConverges, realPowerSeriesTerm, sub_zero,
      abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one] using ha

theorem binomial_endpoint_one_sum (α : ℝ) (hα : -1 < α) :
    RealPowerSeriesHasSum (binomialCoefficient α) 0 1 (realPower 2 α) := by
  obtain ⟨S,hS⟩ := binomial_one_converges α hα
  have he := binomial_one_value α S hS
  change RealSeriesHasSum (fun n => binomialCoefficient α n * (1-0)^n) _
  simpa only [sub_zero, one_pow, mul_one, ← he] using hS

theorem binomial_endpoint_one_converges (α : ℝ) (_hα : ∀ m : ℕ, α ≠ (m : ℝ)) :
    RealPowerSeriesConverges (binomialCoefficient α) 0 1 ↔ -1 < α := by
  change (∃ S, RealSeriesHasSum (fun n => binomialCoefficient α n * (1-0)^n) S) ↔ _
  simp only [sub_zero, one_pow, mul_one]
  exact ⟨fun h => lt_of_not_ge (fun hn => binomial_one_diverges α hn h),
    binomial_one_converges α⟩

/-- Abel identifies the negative-endpoint value as the positive-power limit 0. -/
theorem binomial_endpoint_neg_one_sum (α : ℝ) (hα : 0 < α) :
    RealPowerSeriesHasSum (binomialCoefficient α) 0 (-1) 0 := by
  have hs : Summable (binomialCoefficient α) :=
    summable_norm_iff.mp (by simpa only [Real.norm_eq_abs] using binomial_abs_summable α hα)
  obtain ⟨S,hS⟩ := ordinary_of_summable hs.alternating
  have ha := (real_abel_negative_endpoint (binomialCoefficient α) S hS).2
  have hz := (realPower_pos_tendsto_zero_right α hα).comp binomial_base_zero_approach
  have he : S = 0 := tendsto_nhds_unique ha
    (hz.congr' (binomial_interior_near_neg_one α).symm)
  rw [he] at hS
  change RealSeriesHasSum (fun n => binomialCoefficient α n * (-1-0)^n) 0
  simpa only [sub_zero, mul_comm] using hS

theorem binomial_endpoint_neg_one_converges (α : ℝ) (hα : ∀ m : ℕ, α ≠ (m : ℝ)) :
    RealPowerSeriesConverges (binomialCoefficient α) 0 (-1) ↔ 0 < α := by
  constructor
  · intro h
    by_contra hn
    have hn' : α < 0 := lt_of_le_of_ne (not_lt.mp hn) (by simpa using hα 0)
    apply binomial_neg_one_diverges α hn'
    change ∃ S, RealSeriesHasSum (fun n => binomialCoefficient α n * (-1-0)^n) S at h
    have hf : (fun n => binomialCoefficient α n * (-1-0)^n) =
        (fun n => (-1 : ℝ)^n * binomialCoefficient α n) := by
      funext n
      simp only [sub_zero]
      ring
    rw [hf] at h
    exact h
  · intro hp
    exact ⟨0, binomial_endpoint_neg_one_sum α hp⟩

theorem binomial_endpoint_one_conditional (α : ℝ) (hl : -1 < α) (hu : α < 0) :
    RealPowerSeriesConverges (binomialCoefficient α) 0 1 ∧
    ¬ RealPowerSeriesAbsolutelyConverges (binomialCoefficient α) 0 1 := by
  refine ⟨⟨_, binomial_endpoint_one_sum α hl⟩, ?_⟩
  intro ha
  apply binomial_neg_one_diverges α hu
  have he : (fun n => (-1 : ℝ)^n * binomialCoefficient α n) =
      (fun n => |binomialCoefficient α n|) := funext (binomial_signed_abs α hu.le)
  rw [he]
  simpa only [RealPowerSeriesAbsolutelyConverges, realPowerSeriesTerm, sub_zero,
    one_pow, mul_one] using ha

theorem binomial_natural_all_arguments (m : ℕ) (x : ℝ) :
    (∀ n : ℕ, m < n → binomialCoefficient (m : ℝ) n = 0) ∧
    RealPowerSeriesAbsolutelyConverges (binomialCoefficient (m : ℝ)) 0 x ∧
    RealPowerSeriesHasSum (binomialCoefficient (m : ℝ)) 0 x ((1+x)^m) := by
  have hz : ∀ n ∉ Finset.range (m+1), binomialCoefficient (m : ℝ) n * x^n = 0 := by
    intro n hn
    have hn' : m+1 ≤ n := by simpa using hn
    rw [binomialCoefficient_termination m n (by omega), zero_mul]
  have hs : HasSum (fun n => binomialCoefficient (m : ℝ) n * x^n) ((1+x)^m) := by
    rw [← binomial_natural_identity m x]
    exact hasSum_sum_of_ne_finset_zero hz
  refine ⟨binomialCoefficient_termination m, ?_, ?_⟩
  · have hsabs : Summable (fun n => |binomialCoefficient (m : ℝ) n * x^n|) := by
      apply summable_of_ne_finset_zero (s := Finset.range (m+1))
      intro n hn
      rw [hz n hn, abs_zero]
    simpa only [RealPowerSeriesAbsolutelyConverges, realPowerSeriesTerm, sub_zero] using
      ordinary_of_summable hsabs
  · change RealSeriesHasSum (fun n => binomialCoefficient (m : ℝ) n * (x-0)^n) _
    simpa only [sub_zero] using PowerSeriesDifferentiation.real_hasSum_of_hasSum hs

theorem binomial_natural_endpoints (m : ℕ) :
    RealPowerSeriesHasSum (binomialCoefficient (m : ℝ)) 0 1 ((2 : ℝ)^m) ∧
    RealPowerSeriesHasSum (binomialCoefficient (m : ℝ)) 0 (-1)
      (if m = 0 then 1 else 0) := by
  constructor
  · simpa only [show (1 : ℝ)+1 = 2 by norm_num] using (binomial_natural_all_arguments m 1).2.2
  · simpa only [add_neg_cancel, zero_pow_eq] using (binomial_natural_all_arguments m (-1)).2.2

theorem binomial_interior_and_radius :
    (∀ (α x : ℝ), |x| < 1 → RealPowerSeriesHasSum
      (binomialCoefficient α) 0 x (realPower (1+x) α)) ∧
    (∀ α : ℝ, (∀ m : ℕ, α ≠ (m : ℝ)) →
      realPowerSeriesRadius (binomialCoefficient α) = 1) :=
  ⟨binomial_interior, binomial_nonnatural_radius⟩

end SingleVariableAnalysis
