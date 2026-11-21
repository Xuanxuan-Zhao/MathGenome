import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.LogArctanSeries
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.LogConstruction
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.TrigInverses
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Abel
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch11.Alternating
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The logarithm interior uses Mathlib's finite Taylor remainder proof in
`Real.hasSum_pow_div_log_of_abs_lt_one`; alternation and Abel supply x=1.
The arctangent interior uses `Real.hasSum_arctan` (proved through the complex
logarithm Taylor series and the real principal-branch identification), and
`Real.tendsto_sum_pi_div_four` uses alternation and Abel at 1. Oddness supplies
-1. The upstream inverse/series bridges identify the original functions.
Exterior terms cannot tend to zero: their absolute values times m/|x|^m
are identically 1, whereas m/|x|^m tends to zero. At log's negative endpoint
the partial sums are the negative harmonic partial sums with a one-index shift.
-/
noncomputable section
namespace SingleVariableAnalysis
open Filter Set
open scoped BigOperators Topology

def logSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ)^n * x^(n+1) / (n+1 : ℝ)
def arctanSeriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ)^n * x^(2*n+1) / (2*n+1 : ℝ)

namespace LogArctanSeries

private theorem ordinary_of_tendsto {a : ℕ → ℝ} {S : ℝ}
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S)) :
    RealSeriesHasSum a S :=
  (realSequenceConverges_iff _ _).mpr ((abel_tendsto_sum_range_iff a S).mpr h)

private theorem log_interior {x : ℝ} (hx : |x| < 1) :
    HasSum (logSeriesTerm x) (Real.log (1+x)) := by
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one
    (x := -x) (by simpa using hx)).neg
  convert h using 1
  · funext n
    dsimp [logSeriesTerm]
    rw [neg_pow x, pow_succ (-1 : ℝ)]
    ring
  · simp

private theorem arctan_interior {x : ℝ} (hx : |x| < 1) :
    HasSum (arctanSeriesTerm x) (Real.arctan x) := by
  unfold arctanSeriesTerm
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    Real.hasSum_arctan (x := x) (by simpa only [Real.norm_eq_abs] using hx)

private theorem log_one : RealSeriesHasSum (logSeriesTerm 1) (Real.log 2) := by
  obtain ⟨S, hS⟩ := alternating_harmonic_conditional.1
  let a : ℕ → ℝ := fun n => (-1 : ℝ)^n / (n+1 : ℝ)
  have ha : RealSeriesHasSum a S := hS
  have hab := real_abel_endpoint a S ha
  have ht := hab.mul (tendsto_id.mono_left nhdsWithin_le_nhds :
    Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1))
  simp only [mul_one] at ht
  have he (y : ℝ) (hy : |y| < 1) :
      (∑' n, a n * y^n) * y = Real.log (1+y) := by
    rw [← tsum_mul_right]
    convert (log_interior hy).tsum_eq using 1
    congr 1
    funext n
    dsimp [a, logSeriesTerm]
    rw [pow_succ]
    ring
  have hlog : Tendsto (fun y : ℝ => Real.log (1+y)) (𝓝[<] 1) (𝓝 S) := by
    apply ht.congr'
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with y hy
    exact he y (abs_lt.mpr hy)
  have hc : Tendsto (fun y : ℝ => Real.log (1+y)) (𝓝[<] 1) (𝓝 (Real.log 2)) := by
    have hcont : ContinuousAt (fun y : ℝ => Real.log (1+y)) 1 :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ)+1 ≠ 0)).comp
        (continuousAt_const.add continuousAt_id)
    convert hcont.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1) using 1; norm_num
  have hval : S = Real.log 2 := tendsto_nhds_unique hlog hc
  rw [hval] at ha
  convert ha using 1
  funext n
  simp [logSeriesTerm, a]

private theorem arctan_one :
    RealSeriesHasSum (arctanSeriesTerm 1) (Real.pi/4) := by
  apply ordinary_of_tendsto
  simpa only [arctanSeriesTerm, one_pow, mul_one, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one] using Real.tendsto_sum_pi_div_four

private theorem arctan_neg (x : ℝ) (n : ℕ) :
    arctanSeriesTerm (-x) n = -arctanSeriesTerm x n := by
  unfold arctanSeriesTerm
  rw [neg_pow x]
  simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
  ring

private theorem arctan_minus_one :
    RealSeriesHasSum (arctanSeriesTerm (-1)) (-(Real.pi/4)) := by
  have h := real_series_const_mul _ _ arctan_one (-1)
  simpa only [neg_one_mul, ← arctan_neg] using h

end LogArctanSeries
end SingleVariableAnalysis

namespace SingleVariableAnalysis.LogArctanSeries
open Filter Set
open scoped BigOperators Topology

/-- A subsequence of exponential-over-linear terms cannot tend to zero. -/
private theorem not_zero_limit_pow_div (x : ℝ) (hx : 1 < |x|)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hpos : ∀ n, 0 < m n) :
    ¬ Tendsto (fun n => |x|^(m n)/(m n : ℝ)) atTop (𝓝 0) := by
  intro ht
  have hi : Tendsto (fun n => (m n : ℝ)/|x|^(m n)) atTop (𝓝 0) := by
    simpa only [pow_one, Function.comp_def] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 hx).comp hm
  have hp := ht.mul hi
  have he (n : ℕ) : (|x|^(m n)/(m n : ℝ)) * ((m n : ℝ)/|x|^(m n)) = 1 := by
    have hmn : (m n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hpos n))
    have hxn : |x|^(m n) ≠ 0 := pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hx))
    field_simp
  simp only [zero_mul] at hp
  have hh : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := hp.congr he
  have := tendsto_nhds_unique hh (tendsto_const_nhds (x := (1 : ℝ)))
  norm_num at this

theorem log_exterior_term_test :
    Specs.SingleVariableAnalysis.Ch13.LogArctanSeries.logExteriorTermTest := by
  intro x hx ht
  have h := ((realSequenceConverges_iff _ _).mp ht).abs
  simp only [abs_zero] at h
  apply not_zero_limit_pow_div x hx (fun n => n+1) (tendsto_add_atTop_nat 1)
    (fun n => Nat.succ_pos n)
  apply h.congr
  intro n
  simp [Specs.SingleVariableAnalysis.Ch13.LogArctanSeries.logSeriesTermValue,
    abs_div, abs_mul, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ)+1),
    Nat.cast_add]

theorem arctan_exterior_term_test :
    Specs.SingleVariableAnalysis.Ch13.LogArctanSeries.arctanExteriorTermTest := by
  intro x hx ht
  have h := ((realSequenceConverges_iff _ _).mp ht).abs
  simp only [abs_zero] at h
  have hm : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ 2*n+1 by omega) tendsto_id
  apply not_zero_limit_pow_div x hx (fun n => 2*n+1) hm (fun n => by omega)
  apply h.congr
  intro n
  simp [Specs.SingleVariableAnalysis.Ch13.LogArctanSeries.arctanSeriesTermValue,
    abs_div, abs_mul, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < 2*(n : ℝ)+1),
    Nat.cast_add, Nat.cast_mul]

theorem exterior_divergence :
    Specs.SingleVariableAnalysis.Ch13.LogArctanSeries.exteriorDivergence := by
  intro x hx
  constructor
  · intro h
    exact log_exterior_term_test x hx (real_series_term_limit _ h)
  · intro h
    exact arctan_exterior_term_test x hx (real_series_term_limit _ h)

private theorem log_minus_one_term (n : ℕ) :
    logSeriesTerm (-1) n = -(1/(n+1 : ℝ)) := by
  simp [logSeriesTerm, pow_succ, ← mul_pow, neg_div, one_div]

private theorem log_minus_one_partial (N : ℕ) :
    realPartialSum (logSeriesTerm (-1)) N =
      -realPartialSum (fun n => 1/(n : ℝ)) (N+1) := by
  unfold realPartialSum
  simp_rw [log_minus_one_term]
  rw [Finset.sum_range_succ' (fun n : ℕ => 1/(n : ℝ)) (N+1)]
  simp [Finset.sum_neg_distrib, Nat.cast_add, Nat.cast_one]

theorem log_negative_endpoint :
    Specs.SingleVariableAnalysis.Ch13.LogArctanSeries.logNegativeEndpoint := by
  have hd : DivergesToNegInfinity (realPartialSum (logSeriesTerm (-1))) := by
    intro B
    obtain ⟨N, hN⟩ := harmonic_divergesToPosInfinity (-B)
    refine ⟨N, fun n hn => ?_⟩
    change realPartialSum (logSeriesTerm (-1)) n < B
    rw [log_minus_one_partial]
    have hh := hN (n+1) (by omega)
    linarith
  refine ⟨hd, ?_⟩
  rintro ⟨S, hS⟩
  exact negInfinity_not_finite _ hd S hS

theorem log_identity : Specs.SingleVariableAnalysis.Ch13.LogArctanSeries.logIdentity := by
  intro x hl hu
  change RealSeriesHasSum (logSeriesTerm x) (seriesLog (1+x))
  rw [seriesLog_eq_realLog _ (by linarith)]
  rcases lt_or_eq_of_le hu with hu | rfl
  · exact ordinary_of_tendsto (log_interior (abs_lt.mpr ⟨hl, hu⟩)).tendsto_sum_nat
  · convert log_one using 1; norm_num

theorem arctan_identity : Specs.SingleVariableAnalysis.Ch13.LogArctanSeries.arctanIdentity := by
  intro x hl hu
  change RealSeriesHasSum (arctanSeriesTerm x) (Real.arctan x)
  by_cases hn : x = -1
  · subst x
    simpa only [Real.arctan_neg, Real.arctan_one] using arctan_minus_one
  by_cases hp : x = 1
  · subst x
    simpa only [Real.arctan_one] using arctan_one
  exact ordinary_of_tendsto (arctan_interior
    (abs_lt.mpr ⟨lt_of_le_of_ne hl (Ne.symm hn), lt_of_le_of_ne hu hp⟩)).tendsto_sum_nat

theorem log_endpoint : Specs.SingleVariableAnalysis.Ch13.LogArctanSeries.logEndpoint := by
  change RealSeriesHasSum (logSeriesTerm 1) (seriesLog 2)
  rw [seriesLog_eq_realLog 2 (by norm_num)]
  exact log_one

theorem arctan_endpoints : Specs.SingleVariableAnalysis.Ch13.LogArctanSeries.arctanEndpoints := by
  change RealSeriesHasSum (arctanSeriesTerm 1)
      (analyticPi/4) ∧
    RealSeriesHasSum (arctanSeriesTerm (-1))
      (-(analyticPi/4))
  rw [PiPeriod.analyticPi_eq_pi]
  exact ⟨arctan_one, arctan_minus_one⟩

theorem log_domain : Specs.SingleVariableAnalysis.Ch13.LogArctanSeries.logDomain := by
  intro x
  constructor
  · intro h
    have hx : |x| ≤ 1 := by
      by_contra! hx
      exact (exterior_divergence x hx).1 h
    have hl := (abs_le.mp hx).1
    have hu := (abs_le.mp hx).2
    refine ⟨lt_of_le_of_ne hl ?_, hu⟩
    intro he
    subst x
    exact log_negative_endpoint.2 h
  · rintro ⟨hl, hu⟩
    exact ⟨_, log_identity x hl hu⟩

theorem arctan_domain : Specs.SingleVariableAnalysis.Ch13.LogArctanSeries.arctanDomain := by
  intro x
  constructor
  · intro h
    apply abs_le.mp
    by_contra! hx
    exact (exterior_divergence x hx).2 h
  · rintro ⟨hl, hu⟩
    exact ⟨_, arctan_identity x hl hu⟩

end SingleVariableAnalysis.LogArctanSeries
