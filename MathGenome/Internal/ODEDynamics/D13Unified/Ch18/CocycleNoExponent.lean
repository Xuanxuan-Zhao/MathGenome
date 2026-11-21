import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.CocycleNoExponent
import MathGenome.Internal.ODEDynamics.D13Unified.Ch18.GrowthDefinitions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.ShiftSpaces
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The scalar cocycle is multiplication by exp(s₀) over the native one-sided shift.
The j-th block (numbered from zero) has length 2^(2^(j+1)). Earlier blocks
have total length at most j * 2^(2^j), so their proportion is at most j/2^j.
At each endpoint the mean differs from its last symbol by at most this
proportion. The even and odd endpoint subsequences therefore tend to 0 and 1.
The final theorem uses the shared extended-real exponent definitions and
excludes every extended-real limit for every nonzero scalar direction.
This is an exceptional-point construction; it makes no almost-everywhere claim.
-/
noncomputable section
open Filter Finset
open scoped Topology BigOperators
namespace D13Unified.Ch18.CocycleNoExponent
open Specs.D13Unified.Ch17.ShiftSpaces
open D13Unified.Ch18.GrowthDefinitions
abbrev blockLength := Specs.D13Unified.Ch18.CocycleNoExponent.blockLength
abbrev endpoint := Specs.D13Unified.Ch18.CocycleNoExponent.endpoint
abbrev blockIndex := Specs.D13Unified.Ch18.CocycleNoExponent.blockIndex
abbrev basePoint := Specs.D13Unified.Ch18.CocycleNoExponent.basePoint
abbrev scalar := Specs.D13Unified.Ch18.CocycleNoExponent.scalar
abbrev generator := Specs.D13Unified.Ch18.CocycleNoExponent.generator
abbrev logAverage := Specs.D13Unified.Ch18.CocycleNoExponent.logAverage

lemma length_pos (j : ℕ) : 0 < blockLength j := by
  unfold blockLength Specs.D13Unified.Ch18.CocycleNoExponent.blockLength
  positivity

lemma endpoint_succ (j : ℕ) : endpoint (j+1) = endpoint j + blockLength j :=
  Finset.sum_range_succ _ _

lemma endpoint_mono : Monotone endpoint := by
  apply monotone_nat_of_le_succ
  intro j
  rw [endpoint_succ]
  omega

lemma endpoint_ge (j : ℕ) : j ≤ endpoint j := by
  induction j with
  | zero => simp [endpoint, Specs.D13Unified.Ch18.CocycleNoExponent.endpoint]
  | succ j ih => rw [endpoint_succ]; have := length_pos j; omega

lemma endpoint_pos (j : ℕ) : 0 < endpoint (j+1) := lt_of_lt_of_le (by omega) (endpoint_ge _)

lemma index_of_mem (j i : ℕ) (hlo : endpoint j ≤ i) (hhi : i < endpoint (j+1)) :
    blockIndex i = j := by
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨(endpoint_ge j).trans hlo, fun _ => hlo, ?_⟩
  intro k hjk hki hk
  have := endpoint_mono (Nat.succ_le_of_lt hjk)
  change endpoint k ≤ i at hk
  change endpoint (j+1) ≤ endpoint k at this
  omega

theorem blocks : Specs.D13Unified.Ch18.CocycleNoExponent.blocksStatement := by
  intro j i hlo hhi
  change blockIndex i % 2 = j % 2
  rw [index_of_mem j i hlo hhi]

lemma endpoint_bound (j : ℕ) : endpoint j ≤ j * 2 ^ (2 ^ j) := by
  unfold endpoint Specs.D13Unified.Ch18.CocycleNoExponent.endpoint
  calc
    _ ≤ ∑ _k ∈ range j, 2 ^ (2 ^ j) := by
      apply sum_le_sum
      intro k hk
      exact Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide)
        (Nat.succ_le_of_lt (mem_range.mp hk)))
    _ = _ := by simp

lemma length_square (j : ℕ) : blockLength j = (2 ^ (2 ^ j)) ^ 2 := by
  unfold blockLength Specs.D13Unified.Ch18.CocycleNoExponent.blockLength
  rw [pow_succ, pow_mul]

lemma proportion_bound (j : ℕ) :
    (endpoint j : ℝ) / blockLength j ≤ (j : ℝ) / (2 : ℝ)^j := by
  have hb : (endpoint j : ℝ) ≤ (j : ℝ) * (2 : ℝ)^(2^j) := by
    exact_mod_cast endpoint_bound j
  have hp : (0 : ℝ) < (2 : ℝ)^(2^j) := by positivity
  have hl : (blockLength j : ℝ) = ((2 : ℝ)^(2^j))^2 := by
    exact_mod_cast length_square j
  have he : j ≤ 2^j := by
    exact Nat.le_of_lt (Nat.lt_two_pow_self)
  have he' : (2 : ℝ)^j ≤ (2 : ℝ)^(2^j) := pow_le_pow_right₀ (by norm_num) he
  calc
    _ ≤ ((j : ℝ) * (2 : ℝ)^(2^j)) / ((2 : ℝ)^(2^j))^2 := by
      rw [hl]; exact div_le_div_of_nonneg_right hb (by positivity)
    _ = (j : ℝ) / (2 : ℝ)^(2^j) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) he'

theorem earlier_proportion :
    Specs.D13Unified.Ch18.CocycleNoExponent.earlierProportionStatement := by
  apply squeeze_zero (fun j => by positivity) proportion_bound
  simpa using tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1 : ℝ) < 2)

lemma scalar_pos (s : OneSided) : 0 < scalar s := Real.exp_pos _

lemma scalar_bounds (s : OneSided) : 1 ≤ scalar s ∧ scalar s ≤ Real.exp 1 := by
  have hs : (s 0).val ≤ 1 := by have := (s 0).isLt; omega
  constructor
  · exact Real.one_le_exp (by positivity)
  · exact Real.exp_le_exp.mpr (by exact_mod_cast hs)

lemma scalar_continuous : Continuous scalar := by
  have h : Continuous (fun b : Binary => (b.val : ℝ)) := continuous_of_discreteTopology
  exact Real.continuous_exp.comp (h.comp (continuous_apply 0))

theorem regularity : Specs.D13Unified.Ch18.CocycleNoExponent.regularityStatement := by
  refine ⟨scalar_continuous, scalar_continuous.smul continuous_const, scalar_bounds, ?_, ?_, ?_⟩
  · intro s
    change Function.Bijective (fun v : ℝ => scalar s * v)
    exact (Equiv.mulLeft₀ (scalar s) (scalar_pos s).ne').bijective
  · refine ⟨Real.exp 1, fun s => ?_⟩
    simpa [generator, Specs.D13Unified.Ch18.CocycleNoExponent.generator, norm_smul,
      Real.norm_eq_abs, abs_of_pos (scalar_pos s)] using (scalar_bounds s).2
  · refine ⟨1, fun s => ?_⟩
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos (scalar_pos s)]
      using (inv_le_one₀ (scalar_pos s)).mpr (scalar_bounds s).1

lemma shift_iterate (s : OneSided) (n k : ℕ) : (shiftPlus^[n] s) k = s (k+n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (shiftPlus^[n] s) (k+1) = _
    rw [ih]
    congr 1
    omega

lemma log_average_eq (s : OneSided) (n : ℕ) :
    logAverage s n = (∑ k ∈ range n, ((s k).val : ℝ)) / n := by
  unfold logAverage Specs.D13Unified.Ch18.CocycleNoExponent.logAverage
  congr 1
  simp only [Specs.D13Unified.Ch18.CocycleNoExponent.scalar, shift_iterate, zero_add]
  rw [← Real.exp_sum, Real.log_exp]

theorem product_formula : Specs.D13Unified.Ch18.CocycleNoExponent.productFormulaStatement := by
  intro s n v
  induction n with
  | zero => simp [Specs.D13Unified.Ch18.GrowthDefinitions.cocycleProduct]
  | succ n ih =>
    rw [cocycleProduct_succ]
    change scalar (shiftPlus^[n] s) * cocycleProduct shiftPlus generator n s v = _
    rw [ih, sum_range_succ, Real.exp_add]
    simp only [scalar, Specs.D13Unified.Ch18.CocycleNoExponent.scalar, shift_iterate, zero_add]
    ring

theorem rate_formula : Specs.D13Unified.Ch18.CocycleNoExponent.rateFormulaStatement := by
  intro s v hv n hn
  have he : ‖cocycleProduct shiftPlus generator n s v‖ / ‖v‖ =
      Real.exp (∑ k ∈ range n, ((s k).val : ℝ)) := by
    rw [product_formula, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hv)
  change (if ‖cocycleProduct shiftPlus generator n s v‖ / ‖v‖ = 0 then ⊥ else
    ((Real.log (‖cocycleProduct shiftPlus generator n s v‖ / ‖v‖) / n : ℝ) : EReal)) = _
  rw [he, ite_eq_right (Real.exp_ne_zero _), Real.log_exp]
  exact congrArg (fun r : ℝ => (r : EReal)) (log_average_eq s n).symm

/-- The sum of the first `n` symbols, interpreted in ℝ. -/
def digitSum (s : OneSided) (n : ℕ) : ℝ := ∑ k ∈ range n, ((s k).val : ℝ)

lemma digitSum_bounds (s : OneSided) (n : ℕ) : 0 ≤ digitSum s n ∧ digitSum s n ≤ n := by
  constructor
  · exact sum_nonneg (fun _ _ => by positivity)
  · calc
      _ ≤ ∑ _k ∈ range n, (1 : ℝ) := by
        apply sum_le_sum
        intro k hk
        have := (s k).isLt
        exact_mod_cast (show (s k).val ≤ 1 by omega)
      _ = _ := by simp

lemma digitSum_endpoint (j : ℕ) :
    digitSum basePoint (endpoint (j+1)) =
      digitSum basePoint (endpoint j) + (blockLength j : ℝ) * (j%2 : ℕ) := by
  rw [endpoint_succ, digitSum, sum_range_add]
  congr 1
  calc
    _ = ∑ _k ∈ range (blockLength j), ((j%2 : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro k hk
      congr 1
      apply blocks j (endpoint j + k)
      · change endpoint j ≤ endpoint j + k; omega
      change endpoint j + k < endpoint (j+1)
      rw [endpoint_succ]
      have := mem_range.mp hk
      omega
    _ = _ := by simp

lemma endpoint_error (j : ℕ) :
    |logAverage basePoint (endpoint (j+1)) - (j%2 : ℕ)| ≤
      (endpoint j : ℝ) / blockLength j := by
  have hb : (0 : ℝ) < blockLength j := by exact_mod_cast length_pos j
  have hs : (0 : ℝ) < endpoint (j+1) := by exact_mod_cast endpoint_pos j
  have hsum : (endpoint (j+1) : ℝ) = (endpoint j : ℝ) + blockLength j := by
    exact_mod_cast endpoint_succ j
  have hc0 : (0 : ℝ) ≤ (j%2 : ℕ) := by positivity
  have hc1 : ((j%2 : ℕ) : ℝ) ≤ 1 := by
    have : j%2 ≤ 1 := by omega
    exact_mod_cast this
  have hn := digitSum_bounds basePoint (endpoint j)
  have hnum : |digitSum basePoint (endpoint j) - ((j%2 : ℕ) : ℝ) * endpoint j| ≤
      (endpoint j : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith [show (0 : ℝ) ≤ endpoint j by positivity]
  have hid : logAverage basePoint (endpoint (j+1)) - (j%2 : ℕ) =
      (digitSum basePoint (endpoint j) - ((j%2 : ℕ) : ℝ) * endpoint j) /
        endpoint (j+1) := by
    rw [log_average_eq]
    change digitSum basePoint (endpoint (j+1)) / _ - _ = _
    rw [digitSum_endpoint]
    field_simp
    nlinarith
  rw [hid, abs_div, abs_of_pos hs]
  exact (div_le_div_of_nonneg_right hnum hs.le).trans
    (div_le_div_of_nonneg_left (by positivity) hb (by linarith))

lemma endpoint_error_tendsto :
    Tendsto (fun j => logAverage basePoint (endpoint (j+1)) - (j%2 : ℕ)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun j => ?_) earlier_proportion
  simpa only [Real.norm_eq_abs] using endpoint_error j

lemma even_atTop : Tendsto (fun j : ℕ => 2*j) atTop atTop :=
  tendsto_atTop_mono (fun j => by dsimp; omega) tendsto_id

lemma odd_atTop : Tendsto (fun j : ℕ => 2*j+1) atTop atTop :=
  tendsto_atTop_mono (fun j => by dsimp; omega) tendsto_id

lemma endpoint_atTop : Tendsto endpoint atTop atTop :=
  tendsto_atTop_mono endpoint_ge tendsto_id

lemma zero_subsequence :
    Tendsto (fun j => logAverage basePoint (endpoint (2*j+1))) atTop (𝓝 0) := by
  simpa [Function.comp_def, Nat.mul_mod] using endpoint_error_tendsto.comp even_atTop

lemma one_subsequence :
    Tendsto (fun j => logAverage basePoint (endpoint (2*j+2))) atTop (𝓝 1) := by
  have h : Tendsto (fun j => logAverage basePoint (endpoint (2*j+2)) - 1) atTop (𝓝 0) := by
    simpa [Function.comp_def, Nat.add_mod, Nat.mul_mod, Nat.add_assoc] using endpoint_error_tendsto.comp odd_atTop
  simpa using h.add_const 1

theorem subsequences : Specs.D13Unified.Ch18.CocycleNoExponent.subsequencesStatement := by
  refine ⟨endpoint_atTop.comp odd_atTop, ?_, zero_subsequence, one_subsequence⟩
  exact endpoint_atTop.comp (tendsto_atTop_mono (fun j => by dsimp; omega) tendsto_id)

lemma shifted_even_atTop : Tendsto (fun j => endpoint (2*j+1)-1) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro j
  change j ≤ endpoint (2*j+1)-1
  have := endpoint_ge (2*j+1)
  omega

lemma shifted_odd_atTop : Tendsto (fun j => endpoint (2*j+2)-1) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro j
  change j ≤ endpoint (2*j+2)-1
  have := endpoint_ge (2*j+2)
  omega

theorem no_exponent : Specs.D13Unified.Ch18.CocycleNoExponent.noExponentStatement := by
  intro v hv
  have hn : ¬ ∃ a : EReal, HasCocycleDirectionalExponent shiftPlus generator basePoint v hv a := by
    rintro ⟨a, ha⟩
    have h0 : Tendsto (fun j => (logAverage basePoint (endpoint (2*j+1)) : EReal))
        atTop (𝓝 a) := by
      have h := ha.comp shifted_even_atTop
      convert h using 1
      funext j
      have hp := endpoint_pos (2*j)
      have he : endpoint (2*j+1)-1+1 = endpoint (2*j+1) := by omega
      simp only [HasCocycleDirectionalExponent,
        Specs.D13Unified.Ch18.GrowthDefinitions.HasCocycleDirectionalExponent] at *
      dsimp only [Function.comp_def]
      rw [rate_formula]
      simp only [he]
    have h1 : Tendsto (fun j => (logAverage basePoint (endpoint (2*j+2)) : EReal))
        atTop (𝓝 a) := by
      have h := ha.comp shifted_odd_atTop
      convert h using 1
      funext j
      have hp : 0 < endpoint (2*j+2) := by simpa [Nat.add_assoc] using endpoint_pos (2*j+1)
      have he : endpoint (2*j+2)-1+1 = endpoint (2*j+2) := by omega
      simp only [HasCocycleDirectionalExponent,
        Specs.D13Unified.Ch18.GrowthDefinitions.HasCocycleDirectionalExponent] at *
      dsimp only [Function.comp_def]
      rw [rate_formula]
      simp only [he]
    have he0 : a = (0 : EReal) := tendsto_nhds_unique h0
      (by simpa using EReal.tendsto_coe.mpr zero_subsequence)
    have he1 : a = (1 : EReal) := tendsto_nhds_unique h1
      (by simpa using EReal.tendsto_coe.mpr one_subsequence)
    exact zero_ne_one (he0.symm.trans he1)
  refine ⟨hn, ?_⟩
  exact (partialLimit_none_iff _ _).mpr hn

end D13Unified.Ch18.CocycleNoExponent
