import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.MZDeterministicMeans
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
noncomputable section

namespace ProbabilityFoundations.Ch08
namespace MZ

/-- Lower and upper cutoff sums, evaluated at one fixed sample value. -/
def lowerSum (p : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, if |x| ≤ weight p (k + 1) then x else 0

def upperCount (p : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, if weight p (k + 1) < |x| then 1 else 0

lemma weight_pos {p : ℝ} (n : ℕ) (hn : n ≠ 0) : 0 < weight p n :=
  Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _

lemma weight_pow {p : ℝ} (hp : 0 < p) (n : ℕ) : (weight p n) ^ p = n := by
  simp only [weight, Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.weight,
    one_div]
  exact Real.rpow_inv_rpow (Nat.cast_nonneg n) (ne_of_gt hp)

lemma weight_mono {p : ℝ} (hp : 0 < p) : Monotone (weight p) := by
  intro i j hij
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hij) (by positivity)

lemma weight_tendsto {p : ℝ} (hp : 0 < p) : Tendsto (weight p) atTop atTop :=
  (tendsto_rpow_atTop (by positivity : 0 < 1 / p)).comp tendsto_natCast_atTop_atTop

lemma small_power_bound {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hab : a ≤ b) (hp : 0 < p) (hp1 : p ≤ 1) : b ^ p * a / b ≤ a ^ p := by
  have hh : a / b ≤ (a / b) ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_ge' (div_nonneg ha hb.le)
      ((div_le_one hb).mpr hab) hp.le hp1
  have hh' := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hb.le p)
  rw [Real.div_rpow ha hb.le] at hh'
  have hb' : b ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb p)
  field_simp [ne_of_gt hb, hb'] at hh' ⊢
  nlinarith

lemma large_power_bound {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hab : b ≤ a) (hp : 1 ≤ p) : b ^ p * a / b ≤ a ^ p := by
  have hh : a / b ≤ (a / b) ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le ((one_le_div hb).mpr hab) hp
  have hh' := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hb.le p)
  rw [Real.div_rpow ha hb.le] at hh'
  have hb' : b ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hb p)
  field_simp [ne_of_gt hb, hb'] at hh' ⊢
  nlinarith

lemma abs_lowerSum_le (p : ℝ) (n : ℕ) (x : ℝ) :
    |lowerSum p n x| ≤ (n : ℝ) * |x| := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, |if |x| ≤ weight p (k + 1) then x else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, |x| := by
      apply Finset.sum_le_sum
      intro k hk
      split_ifs <;> simp [abs_nonneg]
    _ = _ := by simp

lemma lowerSum_eq_zero {p : ℝ} (hp : 0 < p) (n : ℕ) (x : ℝ)
    (hx : weight p n < |x|) : lowerSum p n x = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  have hw := weight_mono hp (show k + 1 ≤ n by simpa using Finset.mem_range.mp hk)
  exact ite_eq_right (not_le.mpr (hw.trans_lt hx))

lemma lowerSum_bound {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (n : ℕ) (x : ℝ) :
    |lowerSum p n x / weight p n| ≤ |x| ^ p := by
  by_cases hn : n = 0
  · simp [hn, lowerSum, Real.rpow_nonneg]
  have hw := weight_pos (p := p) n hn
  rw [abs_div, abs_of_pos hw]
  by_cases hx : |x| ≤ weight p n
  · calc
      _ ≤ (n : ℝ) * |x| / weight p n :=
        div_le_div_of_nonneg_right (abs_lowerSum_le p n x) hw.le
      _ ≤ |x| ^ p := by
        rw [← weight_pow hp n]
        exact small_power_bound (abs_nonneg x) hw hx hp hp1.le
  · rw [lowerSum_eq_zero hp n x (lt_of_not_ge hx)]
    simpa using Real.rpow_nonneg (abs_nonneg x) p

lemma lowerSum_tendsto {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (x : ℝ) :
    Tendsto (fun n => lowerSum p n x / weight p n) atTop (𝓝 0) := by
  have he : 0 < 1 / p - 1 := by
    have : 1 < 1 / p := (lt_div_iff₀ hp).mpr (by simpa using hp1)
    linarith
  have ht : Tendsto (fun n : ℕ => |x| * (n : ℝ) ^ (1 - 1 / p)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero, Function.comp_apply] using
      (tendsto_const_nhds (x := |x|)).mul ((tendsto_rpow_neg_atTop he).comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  apply squeeze_zero_norm' _ ht
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (weight_pos n (by omega))]
  calc
    _ ≤ (n : ℝ) * |x| / weight p n :=
      div_le_div_of_nonneg_right (abs_lowerSum_le p n x)
        (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / p))
    _ = _ := by
      rw [weight, Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.weight,
        Real.rpow_sub hn0, Real.rpow_one]
      ring

lemma upperCount_nonneg (p : ℝ) (n : ℕ) (x : ℝ) : 0 ≤ upperCount p n x := by
  apply Finset.sum_nonneg
  intros
  split_ifs <;> norm_num

lemma upperCount_le_nat (p : ℝ) (n : ℕ) (x : ℝ) : upperCount p n x ≤ n := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intros
      split_ifs <;> norm_num
    _ = _ := by simp

lemma upperCount_le_power {p : ℝ} (hp : 0 < p) (n : ℕ) (x : ℝ) :
    upperCount p n x ≤ |x| ^ p := by
  induction n with
  | zero => simpa [upperCount] using Real.rpow_nonneg (abs_nonneg x) p
  | succ n ih =>
    change (∑ k ∈ Finset.range (n + 1), if weight p (k + 1) < |x| then (1 : ℝ) else 0) ≤ _
    rw [Finset.sum_range_succ]
    by_cases hx : weight p (n + 1) < |x|
    · rw [ite_eq_left hx]
      have hlt : ((n + 1 : ℕ) : ℝ) < |x| ^ p := by
        apply (Real.rpow_inv_lt_iff_of_pos (Nat.cast_nonneg _) (abs_nonneg _) hp).mp
        simpa only [weight, Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.weight,
          one_div] using hx
      have hh := upperCount_le_nat p n x
      change upperCount p n x + 1 ≤ _
      push_cast at hlt
      linarith
    · simpa only [upperCount, ite_eq_right hx, add_zero] using ih

lemma upperCount_bound {p : ℝ} (hp : 1 < p) (n : ℕ) (x : ℝ) :
    |upperCount p n x * x / weight p n| ≤ |x| ^ p := by
  by_cases hn : n = 0
  · simp [hn, upperCount, Real.rpow_nonneg]
  have hw := weight_pos (p := p) n hn
  rw [abs_div, abs_mul, abs_of_nonneg (upperCount_nonneg p n x), abs_of_pos hw]
  by_cases hx : |x| ≤ weight p n
  · calc
      _ ≤ |x| ^ p * |x| / weight p n := by
        gcongr
        exact upperCount_le_power (by linarith) n x
      _ ≤ |x| ^ p := by
        apply (div_le_iff₀ hw).mpr
        exact mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg (abs_nonneg _) _)
  · calc
      _ ≤ (n : ℝ) * |x| / weight p n := by
        gcongr
        exact upperCount_le_nat p n x
      _ ≤ |x| ^ p := by
        rw [← weight_pow (by linarith : 0 < p) n]
        exact large_power_bound (abs_nonneg x) hw (le_of_not_ge hx) hp.le

lemma upperCount_tendsto {p : ℝ} (hp : 0 < p) (x : ℝ) :
    Tendsto (fun n => upperCount p n x * x / weight p n) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => (|x| ^ p * |x|) / weight p n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (weight_tendsto hp)
  apply squeeze_zero_norm' _ ht
  apply Eventually.of_forall
  intro n
  rw [Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_nonneg (upperCount_nonneg p n x),
    abs_of_nonneg (show 0 ≤ weight p n from Real.rpow_nonneg (Nat.cast_nonneg n) (1 / p))]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (upperCount_le_power hp n x) (abs_nonneg x))
    (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / p))

lemma lowerSum_eq_truncated {Ω : Type*} (p : ℝ) (Y : Ω → ℝ) (n : ℕ) (ω : Ω) :
    lowerSum p n (Y ω) = ∑ k ∈ Finset.range n, truncated p (fun _ => Y) k ω := by
  simp only [lowerSum, truncated,
    Specs.ProbabilityFoundations.Ch08.MarcinkiewiczZygmundTruncation.truncated,
    Set.indicator_apply, Set.mem_ofPred_eq]

lemma upperCount_mul_eq {Ω : Type*} (p : ℝ) (Y : Ω → ℝ) (n : ℕ) (ω : Ω) :
    upperCount p n (Y ω) * Y ω =
      (n : ℝ) * Y ω - lowerSum p n (Y ω) := by
  rw [upperCount, Finset.sum_mul]
  have heq : (n : ℝ) * Y ω = ∑ k ∈ Finset.range n, Y ω := by simp
  rw [heq, lowerSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hx : |Y ω| ≤ weight p (k + 1)
  · simp [hx, not_lt.mpr hx]
  · simp [hx, lt_of_not_ge hx]

end MZ

universe u

/-- The subunit deterministic mean correction with the original moment hypothesis. -/
theorem mz_deterministic_means_subunit :
    Specs.ProbabilityFoundations.Ch08.MZDeterministicMeans.subunitType := by
  intro Ω mΩ P hP X p hX hd hp hp1 hmom
  let T : ℕ → Ω → ℝ := MZ.truncated p (fun _ => X 0)
  have hT (k : ℕ) : Integrable (T k) P :=
    (MZ.truncated_memLp P p _ k (hX 0)).integrable (by norm_num)
  have hsum (n : ℕ) : Integrable (fun ω => MZ.lowerSum p n (X 0 ω)) P := by
    simp_rw [MZ.lowerSum_eq_truncated]
    exact integrable_finsetSum _ (fun k hk => hT k)
  have ht := tendsto_integral_of_dominated_convergence
    (F := fun n ω => MZ.lowerSum p n (X 0 ω) / MZ.weight p n)
    (f := fun _ => (0 : ℝ)) (fun ω => |X 0 ω| ^ p)
    (fun n => ((hsum n).div_const _).aestronglyMeasurable) hmom
    (fun n => Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using MZ.lowerSum_bound hp hp1 n (X 0 ω))
    (Eventually.of_forall fun ω => MZ.lowerSum_tendsto hp hp1 (X 0 ω))
  simp only [integral_zero] at ht
  convert ht using 1
  funext n
  rw [integral_div]
  congr 1
  rw [show (fun ω => MZ.lowerSum p n (X 0 ω)) =
      (fun ω => ∑ k ∈ Finset.range n, T k ω) by
    funext ω; exact MZ.lowerSum_eq_truncated p (X 0) n ω]
  rw [integral_finsetSum _ (fun k hk => hT k)]
  apply Finset.sum_congr rfl
  intro k hk
  exact (MZ.truncated_identDistrib P p X k (hd k)).integral_eq

/-- Above exponent one the deterministic correction is centered by the true mean. -/
theorem mz_deterministic_means_centered :
    Specs.ProbabilityFoundations.Ch08.MZDeterministicMeans.centeredType := by
  intro Ω mΩ P hP X p hX hd hp hp2 hmom
  have hp0 : 0 < p := by linarith
  have hfirst : Integrable (X 0) P := by
    apply ((integrable_const (1 : ℝ)).add hmom).mono' (hX 0).aestronglyMeasurable
    filter_upwards [] with ω
    change |X 0 ω| ≤ 1 + |X 0 ω| ^ p
    by_cases hh : |X 0 ω| ≤ 1
    · exact hh.trans (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _))
    · have hh' : |X 0 ω| ≤ |X 0 ω| ^ p := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hh) hp.le
      linarith
  let T : ℕ → Ω → ℝ := MZ.truncated p (fun _ => X 0)
  have hT (k : ℕ) : Integrable (T k) P :=
    (MZ.truncated_memLp P p _ k (hX 0)).integrable (by norm_num)
  have hsum (n : ℕ) : Integrable (fun ω => MZ.lowerSum p n (X 0 ω)) P := by
    simp_rw [MZ.lowerSum_eq_truncated]
    exact integrable_finsetSum _ (fun k hk => hT k)
  have htail (n : ℕ) : Integrable (fun ω => MZ.upperCount p n (X 0 ω) * X 0 ω) P := by
    simp_rw [MZ.upperCount_mul_eq]
    exact (hfirst.const_mul _).sub (hsum n)
  have ht := tendsto_integral_of_dominated_convergence
    (F := fun n ω => MZ.upperCount p n (X 0 ω) * X 0 ω / MZ.weight p n)
    (f := fun _ => (0 : ℝ)) (fun ω => |X 0 ω| ^ p)
    (fun n => ((htail n).div_const _).aestronglyMeasurable) hmom
    (fun n => Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using MZ.upperCount_bound hp n (X 0 ω))
    (Eventually.of_forall fun ω => MZ.upperCount_tendsto hp0 (X 0 ω))
  have hneg := ht.neg
  simp only [integral_zero, neg_zero] at hneg
  convert hneg using 1
  funext n
  rw [integral_div]
  simp_rw [MZ.upperCount_mul_eq]
  rw [integral_sub (hfirst.const_mul _) (hsum n), integral_const_mul]
  rw [show (fun ω => MZ.lowerSum p n (X 0 ω)) =
      (fun ω => ∑ k ∈ Finset.range n, T k ω) by
    funext ω; exact MZ.lowerSum_eq_truncated p (X 0) n ω]
  rw [integral_finsetSum _ (fun k hk => hT k)]
  have heq : (∑ k ∈ Finset.range n, ∫ ω, MZ.truncated p X k ω ∂P) =
      ∑ k ∈ Finset.range n, ∫ ω, T k ω ∂P := by
    apply Finset.sum_congr rfl
    intro k hk
    exact (MZ.truncated_identDistrib P p X k (hd k)).integral_eq
  rw [heq]
  ring

end ProbabilityFoundations.Ch08
