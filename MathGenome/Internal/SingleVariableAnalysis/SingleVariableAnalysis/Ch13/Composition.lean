import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Recentering
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic

set_option maxHeartbeats 800000

/-!
Local scalar composition (K03.13.composition, paper.tex:1432–1446).
Finite formal power-series algebra supplies the coefficient identities. Absolute
Cauchy products and an explicitly summable double majorant justify evaluation.
No analyticity theorem or unproved convergence certificate is assumed.
-/
noncomputable section
open scoped BigOperators ENNReal Topology
namespace SingleVariableAnalysis
namespace Composition

/-- The positive-degree part of the inner coefficient sequence. -/
def positivePart {K : Type*} [Zero K] (b : ℕ → K) (j : ℕ) : K :=
  if j = 0 then 0 else b j

/-- Coefficient of the m-th power of the inner series with zero constant term. -/
def powerCoefficient {K : Type*} [CommSemiring K] (b : ℕ → K) (m k : ℕ) : K :=
  PowerSeries.coeff k ((PowerSeries.mk (positivePart b)) ^ m)

/-- The finite coefficient of the composed series. -/
def coefficient {K : Type*} [CommSemiring K] (A b : ℕ → K) (k : ℕ) : K :=
  ∑ m ∈ Finset.range (k+1), A m * powerCoefficient b m k

@[simp] theorem positivePart_zero {K : Type*} [Zero K] (b : ℕ → K) :
    positivePart b 0 = 0 := by simp [positivePart]

@[simp] theorem positivePart_pos {K : Type*} [Zero K] (b : ℕ → K) {j : ℕ}
    (hj : j ≠ 0) : positivePart b j = b j := by simp [positivePart, hj]

@[simp] theorem powerCoefficient_zero {K : Type*} [CommSemiring K] (b : ℕ → K) (k : ℕ) :
    powerCoefficient b 0 k = if k = 0 then 1 else 0 := by
  simp [powerCoefficient, PowerSeries.coeff_one]

theorem powerCoefficient_succ {K : Type*} [CommSemiring K] (b : ℕ → K) (m k : ℕ) :
    powerCoefficient b (m+1) k =
      ∑ j ∈ Finset.range (k+1), powerCoefficient b m j * positivePart b (k-j) := by
  simp only [powerCoefficient, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mk]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i ((PowerSeries.mk (positivePart b)) ^ m) *
      positivePart b j) k

/-- This is precisely the ordered multi-index sum in the source, including m=0. -/
theorem powerCoefficient_formula {K : Type*} [CommSemiring K] (b : ℕ → K) (m k : ℕ) :
    powerCoefficient b m k =
      ∑ l ∈ (Finset.finsuppAntidiag (Finset.range m) k).filter
        (fun l => ∀ i ∈ Finset.range m, 0 < l i), ∏ i ∈ Finset.range m, b (l i) := by
  classical
  rw [powerCoefficient, PowerSeries.coeff_pow, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [PowerSeries.coeff_mk]
  split_ifs with hp
  · apply Finset.prod_congr rfl
    intro i hi
    exact positivePart_pos b (Nat.ne_of_gt (hp i hi))
  · push Not at hp
    obtain ⟨i, hi, hz⟩ := hp
    apply Finset.prod_eq_zero hi
    simp [positivePart, Nat.eq_zero_of_le_zero hz]

theorem powerCoefficient_below {K : Type*} [CommSemiring K] (b : ℕ → K)
    (m k : ℕ) (hk : k < m) : powerCoefficient b m k = 0 := by
  induction m generalizing k with
  | zero => omega
  | succ m ih =>
    rw [powerCoefficient_succ]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk := Finset.mem_range.mp hj
    by_cases hjm : j < m
    · rw [ih j hjm, zero_mul]
    · have hz : k-j = 0 := by omega
      simp [hz]

theorem powerCoefficient_scale {K : Type*} [CommSemiring K] (b : ℕ → K)
    (h : K) (m k : ℕ) :
    powerCoefficient (fun j => b j * h^j) m k = powerCoefficient b m k * h^k := by
  have he : PowerSeries.mk (positivePart (fun j => b j * h^j)) =
      PowerSeries.rescale h (PowerSeries.mk (positivePart b)) := by
    ext j
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_rescale]
    by_cases hj : j = 0 <;> simp [positivePart, hj, mul_comm]
  simp only [powerCoefficient, he, ← map_pow, PowerSeries.coeff_rescale]
  ring

theorem positivePart_norm {K : Type*} [SeminormedAddCommGroup K] (b : ℕ → K) (j : ℕ) :
    ‖positivePart b j‖ = positivePart (fun j => ‖b j‖) j := by
  by_cases hj : j = 0 <;> simp [positivePart, hj]

theorem powerCoefficient_norm {K : Type*} [RCLike K] (b : ℕ → K) (m k : ℕ) :
    ‖powerCoefficient b m k‖ ≤ powerCoefficient (fun j => ‖b j‖) m k := by
  classical
  simp only [powerCoefficient, PowerSeries.coeff_pow, PowerSeries.coeff_mk]
  calc
    _ ≤ ∑ l ∈ Finset.finsuppAntidiag (Finset.range m) k,
        ‖∏ i ∈ Finset.range m, positivePart b (l i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_prod, positivePart_norm]

theorem powerCoefficient_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (m k : ℕ) :
    0 ≤ powerCoefficient b m k := by
  classical
  rw [powerCoefficient, PowerSeries.coeff_pow]
  apply Finset.sum_nonneg
  intro l hl
  apply Finset.prod_nonneg
  intro i hi
  simp only [PowerSeries.coeff_mk, positivePart]
  split_ifs <;> simp_all

/-- Absolute Cauchy products justify each finite power. -/
theorem power_sums {K : Type*} [RCLike K] (b : ℕ → K)
    (hb : Summable (fun j => ‖positivePart b j‖)) (m : ℕ) :
    Summable (fun k => ‖powerCoefficient b m k‖) ∧
      HasSum (powerCoefficient b m) ((∑' j, positivePart b j)^m) := by
  induction m with
  | zero =>
    have he : powerCoefficient b 0 = (fun k => if k = 0 then 1 else 0) :=
      funext (powerCoefficient_zero b)
    rw [he, pow_zero]
    refine ⟨?_, hasSum_ite_eq (0 : ℕ) (1 : K)⟩
    simpa only [apply_ite norm, norm_one, norm_zero] using
      (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable
  | succ m ih =>
    simp_rw [powerCoefficient_succ]
    refine ⟨summable_norm_sum_mul_range_of_summable_norm ih.1 hb, ?_⟩
    have he := hasSum_sum_range_mul_of_summable_norm ih.1 hb
    rw [ih.2.tsum_eq] at he
    simpa only [← powerCoefficient_succ, pow_succ] using he

/-- The positive-degree majorant at radius r. -/
def majorant {K : Type*} [SeminormedAddCommGroup K] (b : ℕ → K) (r : ℝ) : ℝ :=
  ∑' j, ‖positivePart b j‖ * r^j

@[simp] theorem positivePart_scale {K : Type*} [Semiring K] (b : ℕ → K) (h : K) (j : ℕ) :
    positivePart (fun j => b j * h^j) j = positivePart b j * h^j := by
  by_cases hj : j = 0 <;> simp [positivePart, hj]

theorem power_monomial_sums {K : Type*} [RCLike K] (b : ℕ → K) (h : K)
    (hb : Summable (fun j => ‖positivePart b j * h^j‖)) (m : ℕ) :
    Summable (fun k => ‖powerCoefficient b m k * h^k‖) ∧
      HasSum (fun k => powerCoefficient b m k * h^k)
        ((∑' j, positivePart b j * h^j)^m) := by
  have he : powerCoefficient (fun j => b j * h^j) m =
      (fun k => powerCoefficient b m k * h^k) := funext (powerCoefficient_scale b h m)
  simpa only [positivePart_scale, he] using
    power_sums (fun j => b j * h^j) (by simpa only [positivePart_scale] using hb) m

theorem majorant_summable {K : Type*} [RCLike K] (b : ℕ → K) {s r : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) (hb : Summable (fun j => ‖b j‖ * s^j)) :
    Summable (fun j => ‖positivePart b j‖ * r^j) := by
  apply hb.of_nonneg_of_le (fun j => by positivity)
  intro j
  by_cases hj : j = 0
  · simp [hj]
  · simp only [positivePart_pos b hj]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs j) (norm_nonneg _)

theorem majorant_nonneg {K : Type*} [SeminormedAddCommGroup K] (b : ℕ → K)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ majorant b r :=
  tsum_nonneg (fun j => mul_nonneg (norm_nonneg _) (pow_nonneg hr _))

/-- Vanishing of the constant term gives the source's linear small-radius estimate. -/
theorem majorant_le {K : Type*} [RCLike K] (b : ℕ → K) {s r : ℝ}
    (hs : 0 < s) (hr : 0 ≤ r) (hrs : r ≤ s)
    (hb : Summable (fun j => ‖b j‖ * s^j)) :
    majorant b r ≤ (r/s) * majorant b s := by
  have hbs := majorant_summable b hs.le le_rfl hb
  have hbr := majorant_summable b hr hrs hb
  unfold majorant
  rw [← hbs.tsum_mul_left]
  apply hbr.tsum_le_tsum _ (hbs.mul_left _)
  intro j
  cases j with
  | zero => simp
  | succ n =>
    have he : (r/s) * s^(n+1) = r * s^n := by
      rw [pow_succ]
      field_simp
    calc
      ‖positivePart b (n+1)‖ * r^(n+1) ≤
          ‖positivePart b (n+1)‖ * (r * s^n) := by
        gcongr
        rw [pow_succ, mul_comm]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs n) hr
      _ = ‖positivePart b (n+1)‖ * ((r/s) * s^(n+1)) := by rw [he]
      _ = (r/s) * (‖positivePart b (n+1)‖ * s^(n+1)) := by ring

theorem exists_small_majorant {K : Type*} [RCLike K] (b : ℕ → K) {s ε : ℝ}
    (hs : 0 < s) (hε : 0 < ε) (hb : Summable (fun j => ‖b j‖ * s^j)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ s ∧ majorant b r < ε := by
  have hM := majorant_nonneg b hs.le
  obtain ⟨r, hr, hrs⟩ := exists_between (lt_min hs
    (div_pos (mul_pos hε hs) (by linarith : 0 < majorant b s + 1)))
  have hrr := (lt_min_iff.mp hrs).1.le
  refine ⟨r, hr, hrr, (majorant_le b hs hr.le hrr hb).trans_lt ?_⟩
  have hh : r * (majorant b s + 1) < ε*s :=
    (lt_div_iff₀ (by linarith : 0 < majorant b s + 1)).mp (lt_min_iff.mp hrs).2
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hs).mpr
  nlinarith

theorem positivePart_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    0 ≤ positivePart b j := by simp only [positivePart]; split_ifs <;> simp_all

/-- A row of the nonnegative majorant sums to U(r)^m. -/
theorem majorant_power_sums {K : Type*} [RCLike K] (b : ℕ → K) {r : ℝ}
    (hr : 0 ≤ r) (hb : Summable (fun j => ‖positivePart b j‖ * r^j)) (m : ℕ) :
    HasSum (fun k => powerCoefficient (fun j => ‖b j‖) m k * r^k)
      (majorant b r ^ m) := by
  have hp (j : ℕ) : 0 ≤ positivePart (fun j => ‖b j‖) j :=
    positivePart_nonneg _ (fun j => norm_nonneg _) j
  have hn : Summable (fun j => ‖positivePart (fun j => ‖b j‖) j * r^j‖) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hr,
      abs_of_nonneg (hp _), ← positivePart_norm, abs_norm] using hb
  simpa only [← positivePart_norm, majorant] using
    (power_monomial_sums (fun j => ‖b j‖) r hn m).2

/-- Summability of the nonnegative double majorant justifies every reordering. -/
theorem double_majorant {K : Type*} [RCLike K] (A b : ℕ → K) {r : ℝ}
    (hr : 0 ≤ r) (hb : Summable (fun j => ‖positivePart b j‖ * r^j))
    (hA : Summable (fun m => ‖A m‖ * majorant b r ^ m)) :
    Summable (fun p : ℕ × ℕ => ‖A p.1‖ *
      powerCoefficient (fun j => ‖b j‖) p.1 p.2 * r^p.2) ∧
    (∑' p : ℕ × ℕ, ‖A p.1‖ *
      powerCoefficient (fun j => ‖b j‖) p.1 p.2 * r^p.2) =
      ∑' m, ‖A m‖ * majorant b r ^ m := by
  have hrow (m : ℕ) := (majorant_power_sums b hr hb m).mul_left ‖A m‖
  have hn (p : ℕ × ℕ) : 0 ≤ ‖A p.1‖ *
      powerCoefficient (fun j => ‖b j‖) p.1 p.2 * r^p.2 := by
    exact mul_nonneg (mul_nonneg (norm_nonneg _)
      (powerCoefficient_nonneg _ (fun j => norm_nonneg _) _ _)) (pow_nonneg hr _)
  have hs : Summable (fun p : ℕ × ℕ => ‖A p.1‖ *
      powerCoefficient (fun j => ‖b j‖) p.1 p.2 * r^p.2) := by
    apply (summable_prod_of_nonneg hn).mpr
    constructor
    · intro m
      simpa only [mul_assoc] using (hrow m).summable
    · simpa only [mul_assoc, (hrow _).tsum_eq] using hA
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod]
  apply tsum_congr
  intro m
  simpa only [mul_assoc] using (hrow m).tsum_eq

/-- Evaluation with its absolute double bound; no rearrangement of a conditional series. -/
theorem evaluate {K : Type*} [RCLike K] (A b : ℕ → K) {r : ℝ}
    (hr : 0 ≤ r) (hb : Summable (fun j => ‖positivePart b j‖ * r^j))
    (hA : Summable (fun m => ‖A m‖ * majorant b r ^ m)) (h : K) (hh : ‖h‖ ≤ r) :
    Summable (fun k => ‖coefficient A b k * h^k‖) ∧
    HasSum (fun k => coefficient A b k * h^k)
      (∑' m, A m * (∑' j, positivePart b j * h^j)^m) := by
  have hd := (double_majorant A b hr hb hA).1
  have hn : Summable (fun p : ℕ × ℕ => ‖A p.1 * powerCoefficient b p.1 p.2 * h^p.2‖) := by
    apply hd.of_nonneg_of_le (fun p => norm_nonneg _)
    intro p
    simp only [norm_mul, norm_pow]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (powerCoefficient_norm b _ _) (norm_nonneg _))
      (pow_le_pow_left₀ (norm_nonneg h) hh _) (pow_nonneg (norm_nonneg h) _)
      (mul_nonneg (norm_nonneg _) (powerCoefficient_nonneg _ (fun j => norm_nonneg _) _ _))
  have hbh : Summable (fun j => ‖positivePart b j * h^j‖) := by
    apply hb.of_nonneg_of_le (fun j => norm_nonneg _)
    intro j
    simp only [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg h) hh _) (norm_nonneg _)
  have hc (k : ℕ) : (∑' m, A m * powerCoefficient b m k * h^k) = coefficient A b k * h^k := by
    rw [tsum_eq_sum (s := Finset.range (k+1))]
    · simp only [coefficient, Finset.sum_mul]
    · intro m hm
      simp [powerCoefficient_below b m k (by simpa using hm)]
  have hrow (m : ℕ) : (∑' k, A m * powerCoefficient b m k * h^k) =
      A m * (∑' j, positivePart b j * h^j)^m := by
    simpa only [mul_assoc] using ((power_monomial_sums b h hbh m).2.mul_left (A m)).tsum_eq
  have hs := hn.of_norm
  constructor
  · simpa only [hc, Prod.swap] using
      summable_norm_rows (fun k m => A m * powerCoefficient b m k * h^k) hn.prod_symm
  · have he := hs.prod_symm.prod.hasSum
    simp only [Prod.swap, hc] at he
    have heq : (∑' k, coefficient A b k * h^k) =
        ∑' m, A m * (∑' j, positivePart b j * h^j)^m := by
      calc
        _ = ∑' k, ∑' m, A m * powerCoefficient b m k * h^k :=
          tsum_congr (fun k => (hc k).symm)
        _ = ∑' m, ∑' k, A m * powerCoefficient b m k * h^k :=
          Summable.tsum_comm (f := fun m k => A m * powerCoefficient b m k * h^k) hs
        _ = _ := tsum_congr hrow
    rw [heq] at he
    exact he

/-- Splitting off the constant term identifies the original inner sum. -/
theorem inner_hasSum {K : Type*} [RCLike K] (b : ℕ → K) (h : K)
    (hb : Summable (fun j => ‖positivePart b j * h^j‖)) :
    HasSum (fun j => b j * h^j) (b 0 + ∑' j, positivePart b j * h^j) := by
  have he := (hasSum_ite_eq (0 : ℕ) (b 0)).add hb.of_norm.hasSum
  convert he using 1
  ext j
  by_cases hj : j = 0 <;> simp [positivePart, hj]

/-- Constructive local composition at an arbitrary scalar inner value.
The radii s,t are any absolutely convergent interior test radii. -/
theorem local_compose {K : Type*} [RCLike K] (a b : ℕ → K) (w : K)
    (s t : ℝ) (hs : 0 < s) (hw : ‖w‖ < t)
    (hb : Summable (fun j => ‖b j‖ * s^j))
    (ha : Summable (fun n => ‖a n‖ * t^n)) :
    let A := Recentering.coefficient a w
    ∃ r : ℝ, 0 < r ∧ r ≤ s ∧ ‖w‖ + majorant b r < t ∧
      Summable (fun m => ‖A m‖ * majorant b r ^ m) ∧
      Summable (fun k => ‖coefficient A b k‖ * r^k) ∧
      ∀ h : K, ‖h‖ ≤ r → ∃ v S : K,
        ‖v‖ ≤ majorant b r ∧ HasSum (fun j => b j * h^j) (b 0 + v) ∧
        HasSum (fun n => a n * (w+v)^n) S ∧
        HasSum (fun k => coefficient A b k * h^k) S ∧
        Summable (fun k => ‖coefficient A b k * h^k‖) := by
  dsimp only
  obtain ⟨r, hr, hrs, hU⟩ := exists_small_majorant b hs (sub_pos.mpr hw) hb
  have hUr := majorant_nonneg b hr.le
  have hwt : ‖w‖ + majorant b r < t := by linarith
  have hbr := majorant_summable b hr.le hrs hb
  have hsum : Summable (fun n => ‖a n‖ * (‖w‖+majorant b r)^n) := by
    apply ha.of_nonneg_of_le (fun n => by positivity)
    intro n
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hwt.le _) (norm_nonneg _)
  have hA : Summable (fun m => ‖Recentering.coefficient a w m‖ * majorant b r ^ m) := by
    obtain ⟨S, ho, hA, hn⟩ := Recentering.recenter a w (majorant b r : K) (by
      simpa only [RCLike.norm_ofReal, abs_of_nonneg hUr] using hsum)
    simpa only [norm_mul, norm_pow, RCLike.norm_ofReal, abs_of_nonneg hUr] using hn
  have hC : Summable (fun k => ‖coefficient (Recentering.coefficient a w) b k‖ * r^k) := by
    have ht := (evaluate (Recentering.coefficient a w) b hr.le hbr hA (r : K)
      (by simpa only [RCLike.norm_ofReal, abs_of_pos hr] using (le_refl r))).1
    simpa only [norm_mul, norm_pow, RCLike.norm_ofReal, abs_of_pos hr] using ht
  refine ⟨r, hr, hrs, hwt, hA, hC, ?_⟩
  intro h hh
  have hbh : Summable (fun j => ‖positivePart b j * h^j‖) := by
    apply hbr.of_nonneg_of_le (fun j => norm_nonneg _)
    intro j
    simp only [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh _) (norm_nonneg _)
  let v := ∑' j, positivePart b j * h^j
  have hv : ‖v‖ ≤ majorant b r := by
    apply (norm_tsum_le_tsum_norm hbh).trans
    apply hbh.tsum_le_tsum _ hbr
    intro j
    simp only [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh _) (norm_nonneg _)
  have hsumv : Summable (fun n => ‖a n‖ * (‖w‖+‖v‖)^n) := by
    apply hsum.of_nonneg_of_le (fun n => by positivity)
    intro n
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith) _) (norm_nonneg _)
  obtain ⟨S, ho, hrec, hn⟩ := Recentering.recenter a w v hsumv
  have he := evaluate (Recentering.coefficient a w) b hr.le hbr hA h hh
  refine ⟨v, S, hv, inner_hasSum b h hbh, ho, ?_, he.1⟩
  simpa only [v, hrec.tsum_eq] using he.2

/-- Absolute convergence at a positive distance bounds the canonical real radius below. -/
theorem real_radius_lower_bound (a : ℕ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (ha : Summable (fun n => ‖a n‖ * r^n)) :
    ENNReal.ofReal r ≤ realPowerSeriesRadius a := by
  apply le_of_not_gt
  intro h
  have hs : Summable (fun n => ‖a n * r^n‖) := by
    simpa only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hr] using ha
  apply real_powerSeries_radius_diverges a 0 r (by simpa [abs_of_nonneg hr] using h)
  have ho := real_series_hasSum_of_hasSum hs.of_norm.hasSum
  refine ⟨∑' n, a n * r^n, ?_⟩
  change RealSeriesHasSum (fun n => a n * (r-0)^n) _
  simpa only [sub_zero] using ho

/-- The complex radius has the same absolute-convergence lower bound. -/
theorem complex_radius_lower_bound (a : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : Summable (fun n => ‖a n‖ * r^n)) :
    ENNReal.ofReal r ≤ complexPowerSeriesRadius a := by
  apply le_of_not_gt
  intro h
  have hs : Summable (fun n => ‖a n * (r : ℂ)^n‖) := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] using ha
  apply complex_powerSeries_radius_diverges a 0 (r : ℂ) (by
    simpa only [Complex.ofReal_zero, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] using h)
  have ho := complex_series_hasSum_of_hasSum hs.of_norm.hasSum
  refine ⟨∑' n, a n * (r : ℂ)^n, ?_⟩
  change ComplexSeriesHasSum (fun n => a n * ((r : ℂ)-(0 : ℝ))^n) _
  simpa only [Complex.ofReal_zero, sub_zero] using ho

/-- Real composition in the original ordered-partial-sum interface. The coefficient
formula and the convergent double majorant are given by `powerCoefficient_formula`
and `double_majorant`. The input value is the inner constant coefficient. -/
theorem real_composition (a b : ℕ → ℝ) (c d : ℝ)
    (hb : 0 < realPowerSeriesRadius b)
    (ha : ENNReal.ofReal |b 0-d| < realPowerSeriesRadius a) :
    let A := realRecenteredCoefficient a d (b 0)
    let C := coefficient A b
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < realPowerSeriesRadius b ∧
      ENNReal.ofReal r ≤ realPowerSeriesRadius C ∧
      Summable (fun m => |A m| * majorant b r ^ m) ∧
      Summable (fun k => |C k| * r^k) ∧
      ∀ h : ℝ, |h| ≤ r → ∃ G S : ℝ,
        ENNReal.ofReal |G-d| < realPowerSeriesRadius a ∧ RealPowerSeriesHasSum b c (c+h) G ∧
        RealPowerSeriesHasSum a d G S ∧
        RealPowerSeriesHasSum C c (c+h) S ∧
        RealPowerSeriesAbsolutelyConverges C c (c+h) := by
  obtain ⟨s, hs, hsR⟩ := Recentering.positive_gap (t := 0) le_rfl (by simpa using hb)
  obtain ⟨δ, hδ, htR⟩ := Recentering.positive_gap (abs_nonneg (b 0-d)) ha
  obtain ⟨r, hr, hrs, hwt, hA, hC, he⟩ := local_compose a b (b 0-d)
    s (|b 0-d|+δ) hs (by simpa only [Real.norm_eq_abs] using lt_add_of_pos_right |b 0-d| hδ)
    (Recentering.real_majorant b s hs.le (by simpa only [zero_add] using hsR))
    (Recentering.real_majorant a (|b 0-d|+δ) (by positivity) htR)
  refine ⟨r, hr, (ENNReal.ofReal_le_ofReal hrs).trans_lt (by simpa using hsR),
    real_radius_lower_bound _ r hr.le hC, ?_, ?_, ?_⟩
  · simpa only [realRecenteredCoefficient, Real.norm_eq_abs] using hA
  · simpa only [realRecenteredCoefficient, Real.norm_eq_abs] using hC
  · intro h hh
    obtain ⟨v, S, hv, hi, ho, hc, hn⟩ := he h (by simpa only [Real.norm_eq_abs] using hh)
    refine ⟨b 0+v, S, ?_, ?_, ?_, ?_, ?_⟩
    · have heq : b 0+v-d = (b 0-d)+v := by ring
      apply (ENNReal.ofReal_le_ofReal (show |b 0+v-d| ≤ |b 0-d|+majorant b r from ?_)).trans_lt
        ((ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hwt.le)).trans_lt htR)
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add le_rfl (by simpa only [Real.norm_eq_abs] using hv))
    · change RealSeriesHasSum (fun j => b j * (c+h-c)^j) (b 0+v)
      simpa only [add_sub_cancel_left] using real_series_hasSum_of_hasSum hi
    · change RealSeriesHasSum (fun n => a n * (b 0+v-d)^n) S
      have hx : b 0+v-d = (b 0-d)+v := by ring
      simpa only [hx] using real_series_hasSum_of_hasSum ho
    · change RealSeriesHasSum (fun k => coefficient (realRecenteredCoefficient a d (b 0)) b k * (c+h-c)^k) S
      simpa only [realRecenteredCoefficient, add_sub_cancel_left] using real_series_hasSum_of_hasSum hc
    · change RealSeriesConverges (fun k => |coefficient (realRecenteredCoefficient a d (b 0)) b k * (c+h-c)^k|)
      have ht := real_series_hasSum_of_hasSum hn.hasSum
      exact ⟨_, by simpa only [realRecenteredCoefficient, add_sub_cancel_left,
        Real.norm_eq_abs] using ht⟩

/-- Complex composition, including nonreal inner values. Only the original centers
c,d are real; recentering is performed at the actual scalar b₀. -/
theorem complex_composition (a b : ℕ → ℂ) (c d : ℝ)
    (hb : 0 < complexPowerSeriesRadius b)
    (ha : ENNReal.ofReal ‖b 0-(d : ℂ)‖ < complexPowerSeriesRadius a) :
    let A := Recentering.coefficient a (b 0-(d : ℂ))
    let C := coefficient A b
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r < complexPowerSeriesRadius b ∧
      ENNReal.ofReal r ≤ complexPowerSeriesRadius C ∧
      Summable (fun m => ‖A m‖ * majorant b r ^ m) ∧
      Summable (fun k => ‖C k‖ * r^k) ∧
      ∀ h : ℂ, ‖h‖ ≤ r → ∃ G S : ℂ,
        ENNReal.ofReal ‖G-(d : ℂ)‖ < complexPowerSeriesRadius a ∧ ComplexPowerSeriesHasSum b c ((c : ℂ)+h) G ∧
        ComplexPowerSeriesHasSum a d G S ∧
        ComplexPowerSeriesHasSum C c ((c : ℂ)+h) S ∧
        ComplexPowerSeriesAbsolutelyConverges C c ((c : ℂ)+h) := by
  obtain ⟨s, hs, hsR⟩ := Recentering.positive_gap (t := 0) le_rfl (by simpa using hb)
  obtain ⟨δ, hδ, htR⟩ := Recentering.positive_gap (norm_nonneg (b 0-(d : ℂ))) ha
  obtain ⟨r, hr, hrs, hwt, hA, hC, he⟩ := local_compose a b (b 0-(d : ℂ))
    s (‖b 0-(d : ℂ)‖+δ) hs (lt_add_of_pos_right _ hδ)
    (Recentering.complex_majorant b s hs.le (by simpa only [zero_add] using hsR))
    (Recentering.complex_majorant a (‖b 0-(d : ℂ)‖+δ) (by positivity) htR)
  refine ⟨r, hr, (ENNReal.ofReal_le_ofReal hrs).trans_lt (by simpa using hsR),
    complex_radius_lower_bound _ r hr.le hC, hA, hC, ?_⟩
  intro h hh
  obtain ⟨v, S, hv, hi, ho, hc, hn⟩ := he h hh
  refine ⟨b 0+v, S, ?_, ?_, ?_, ?_, ?_⟩
  · have heq : b 0+v-(d : ℂ) = (b 0-(d : ℂ))+v := by ring
    apply (ENNReal.ofReal_le_ofReal (show ‖b 0+v-(d : ℂ)‖ ≤ ‖b 0-(d : ℂ)‖+majorant b r from ?_)).trans_lt
      ((ENNReal.ofReal_le_ofReal hwt.le).trans_lt htR)
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hv)
  · change ComplexSeriesHasSum (fun j => b j * ((c : ℂ)+h-(c : ℂ))^j) (b 0+v)
    simpa only [add_sub_cancel_left] using complex_series_hasSum_of_hasSum hi
  · change ComplexSeriesHasSum (fun n => a n * (b 0+v-(d : ℂ))^n) S
    have hx : b 0+v-(d : ℂ) = (b 0-(d : ℂ))+v := by ring
    simpa only [hx] using complex_series_hasSum_of_hasSum ho
  · change ComplexSeriesHasSum (fun k => coefficient (Recentering.coefficient a (b 0-(d : ℂ))) b k *
      ((c : ℂ)+h-(c : ℂ))^k) S
    simpa only [add_sub_cancel_left] using complex_series_hasSum_of_hasSum hc
  · change RealSeriesConverges (fun k => ‖coefficient (Recentering.coefficient a (b 0-(d : ℂ))) b k *
      ((c : ℂ)+h-(c : ℂ))^k‖)
    have ht := real_series_hasSum_of_hasSum hn.hasSum
    exact ⟨_, by simpa only [add_sub_cancel_left] using ht⟩

/-- Evaluating at the center leaves exactly the constant coefficient. -/
theorem hasSum_at_zero {K : Type*} [RCLike K] (b : ℕ → K) :
    HasSum (fun n => b n * (0 : K)^n) (b 0) := by
  convert hasSum_ite_eq (0 : ℕ) (b 0) using 1
  ext n
  by_cases hn : n = 0 <;> simp [hn]

/-- Restricting a majorant to a smaller closed disk. -/
theorem majorant_mono {K : Type*} [RCLike K] (b : ℕ → K) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s)
    (hb : Summable (fun j => ‖positivePart b j‖ * s^j)) :
    majorant b r ≤ majorant b s := by
  have hle (j : ℕ) : ‖positivePart b j‖ * r^j ≤ ‖positivePart b j‖ * s^j :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs j) (norm_nonneg _)
  have hs := hb.of_nonneg_of_le (fun j => by positivity) hle
  exact hs.tsum_le_tsum hle hb

/-- Direct functional form: the locally defined power-series sums compose. -/
theorem real_composition_functions (a b : ℕ → ℝ) (c d : ℝ) (g F : ℝ → ℝ)
    (hb : 0 < realPowerSeriesRadius b)
    (hg : ∃ ε : ℝ, 0 < ε ∧ ∀ x, |x-c| < ε →
      RealPowerSeriesHasSum b c x (g x))
    (hF : ∀ y, ENNReal.ofReal |y-d| < realPowerSeriesRadius a →
      RealPowerSeriesHasSum a d y (F y))
    (ha : ENNReal.ofReal |g c-d| < realPowerSeriesRadius a) :
    let A := realRecenteredCoefficient a d (g c)
    let C := coefficient A b
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ realPowerSeriesRadius C ∧
      Summable (fun m => |A m| * majorant b r ^ m) ∧
      Summable (fun k => |C k| * r^k) ∧
      ∀ x : ℝ, |x-c| < r → RealPowerSeriesHasSum C c x (F (g x)) := by
  obtain ⟨ε, hε, hg⟩ := hg
  have hzero : RealPowerSeriesHasSum b c c (b 0) := by
    change RealSeriesHasSum (fun n => b n * (c-c)^n) (b 0)
    simpa only [sub_self] using real_series_hasSum_of_hasSum (hasSum_at_zero b)
  have hgc : g c = b 0 := real_powerSeries_sum_unique b c c _ _
    (hg c (by simpa using hε)) hzero
  dsimp only
  rw [hgc] at ha ⊢
  obtain ⟨r, hr, hrb, hrC, hA, hC, he⟩ := real_composition a b c d hb ha
  let q := min r ε
  have hq : 0 < q := lt_min hr hε
  have hqr : q ≤ r := min_le_left _ _
  have hU : majorant b q ≤ majorant b r := majorant_mono b hq.le hqr
    (majorant_summable b hr.le le_rfl (Recentering.real_majorant b r hr.le hrb))
  refine ⟨q, hq, (ENNReal.ofReal_le_ofReal hqr).trans hrC, ?_, ?_, ?_⟩
  · exact hA.of_nonneg_of_le (fun m => mul_nonneg (by positivity)
      (pow_nonneg (majorant_nonneg b hq.le) m)) (fun m =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (majorant_nonneg b hq.le) hU m) (abs_nonneg _))
  · exact hC.of_nonneg_of_le (fun k => by positivity) (fun k =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq.le hqr k) (abs_nonneg _))
  · intro x hx
    obtain ⟨G, S, hG, hi, ho, hc, hn⟩ := he (x-c) (hx.le.trans hqr)
    have hix : RealPowerSeriesHasSum b c x G := by simpa only [add_sub_cancel] using hi
    have hcx : RealPowerSeriesHasSum (coefficient (realRecenteredCoefficient a d (b 0)) b) c x S := by
      simpa only [add_sub_cancel] using hc
    have hgG : g x = G := real_powerSeries_sum_unique b c x _ _
      (hg x (hx.trans_le (min_le_right _ _))) hix
    have hFS : F (g x) = S := by
      rw [hgG]
      exact real_powerSeries_sum_unique a d G _ _ (hF G hG) ho
    simpa only [hFS] using hcx

/-- The same functional form for complex values, with arbitrary complex g(c). -/
theorem complex_composition_functions (a b : ℕ → ℂ) (c d : ℝ) (g F : ℂ → ℂ)
    (hb : 0 < complexPowerSeriesRadius b)
    (hg : ∃ ε : ℝ, 0 < ε ∧ ∀ z, ‖z-(c : ℂ)‖ < ε →
      ComplexPowerSeriesHasSum b c z (g z))
    (hF : ∀ y, ENNReal.ofReal ‖y-(d : ℂ)‖ < complexPowerSeriesRadius a →
      ComplexPowerSeriesHasSum a d y (F y))
    (ha : ENNReal.ofReal ‖g (c : ℂ)-(d : ℂ)‖ < complexPowerSeriesRadius a) :
    let A := Recentering.coefficient a (g (c : ℂ)-(d : ℂ))
    let C := coefficient A b
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ complexPowerSeriesRadius C ∧
      Summable (fun m => ‖A m‖ * majorant b r ^ m) ∧
      Summable (fun k => ‖C k‖ * r^k) ∧
      ∀ z : ℂ, ‖z-(c : ℂ)‖ < r → ComplexPowerSeriesHasSum C c z (F (g z)) := by
  obtain ⟨ε, hε, hg⟩ := hg
  have hzero : ComplexPowerSeriesHasSum b c (c : ℂ) (b 0) := by
    change ComplexSeriesHasSum (fun n => b n * ((c : ℂ)-(c : ℂ))^n) (b 0)
    simpa only [sub_self] using complex_series_hasSum_of_hasSum (hasSum_at_zero b)
  have hgc : g (c : ℂ) = b 0 := complex_powerSeries_sum_unique b c (c : ℂ) _ _
    (hg (c : ℂ) (by simpa using hε)) hzero
  dsimp only
  rw [hgc] at ha ⊢
  obtain ⟨r, hr, hrb, hrC, hA, hC, he⟩ := complex_composition a b c d hb ha
  let q := min r ε
  have hq : 0 < q := lt_min hr hε
  have hqr : q ≤ r := min_le_left _ _
  have hU : majorant b q ≤ majorant b r := majorant_mono b hq.le hqr
    (majorant_summable b hr.le le_rfl (Recentering.complex_majorant b r hr.le hrb))
  refine ⟨q, hq, (ENNReal.ofReal_le_ofReal hqr).trans hrC, ?_, ?_, ?_⟩
  · exact hA.of_nonneg_of_le (fun m => mul_nonneg (by positivity)
      (pow_nonneg (majorant_nonneg b hq.le) m)) (fun m =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (majorant_nonneg b hq.le) hU m) (norm_nonneg _))
  · exact hC.of_nonneg_of_le (fun k => by positivity) (fun k =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq.le hqr k) (norm_nonneg _))
  · intro z hz
    obtain ⟨G, S, hG, hi, ho, hc, hn⟩ := he (z-(c : ℂ)) (hz.le.trans hqr)
    have hiz : ComplexPowerSeriesHasSum b c z G := by simpa only [add_sub_cancel] using hi
    have hcz : ComplexPowerSeriesHasSum (coefficient (Recentering.coefficient a (b 0-(d : ℂ))) b) c z S := by
      simpa only [add_sub_cancel] using hc
    have hgG : g z = G := complex_powerSeries_sum_unique b c z _ _
      (hg z (hz.trans_le (min_le_right _ _))) hiz
    have hFS : F (g z) = S := by
      rw [hgG]
      exact complex_powerSeries_sum_unique a d G _ _ (hF G hG) ho
    simpa only [hFS] using hcz

/-- Complex-valued inner functions defined only for real inputs also satisfy the
composition theorem. This retains the manuscript's real-increment convention. -/
theorem complex_real_composition_functions (a b : ℕ → ℂ) (c d : ℝ) (g : ℝ → ℂ) (F : ℂ → ℂ)
    (hb : 0 < complexPowerSeriesRadius b)
    (hg : ∃ ε : ℝ, 0 < ε ∧ ∀ x, |x-c| < ε →
      ComplexPowerSeriesHasSum b c (x : ℂ) (g x))
    (hF : ∀ y, ENNReal.ofReal ‖y-(d : ℂ)‖ < complexPowerSeriesRadius a →
      ComplexPowerSeriesHasSum a d y (F y))
    (ha : ENNReal.ofReal ‖g c-(d : ℂ)‖ < complexPowerSeriesRadius a) :
    let A := Recentering.coefficient a (g c-(d : ℂ))
    let C := coefficient A b
    ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ complexPowerSeriesRadius C ∧
      Summable (fun m => ‖A m‖ * majorant b r ^ m) ∧
      Summable (fun k => ‖C k‖ * r^k) ∧
      ∀ x : ℝ, |x-c| < r → ComplexPowerSeriesHasSum C c (x : ℂ) (F (g x)) := by
  obtain ⟨ε, hε, hg⟩ := hg
  have hzero : ComplexPowerSeriesHasSum b c (c : ℂ) (b 0) := by
    change ComplexSeriesHasSum (fun n => b n * ((c : ℂ)-(c : ℂ))^n) (b 0)
    simpa only [sub_self] using complex_series_hasSum_of_hasSum (hasSum_at_zero b)
  have hgc : g c = b 0 := complex_powerSeries_sum_unique b c (c : ℂ) _ _
    (hg c (by simpa using hε)) hzero
  dsimp only
  rw [hgc] at ha ⊢
  obtain ⟨r, hr, hrb, hrC, hA, hC, he⟩ := complex_composition a b c d hb ha
  let q := min r ε
  have hq : 0 < q := lt_min hr hε
  have hqr : q ≤ r := min_le_left _ _
  have hU : majorant b q ≤ majorant b r := majorant_mono b hq.le hqr
    (majorant_summable b hr.le le_rfl (Recentering.complex_majorant b r hr.le hrb))
  refine ⟨q, hq, (ENNReal.ofReal_le_ofReal hqr).trans hrC, ?_, ?_, ?_⟩
  · exact hA.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _)
      (pow_nonneg (majorant_nonneg b hq.le) m)) (fun m =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (majorant_nonneg b hq.le) hU m) (norm_nonneg _))
  · exact hC.of_nonneg_of_le (fun k => by positivity) (fun k =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq.le hqr k) (norm_nonneg _))
  · intro x hx
    obtain ⟨G, S, hG, hi, ho, hc, hn⟩ := he ((x-c : ℝ) : ℂ) (by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using hx.le.trans hqr)
    have heq : (c : ℂ)+((x-c : ℝ) : ℂ) = (x : ℂ) := by push_cast; ring
    have hix : ComplexPowerSeriesHasSum b c (x : ℂ) G := by simpa only [heq] using hi
    have hcx : ComplexPowerSeriesHasSum (coefficient (Recentering.coefficient a (b 0-(d : ℂ))) b) c (x : ℂ) S := by
      simpa only [heq] using hc
    have hgG : g x = G := complex_powerSeries_sum_unique b c (x : ℂ) _ _
      (hg x (hx.trans_le (min_le_right _ _))) hix
    have hFS : F (g x) = S := by
      rw [hgG]
      exact complex_powerSeries_sum_unique a d G _ _ (hF G hG) ho
    simpa only [hFS] using hcx

/-- Substituting the positive multi-index formula gives exactly the source's
finite coefficient ∑_{m≤k} A_m ∑_{j₁+...+j_m=k, jᵢ≥1} b_{j₁}...b_{j_m}. -/
theorem coefficient_formula {K : Type*} [CommSemiring K] (A b : ℕ → K) (k : ℕ) :
    coefficient A b k = ∑ m ∈ Finset.range (k+1), A m *
      ∑ l ∈ (Finset.finsuppAntidiag (Finset.range m) k).filter
        (fun l => ∀ i ∈ Finset.range m, 0 < l i), ∏ i ∈ Finset.range m, b (l i) := by
  classical
  simp only [coefficient, powerCoefficient_formula]

end Composition
end SingleVariableAnalysis
