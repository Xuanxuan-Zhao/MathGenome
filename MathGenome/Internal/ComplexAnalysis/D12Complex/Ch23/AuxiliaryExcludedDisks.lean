import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch23.AuxiliaryExcludedDisks
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch23.OmittedValuesTransform
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.Positivity

/-!
The excluded-disk part of paper.tex:4164–4197. The omitted lattice is
computed from the cosh identity, independently of any normality theorem.
The real gaps follow from cosh addition and monotonicity. Rounding the
imaginary coordinate and choosing a real interval give coordinate errors
strictly below one, hence distance strictly below two.
-/

noncomputable section
namespace D12Complex.AuxiliaryExcludedDisks
open Filter
open scoped Topology

/-- Candidate-owned export of the canonical real lattice coordinate. -/
abbrev a_definition : Specs.D12Complex.Ch23.AuxiliaryExcludedDisks.a_type := a

/-- Candidate-owned export of the canonical complex lattice point. -/
abbrev latticePoint_definition :
    Specs.D12Complex.Ch23.AuxiliaryExcludedDisks.latticePoint_type := latticePoint

@[simp] theorem a_one : a 1 = 0 := by norm_num [a]

lemma a_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ a n := by
  apply Real.log_nonneg
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 1 ≤ Real.sqrt n := (Real.le_sqrt (by norm_num) (by positivity)).2 (by simpa using h)
  linarith [Real.sqrt_nonneg ((n : ℝ) - 1)]

lemma cosh_two_a {n : ℕ} (hn : 1 ≤ n) : Real.cosh (2 * a n) = 2 * n - 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hu := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hv := Real.sq_sqrt (show 0 ≤ (n : ℝ) - 1 by linarith)
  have hp : 0 < Real.sqrt n + Real.sqrt ((n : ℝ) - 1) := by positivity
  have hi : (Real.sqrt n + Real.sqrt ((n : ℝ) - 1))⁻¹ =
      Real.sqrt n - Real.sqrt ((n : ℝ) - 1) := by
    apply inv_eq_of_mul_eq_one_right
    nlinarith
  have he := Real.exp_nat_mul (Real.log (Real.sqrt n + Real.sqrt ((n : ℝ) - 1))) 2
  norm_num only [Nat.cast_ofNat] at he
  rw [a, Real.cosh_eq, Real.exp_neg, he, Real.exp_log hp, ← inv_pow, hi]
  nlinarith

theorem a_strictMono : StrictMonoOn a (Set.Ici 1) := by
  intro m hm n hn hmn
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by exact lt_of_lt_of_le Nat.zero_lt_one hm)
  apply Real.log_lt_log (by positivity)
  apply add_lt_add_of_lt_of_le
  · exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hmn)
  · apply Real.sqrt_le_sqrt
    have : (m : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt hmn
    linarith

theorem a_tendsto : Tendsto a atTop atTop := by
  have h : Tendsto (fun n : ℕ => Real.log (Real.sqrt (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply tendsto_atTop_mono' atTop _ h
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hp : 0 < Real.sqrt (n : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast (show 0 < n by omega)
  exact Real.log_le_log hp (by linarith [Real.sqrt_nonneg ((n : ℝ) - 1)])

theorem a_gap (n : ℕ) (hn : 1 ≤ n) : a (n + 1) - a n ≤ a 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := a_nonneg hn
  have h2 := a_nonneg (n := 2) (by norm_num)
  have h3 := a_nonneg (n := n+1) (by omega)
  have hcosh : Real.cosh (2 * a (n + 1)) ≤ Real.cosh (2 * (a n + a 2)) := by
    rw [mul_add, Real.cosh_add, cosh_two_a hn, cosh_two_a (n := 2) (by norm_num),
      cosh_two_a (n := n+1) (by omega)]
    have hp : 0 ≤ Real.sinh (2 * a n) * Real.sinh (2 * a 2) :=
      mul_nonneg (Real.sinh_nonneg_iff.mpr (by linarith))
        (Real.sinh_nonneg_iff.mpr (by linarith))
    push_cast
    nlinarith
  have hh := Real.cosh_le_cosh.mp hcosh
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hh
  linarith

theorem a_two_lt_one : a 2 < 1 := by
  unfold a
  norm_num
  apply (Real.log_lt_iff_lt_exp (by positivity)).2
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have he := Real.exp_one_gt_d9
  nlinarith

theorem imaginary_spacing : Real.pi / 2 < 2 := by linarith [Real.pi_lt_four]

/-- Integer imaginary translations only change the sign of cosh. -/
lemma cosh_int_translate (w : ℂ) (k : ℤ) :
    Complex.cosh (w + (k : ℂ) * ((Real.pi : ℂ) * Complex.I)) = Complex.cosh w ∨
    Complex.cosh (w + (k : ℂ) * ((Real.pi : ℂ) * Complex.I)) = -Complex.cosh w := by
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    have harg : w + (k : ℂ) * ((Real.pi : ℂ) * Complex.I) =
        w + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hm]
      push_cast
      ring
    rw [harg]
    exact (Complex.cosh_periodic.int_mul m) w
  · right
    have harg : w + (k : ℂ) * ((Real.pi : ℂ) * Complex.I) =
        w + ((m : ℂ) * (2 * ((Real.pi : ℂ) * Complex.I)) +
          (Real.pi : ℂ) * Complex.I) := by
      rw [hm]
      push_cast
      ring
    rw [harg]
    exact (Complex.cosh_antiperiodic.int_odd_mul_antiperiodic m) w

lemma cosh_lattice {n : ℕ} (hn : 1 ≤ n) (k : ℤ) (b : Bool) :
    Complex.cosh (2 * latticePoint n k b) = (2 * (n : ℂ) - 1) ∨
    Complex.cosh (2 * latticePoint n k b) = -(2 * (n : ℂ) - 1) := by
  have hbase : Complex.cosh (2 * ((if b then a n else -a n : ℝ) : ℂ)) =
      2 * (n : ℂ) - 1 := by
    have hc : Complex.cosh ((2 * a n : ℝ) : ℂ) = ((2 * n - 1 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_cosh, cosh_two_a hn]
    cases b <;> simpa [mul_neg] using hc
  have he : 2 * latticePoint n k b =
      2 * ((if b then a n else -a n : ℝ) : ℂ) + (k : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    unfold latticePoint
    ring
  rw [he]
  simpa only [hbase] using cosh_int_translate
    (2 * ((if b then a n else -a n : ℝ) : ℂ)) k

lemma exp_odd_pi_I (n : ℕ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (2 * (n : ℂ) - 1)) = -1 := by
  have he : (Real.pi : ℂ) * Complex.I * (2 * (n : ℂ) - 1) =
      ((n : ℤ) - 1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

lemma transform_at_lattice {n : ℕ} (hn : 1 ≤ n) (k : ℤ) (b : Bool) :
    -Complex.exp ((Real.pi : ℂ) * Complex.I * Complex.cosh (2 * latticePoint n k b)) = 1 := by
  obtain h | h := cosh_lattice hn k b
  · rw [h, exp_odd_pi_I]
    norm_num
  · rw [h, mul_neg, Complex.exp_neg, exp_odd_pi_I]
    norm_num

theorem lattice_omitted :
    Specs.D12Complex.Ch23.AuxiliaryExcludedDisks.lattice_omitted_type := by
  intro Ω f g hone hidentity z hz n hn k b heq
  apply hone z hz
  rw [hidentity z hz, heq, transform_at_lattice hn]

/-- A nonnegative real number lies less than one to the right of some aₙ. -/
lemma real_coordinate_net (x : ℝ) (hx : 0 ≤ x) :
    ∃ n : ℕ, 1 ≤ n ∧ |x - a n| < 1 := by
  have hex : ∃ n : ℕ, x < a (n + 1) := by
    obtain ⟨m, hm, hmx⟩ := exists_lt_of_tendsto_atTop a_tendsto 1 x
    exact ⟨m - 1, by simpa [Nat.sub_add_cancel hm] using hmx⟩
  let N := Nat.find hex
  have hN : x < a (N + 1) := Nat.find_spec hex
  have hNpos : 1 ≤ N := by
    by_contra h
    have hz : N = 0 := by omega
    simp [hz] at hN
    linarith
  have hlow : a N ≤ x := by
    have hm := Nat.find_min hex (show N - 1 < N by omega)
    have he : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
    rw [he] at hm
    exact le_of_not_gt hm
  refine ⟨N, hNpos, ?_⟩
  rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
  have hg := a_gap N hNpos
  linarith [a_two_lt_one]

lemma signed_real_coordinate_net (x : ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ b : Bool, |x - (if b then a n else -a n)| < 1 := by
  obtain ⟨n, hn, h⟩ := real_coordinate_net |x| (abs_nonneg x)
  by_cases hx : 0 ≤ x
  · exact ⟨n, hn, true, by simpa [abs_of_nonneg hx] using h⟩
  · refine ⟨n, hn, false, ?_⟩
    rw [abs_of_neg (lt_of_not_ge hx)] at h
    have he : -x - a n = -(x + a n) := by ring
    rw [he, abs_neg] at h
    simpa [sub_neg_eq_add] using h

lemma imaginary_coordinate_net (y : ℝ) :
    ∃ k : ℤ, |y - Real.pi * k / 2| < 1 := by
  let k : ℤ := round (2 * y / Real.pi)
  have h := abs_sub_round (2 * y / Real.pi)
  have hp := Real.pi_pos
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ Real.pi / 2 by positivity)
  have he : Real.pi / 2 * |2 * y / Real.pi - k| = |y - Real.pi * k / 2| := by
    rw [← abs_of_pos (show 0 < Real.pi / 2 by positivity), ← abs_mul]
    congr 1
    field_simp
  rw [he] at hmul
  exact ⟨k, lt_of_le_of_lt hmul (by linarith [Real.pi_lt_four])⟩

theorem lattice_meets_disk :
    Specs.D12Complex.Ch23.AuxiliaryExcludedDisks.lattice_meets_disk_type := by
  intro c
  obtain ⟨n, hn, b, hx⟩ := signed_real_coordinate_net c.re
  obtain ⟨k, hy⟩ := imaginary_coordinate_net c.im
  refine ⟨n, hn, k, b, ?_⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm]
  have hb := Complex.norm_le_abs_re_add_abs_im (c - latticePoint n k b)
  have hre : (c - latticePoint n k b).re = c.re - (if b then a n else -a n) := by
    simp [latticePoint]
  have him : (c - latticePoint n k b).im = c.im - Real.pi * k / 2 := by
    simp [latticePoint]
  rw [hre, him] at hb
  linarith

theorem no_disk_of_transform :
    Specs.D12Complex.Ch23.AuxiliaryExcludedDisks.no_disk_of_transform_type := by
  intro Ω f g hone hidentity c hsub
  obtain ⟨n, hn, k, b, hp⟩ := lattice_meets_disk c
  obtain ⟨z, hz, heq⟩ := hsub hp
  exact lattice_omitted Ω f g hone hidentity z hz n hn k b heq

theorem exists_transform_no_disk :
    Specs.D12Complex.Ch23.AuxiliaryExcludedDisks.exists_transform_no_disk_type := by
  intro Ω f hΩ hsc hf hzero hone
  obtain ⟨g, hg, hidentity⟩ :=
    OmittedValuesTransform.exists_transform Ω f hΩ hsc hf hzero hone
  exact ⟨g, hg, hidentity, no_disk_of_transform Ω f g hone hidentity⟩

end D12Complex.AuxiliaryExcludedDisks
