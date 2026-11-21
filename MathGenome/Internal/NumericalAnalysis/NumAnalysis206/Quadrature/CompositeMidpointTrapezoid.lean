import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.CompositeMidpointTrapezoid
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.IntervalTaylor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp

namespace NumAnalysis206.Quadrature
open Set
open scoped BigOperators
open NumAnalysis206.Approximation

noncomputable abbrev quadratureStep := CompositeMidpointTrapezoidSpec.stepValue
noncomputable abbrev quadratureNode := CompositeMidpointTrapezoidSpec.nodeValue
noncomputable abbrev compositeMidpoint := CompositeMidpointTrapezoidSpec.midpointValue
noncomputable abbrev compositeTrapezoid := CompositeMidpointTrapezoidSpec.trapezoidValue

variable {a b : ℝ} {f : ℝ → ℝ} {D : ℕ → ℝ → ℝ}

/-- Taylor's affine part integrates exactly at the midpoint; integrate the
quadratic absolute remainder to obtain the sharp local coefficient. -/
theorem midpoint_panel_bound (hab : a ≤ b) (hD : IntervalJet a b 2 f D)
    {M : ℝ} (hM : ∀ t ∈ Icc a b, |D 2 t| ≤ M) :
    |(∫ t in a..b, f t) - (b - a) * f ((a + b) / 2)| ≤
      (b - a) ^ 3 / 24 * M := by
  let c := (a + b) / 2
  have hc : c ∈ Icc a b := by dsimp [c]; constructor <;> linarith
  let P : ℝ → ℝ := fun t => f c + D 1 c * (t - c)
  have hP : Continuous P := by dsimp [P]; fun_prop
  have hf : ContinuousOn f (Icc a b) := (hD.2.1 0 (by omega)).congr hD.1.symm
  have hfi : IntervalIntegrable f MeasureTheory.volume a b := hf.intervalIntegrable_of_Icc hab
  have hPi : IntervalIntegrable P MeasureTheory.volume a b := hP.intervalIntegrable a b
  have ht (t : ℝ) (ht : t ∈ Icc a b) :
      |f t - P t| ≤ M / 2 * (t - c) ^ 2 := by
    have h := jet_taylor_bound hab (by omega : 1 ≤ 2) hD hc ht (fun x hx =>
      hM x ((uIcc_subset_Icc hc ht) hx))
    have hsum : jetTaylorSum D 2 c t = P t := by
      simp [jetTaylorSum, IntervalTaylorSpec.sumValue, Finset.sum_range_succ, P, hD.1 hc]
    rw [hsum] at h
    norm_num only [Nat.factorial_two, Nat.cast_ofNat, sq_abs] at h
    convert h using 1
    ring
  have hpint : (∫ t in a..b, P t) = (b - a) * f c := by
    have hlin : (∫ t in a..b, t - c) = 0 := by
      rw [intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ => c)
        (continuous_id.intervalIntegrable a b) (continuous_const.intervalIntegrable a b)]
      simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
      dsimp [c]
      ring
    change (∫ t in a..b, f c + D 1 c * (t - c)) = _
    rw [intervalIntegral.integral_add (f := fun _ : ℝ => f c)
      (g := fun t => D 1 c * (t - c)) (continuous_const.intervalIntegrable a b)
      ((by fun_prop : Continuous (fun t => D 1 c * (t - c))).intervalIntegrable a b),
      intervalIntegral.integral_const_mul, hlin]
    simp
  have hquad : (∫ t in a..b, M / 2 * (t - c) ^ 2) = (b - a) ^ 3 / 24 * M := by
    have hd (x : ℝ) : HasDerivAt (fun t => M / 6 * (t - c) ^ 3)
        (M / 2 * (x - c) ^ 2) x := by
      convert (((hasDerivAt_id x).sub_const c).pow 3).const_mul (M / 6) using 1 <;> dsimp <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      ((by fun_prop : Continuous (fun t => M / 2 * (t - c) ^ 2)).intervalIntegrable a b)]
    dsimp [c]
    ring
  rw [← hpint, ← intervalIntegral.integral_sub hfi hPi]
  calc
    _ ≤ ∫ t in a..b, |f t - P t| := intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ t in a..b, M / 2 * (t - c) ^ 2 := by
      apply intervalIntegral.integral_mono_on hab
        ((hf.sub hP.continuousOn).abs.intervalIntegrable_of_Icc hab)
        ((by fun_prop : Continuous (fun t => M / 2 * (t - c) ^ 2)).intervalIntegrable a b) ht
    _ = _ := hquad

@[simp] theorem quadratureNode_zero (a b : ℝ) (n : ℕ) : quadratureNode a b n 0 = a := by
  simp [quadratureNode, CompositeMidpointTrapezoidSpec.nodeValue]

@[simp] theorem quadratureNode_last (a b : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    quadratureNode a b n n = b := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  dsimp [quadratureNode, CompositeMidpointTrapezoidSpec.nodeValue,
    CompositeMidpointTrapezoidSpec.stepValue]
  field_simp
  ring

theorem quadratureNode_width (a b : ℝ) (n j : ℕ) :
    quadratureNode a b n (j + 1) - quadratureNode a b n j = quadratureStep a b n := by
  simp only [quadratureNode, CompositeMidpointTrapezoidSpec.nodeValue,
    Nat.cast_add, Nat.cast_one]
  ring

theorem quadratureNode_mono (hab : a ≤ b) (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    quadratureNode a b n i ≤ quadratureNode a b n j := by
  have hh : 0 ≤ quadratureStep a b n := div_nonneg (sub_nonneg.mpr hab) n.cast_nonneg
  exact add_le_add (le_refl a) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hh)

theorem quadratureNode_mem (hab : a ≤ b) (n : ℕ) (hn : 1 ≤ n) {j : ℕ} (hj : j ≤ n) :
    quadratureNode a b n j ∈ Icc a b := by
  constructor
  · simpa using quadratureNode_mono hab n (Nat.zero_le j)
  · simpa [quadratureNode_last a b n hn] using quadratureNode_mono hab n hj

/-- The panel-sum definition is the usual endpoint-weighted trapezoidal sum. -/
theorem compositeTrapezoid_eq (n : ℕ) (hn : 1 ≤ n) :
    compositeTrapezoid f a b n = trapezoidal_integral f n a b := by
  have hb : a + (n : ℝ) * quadratureStep a b n = b := quadratureNode_last a b n hn
  have he := sum_trapezoidal_integral_adjacent_intervals
    (f := f) (a := a) (h := quadratureStep a b n) (by omega : 0 < n)
  rw [hb] at he
  rw [← he]
  unfold compositeTrapezoid CompositeMidpointTrapezoidSpec.trapezoidValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [trapezoidal_integral_one]
  simp only [CompositeMidpointTrapezoidSpec.nodeValue, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

/-- W56, trapezoidal rule. The library within-derivative bound is supplied on
all real inputs: off the closed interval its chosen derivative is zero. -/
theorem composite_trapezoid_error (n : ℕ) (hab : a < b) (hn : 1 ≤ n)
    (hD : IntervalJet a b 2 f D) :
    |(∫ t in a..b, f t) - compositeTrapezoid f a b n| ≤
      (b - a) * (quadratureStep a b n) ^ 2 / 12 * ‖PeanoKernelSpec.derivativeValue hD‖ := by
  have hf : ContDiffOn ℝ 2 f (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact jet_to_contDiff hab.le hD
  have hM (x : ℝ) : |iteratedDerivWithin 2 f (uIcc a b) x| ≤
      ‖PeanoKernelSpec.derivativeValue hD‖ := by
    rw [uIcc_of_le hab.le]
    by_cases hx : x ∈ Icc a b
    · rw [← jet_eq_iterated hab hD 2 le_rfl hx]
      exact (PeanoKernelSpec.derivativeValue hD).norm_coe_le_norm ⟨x, hx⟩
    · rw [iteratedDerivWithin_succ, derivWithin_zero_of_notMem_closure
        (by rwa [closure_Icc]), abs_zero]
      exact norm_nonneg _
  have he := trapezoidal_error_le_of_c2 hf hM (by omega : 0 < n)
  rw [compositeTrapezoid_eq n hn, abs_sub_comm]
  change |trapezoidal_error f n a b| ≤ _
  convert he using 1
  rw [abs_of_pos (sub_pos.mpr hab)]
  dsimp [quadratureStep, CompositeMidpointTrapezoidSpec.stepValue]
  ring

/-- W56, midpoint rule, including a single panel. -/
theorem composite_midpoint_error (n : ℕ) (hab : a < b) (hn : 1 ≤ n)
    (hD : IntervalJet a b 2 f D) :
    |(∫ t in a..b, f t) - compositeMidpoint f a b n| ≤
      (b - a) * (quadratureStep a b n) ^ 2 / 24 * ‖PeanoKernelSpec.derivativeValue hD‖ := by
  let t := quadratureNode a b n
  let h := quadratureStep a b n
  let M := ‖PeanoKernelSpec.derivativeValue hD‖
  have ht (j : ℕ) (hj : j ≤ n) : t j ∈ Icc a b := quadratureNode_mem hab.le n hn hj
  have horder (j : ℕ) : t j ≤ t (j + 1) := quadratureNode_mono hab.le n (by omega)
  have hf : ContinuousOn f (Icc a b) := (hD.2.1 0 (by omega)).congr hD.1.symm
  have hi (j : ℕ) (hj : j < n) : IntervalIntegrable f MeasureTheory.volume (t j) (t (j + 1)) :=
    (hf.mono (Icc_subset_Icc (ht j hj.le).1 (ht (j + 1) (by omega)).2)).intervalIntegrable_of_Icc
      (horder j)
  have hsum : (∑ j ∈ Finset.range n, ∫ x in t j..t (j + 1), f x) = ∫ x in a..b, f x := by
    simpa [t, quadratureNode_last a b n hn] using
      (intervalIntegral.sum_integral_adjacent_intervals hi)
  have hb (j : ℕ) (hj : j ∈ Finset.range n) :
      |(∫ x in t j..t (j + 1), f x) - h * f ((t j + t (j + 1)) / 2)| ≤ h ^ 3 / 24 * M := by
    have hj' := Finset.mem_range.mp hj
    have hJ := jet_restrict (ht j hj'.le).1 (ht (j + 1) (by omega)).2 hD
    have hp := midpoint_panel_bound (horder j) hJ (M := M) (fun x hx =>
      (PeanoKernelSpec.derivativeValue hD).norm_coe_le_norm
        ⟨x, (Icc_subset_Icc (ht j hj'.le).1 (ht (j + 1) (by omega)).2) hx⟩)
    simpa only [t, quadratureNode_width] using hp
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnh : (n : ℝ) * h = b - a := by
    dsimp [h, quadratureStep, CompositeMidpointTrapezoidSpec.stepValue]
    field_simp
  calc
    |(∫ x in a..b, f x) - compositeMidpoint f a b n| =
        |∑ j ∈ Finset.range n,
          ((∫ x in t j..t (j + 1), f x) - h * f ((t j + t (j + 1)) / 2))| := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
      rfl
    _ ≤ ∑ j ∈ Finset.range n,
        |(∫ x in t j..t (j + 1), f x) - h * f ((t j + t (j + 1)) / 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range n, h ^ 3 / 24 * M := Finset.sum_le_sum hb
    _ = (n : ℝ) * (h ^ 3 / 24 * M) := by simp
    _ = (b - a) * h ^ 2 / 24 * M := by rw [← hnh]; ring

end NumAnalysis206.Quadrature
