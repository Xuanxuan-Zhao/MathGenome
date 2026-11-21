import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Newton.ScalarConvergence
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Newton.ScalarError
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! W73: exact scalar Newton iterates stay in the certified neighborhood
and converge quadratically to the specified simple root. -/
namespace NumAnalysis206.Newton
open Set Filter
open Specs.NumAnalysis206.Newton

theorem scalarNewton_local_convergence :
    Specs.NumAnalysis206.Newton.ScalarConvergence.localConvergence := by
  intro f p R m M U hR hU hsub hf hp hm hslope hcurv r x₀ hr hrR hq hx₀
  let x := scalarNewtonIteratesValue f x₀
  let C := M / (2 * m)
  let q := M * r / (2 * m)
  have hpI : p ∈ Icc (p - R) (p + R) := ⟨by linarith, by linarith⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans (hcurv p hpI)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hx0 : x 0 = x₀ := rfl
  have hrec (n : ℕ) : x (n + 1) = scalarNewtonValue f (x n) :=
    scalarNewtonIterates_succ f x₀ n
  have hinR {t : ℝ} (ht : |t - p| ≤ r) : t ∈ Icc (p - R) (p + R) := by
    obtain ⟨hl, hu⟩ := abs_le.mp ht
    exact ⟨by linarith, by linarith⟩
  have hstep (n : ℕ) (hn : |x n - p| ≤ r) :
      scalarStepValidValue f (x n) ∧
      |x (n + 1) - p| ≤ M * |x n - p| ^ 2 / (2 * m) := by
    rw [hrec]
    exact scalarNewton_step_error f p R m M U hR hU hsub hf hp hm hslope hcurv
      (x n) (hinR hn)
  have hlinear (n : ℕ) (hn : |x n - p| ≤ r) :
      |x (n + 1) - p| ≤ q * |x n - p| := by
    have hsquare : |x n - p| ^ 2 ≤ r * |x n - p| := by
      nlinarith [abs_nonneg (x n - p)]
    calc
      |x (n + 1) - p| ≤ M * |x n - p| ^ 2 / (2 * m) := (hstep n hn).2
      _ = C * |x n - p| ^ 2 := by dsimp [C]; ring
      _ ≤ C * (r * |x n - p|) := mul_le_mul_of_nonneg_left hsquare hC
      _ = q * |x n - p| := by dsimp [C, q]; ring
  have hbounds (n : ℕ) :
      |x n - p| ≤ r ∧ |x n - p| ≤ q ^ n * |x₀ - p| := by
    induction n with
    | zero => simpa only [hx0, pow_zero, one_mul] using And.intro hx₀ (le_refl |x₀ - p|)
    | succ n ih =>
      have hl := hlinear n ih.1
      constructor
      · calc
          |x (n + 1) - p| ≤ q * |x n - p| := hl
          _ ≤ q * r := mul_le_mul_of_nonneg_left ih.1 hq0
          _ ≤ r := by nlinarith
      · calc
          |x (n + 1) - p| ≤ q * |x n - p| := hl
          _ ≤ q * (q ^ n * |x₀ - p|) := mul_le_mul_of_nonneg_left ih.2 hq0
          _ = q ^ (n + 1) * |x₀ - p| := by rw [pow_succ]; ring
  have hall (n : ℕ) := hstep n (hbounds n).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨hl, hu⟩ := abs_le.mp (hbounds n).1
    exact ⟨⟨by linarith, by linarith⟩, (hall n).1, hrec n, (hall n).2, (hbounds n).2⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    have hlim : Tendsto (fun n : ℕ => q ^ n * |x₀ - p|) atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).mul_const |x₀ - p|
    simpa only [Real.dist_eq] using
      squeeze_zero (fun n => abs_nonneg (x n - p)) (fun n => (hbounds n).2) hlim
  · intro hzero n
    apply sub_eq_zero.mp
    apply abs_eq_zero.mp
    exact le_antisymm (by simpa [hzero] using (hall n).2) (abs_nonneg _)
  · intro N hroot k
    exact exactIterates_absorbing_after_root f (scalarNewtonValue f) x₀ N hroot k

end NumAnalysis206.Newton
