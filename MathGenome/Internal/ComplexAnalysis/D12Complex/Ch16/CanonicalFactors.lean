import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.CanonicalFactors
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
Canonical factors (paper.tex:2778–2788). The polynomial correction uses
indices k+1, so genus zero is literally the empty sum. The logarithm is
defined by the negative tail series; its equality to log(1-w) plus the
correction is established only inside the unit disk. This equality supplies
holomorphy and exponentiation without selecting a principal log of factor.
-/
noncomputable section
open Filter
open scoped Topology
namespace D12Complex.CanonicalFactors

/-- Weierstrass elementary factor, with the empty sum covering genus zero. -/
def factor : ℕ → ℂ → ℂ := Specs.D12Complex.Ch16.CanonicalFactors.factor_value

/-- The branch normalized at zero, expressed by its actual tail series. -/
def logFactor : ℕ → ℂ → ℂ := Specs.D12Complex.Ch16.CanonicalFactors.logFactor_value

private def correction (p : ℕ) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1 : ℂ)

private lemma differentiable_correction (p : ℕ) : Differentiable ℂ (correction p) := by
  unfold correction
  fun_prop

theorem factor_zero_index : ∀ w : ℂ, factor 0 w = 1 - w := by
  intro w
  simp [factor, Specs.D12Complex.Ch16.CanonicalFactors.factor_value]

theorem factor_entire : ∀ p : ℕ, HolomorphicOn Set.univ (factor p) := by
  intro p
  refine ⟨isOpen_univ, fun w _ => ?_⟩
  change DifferentiableAt ℂ (fun w => (1-w) * Complex.exp (correction p w)) w
  exact ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).mul
    ((differentiable_correction p w).cexp)

theorem factor_eq_zero_iff : ∀ (p : ℕ) (w : ℂ), factor p w = 0 ↔ w = 1 := by
  intro p w
  change (1-w) * Complex.exp (correction p w) = 0 ↔ w = 1
  rw [mul_eq_zero]
  simp only [Complex.exp_ne_zero, or_false, sub_eq_zero]
  exact eq_comm

theorem factor_simple_zero : ∀ p : ℕ, analyticOrderAt (factor p) 1 = 1 := by
  intro p
  have hf : AnalyticAt ℂ (factor p) 1 := by
    change AnalyticAt ℂ (fun w => (1-w) * Complex.exp (correction p w)) 1
    exact (analyticAt_const.sub analyticAt_id).mul
      (((differentiable_correction p).analyticAt (1 : ℂ)).cexp)
  apply hf.analyticOrderAt_eq_natCast.mpr
  refine ⟨fun w => -Complex.exp (correction p w), ?_, ?_, ?_⟩
  · exact (((differentiable_correction p).analyticAt (1 : ℂ)).cexp).neg
  · exact neg_ne_zero.mpr (Complex.exp_ne_zero _)
  · filter_upwards [] with w
    change (1-w) * Complex.exp (correction p w) = (w-1)^1 • -Complex.exp (correction p w)
    simp only [pow_one, smul_eq_mul]
    ring

private lemma tail_hasSum (p : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => w ^ (n + p + 1) / (n + p + 1 : ℂ))
      (-Complex.log (1-w) - correction p w) := by
  have h := Complex.hasSum_taylorSeries_neg_log' hw
  have h' : HasSum (fun n : ℕ => w ^ (n+1) / (n+1 : ℂ))
      ((-Complex.log (1-w) - correction p w) +
        ∑ k ∈ Finset.range p, w ^ (k+1) / (k+1 : ℂ)) := by
    convert h using 1
    unfold correction
    ring
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using (hasSum_nat_add_iff p).mpr h'

theorem logFactor_eq_log_add : ∀ (p : ℕ) (w : ℂ), ‖w‖ < 1 →
    logFactor p w = Complex.log (1 - w) + correction p w := by
  intro p w hw
  change -(∑' n : ℕ, w ^ (n+p+1) / (n+p+1 : ℂ)) = _
  rw [(tail_hasSum p hw).tsum_eq]
  ring

theorem logFactor_hasSum : ∀ (p : ℕ) (w : ℂ), ‖w‖ < 1 →
    HasSum (fun n : ℕ => -(w ^ (n+p+1) / (n+p+1 : ℂ))) (logFactor p w) := by
  intro p w hw
  rw [logFactor_eq_log_add p w hw]
  convert (tail_hasSum p hw).neg using 1; ring

theorem logFactor_holomorphic : ∀ p : ℕ,
    HolomorphicOn (Metric.ball 0 1) (logFactor p) := by
  intro p
  refine ⟨Metric.isOpen_ball, fun w hw => ?_⟩
  have hw' : ‖w‖ < 1 := by simpa using hw
  have hslit : 1-w ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using
      Complex.mem_slitPlane_of_norm_lt_one (by simpa using hw' : ‖-w‖ < 1)
  have hd : DifferentiableAt ℂ (fun z => Complex.log (1-z) + correction p z) w :=
    ((Complex.differentiableAt_log hslit).comp w
      ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)).add (differentiable_correction p w)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Metric.isOpen_ball.mem_nhds hw] with z hz
  exact logFactor_eq_log_add p z (by simpa using hz)

theorem logFactor_zero : ∀ p : ℕ, logFactor p 0 = 0 := by
  intro p
  rw [logFactor_eq_log_add p 0 (by simp)]
  simp [correction]

theorem exp_logFactor : ∀ (p : ℕ) (w : ℂ), ‖w‖ < 1 →
    Complex.exp (logFactor p w) = factor p w := by
  intro p w hw
  have hne : 1-w ≠ 0 := by
    intro h
    have : w = 1 := (sub_eq_zero.mp h).symm
    simp [this] at hw
  rw [logFactor_eq_log_add p w hw, Complex.exp_add, Complex.exp_log hne]
  rfl

private lemma logTaylor_neg (p : ℕ) (w : ℂ) :
    Complex.logTaylor (p+1) (-w) = -correction p w := by
  induction p with
  | zero => simp [Complex.logTaylor, correction]
  | succ p ih =>
    rw [Complex.logTaylor_succ]
    change Complex.logTaylor (p+1) (-w) + _ = _
    rw [ih]
    have he : (-1 : ℂ) ^ (p+1+1) * (-w) ^ (p+1) = - w ^ (p+1) := by
      rw [pow_succ, mul_comm _ (-1), mul_assoc, ← mul_pow]
      simp
    simp only [he]
    simp only [correction, Finset.sum_range_succ]
    push_cast
    ring

theorem norm_logFactor_le : ∀ (p : ℕ) (w : ℂ), ‖w‖ ≤ 1 / 2 →
    ‖logFactor p w‖ ≤ 2 * ‖w‖ ^ (p+1) := by
  intro p w hw
  have hw' : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hb := Complex.norm_log_sub_logTaylor_le p (z := -w) (by simpa using hw')
  rw [logTaylor_neg, sub_neg_eq_add, ← sub_eq_add_neg, ← logFactor_eq_log_add p w hw'] at hb
  simp only [norm_neg] at hb
  have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
    apply (inv_le_comm₀ (by linarith : 0 < 1 - ‖w‖) (by norm_num : (0 : ℝ) < 2)).mpr
    norm_num
    linarith
  have hp : (1 : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast Nat.le_add_left 1 p
  calc
    ‖logFactor p w‖ ≤ ‖w‖ ^ (p+1) * (1-‖w‖)⁻¹ / (p+1) := hb
    _ ≤ ‖w‖ ^ (p+1) * (1-‖w‖)⁻¹ := div_le_self (by positivity) hp
    _ ≤ 2 * ‖w‖ ^ (p+1) := by nlinarith [pow_nonneg (norm_nonneg w) (p+1)]

theorem norm_factor_sub_one_le : ∀ (p : ℕ) (w : ℂ), ‖w‖ ≤ 1 / 2 →
    ‖factor p w - 1‖ ≤ 6 * ‖w‖ ^ (p+1) := by
  intro p w hw
  have hlog := norm_logFactor_le p w hw
  have hp : ‖w‖ ^ (p+1) ≤ ‖w‖ := by
    exact pow_le_of_le_one (norm_nonneg w) (by linarith) (by omega)
  have hl : ‖logFactor p w‖ ≤ 1 := by linarith
  rw [← exp_logFactor p w (lt_of_le_of_lt hw (by norm_num))]
  have h := Complex.norm_exp_sub_one_le hl
  nlinarith [pow_nonneg (norm_nonneg w) (p+1)]

end D12Complex.CanonicalFactors
