import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.MatrixExponential
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.ExponentialCalculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

open scoped Matrix.Norms.Operator ContDiff
open Filter

set_option backward.isDefEq.respectTransparency false

namespace D13Unified.Ch07

variable {𝕂 n : Type*} [RCLike 𝕂] [Fintype n] [DecidableEq n]

theorem matrixExp_locallyUniform (A : Matrix n n 𝕂) :
    TendstoLocallyUniformly
      (fun N : ℕ => fun t : ℝ =>
        ∑ j ∈ Finset.range N, (t ^ j / (Nat.factorial j : ℝ)) • A ^ j)
      (matrixExp A) atTop := by
  change TendstoLocallyUniformly _ (fun t : ℝ => NormedSpace.exp (t • A)) atTop
  have h := (NormedSpace.exp_hasFPowerSeriesOnBall (𝕂 := ℝ)
    (𝔸 := Matrix n n 𝕂)).tendstoLocallyUniformlyOn
  simp only [Metric.eball_top_eq_univ, zero_add, tendstoLocallyUniformlyOn_univ] at h
  have hc := h.comp (fun t : ℝ => t • A) (continuous_id.smul continuous_const)
  simpa only [Function.comp_def, FormalMultilinearSeries.partialSum,
    NormedSpace.expSeries_apply_eq, smul_pow, smul_smul,
    div_eq_mul_inv, mul_comm, matrixExp] using hc

theorem matrixExp_smooth (A : Matrix n n 𝕂) : ContDiff ℝ ∞ (matrixExp A) := by
  have h : AnalyticOnNhd ℝ (NormedSpace.exp : Matrix n n 𝕂 → Matrix n n 𝕂)
      Set.univ := fun x _ => NormedSpace.exp_analytic x
  exact h.contDiff.comp (contDiff_id.smul contDiff_const)

theorem matrixExp_hasDerivAt_left (A : Matrix n n 𝕂) (t : ℝ) :
    HasDerivAt (matrixExp A) (A * matrixExp A t) t :=
  hasDerivAt_exp_smul_const' A t

theorem matrixExp_hasDerivAt_right (A : Matrix n n 𝕂) (t : ℝ) :
    HasDerivAt (matrixExp A) (matrixExp A t * A) t :=
  hasDerivAt_exp_smul_const A t

@[simp] theorem matrixExp_zero (A : Matrix n n 𝕂) : matrixExp A 0 = 1 := by
  simp [matrixExp]

theorem matrixExp_add_time (A : Matrix n n 𝕂) (s t : ℝ) :
    matrixExp A (s + t) = matrixExp A s * matrixExp A t := by
  simp only [matrixExp, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl A).smul_left s).smul_right t)

theorem matrixExp_inv (A : Matrix n n 𝕂) (t : ℝ) :
    (matrixExp A t)⁻¹ = matrixExp A (-t) := by
  simp only [matrixExp, neg_smul, Matrix.nonsing_inv_eq_ringInverse]
  exact Ring.inverse_exp _

theorem matrixExp_add_of_commute (A B : Matrix n n 𝕂) (hAB : A * B = B * A) :
    matrixExp (A + B) 1 = matrixExp A 1 * matrixExp B 1 := by
  simp only [matrixExp, one_smul]
  exact NormedSpace.exp_add_of_commute hAB

/-- Series majorization, allowing the zero ring (whose identity has norm zero). -/
private theorem norm_exp_le_exp_norm {𝔸 : Type*} [NormedRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸] (h1 : ‖(1 : 𝔸)‖ ≤ 1) (x : 𝔸) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  have hscalar : HasSum (fun j : ℕ => ‖x‖ ^ j / (Nat.factorial j : ℝ))
      (Real.exp ‖x‖) := by
    simpa only [Real.exp_eq_exp_ℝ, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  apply (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕂) x).norm_le_of_bounded hscalar
  intro j
  have hpow : ‖x ^ j‖ ≤ ‖x‖ ^ j := by
    cases j with
    | zero => simpa only [pow_zero] using h1
    | succ j => exact norm_pow_le' x (Nat.succ_pos j)
  rw [norm_smul, norm_inv, RCLike.norm_natCast]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr (Nat.cast_nonneg (Nat.factorial j)))

theorem matrixExp_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    [FiniteDimensional 𝕂 E] (b : Module.Basis n 𝕂 E) (A : Matrix n n 𝕂) (t : ℝ) :
    matrixOperatorNorm b (matrixExp A t) ≤
      Real.exp (|t| * matrixOperatorNorm b A) := by
  letI : CompleteSpace E := FiniteDimensional.complete 𝕂 E
  unfold matrixOperatorNorm
  rw [matrixOperator_exp]
  have h1 : ‖(1 : E →L[𝕂] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h := norm_exp_le_exp_norm (𝕂 := 𝕂) h1
    ((algebraMap ℝ 𝕂 t) • matrixOperatorEquiv b A)
  simpa only [norm_smul, norm_algebraMap', Real.norm_eq_abs] using h

end D13Unified.Ch07
