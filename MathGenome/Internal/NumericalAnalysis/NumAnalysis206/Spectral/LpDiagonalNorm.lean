import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.LpDiagonalNorm
import Mathlib.Tactic.GCongr

noncomputable section
open scoped NNReal BigOperators ENNReal
namespace NumAnalysis206.LpDiagonalNorm

/-- Coordinatewise domination of moduli implies domination in every finite ℓ_p norm. -/
lemma piLp_norm_mono {ι K : Type*} [Fintype ι] [RCLike K]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (x y : PiLp p (fun _ : ι => K))
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases p.dichotomy with (rfl | hp)
  · rw [← PiLp.norm_ofLp, ← PiLp.norm_ofLp]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i =>
      (h i).trans (norm_le_pi_norm (WithLp.ofLp y) i)
  · rw [PiLp.norm_eq_sum (zero_lt_one.trans_le hp),
      PiLp.norm_eq_sum (zero_lt_one.trans_le hp)]
    gcongr with i
    exact h i

/-- The diagonal operator norm on finite ℓ_p is the sup norm of the diagonal. -/
lemma norm_toLpLin_diagonal {ι K : Type*} [Fintype ι] [DecidableEq ι] [RCLike K]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (d : ι → K) :
    ‖(Matrix.toLpLin p p (Matrix.diagonal d)).toContinuousLinearMap‖ = ‖d‖ := by
  let T := (Matrix.toLpLin p p (Matrix.diagonal d)).toContinuousLinearMap
  have hT (x : PiLp p (fun _ : ι => K)) (i : ι) : T x i = d i * x i := by
    simp [T, Matrix.toLpLin_apply, Matrix.mulVec_diagonal]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg d)
    intro x
    calc
      ‖T x‖ ≤ ‖(‖d‖ : ℝ) • x‖ := piLp_norm_mono _ _ fun i => by
        rw [hT, norm_mul, PiLp.smul_apply, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg d)]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm d i) (norm_nonneg _)
      _ = ‖d‖ * ‖x‖ := by simp [norm_smul]
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg T)).mpr
    intro i
    have h := T.le_opNorm (PiLp.single p i (1 : K))
    have hi := PiLp.norm_apply_le (T (PiLp.single p i (1 : K))) i
    simpa [hT, PiLp.norm_single] using hi.trans h

/-- W39: all exponents 1 ≤ p ≤ ∞, with maximum zero in dimension zero. -/
theorem diagonal_norm : Specs.NumAnalysis206.LpDiagonalNorm.diagonal_norm := by
  intro K _ n p hp d
  haveI : Fact (1 ≤ p) := ⟨hp⟩
  change ‖(Matrix.toLpLin p p (Matrix.diagonal d)).toContinuousLinearMap‖ = _
  rw [norm_toLpLin_diagonal]
  exact congrArg (fun a : ℝ≥0 => (a : ℝ)) (Pi.nnnorm_def d)

end NumAnalysis206.LpDiagonalNorm
