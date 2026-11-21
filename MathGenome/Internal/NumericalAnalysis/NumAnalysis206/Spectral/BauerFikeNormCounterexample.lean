import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.BauerFikeNormCounterexample
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Spectral.BauerFikeResolvent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open NumAnalysis206.BauerFikeExampleData
open scoped Matrix
namespace NumAnalysis206.BauerFikeNormCounterexample

lemma shear_inv (M : ℝ) : (S M)⁻¹ = !![1, -(M : ℂ); 0, 1] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S, Matrix.mul_apply, Fin.sum_univ_two]

lemma shear_unit (M : ℝ) : IsUnit (S M) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  simp [S, Matrix.det_fin_two]

lemma perturbation_entries (M : ℝ) (hM : M ≠ 0) :
    E M = !![-1, -(M : ℂ); (M : ℂ)⁻¹, 1] := by
  have hc : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  rw [E, shear_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, S, Matrix.mul_apply, Fin.sum_univ_two, hc]

lemma conjugate_perturbation (M : ℝ) : S M * E M * (S M)⁻¹ = B M := by
  have h := (Matrix.isUnit_iff_isUnit_det _).mp (shear_unit M)
  calc
    _ = (S M * (S M)⁻¹) * B M * (S M * (S M)⁻¹) := by simp only [E]; noncomm_ring
    _ = B M := by rw [Matrix.mul_nonsing_inv _ h]; simp

lemma basis_coordinates (M : ℝ) (x : X) :
    (basis M).equivFun.symm x = (S M).mulVec x := by
  simp only [basis, Module.Basis.map_equivFun, LinearEquiv.symm_trans_apply]
  ext i
  fin_cases i <;> simp [shear, S, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma coordinate_norm (M : ℝ) (x : X) :
    ‖(basis M).equivFun.symm x‖ = vectorNorm M x := by
  rw [basis_coordinates]
  rfl

lemma represented_apply (M : ℝ) (C : Mat) (x : X) :
    Matrix.toLin (basis M) (basis M) C x =
      (S M * C * (S M)⁻¹).mulVec x := by
  have hcoord (y : X) : (basis M).equivFun y = ((S M)⁻¹).mulVec y := by
    simp only [basis, Module.Basis.map_equivFun, LinearEquiv.trans_apply]
    ext i
    fin_cases i <;> simp [shear, shear_inv, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      sub_eq_add_neg]
  have h := Matrix.repr_toLin (basis M) (basis M) C x
  have heq : Matrix.toLin (basis M) (basis M) C x =
      (basis M).equivFun.symm (C.mulVec ((basis M).equivFun x)) := by
    apply (basis M).equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    exact h
  rw [heq, basis_coordinates, hcoord, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

lemma norm_perturbation (M : ℝ) (hM : 0 < M) : matrixNorm M (E M) = 1 / M := by
  let F := (Matrix.toLin (basis M) (basis M) (E M)).toContinuousLinearMap
  have hF (x : X) : F x = ![0, (M : ℂ)⁻¹ * x 0] := by
    change Matrix.toLin (basis M) (basis M) (E M) x = _
    rw [represented_apply, conjugate_perturbation]
    ext i
    fin_cases i <;> simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hinv : ‖(M : ℂ)⁻¹‖ = 1 / M := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, one_div]
  change ‖F‖ = 1 / M
  apply le_antisymm
  · apply F.opNorm_le_bound (le_of_lt (one_div_pos.mpr hM))
    intro x
    rw [hF]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (le_of_lt (one_div_pos.mpr hM))
      (norm_nonneg x))).mpr
    intro i
    fin_cases i
    · change ‖(0 : ℂ)‖ ≤ _
      rw [norm_zero]
      positivity
    · change ‖(M : ℂ)⁻¹ * x 0‖ ≤ _
      rw [norm_mul, hinv]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x 0)
        (le_of_lt (one_div_pos.mpr hM))
  · have ht := F.le_opNorm (![1, 0] : X)
    have hx : ‖(![1, 0] : X)‖ = 1 := by
      apply le_antisymm
      · exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (by intro i; fin_cases i <;> norm_num)
      · simpa using (norm_le_pi_norm (![1, 0] : X) 0)
    have hy := norm_le_pi_norm (F (![1, 0] : X)) 1
    rw [hF] at hy
    have hy' : 1 / M ≤ ‖F (![1, 0] : X)‖ := by simpa [hF, hinv] using hy
    exact hy'.trans (by simpa [hx] using ht)

lemma norm_identity (M : ℝ) : matrixNorm M (1 : Mat) = 1 := by
  change ‖(Matrix.toLin (basis M) (basis M) 1).toContinuousLinearMap‖ = 1
  rw [Matrix.toLin_one]
  change ‖ContinuousLinearMap.id ℂ X‖ = 1
  exact ContinuousLinearMap.norm_id

lemma spectrum_A : spectrum ℂ A = {0, 1} := by
  ext μ
  simp only [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    not_not, Algebra.algebraMap_eq_smul_one]
  have hd : (μ • (1 : Mat) - A).det = μ * (μ - 1) := by
    simp [A, Matrix.det_fin_two]
  rw [hd]
  simp [mul_eq_zero, sub_eq_zero]

lemma spectrum_perturbed (M : ℝ) (hM : M ≠ 0) :
    spectrum ℂ (A + E M) = {(rootPlus : ℂ), (rootMinus : ℂ)} := by
  have hc : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hs : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  ext μ
  simp only [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    not_not, Algebra.algebraMap_eq_smul_one]
  have hd : (μ • (1 : Mat) - (A + E M)).det = μ ^ 2 - μ - 1 := by
    rw [perturbation_entries M hM]
    simp [A, Matrix.det_fin_two, hc]
    ring
  have hf : μ ^ 2 - μ - 1 =
      (μ - (rootPlus : ℂ)) * (μ - (rootMinus : ℂ)) := by
    unfold rootPlus rootMinus
    push_cast
    linear_combination (1 / 4 : ℂ) * hs
  rw [hd, hf]
  simp [mul_eq_zero, sub_eq_zero]

private lemma infDist_pair {Y : Type*} [PseudoMetricSpace Y] (x a b : Y) :
    Metric.infDist x ({a, b} : Set Y) = min (dist x a) (dist x b) := by
  apply le_antisymm
  · exact le_min (Metric.infDist_le_dist_of_mem (by simp))
      (Metric.infDist_le_dist_of_mem (by simp))
  · apply (Metric.le_infDist (by simp : ({a, b} : Set Y).Nonempty)).mpr
    intro y hy
    rcases (by simpa using hy : y = a ∨ y = b) with rfl | rfl
    · exact min_le_left _ _
    · exact min_le_right _ _

lemma gap_pos : 1 / 2 < gap := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  unfold gap
  nlinarith

lemma distance_roots (μ : ℂ) (hμ : μ = (rootPlus : ℂ) ∨ μ = (rootMinus : ℂ)) :
    Metric.infDist μ (spectrum ℂ A) = gap := by
  have hs : 2 < Real.sqrt 5 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have := Real.sqrt_nonneg (5 : ℝ)
    nlinarith
  have hdr (x y : ℝ) : dist (x : ℂ) (y : ℂ) = |x - y| := by
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [spectrum_A, infDist_pair]
  rcases hμ with rfl | rfl
  · change min (dist (rootPlus : ℂ) ((0 : ℝ) : ℂ))
      (dist (rootPlus : ℂ) ((1 : ℝ) : ℂ)) = _
    rw [hdr, hdr, abs_of_nonneg (by unfold rootPlus; linarith),
      abs_of_nonneg (by unfold rootPlus; linarith), min_eq_right (by linarith)]
    unfold rootPlus gap
    ring
  · change min (dist (rootMinus : ℂ) ((0 : ℝ) : ℂ))
      (dist (rootMinus : ℂ) ((1 : ℝ) : ℂ)) = _
    rw [hdr, hdr, abs_of_nonpos (by unfold rootMinus; linarith),
      abs_of_nonpos (by unfold rootMinus; linarith), min_eq_left (by linarith)]
    unfold rootMinus gap
    ring

/-- The unconditional spectral-distance version fails, while the arbitrary-norm
resolvent inequality applies to both eigenvalues of this same example. -/
theorem counterexample : Specs.NumAnalysis206.BauerFikeNormCounterexample.counterexample := by
  intro M hM
  have hp : 0 < M := lt_trans (by norm_num) hM
  have hn : M ≠ 0 := ne_of_gt hp
  have hnorm := norm_perturbation M hp
  have hcond : matrixNorm M (1 : Mat) * matrixNorm M ((1 : Mat)⁻¹) = 1 := by
    simp [norm_identity]
  refine ⟨shear_unit M, coordinate_norm M, conjugate_perturbation M, hnorm, hcond,
    spectrum_A, spectrum_perturbed M hn, ?_⟩
  intro μ hμ
  have hroots : μ = (rootPlus : ℂ) ∨ μ = (rootMinus : ℂ) := by
    simpa only [spectrum_perturbed M hn, Set.mem_insert_iff, Set.mem_singleton_iff] using hμ
  have hd := distance_roots μ hroots
  have hsmall : 1 / M < gap := by
    have hi : 1 / M < 1 / (2 : ℝ) := one_div_lt_one_div_of_lt (by norm_num) hM
    exact hi.trans gap_pos
  have hout : μ ∉ spectrum ℂ A := by
    intro hin
    have hz := Metric.infDist_zero_of_mem hin
    rw [hd] at hz
    linarith [gap_pos]
  refine ⟨hd, ?_, hout, ?_⟩
  · rw [hcond, one_mul, hnorm, hd]
    exact hsmall
  · have hA : A = (1 : Mat) * Matrix.diagonal (![0, 1] : Fin 2 → ℂ) * (1 : Mat)⁻¹ := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [A]
    have hr := BauerFikeResolvent.resolvent_bound (basis M) A (1 : Mat) (E M)
      (![0, 1] : Fin 2 → ℂ) μ isUnit_one hA hμ hout
    have hdiag : Matrix.diagonal (![0, 1] : Fin 2 → ℂ) = A := by
      simpa using hA.symm
    simpa only [matrixNorm, hdiag, inv_one, one_mul, mul_one] using hr

end NumAnalysis206.BauerFikeNormCounterexample
