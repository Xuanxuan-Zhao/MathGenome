import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.MatrixLyapunov
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.SpectralDecay
import MathGenome.Internal.ODEDynamics.D13Unified.Ch07.ExponentialCalculus
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section
open Filter MeasureTheory Set
open scoped Topology Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

namespace D13Unified.Ch12
open D13Unified.Ch07
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma hurwitz_spectral_gap (A : Matrix n n ℝ) (hA : IsHurwitz A) :
    ∃ b : ℝ, 0 < b ∧ ∀ μ : ℂ,
      Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' (A.map Complex.ofReal)) μ →
        μ.re + b < 0 := by
  have aux : ∀ s : Finset ℂ, (∀ μ ∈ s, μ.re < 0) →
      ∃ b : ℝ, 0 < b ∧ ∀ μ ∈ s, μ.re + b < 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨1, zero_lt_one, by simp⟩
    | @insert μ s hnot ih =>
      intro h
      obtain ⟨b, hb, hs⟩ := ih (fun z hz => h z (Finset.mem_insert_of_mem hz))
      refine ⟨min b (-μ.re / 2), lt_min hb (by have := h μ (Finset.mem_insert_self _ _); linarith), ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · have := h z (Finset.mem_insert_self _ _)
        have := min_le_right b (-z.re / 2)
        linarith
      · have := hs z hz
        have := min_le_left b (-μ.re / 2)
        linarith
  let S := (Module.End.finite_hasEigenvalue (Matrix.toLinAlgEquiv' (A.map Complex.ofReal))).toFinset
  obtain ⟨b, hb, h⟩ := aux S (by simpa [S, IsHurwitz] using hA)
  exact ⟨b, hb, by simpa [S] using h⟩

lemma matrixExp_tendsto_zero (A : Matrix n n ℝ) (hA : IsHurwitz A) :
    Tendsto (matrixExp A) atTop (𝓝 0) := by
  simpa using matrixExp_weighted_tendsto_zero_real A 0 (by simpa [IsHurwitz] using hA)

lemma matrixExp_transpose (A : Matrix n n ℝ) (t : ℝ) :
    matrixExp A.transpose t = (matrixExp A t).transpose := by
  simp only [matrixExp, ← Matrix.transpose_smul, Matrix.exp_transpose]

lemma lyapunovIntegrand_eq (A Q : Matrix n n ℝ) (t : ℝ) :
    lyapunovIntegrand A Q t = (matrixExp A t).transpose * Q * matrixExp A t := by
  change matrixExp A.transpose t * Q * matrixExp A t = _
  rw [matrixExp_transpose]

lemma lyapunovIntegrand_continuous (A Q : Matrix n n ℝ) :
    Continuous (lyapunovIntegrand A Q) := by
  exact ((matrixExp_smooth A.transpose).continuous.mul continuous_const).mul
    (matrixExp_smooth A).continuous

lemma lyapunovIntegrand_tendsto_zero (A Q : Matrix n n ℝ) (hA : IsHurwitz A) :
    Tendsto (lyapunovIntegrand A Q) atTop (𝓝 0) := by
  change Tendsto (fun t => lyapunovIntegrand A Q t) atTop (𝓝 0)
  simp_rw [lyapunovIntegrand_eq]
  have h := matrixExp_tendsto_zero A hA
  have ht := (continuous_id.matrix_transpose.tendsto (0 : Matrix n n ℝ)).comp h
  simpa only [Function.comp_def, id_eq, lyapunovIntegrand_eq, Matrix.transpose_zero, zero_mul, mul_zero] using
    (ht.mul_const Q).mul h

lemma lyapunovIntegrand_integrable (A Q : Matrix n n ℝ) (hA : IsHurwitz A) :
    IntegrableOn (lyapunovIntegrand A Q) (Ioi 0) := by
  obtain ⟨b, hb, hspec⟩ := hurwitz_spectral_gap A hA
  have hw := matrixExp_weighted_tendsto_zero_real A b hspec
  have h := matrixExp_tendsto_zero A hA
  have ht := (continuous_id.matrix_transpose.tendsto (0 : Matrix n n ℝ)).comp h
  have hw' : Tendsto (fun t : ℝ => Real.exp (b * t) • lyapunovIntegrand A Q t)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, lyapunovIntegrand_eq, Matrix.transpose_zero, zero_mul, mul_zero,
      Matrix.mul_smul] using (ht.mul_const Q).mul hw
  have hc : Continuous (fun t : ℝ => Real.exp (b * t) • lyapunovIntegrand A Q t) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      (lyapunovIntegrand_continuous A Q)
  obtain ⟨C, hC, hbound⟩ := norm_bounded_on_nonnegative _ hc hw'
  apply Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hb).const_mul C)
    (lyapunovIntegrand_continuous A Q).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hh := hbound t (le_of_lt ht)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hh
  have hcancel : Real.exp (b * t) * Real.exp (-b * t) = 1 := by
    rw [← Real.exp_add]
    rw [show b * t + -b * t = 0 by ring, Real.exp_zero]
  have := mul_le_mul_of_nonneg_right hh (Real.exp_nonneg (-b * t))
  nlinarith [Real.exp_pos (b * t), Real.exp_pos (-b * t), norm_nonneg (lyapunovIntegrand A Q t)]

lemma lyapunovIntegrand_hasDerivAt (A D : Matrix n n ℝ) (t : ℝ) :
    HasDerivAt (lyapunovIntegrand A D)
      (lyapunovIntegrand A (A.transpose * D + D * A) t) t := by
  have h := ((matrixExp_hasDerivAt_right A.transpose t).mul_const D).mul
    (matrixExp_hasDerivAt_left A t)
  convert h using 1 <;> first | rfl |
    simp only [lyapunovIntegrand, Specs.D13Unified.Ch07.MatrixExponential.exponentialValue,
      matrixExp, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

lemma lyapunovIntegrand_hasDerivAt' (A D : Matrix n n ℝ) (t : ℝ) :
    HasDerivAt (lyapunovIntegrand A D)
      (A.transpose * lyapunovIntegrand A D t + lyapunovIntegrand A D t * A) t := by
  have h := ((matrixExp_hasDerivAt_left A.transpose t).mul_const D).mul
    (matrixExp_hasDerivAt_right A t)
  convert h using 1 <;> first | rfl |
    simp only [lyapunovIntegrand, Specs.D13Unified.Ch07.MatrixExponential.exponentialValue,
      matrixExp, Matrix.mul_assoc]

lemma integral_lyapunovOperator (A D : Matrix n n ℝ) (hA : IsHurwitz A) :
    (∫ t : ℝ in Ioi 0, lyapunovIntegrand A (A.transpose * D + D * A) t) = -D := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t (_ : t ∈ Ici (0 : ℝ)) => lyapunovIntegrand_hasDerivAt A D t)
    (lyapunovIntegrand_integrable A _ hA) (lyapunovIntegrand_tendsto_zero A D hA)
  simpa [lyapunovIntegrand, Specs.D13Unified.Ch07.MatrixExponential.exponentialValue] using h

lemma lyapunovIntegral_solves (A Q : Matrix n n ℝ) (hA : IsHurwitz A) :
    A.transpose * lyapunovIntegral A Q + lyapunovIntegral A Q * A = -Q := by
  have hi := lyapunovIntegrand_integrable A Q hA
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t (_ : t ∈ Ici (0 : ℝ)) => lyapunovIntegrand_hasDerivAt' A Q t)
    ((hi.const_mul _).add (hi.mul_const _)) (lyapunovIntegrand_tendsto_zero A Q hA)
  rw [integral_add (hi.const_mul _) (hi.mul_const _),
    integral_const_mul_of_integrable hi, integral_mul_const_of_integrable hi] at h
  simpa [lyapunovIntegral, lyapunovIntegrand, Specs.D13Unified.Ch07.MatrixExponential.exponentialValue] using h

lemma lyapunov_solution_eq_integral (A P Q : Matrix n n ℝ) (hA : IsHurwitz A)
    (hP : A.transpose * P + P * A = -Q) : P = lyapunovIntegral A Q := by
  have h := integral_lyapunovOperator A P hA
  rw [hP] at h
  have hneg : lyapunovIntegrand A (-Q) = fun t => -lyapunovIntegrand A Q t := by
    funext t
    simp [lyapunovIntegrand]
  rw [hneg, integral_neg] at h
  exact neg_injective h.symm

lemma lyapunovIntegral_improper_limit (A Q : Matrix n n ℝ) (hA : IsHurwitz A) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, lyapunovIntegrand A Q t)
      atTop (𝓝 (lyapunovIntegral A Q)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (lyapunovIntegrand_integrable A Q hA) tendsto_id

lemma lyapunovIntegrand_posDef (A Q : Matrix n n ℝ) (hQ : Q.PosDef) (t : ℝ) :
    (lyapunovIntegrand A Q t).PosDef := by
  have hu : IsUnit (matrixExp A t) := Matrix.isUnit_exp _
  have hp := hQ.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hu)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, lyapunovIntegrand_eq] using hp

/-- Evaluation of a real quadratic form, linear in its matrix. -/
def quadraticEvaluation (x : n → ℝ) : Matrix n n ℝ →ₗ[ℝ] ℝ where
  toFun M := x ⬝ᵥ M.mulVec x
  map_add' M N := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' r M := by simp [Matrix.smul_mulVec, dotProduct_smul]

lemma lyapunovIntegral_posDef (A Q : Matrix n n ℝ) (hA : IsHurwitz A) (hQ : Q.PosDef) :
    (lyapunovIntegral A Q).PosDef := by
  let tr : Matrix n n ℝ →L[ℝ] Matrix n n ℝ :=
    (Matrix.transposeLinearEquiv n n ℝ ℝ).toLinearMap.toContinuousLinearMap
  have hi := lyapunovIntegrand_integrable A Q hA
  have hsym : (lyapunovIntegral A Q).transpose = lyapunovIntegral A Q := by
    calc
      _ = ∫ t : ℝ in Ioi 0, (lyapunovIntegrand A Q t).transpose :=
        (tr.integral_comp_comm hi).symm
      _ = lyapunovIntegral A Q := by
        apply integral_congr_ae
        exact ae_of_all _ fun t => by
          simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
            (lyapunovIntegrand_posDef A Q hQ t).isHermitian
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (by simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hsym)
  intro x hx
  let L : Matrix n n ℝ →L[ℝ] ℝ := (quadraticEvaluation x).toContinuousLinearMap
  have hpos (t : ℝ) : 0 < L (lyapunovIntegrand A Q t) := by
    simpa [L, quadraticEvaluation] using (lyapunovIntegrand_posDef A Q hQ t).dotProduct_mulVec_pos hx
  have hint := L.integrable_comp hi
  have hs : Function.support (fun t => L (lyapunovIntegrand A Q t)) = univ :=
    Set.eq_univ_of_forall (fun t => ne_of_gt (hpos t))
  have hp : 0 < ∫ t : ℝ in Ioi 0, L (lyapunovIntegrand A Q t) := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun t => (hpos t).le)) hint).mpr
    simp [hs]
  rw [L.integral_comp_comm hi] at hp
  simpa [L, quadraticEvaluation, lyapunovIntegral] using hp

omit [DecidableEq n] in
lemma symmetric_dotProduct (P : Matrix n n ℝ) (hP : P.transpose = P) (x y : n → ℝ) :
    x ⬝ᵥ P.mulVec y = y ⬝ᵥ P.mulVec x := by
  calc
    _ = x ⬝ᵥ P.transpose.mulVec y := by rw [hP]
    _ = _ := Matrix.dotProduct_transpose_mulVec P x y

lemma quadratic_lyapunovOperator (A P : Matrix n n ℝ) (hP : P.transpose = P)
    (x : n → ℝ) :
    x ⬝ᵥ (A.transpose * P + P * A).mulVec x =
      2 * (x ⬝ᵥ P.mulVec (A.mulVec x)) := by
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add,
    Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm (P.mulVec x) (A.mulVec x), symmetric_dotProduct P hP (A.mulVec x) x]
  ring

/-- A single positive definite solution forces every complex eigenvalue to
have negative real part. The proof splits a complex eigenvector into real
and imaginary parts, so it needs no additional complex positivity assumption. -/
theorem matrix_lyapunov_converse :
    Specs.D13Unified.Ch12.MatrixLyapunov.converseType := by
  intro n _ _ A P Q hP hQ heq μ hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have he := hv.apply_eq_smul
  change (A.map Complex.ofReal).mulVec v = μ • v at he
  let u : n → ℝ := fun j => (v j).re
  let w : n → ℝ := fun j => (v j).im
  have hre : A.mulVec u = μ.re • u - μ.im • w := by
    ext j
    have hj := congrArg (fun z : n → ℂ => (z j).re) he
    simpa [Matrix.mulVec, dotProduct, Complex.mul_re, u, w, smul_eq_mul] using hj
  have him : A.mulVec w = μ.im • u + μ.re • w := by
    ext j
    have hj := congrArg (fun z : n → ℂ => (z j).im) he
    simpa [Matrix.mulVec, dotProduct, Complex.mul_im, u, w, smul_eq_mul, add_comm] using hj
  have hsym : P.transpose = P := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hP.isHermitian
  have hnonneg (M : Matrix n n ℝ) (hM : M.PosDef) (x : n → ℝ) :
      0 ≤ x ⬝ᵥ M.mulVec x := by
    simpa only [star_trivial] using hM.posSemidef.dotProduct_mulVec_nonneg x
  have hpos : 0 < u ⬝ᵥ Q.mulVec u + w ⬝ᵥ Q.mulVec w := by
    by_cases hu : u = 0
    · have hw : w ≠ 0 := by
        intro hw
        apply hv.2
        ext j
        apply Complex.ext
        · exact congrFun hu j
        · exact congrFun hw j
      have hp := hQ.dotProduct_mulVec_pos hw
      simpa only [hu, Matrix.mulVec_zero, dotProduct_zero, zero_add, star_trivial] using hp
    · have hp : 0 < u ⬝ᵥ Q.mulVec u := by
        simpa only [star_trivial] using hQ.dotProduct_mulVec_pos hu
      exact add_pos_of_pos_of_nonneg hp (hnonneg Q hQ w)
  have hident : 2 * μ.re * (u ⬝ᵥ P.mulVec u + w ⬝ᵥ P.mulVec w) =
      -(u ⬝ᵥ Q.mulVec u + w ⬝ᵥ Q.mulVec w) := by
    have hu := quadratic_lyapunovOperator A P hsym u
    have hw := quadratic_lyapunovOperator A P hsym w
    rw [heq, hre] at hu
    rw [heq, him] at hw
    simp only [Matrix.neg_mulVec, dotProduct_neg, Matrix.mulVec_sub, Matrix.mulVec_add,
      Matrix.mulVec_smul, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul] at hu hw
    rw [symmetric_dotProduct P hsym w u] at hw
    linarith
  by_contra h
  have hnonnegP := add_nonneg (hnonneg P hP u) (hnonneg P hP w)
  have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_not_gt h)) hnonnegP
  linarith

/-- Full spectral characterization, for every prescribed real symmetric
positive definite right hand side. -/
theorem matrix_lyapunov_iff :
    Specs.D13Unified.Ch12.MatrixLyapunov.equivalenceType := by
  intro n _ _ A
  constructor
  · intro hA Q hQ
    exact ⟨lyapunovIntegral A Q, lyapunovIntegral_posDef A Q hA hQ,
      lyapunovIntegral_solves A Q hA⟩
  · intro h
    obtain ⟨P, hP, heq⟩ := h 1 Matrix.PosDef.one
    exact matrix_lyapunov_converse A P 1 hP Matrix.PosDef.one heq

/-- Absolute integrability, convergence of the improper integral, symmetry,
strict positive definiteness, the equation, and uniqueness for the same Q. -/
theorem matrix_lyapunov_integral :
    Specs.D13Unified.Ch12.MatrixLyapunov.integralType := by
  intro n _ _ A Q hA hQ
  exact ⟨lyapunovIntegrand_integrable A Q hA, lyapunovIntegral_improper_limit A Q hA,
    lyapunovIntegral_posDef A Q hA hQ, lyapunovIntegral_solves A Q hA,
    fun P hP => lyapunov_solution_eq_integral A P Q hA hP⟩

end D13Unified.Ch12
