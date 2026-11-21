import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.Jacobi
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Quadrature.Gaussian
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Quadrature.OrthonormalRecurrence

noncomputable section
open MeasureTheory Polynomial Matrix
open scoped BigOperators

namespace NumAnalysis206.Quadrature

def jacobiMatrix : Specs.jacobiMatrixType := Specs.jacobiMatrixValue

def evaluationMatrix : Specs.evaluationMatrixType := @Specs.evaluationMatrixValue

lemma jacobiMatrix_symmetric (μ : Measure ℝ) (n : ℕ) (p : ℕ → ℝ[X]) :
    (jacobiMatrix μ n p)ᵀ = jacobiMatrix μ n p := by
  ext i j
  change (∫ t : ℝ, t * (p i.val).eval t * (p j.val).eval t ∂μ) = _
  congr 1
  funext t
  ring

theorem jacobi_structure : Specs.jacobiStructure := by
  intro μ _ n hn hm hG p hp
  refine ⟨jacobiMatrix_symmetric μ n p, ?_, ?_, ?_⟩
  · intro i j hij
    rcases hij with hij | hij
    · simpa only [Specs.jacobiMatrixValue, eval_mul, eval_X] using
        integral_x_polynomial_far μ hp j.val (by omega) i.val hij
    · change jacobiMatrix μ n p i j = 0
      have hs := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j)
        (jacobiMatrix_symmetric μ n p)
      change jacobiMatrix μ n p j i = jacobiMatrix μ n p i j at hs
      rw [← hs]
      simpa only [jacobiMatrix, Specs.jacobiMatrixValue, eval_mul, eval_X] using
        integral_x_polynomial_far μ hp i.val (by omega) j.val hij
  · intro i
    simpa only [Specs.jacobiMatrixValue, eval_mul, eval_X] using
      integral_x_polynomial_diagonal μ p i.val
  · intro i j hij
    have heq : jacobiMatrix μ n p i j = recurrenceBeta p i.val := by
      change (∫ t : ℝ, t * (p j.val).eval t * (p i.val).eval t ∂μ) = _
      rw [← hij]
      simpa only [eval_mul, eval_X] using
        integral_x_polynomial_top μ n hm hp j.val j.isLt
    refine ⟨heq, ?_⟩
    rw [show Specs.jacobiMatrixValue μ n p i j = jacobiMatrix μ n p i j from rfl, heq]
    exact (three_term_recurrence μ n hn hm hG p hp).2.1 i.val (by omega) (by omega)

/-- Gaussian exactness turns the polynomial inner product into the row inner
product of the evaluation matrix. -/
lemma evaluationMatrix_mul_transpose (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hn : 1 ≤ n) (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    (p : ℕ → ℝ[X]) (hp : IsOrthonormalPolynomialFamily μ n p)
    (π : ℝ[X]) (hπ : IsMonicOrthogonal μ n π)
    (x : Fin n → ℝ) (hx : Function.Injective x) (hr : ∀ i, π.IsRoot (x i)) :
    evaluationMatrix μ p x * (evaluationMatrix μ p x)ᵀ = 1 := by
  classical
  ext j k
  have hw (i : Fin n) : 0 ≤ gaussianWeight μ x i :=
    (gaussian_weights μ n hn hm hG π hπ x hx hr i).2.le
  calc
    _ = ∑ i, gaussianWeight μ x i * (p j.val).eval (x i) * (p k.val).eval (x i) := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (Real.sqrt (gaussianWeight μ x i) * (p j.val).eval (x i)) *
        (Real.sqrt (gaussianWeight μ x i) * (p k.val).eval (x i)) = _
      calc
        _ = Real.sqrt (gaussianWeight μ x i) ^ 2 *
            ((p j.val).eval (x i) * (p k.val).eval (x i)) := by ring
        _ = _ := by rw [Real.sq_sqrt (hw i)]; ring
    _ = ∫ t : ℝ, (p j.val).eval t * (p k.val).eval t ∂μ := by
      have he := gaussian_exactness μ n hn hm π hπ x hx hr (p j.val * p k.val) (by
        have hd := natDegree_mul_le (p := p j.val) (q := p k.val)
        rw [(hp.1 j.val (by omega)).1, (hp.1 k.val (by omega)).1] at hd
        omega)
      simpa only [eval_mul, gaussianWeight, mul_assoc] using he.symm
    _ = _ := by
      simpa only [Matrix.one_apply, Fin.ext_iff] using
        (hp.2 j.val (by omega) k.val (by omega)).2

/-- The entries of the projected multiplication matrix are exactly those of
U diag(x) Uᵀ; the degree needed is only 2n-1. -/
lemma jacobiMatrix_eq_evaluation (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hn : 1 ≤ n) (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    (p : ℕ → ℝ[X]) (hp : IsOrthonormalPolynomialFamily μ n p)
    (π : ℝ[X]) (hπ : IsMonicOrthogonal μ n π)
    (x : Fin n → ℝ) (hx : Function.Injective x) (hr : ∀ i, π.IsRoot (x i)) :
    jacobiMatrix μ n p = evaluationMatrix μ p x * diagonal x * (evaluationMatrix μ p x)ᵀ := by
  classical
  ext i j
  have he := gaussian_exactness μ n hn hm π hπ x hx hr (X * p j.val * p i.val) (by
    have hd := natDegree_mul_le (p := X * p j.val) (q := p i.val)
    have hd' := natDegree_mul_le (p := (X : ℝ[X])) (q := p j.val)
    rw [natDegree_X, (hp.1 j.val (by omega)).1] at hd'
    rw [(hp.1 i.val (by omega)).1] at hd
    omega)
  change (∫ t : ℝ, t * (p j.val).eval t * (p i.val).eval t ∂μ) = _
  simp only [eval_mul, eval_X] at he
  rw [he]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  change Specs.gaussianWeightValue μ x k * (x k * (p j.val).eval (x k) *
    (p i.val).eval (x k)) =
    (Real.sqrt (Specs.gaussianWeightValue μ x k) * (p i.val).eval (x k) * x k) *
    (Real.sqrt (Specs.gaussianWeightValue μ x k) * (p j.val).eval (x k))
  have hs := Real.sq_sqrt (gaussian_weights μ n hn hm hG π hπ x hx hr k).2.le
  calc
    _ = Real.sqrt (Specs.gaussianWeightValue μ x k) ^ 2 *
        (x k * (p j.val).eval (x k) * (p i.val).eval (x k)) := by rw [hs]
    _ = _ := by ring

theorem jacobi_evaluation : Specs.jacobiEvaluation := by
  intro μ _ n hn hm hG p hp π hπ x hx hr
  change evaluationMatrix μ p x * (evaluationMatrix μ p x)ᵀ = 1 ∧
    (evaluationMatrix μ p x)ᵀ * evaluationMatrix μ p x = 1 ∧
    jacobiMatrix μ n p * evaluationMatrix μ p x = evaluationMatrix μ p x * diagonal x
  have hU := evaluationMatrix_mul_transpose μ n hn hm hG p hp π hπ x hx hr
  have hU' := mul_eq_one_comm.mp hU
  refine ⟨hU, hU', ?_⟩
  rw [jacobiMatrix_eq_evaluation μ n hn hm hG p hp π hπ x hx hr]
  simp only [Matrix.mul_assoc, hU', Matrix.mul_one]

/-- Coordinates in an orthogonal eigenbasis satisfy the diagonal eigen-equation. -/
lemma orthogonal_eigen_coordinates {n : ℕ} (J U : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (hU : U * Uᵀ = 1) (hJU : J * U = U * diagonal x)
    (a : ℝ) (v : Fin n → ℝ) (hv : J *ᵥ v = a • v) :
    diagonal x *ᵥ (Uᵀ *ᵥ v) = a • (Uᵀ *ᵥ v) := by
  have hU' : Uᵀ * U = 1 := mul_eq_one_comm.mp hU
  have hrec : U *ᵥ (Uᵀ *ᵥ v) = v := by rw [mulVec_mulVec, hU, one_mulVec]
  have he : U *ᵥ (diagonal x *ᵥ (Uᵀ *ᵥ v)) = a • v := by
    rw [mulVec_mulVec, ← hJU, ← mulVec_mulVec, hrec, hv]
  have he' := congrArg (fun z => Uᵀ *ᵥ z) he
  rw [mulVec_mulVec _ Uᵀ U, hU', one_mulVec, mulVec_smul] at he'
  exact he'

/-- For distinct diagonal entries, each eigenspace consists of scalar multiples
of the corresponding orthogonal column. -/
lemma orthogonal_eigenvector_column {n : ℕ} (J U : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : Function.Injective x)
    (hU : U * Uᵀ = 1) (hJU : J * U = U * diagonal x)
    (i : Fin n) (v : Fin n → ℝ) (hv : J *ᵥ v = x i • v) :
    ∃ c : ℝ, v = c • (fun j => U j i) := by
  classical
  let c := Uᵀ *ᵥ v
  have hc := orthogonal_eigen_coordinates J U x hU hJU (x i) v hv
  have hzero (j : Fin n) (hj : j ≠ i) : c j = 0 := by
    have he := congrFun hc j
    simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at he
    change x j * c j = x i * c j at he
    apply (mul_eq_zero.mp (show (x j - x i) * c j = 0 by nlinarith)).resolve_left
    exact sub_ne_zero.mpr (fun h => hj (hx h))
  refine ⟨c i, ?_⟩
  have hrec : U *ᵥ c = v := by
    dsimp only [c]
    rw [mulVec_mulVec, hU, one_mulVec]
  rw [← hrec]
  ext j
  change (∑ k, U j k * c k) = c i * U j i
  rw [Finset.sum_eq_single i]
  · ring
  · intro k _ hki
    rw [hzero k hki, mul_zero]
  · simp

theorem jacobi_eigenvalues : Specs.jacobiEigenvalues := by
  intro μ _ n hn hm hG p hp π hπ x hx hr a
  obtain ⟨hU, hU', hJU⟩ := jacobi_evaluation μ n hn hm hG p hp π hπ x hx hr
  let U := evaluationMatrix μ p x
  change U * Uᵀ = 1 at hU
  change Uᵀ * U = 1 at hU'
  change jacobiMatrix μ n p * U = U * diagonal x at hJU
  change (∃ v : Fin n → ℝ, v ≠ 0 ∧ jacobiMatrix μ n p *ᵥ v = a • v) ↔ _
  constructor
  · rintro ⟨v, hv0, hv⟩
    let c := Uᵀ *ᵥ v
    have hc0 : c ≠ 0 := by
      intro hc
      apply hv0
      have hrec : U *ᵥ c = v := by
        dsimp only [c]
        rw [mulVec_mulVec, hU, one_mulVec]
      rw [← hrec, hc, mulVec_zero]
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := Function.ne_iff.mp hc0
    have he := congrFun (orthogonal_eigen_coordinates (jacobiMatrix μ n p) U x
      hU hJU a v hv) i
    simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at he
    change x i * c i = a * c i at he
    exact ⟨i, (mul_right_cancel₀ hi he)⟩
  · rintro ⟨i, rfl⟩
    refine ⟨fun j => U j i, ?_, ?_⟩
    · intro hz
      have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i i) hU'
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at he
      have hz' : ∀ j, U j i = 0 := fun j => congrFun hz j
      simp only [hz', mul_zero, Finset.sum_const_zero] at he
      norm_num at he
    · funext j
      have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A j i) hJU
      rw [Matrix.mul_apply, Matrix.mul_diagonal] at he
      change (∑ k, jacobiMatrix μ n p j k * U k i) = x i * U j i
      simpa only [mul_comm] using he

/-- The degree-zero orthonormal polynomial is constant, and its square times
the total mass is one. This applies to every family, not just the chosen one. -/
lemma orthonormal_constant_mass {μ : Measure ℝ} [IsFiniteMeasure μ]
    {n : ℕ} {p : ℕ → ℝ[X]} (hp : IsOrthonormalPolynomialFamily μ n p) (t : ℝ) :
    μ.real Set.univ * (p 0).eval t ^ 2 = 1 := by
  have hp0 := eq_C_of_natDegree_eq_zero (hp.1 0 (by omega)).1
  have he := (hp.2 0 (by omega) 0 (by omega)).2
  have hval (x : ℝ) : (p 0).eval x = (p 0).coeff 0 := by
    simpa only [eval_C] using congrArg (fun q : ℝ[X] => q.eval x) hp0
  simpa only [hval, ite_true, integral_const, smul_eq_mul, pow_two] using he

theorem jacobi_weights : Specs.jacobiWeights := by
  intro μ _ n hn hm hG p hp π hπ x hx hr i v hv hvnorm
  let U := evaluationMatrix μ p x
  obtain ⟨hU, hU', hJU⟩ := jacobi_evaluation μ n hn hm hG p hp π hπ x hx hr
  change U * Uᵀ = 1 at hU
  change Uᵀ * U = 1 at hU'
  change jacobiMatrix μ n p * U = U * diagonal x at hJU
  change jacobiMatrix μ n p *ᵥ v = x i • v at hv
  obtain ⟨c, hc⟩ := orthogonal_eigenvector_column (jacobiMatrix μ n p) U x hx hU hJU i v hv
  have hcol : (∑ j, U j i ^ 2) = 1 := by
    have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i i) hU'
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, pow_two] using he
  have hc2 : c ^ 2 = 1 := by
    rw [hc] at hvnorm
    simpa only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, hcol, mul_one]
      using hvnorm
  let z : Fin n := ⟨0, by omega⟩
  have hv0 : v z = c * U z i := by rw [hc]; rfl
  have hs := Real.sq_sqrt (gaussian_weights μ n hn hm hG π hπ x hx hr i).2.le
  have hm0 := orthonormal_constant_mass hp (x i)
  change Specs.gaussianWeightValue μ x i = μ.real Set.univ * |v z| ^ 2
  symm
  calc
    μ.real Set.univ * |v z| ^ 2 = μ.real Set.univ * (c * U z i) ^ 2 := by
      rw [sq_abs, hv0]
    _ = μ.real Set.univ * (U z i) ^ 2 := by rw [mul_pow, hc2, one_mul]
    _ = Specs.gaussianWeightValue μ x i * (μ.real Set.univ * (p 0).eval (x i) ^ 2) := by
      change μ.real Set.univ * (Real.sqrt (Specs.gaussianWeightValue μ x i) *
        (p 0).eval (x i)) ^ 2 = _
      rw [mul_pow, hs]
      ring
    _ = Specs.gaussianWeightValue μ x i := by rw [hm0, mul_one]

theorem jacobi_projection : Specs.jacobiProjection := by
  classical
  intro μ _ n hm p hp c i
  calc
    _ = ∫ t : ℝ, ∑ j : Fin n,
        c j * (t * (p j.val).eval t * (p i.val).eval t) ∂μ := by
      congr 1
      funext t
      simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j : Fin n, c j * ∫ t : ℝ, t * (p j.val).eval t * (p i.val).eval t ∂μ := by
      rw [integral_finsetSum _ (fun j _ =>
        (integrable_x_polynomial_product μ n hm hp j.val j.isLt i.val (by omega)).const_mul (c j))]
      simp only [integral_const_mul]
    _ = _ := by
      change _ = ∑ j : Fin n, (∫ t : ℝ, t * (p j.val).eval t * (p i.val).eval t ∂μ) * c j
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _

/-- The complete computation interface, with all objects obtained from the
moment and Gram hypotheses rather than supplied as existence certificates. -/
theorem jacobi_computation : Specs.jacobiComputation := by
  intro μ _ n hn hm hG
  obtain ⟨p, hp, hp0, hpn⟩ := orthonormal_polynomials_exist μ n hn hm hG
  obtain ⟨π, hπ, _⟩ := orthogonal_polynomial_exists_unique μ n hn hm hG
  obtain ⟨x, hx, _, hroots, _, hloc⟩ := orthogonal_roots μ n hn hm hG π hπ
  have hr (i : Fin n) : π.IsRoot (x i) := (hroots (x i)).mpr ⟨i, rfl⟩
  exact ⟨p, hp, hp0, π, hπ, hpn π hπ, x, hx, hroots, hloc,
    jacobi_evaluation μ n hn hm hG p hp π hπ x hx hr,
    jacobi_eigenvalues μ n hn hm hG p hp π hπ x hx hr,
    jacobi_weights μ n hn hm hG p hp π hπ x hx hr⟩

end NumAnalysis206.Quadrature
