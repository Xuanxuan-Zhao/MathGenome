import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.OrthogonalPolynomial
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Quadrature.GramSupport
import Mathlib.Algebra.Polynomial.Monic

noncomputable section
open MeasureTheory Polynomial Matrix
open scoped BigOperators

namespace NumAnalysis206.Quadrature

/-- Evaluation of an arbitrary finite coefficient vector, including the empty one. -/
private lemma eval_ofFn_sum (n : ℕ) (a : Fin n → ℝ) (x : ℝ) :
    (Polynomial.ofFn n a).eval x = ∑ j, a j * x ^ j.val := by
  simp [Polynomial.ofFn_eq_sum_monomial, eval_finsetSum, eval_monomial]

/-- Testing against the monomials suffices to test against all smaller polynomials. -/
lemma orthogonal_of_monomials (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hn : 1 ≤ n) (hm : FiniteMoment μ (2 * n)) (p : ℝ[X])
    (hp : p.natDegree ≤ n)
    (h : ∀ i : Fin n, ∫ x : ℝ, p.eval x * x ^ i.val ∂μ = 0) :
    ∀ q : ℝ[X], q.degree < n → ∫ x : ℝ, p.eval x * q.eval x ∂μ = 0 := by
  intro q hq
  have hqn : q.natDegree < n := by
    by_cases hq0 : q = 0
    · simpa [hq0] using (show 0 < n by omega)
    · exact (natDegree_lt_iff_degree_lt hq0).mpr hq
  have hrepr := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hqn
  rw [← hrepr]
  simp only [eval_ofFn_sum, Finset.mul_sum]
  have hi (i : Fin n) : Integrable
      (fun x : ℝ => p.eval x * ((Polynomial.toFn n q) i * x ^ i.val)) μ := by
    have hi := polynomial_products μ n hm p (X ^ i.val) (by
      rw [natDegree_X_pow]
      omega)
    convert hi.const_mul ((Polynomial.toFn n q) i) using 1
    ext x
    simp only [eval_pow, eval_X]
    ring
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_eq_zero
  intro i _
  calc
    (∫ x : ℝ, p.eval x * ((Polynomial.toFn n q) i * x ^ i.val) ∂μ) =
        (Polynomial.toFn n q) i * ∫ x : ℝ, p.eval x * x ^ i.val ∂μ := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    _ = 0 := by rw [h i, mul_zero]

/-- Solve the leading principal Gram system for the lower coefficients. -/
lemma exists_monic_orthogonal (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hn : 1 ≤ n) (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef) :
    ∃ p : ℝ[X], IsMonicOrthogonal μ n p := by
  classical
  let A := (gramMatrix μ n).submatrix Fin.castSucc Fin.castSucc
  have hA : A.PosDef := hG.submatrix (Fin.castSucc_injective n)
  let b : Fin n → ℝ := fun i => ∫ x : ℝ, x ^ (n + i.val) ∂μ
  obtain ⟨a, ha⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hA.isUnit) b
  let r := Polynomial.ofFn n a
  let p : ℝ[X] := X ^ n - r
  have hr : r.natDegree < n := Polynomial.ofFn_natDegree_lt hn a
  have hpm : p.Monic := monic_X_pow_sub (Polynomial.ofFn_degree_lt a)
  have hpn : p.natDegree = n := by
    dsimp [p]
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hr), natDegree_X_pow]
  have hsum (i : Fin n) :
      (∫ x : ℝ, r.eval x * x ^ i.val ∂μ) = (A *ᵥ a) i := by
    have hi (j : Fin n) : Integrable
        (fun x : ℝ => a j * x ^ j.val * x ^ i.val) μ := by
      convert ((lower_moments μ n hm (i.val + j.val) (by omega)).2).const_mul (a j)
        using 1
      ext x
      rw [pow_add]
      ring
    simp only [r, eval_ofFn_sum, Finset.sum_mul]
    rw [integral_finsetSum _ (fun j _ => hi j)]
    simp only [Matrix.mulVec, dotProduct, A, submatrix_apply, gramMatrix,
      Fin.val_castSucc]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm _ (a j), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [pow_add]
    ring
  refine ⟨p, hpm, hpn, orthogonal_of_monomials μ n hn hm p hpn.le ?_⟩
  intro i
  have hi₁ : Integrable (fun x : ℝ => x ^ n * x ^ i.val) μ := by
    simpa only [pow_add] using (lower_moments μ n hm (n + i.val) (by omega)).2
  have hi₂ : Integrable (fun x : ℝ => r.eval x * x ^ i.val) μ := by
    simpa only [eval_pow, eval_X] using
      polynomial_products μ n hm r (X ^ i.val) (by rw [natDegree_X_pow]; omega)
  calc
    (∫ x : ℝ, p.eval x * x ^ i.val ∂μ) =
        (∫ x : ℝ, x ^ n * x ^ i.val - r.eval x * x ^ i.val ∂μ) := by
      congr 1
      funext x
      simp only [p, eval_sub, eval_pow, eval_X]
      ring
    _ = b i - (A *ᵥ a) i := by
      rw [integral_sub hi₁ hi₂, hsum]
      simp only [b, pow_add]
    _ = 0 := by rw [ha, sub_self]

/-- Cancellation of the common leading monomial makes the difference an
admissible orthogonality test; positive definiteness then forces it to vanish. -/
lemma monic_orthogonal_unique (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    {p q : ℝ[X]} (hp : IsMonicOrthogonal μ n p) (hq : IsMonicOrthogonal μ n q) :
    p = q := by
  obtain ⟨hpm, hpn, hpo⟩ := hp
  obtain ⟨hqm, hqn, hqo⟩ := hq
  have hpd : p.degree = n := by rw [degree_eq_natDegree hpm.ne_zero, hpn]
  have hqd : q.degree = n := by rw [degree_eq_natDegree hqm.ne_zero, hqn]
  have hd : (p - q).degree < n := by
    rw [← hpd]
    exact degree_sub_lt_left (hpd.trans hqd.symm) hpm.ne_zero
      (hpm.trans hqm.symm)
  have hdn : (p - q).natDegree ≤ n := by
    exact (natDegree_sub_le p q).trans (by rw [hpn, hqn, max_self])
  have hi₁ := polynomial_products μ n hm p (p - q) (by omega)
  have hi₂ := polynomial_products μ n hm q (p - q) (by omega)
  have hz : (∫ x : ℝ, ((p - q).eval x) ^ 2 ∂μ) = 0 := by
    calc
      _ = ∫ x : ℝ, p.eval x * (p - q).eval x -
          q.eval x * (p - q).eval x ∂μ := by
        congr 1
        funext x
        simp only [eval_sub]
        ring
      _ = 0 := by rw [integral_sub hi₁ hi₂, hpo _ hd, hqo _ hd, sub_self]
  by_contra hne
  have hpos := polynomial_square_positive μ n hm hG (p - q) (sub_ne_zero.mpr hne) hdn
  exact (ne_of_gt hpos) hz

theorem orthogonal_polynomial_exists_unique : Specs.orthogonalPolynomialExistsUnique := by
  intro μ _ n hn hm hG
  obtain ⟨p, hp⟩ := exists_monic_orthogonal μ n hn hm hG
  exact ⟨p, hp, fun q hq => monic_orthogonal_unique μ n hm hG hq hp⟩

end NumAnalysis206.Quadrature
