import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.OrthonormalRecurrence
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Quadrature.OrthogonalPolynomial
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators

namespace NumAnalysis206.Quadrature

lemma gram_posDef_of_le (μ : Measure ℝ) {k n : ℕ} (hkn : k ≤ n)
    (hG : (gramMatrix μ n).PosDef) : (gramMatrix μ k).PosDef := by
  let f : Fin (k + 1) → Fin (n + 1) := Fin.castLE (by omega)
  have hf : Function.Injective f := Fin.castLE_injective _
  exact hG.submatrix hf

/-- Degree zero is included, using the monic constant polynomial one. -/
lemma exists_monic_orthogonal_le (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    (k : ℕ) (hk : k ≤ n) : ∃ q : ℝ[X], IsMonicOrthogonal μ k q := by
  by_cases hk0 : k = 0
  · subst k
    refine ⟨1, monic_one, natDegree_one, ?_⟩
    intro q hq
    have : q = 0 := degree_eq_bot.mp (by simpa using hq)
    simp [this]
  · exact exists_monic_orthogonal μ k (by omega)
      ((lower_moments μ n hm (2 * k) (by omega)).1) (gram_posDef_of_le μ hk hG)

lemma normalize_monic_orthogonal (μ : Measure ℝ) [IsFiniteMeasure μ] (n k : ℕ)
    (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef) (hk : k ≤ n)
    {q : ℝ[X]} (hq : IsMonicOrthogonal μ k q) :
    let p := (Real.sqrt (∫ x : ℝ, (q.eval x) ^ 2 ∂μ))⁻¹ • q
    p.natDegree = k ∧ 0 < p.leadingCoeff ∧
      (∀ r : ℝ[X], r.degree < k → ∫ x : ℝ, p.eval x * r.eval x ∂μ = 0) ∧
      (∫ x : ℝ, p.eval x * p.eval x ∂μ) = 1 := by
  dsimp only
  let s := ∫ x : ℝ, (q.eval x) ^ 2 ∂μ
  have hs : 0 < s := polynomial_square_positive μ n hm hG q hq.1.ne_zero
    (hq.2.1.le.trans hk)
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have ht0 : (Real.sqrt s)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt ht)
  refine ⟨by rw [natDegree_smul _ ht0, hq.2.1], ?_, ?_, ?_⟩
  · rw [leadingCoeff_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero ht0),
      hq.1.leadingCoeff, smul_eq_mul, mul_one]
    exact inv_pos.mpr ht
  · intro r hr
    simp only [eval_smul, smul_eq_mul, mul_assoc, integral_const_mul, hq.2.2 r hr,
      mul_zero]
  · calc
      (∫ x : ℝ, ((Real.sqrt s)⁻¹ • q).eval x *
          ((Real.sqrt s)⁻¹ • q).eval x ∂μ) = (Real.sqrt s)⁻¹ ^ 2 * s := by
        rw [← integral_const_mul]
        congr 1
        funext x
        simp only [eval_smul, smul_eq_mul]
        ring
      _ = 1 := by rw [inv_pow, Real.sq_sqrt hs.le, inv_mul_cancel₀ hs.ne']

theorem orthonormal_polynomials_exist : Specs.orthonormalPolynomialsExist := by
  intro μ _ n hn hm hG
  classical
  choose q hq using exists_monic_orthogonal_le μ n hm hG
  let p : ℕ → ℝ[X] := fun k => if hk : k ≤ n then
    (Real.sqrt (∫ x : ℝ, ((q k hk).eval x) ^ 2 ∂μ))⁻¹ • q k hk else X ^ k
  have hp (k : ℕ) (hk : k ≤ n) :
      (p k).natDegree = k ∧ 0 < (p k).leadingCoeff ∧
      (∀ r : ℝ[X], r.degree < k → ∫ x : ℝ, (p k).eval x * r.eval x ∂μ = 0) ∧
      (∫ x : ℝ, (p k).eval x * (p k).eval x ∂μ) = 1 := by
    simpa only [p, dite_eq_left hk] using normalize_monic_orthogonal μ n k hm hG hk (hq k hk)
  refine ⟨p, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro k hk
    exact ⟨(hp k hk).1, (hp k hk).2.1, (hp k hk).2.2.1⟩
  · intro i hi j hj
    refine ⟨polynomial_products μ n hm (p i) (p j) (by
      rw [(hp i hi).1, (hp j hj).1]
      omega), ?_⟩
    split_ifs with hij
    · subst j
      exact (hp i hi).2.2.2
    · rcases lt_or_gt_of_ne hij with hij | hij
      · rw [show (fun x : ℝ => (p i).eval x * (p j).eval x) =
          (fun x : ℝ => (p j).eval x * (p i).eval x) by funext x; ring]
        exact (hp j hj).2.2.1 _ (by
          rw [degree_eq_natDegree (leadingCoeff_ne_zero.mp (ne_of_gt (hp i hi).2.1)),
            (hp i hi).1]
          exact_mod_cast hij)
      · exact (hp i hi).2.2.1 _ (by
          rw [degree_eq_natDegree (leadingCoeff_ne_zero.mp (ne_of_gt (hp j hj).2.1)),
            (hp j hj).1]
          exact_mod_cast hij)
  · have hq0 : q 0 (by omega) = 1 := (hq 0 (by omega)).1.natDegree_eq_zero.mp
      (hq 0 (by omega)).2.1
    simp [p, hq0, smul_eq_C_mul]
  · intro π hπ
    have heq : q n le_rfl = π := monic_orthogonal_unique μ n hm hG (hq n le_rfl) hπ
    simp only [p, dite_eq_left le_rfl, heq]

/-- A triangular family spans each initial polynomial degree space. -/
lemma polynomial_family_expansion {μ : Measure ℝ} {n : ℕ} {p : ℕ → ℝ[X]}
    (hp : IsOrthonormalPolynomialFamily μ n p) (m : ℕ) (hm : m ≤ n)
    (r : ℝ[X]) (hr : r.natDegree ≤ m) :
    ∃ c : Fin (m + 1) → ℝ, ∑ i, c i • p i.val = r := by
  classical
  let S : Polynomial.Sequence ℝ :=
    { elems' := fun k => if k ≤ n then p k else X ^ k
      degree_eq' := by
        intro k
        by_cases hk : k ≤ n
        · simp only [ite_eq_left hk]
          rw [degree_eq_natDegree (leadingCoeff_ne_zero.mp (ne_of_gt (hp.1 k hk).2.1)),
            (hp.1 k hk).1]
        · simp [hk] }
  have hspan : Submodule.span ℝ (Set.range (fun i : Fin (m + 1) => p i.val)) =
      Polynomial.degreeLE ℝ m := by
    rw [← S.span_degreeLE (fun i hi => isUnit_iff_ne_zero.mpr (by
      have hin : i ≤ n := hi.trans hm
      simpa [S, hin] using (ne_of_gt (hp.1 i hin).2.1)))]
    congr 1
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, by simpa using (show i.val ≤ m by omega), by
        simp [S, show i.val ≤ n by omega]⟩
    · rintro ⟨i, hi, rfl⟩
      have him : i ≤ m := hi
      exact ⟨⟨i, by omega⟩, by simp [S, him.trans hm]⟩
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mp
  rw [hspan, Polynomial.mem_degreeLE]
  exact degree_le_of_natDegree_le hr

/-- Integration of finite polynomial expansions, with the degree bound supplying
all integrability obligations. -/
lemma polynomial_integral_sum_left (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hm : FiniteMoment μ (2 * n)) {ι : Type*} [Fintype ι]
    (p : ι → ℝ[X]) (c : ι → ℝ) (q : ℝ[X])
    (hp : ∀ i, (p i).natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (∫ x : ℝ, (∑ i, c i • p i).eval x * q.eval x ∂μ) =
      ∑ i, c i * ∫ x : ℝ, (p i).eval x * q.eval x ∂μ := by
  simp only [eval_finsetSum, eval_smul, smul_eq_mul, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ =>
    (polynomial_products μ n hm (p i) q (by have := hp i; omega)).const_mul (c i))]
  simp only [integral_const_mul]

/-- The coefficients of a triangular orthonormal expansion are its inner products. -/
lemma orthonormal_polynomial_expansion (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hm : FiniteMoment μ (2 * n)) {p : ℕ → ℝ[X]}
    (hp : IsOrthonormalPolynomialFamily μ n p) (m : ℕ) (hmn : m ≤ n)
    (r : ℝ[X]) (hr : r.natDegree ≤ m) :
    ∑ i : Fin (m + 1), (∫ x : ℝ, r.eval x * (p i.val).eval x ∂μ) • p i.val = r := by
  classical
  obtain ⟨c, hc⟩ := polynomial_family_expansion hp m hmn r hr
  have hcoeff (k : Fin (m + 1)) :
      (∫ x : ℝ, r.eval x * (p k.val).eval x ∂μ) = c k := by
    rw [← hc, polynomial_integral_sum_left μ n hm]
    · have horth (i : Fin (m + 1)) :
          (∫ x : ℝ, (p i.val).eval x * (p k.val).eval x ∂μ) =
            if i = k then 1 else 0 := by
        simpa only [Fin.ext_iff] using (hp.2 i.val (by omega) k.val (by omega)).2
      simp [horth]
    · intro i
      rw [(hp.1 _ (by omega)).1]
      omega
    · rw [(hp.1 _ (by omega)).1]
      omega
  simpa only [hcoeff] using hc

/-- Comparing the highest coefficient of an orthonormal expansion. -/
lemma orthonormal_integral_top (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hm : FiniteMoment μ (2 * n)) {p : ℕ → ℝ[X]}
    (hp : IsOrthonormalPolynomialFamily μ n p) (m : ℕ) (hmn : m ≤ n)
    (r : ℝ[X]) (hr : r.natDegree ≤ m) :
    (∫ x : ℝ, r.eval x * (p m).eval x ∂μ) = r.coeff m / (p m).leadingCoeff := by
  classical
  have heq := congrArg (fun q : ℝ[X] => q.coeff m)
    (orthonormal_polynomial_expansion μ n hm hp m hmn r hr)
  have hcoeff (i : Fin (m + 1)) (hi : i ≠ ⟨m, by omega⟩) :
      (p i.val).coeff m = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [(hp.1 _ (by omega)).1]
    have : i.val ≠ m := by simpa [Fin.ext_iff] using hi
    omega
  simp only [finsetSum_coeff, coeff_smul, smul_eq_mul] at heq
  rw [Finset.sum_eq_single ⟨m, by omega⟩] at heq
  · change (∫ x : ℝ, r.eval x * (p m).eval x ∂μ) * (p m).coeff m = r.coeff m at heq
    have hcm := coeff_natDegree (p := p m)
    rw [(hp.1 m hmn).1] at hcm
    rw [hcm] at heq
    exact (eq_div_iff (ne_of_gt (hp.1 m hmn).2.1)).mpr heq
  · intro i _ hi
    rw [hcoeff i hi, mul_zero]
  · simp

lemma integrable_x_polynomial_product (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hm : FiniteMoment μ (2 * n)) {p : ℕ → ℝ[X]}
    (hp : IsOrthonormalPolynomialFamily μ n p) (j : ℕ) (hj : j < n)
    (i : ℕ) (hi : i ≤ n) :
    Integrable (fun x : ℝ => x * (p j).eval x * (p i).eval x) μ := by
  have hint := polynomial_products μ n hm (X * p j) (p i) (by
    have hd := natDegree_mul_le (p := (X : ℝ[X])) (q := p j)
    rw [natDegree_X, (hp.1 j (by omega)).1] at hd
    rw [(hp.1 i hi).1]
    omega)
  change Integrable (fun x : ℝ => (X * p j).eval x * (p i).eval x) μ at hint
  simpa only [eval_mul, eval_X] using hint

lemma integral_x_polynomial_diagonal (μ : Measure ℝ) (p : ℕ → ℝ[X]) (j : ℕ) :
    (∫ x : ℝ, (X * p j).eval x * (p j).eval x ∂μ) = recurrenceAlpha μ p j := by
  unfold recurrenceAlpha
  congr 1
  funext x
  simp only [eval_mul, eval_X]
  ring

lemma integral_x_polynomial_top (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hm : FiniteMoment μ (2 * n)) {p : ℕ → ℝ[X]}
    (hp : IsOrthonormalPolynomialFamily μ n p) (j : ℕ) (hj : j < n) :
    (∫ x : ℝ, (X * p j).eval x * (p (j + 1)).eval x ∂μ) =
      recurrenceBeta p (j + 1) := by
  rw [orthonormal_integral_top μ n hm hp (j + 1) (by omega) _ (by
    have hd := natDegree_mul_le (p := (X : ℝ[X])) (q := p j)
    rw [natDegree_X, (hp.1 j (by omega)).1] at hd
    omega)]
  have hc := coeff_natDegree (p := p j)
  rw [(hp.1 j (by omega)).1] at hc
  simp only [coeff_X_mul, hc, recurrenceBeta, Nat.add_sub_cancel, Nat.add_one_ne_zero,
    ite_false]

lemma integral_x_polynomial_far (μ : Measure ℝ) {n : ℕ} {p : ℕ → ℝ[X]}
    (hp : IsOrthonormalPolynomialFamily μ n p) (j : ℕ) (hj : j ≤ n)
    (i : ℕ) (hij : i + 1 < j) :
    (∫ x : ℝ, (X * p j).eval x * (p i).eval x ∂μ) = 0 := by
  have hi : i ≤ n := by omega
  have hdeg : (X * p i).degree < (j : WithBot ℕ) := by
    have hd := natDegree_mul_le (p := (X : ℝ[X])) (q := p i)
    rw [natDegree_X, (hp.1 i hi).1] at hd
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast (show
      (X * p i).natDegree < j by omega))
  convert (hp.1 j hj).2.2 (X * p i) hdeg using 1
  congr 1
  funext x
  simp only [eval_mul, eval_X]
  ring

lemma integral_x_polynomial_previous (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hm : FiniteMoment μ (2 * n)) {p : ℕ → ℝ[X]}
    (hp : IsOrthonormalPolynomialFamily μ n p) (j : ℕ) (hj : j + 1 ≤ n) :
    (∫ x : ℝ, (X * p (j + 1)).eval x * (p j).eval x ∂μ) =
      recurrenceBeta p (j + 1) := by
  convert integral_x_polynomial_top μ n hm hp j (by omega) using 1
  congr 1
  funext x
  simp only [eval_mul, eval_X]
  ring

theorem three_term_recurrence : Specs.threeTermRecurrence := by
  intro μ _ n hn hm hG p hp
  refine ⟨by simp [recurrenceBeta], ?_, ?_⟩
  · intro k hk hkn
    rw [recurrenceBeta, ite_eq_right (by omega)]
    exact div_pos (hp.1 (k - 1) (by omega)).2.1 (hp.1 k hkn).2.1
  · intro j hj
    refine ⟨?_, fun i hi => integrable_x_polynomial_product μ n hm hp j hj i hi, ?_⟩
    · convert integrable_x_polynomial_product μ n hm hp j hj j (by omega) using 1
      funext x
      ring
    · have hdegree : (X * p j).natDegree ≤ j + 1 := by
        have hd := natDegree_mul_le (p := (X : ℝ[X])) (q := p j)
        rw [natDegree_X, (hp.1 j (by omega)).1] at hd
        omega
      have heq := orthonormal_polynomial_expansion μ n hm hp (j + 1) (by omega)
        (X * p j) hdegree
      cases j with
      | zero =>
        rw [Fin.sum_univ_two] at heq
        simp only [Fin.val_zero, Fin.val_one] at heq
        rw [integral_x_polynomial_diagonal, integral_x_polynomial_top μ n hm hp 0 hj] at heq
        simpa [recurrenceBeta, add_comm] using heq.symm
      | succ k =>
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc,
          Fin.sum_univ_castSucc] at heq
        simp only [Fin.val_castSucc, Fin.val_last] at heq
        have hz : (∑ i : Fin k,
            (∫ x : ℝ, (X * p (k + 1)).eval x * (p i.val).eval x ∂μ) • p i.val) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          rw [integral_x_polynomial_far μ hp (k + 1) (by omega) i.val (by omega), zero_smul]
        rw [hz, zero_add, integral_x_polynomial_previous μ n hm hp k (by omega),
          integral_x_polynomial_diagonal,
          integral_x_polynomial_top μ n hm hp (k + 1) hj] at heq
        simpa only [Nat.succ_eq_add_one, Nat.add_one_ne_zero, ite_false,
          Nat.add_sub_cancel, Nat.reduceAdd, add_comm, add_left_comm, add_assoc] using heq.symm

end NumAnalysis206.Quadrature
