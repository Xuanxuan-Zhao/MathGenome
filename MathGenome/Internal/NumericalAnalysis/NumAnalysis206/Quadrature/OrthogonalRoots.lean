import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.OrthogonalRoots
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Quadrature.OrthogonalPolynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators

namespace NumAnalysis206.Quadrature

/-- A continuous nonnegative integrand with zero integral vanishes on the support.
Nonnegativity is needed only on the support. -/
lemma polynomial_zero_on_support_of_integral_zero (μ : Measure ℝ)
    (f : ℝ[X]) (hi : Integrable (fun x => f.eval x) μ)
    (hn : ∀ x ∈ μ.support, 0 ≤ f.eval x) (hz : (∫ x, f.eval x ∂μ) = 0) :
    ∀ x ∈ μ.support, f.eval x = 0 := by
  have hnae : 0 ≤ᵐ[μ] (fun x => f.eval x) := by
    filter_upwards [μ.support_mem_ae] with x hx
    exact hn x hx
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnae hi).mp hz
  exact μ.support_subset_of_isClosed (isClosed_eq f.continuous continuous_const) hae

/-- A nonzero polynomial of degree at most n cannot vanish on the support. -/
lemma polynomial_not_zero_on_support (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    (q : ℝ[X]) (hq : q ≠ 0) (hd : q.natDegree ≤ n) :
    ¬ (∀ x ∈ μ.support, q.eval x = 0) := by
  intro hz
  exact (ne_of_gt (polynomial_square_positive μ n hm hG q hq hd))
    ((square_integral_zero_iff μ n hm q hd).mpr hz)

/-- Orthogonality excludes a strictly positive factor of positive degree. -/
lemma orthogonal_no_positive_factor (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    (p : ℝ[X]) (hp : IsMonicOrthogonal μ n p)
    (f q : ℝ[X]) (hfac : p = f * q) (hf : 0 < f.natDegree)
    (hpos : ∀ x : ℝ, 0 < f.eval x) : False := by
  have hp0 := hp.1.ne_zero
  have hf0 : f ≠ 0 := by intro h; simp [h] at hf
  have hq0 : q ≠ 0 := by intro h; simp [hfac, h] at hp0
  have hd : f.natDegree + q.natDegree = n := by
    rw [← natDegree_mul hf0 hq0, ← hfac, hp.2.1]
  have hqn : q.natDegree < n := by omega
  have hqd : q.degree < n := (natDegree_lt_iff_degree_lt hq0).mp hqn
  have hi := polynomial_products μ n hm p q (by rw [hp.2.1]; omega)
  have hz := polynomial_zero_on_support_of_integral_zero μ (p * q)
    (by simpa only [eval_mul] using hi) (by
      intro x hx
      rw [eval_mul, hfac, eval_mul]
      nlinarith [sq_nonneg (q.eval x), hpos x])
    (by simpa only [eval_mul] using hp.2.2 q hqd)
  apply polynomial_not_zero_on_support μ n hm hG q hq0 (by omega)
  intro x hx
  have he := hz x hx
  rw [eval_mul, hfac, eval_mul] at he
  rcases mul_eq_zero.mp he with he | he
  · exact (mul_eq_zero.mp he).resolve_left (ne_of_gt (hpos x))
  · exact he

/-- Every complex root is real: a conjugate pair would supply a strictly
positive real quadratic factor. -/
lemma orthogonal_complex_root_real (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    (p : ℝ[X]) (hp : IsMonicOrthogonal μ n p)
    (z : ℂ) (hz : aeval z p = 0) : z.im = 0 := by
  by_contra him
  obtain ⟨q, hq⟩ := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz him
  apply orthogonal_no_positive_factor μ n hm hG p hp
    (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2)) q hq
  · have he : (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : ℝ[X]) =
        C 1 * X ^ 2 + C (-(2 * z.re)) * X + C (‖z‖ ^ 2) := by
      simp only [C_1, one_mul, map_neg]
      ring
    rw [he, natDegree_quadratic (by norm_num : (1 : ℝ) ≠ 0)]
    norm_num
  · intro x
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
    have hn := Complex.sq_norm_sub_sq_re z
    nlinarith [sq_nonneg (x - z.re), sq_pos_of_ne_zero him]

lemma orthogonal_splits (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    (p : ℝ[X]) (hp : IsMonicOrthogonal μ n p) : p.Splits := by
  apply Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ) (IsAlgClosed.splits _)
  intro z hz
  have hz0 : aeval z p = 0 := by
    simpa only [IsRoot.def, eval_map_algebraMap] using
      (mem_roots (map_ne_zero hp.1.ne_zero)).mp hz
  have him := orthogonal_complex_root_real μ n hm hG p hp z hz0
  exact ⟨z.re, by simpa only [Complex.coe_algebraMap] using
    (Complex.ext (by simp) (by simpa using him.symm) : (z.re : ℂ) = z)⟩

/-- A repeated real factor contradicts positivity of the square of the
polynomial obtained by removing one copy. -/
lemma orthogonal_no_square_factor (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    (p : ℝ[X]) (hp : IsMonicOrthogonal μ n p) (a : ℝ) :
    ¬ ((X - C a) ^ 2 ∣ p) := by
  rintro ⟨q, hq⟩
  have hf0 : (X - C a : ℝ[X]) ≠ 0 := (monic_X_sub_C a).ne_zero
  have hq0 : q ≠ 0 := by
    intro hz
    exact hp.1.ne_zero (by simp [hq, hz])
  have hd : 2 + q.natDegree = n := by
    rw [← hp.2.1, hq, natDegree_mul (pow_ne_zero 2 hf0) hq0,
      natDegree_pow, natDegree_X_sub_C]
  have hqn : q.degree < n := (natDegree_lt_iff_degree_lt hq0).mp (by omega)
  let r : ℝ[X] := (X - C a) * q
  have hr0 : r ≠ 0 := mul_ne_zero hf0 hq0
  have hrd : r.natDegree ≤ n := by
    dsimp [r]
    rw [natDegree_mul hf0 hq0, natDegree_X_sub_C]
    omega
  have hz : (∫ x : ℝ, (r.eval x) ^ 2 ∂μ) = 0 := by
    convert hp.2.2 q hqn using 1
    congr 1
    funext x
    simp only [r, hq, eval_mul, eval_pow]
    ring
  exact (ne_of_gt (polynomial_square_positive μ n hm hG r hr0 hrd)) hz

lemma orthogonal_rootMultiplicity (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    (p : ℝ[X]) (hp : IsMonicOrthogonal μ n p) (a : ℝ) (ha : p.IsRoot a) :
    p.rootMultiplicity a = 1 := by
  have hpos := (rootMultiplicity_pos hp.1.ne_zero).mpr ha
  have hlt : p.rootMultiplicity a < 2 := by
    by_contra h
    exact orthogonal_no_square_factor μ n hm hG p hp a
      ((le_rootMultiplicity_iff hp.1.ne_zero).mp (by omega))
  omega

lemma orthogonal_roots_nodup (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    (p : ℝ[X]) (hp : IsMonicOrthogonal μ n p) : p.roots.Nodup := by
  classical
  apply Multiset.nodup_iff_count_le_one.mpr
  intro a
  by_cases ha : a ∈ p.roots
  · rw [count_roots, orthogonal_rootMultiplicity μ n hm hG p hp a
      ((mem_roots hp.1.ne_zero).mp ha)]
  · simp [Multiset.count_eq_zero_of_notMem ha]

/-- More generally no nonconstant divisor may have a fixed weak sign on the
support. The zeros at endpoints cause no difficulty. -/
lemma orthogonal_no_nonnegative_factor (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    (p : ℝ[X]) (hp : IsMonicOrthogonal μ n p)
    (f q : ℝ[X]) (hfac : p = f * q) (hf : 0 < f.natDegree)
    (hpos : ∀ x ∈ μ.support, 0 ≤ f.eval x) : False := by
  have hp0 := hp.1.ne_zero
  have hf0 : f ≠ 0 := by intro h; simp [h] at hf
  have hq0 : q ≠ 0 := by intro h; simp [hfac, h] at hp0
  have hd : f.natDegree + q.natDegree = n := by
    rw [← natDegree_mul hf0 hq0, ← hfac, hp.2.1]
  have hqn : q.natDegree < n := by omega
  have hqd : q.degree < n := (natDegree_lt_iff_degree_lt hq0).mp hqn
  have hi := polynomial_products μ n hm p q (by rw [hp.2.1]; omega)
  have hz := polynomial_zero_on_support_of_integral_zero μ (p * q)
    (by simpa only [eval_mul] using hi) (by
      intro x hx
      rw [eval_mul, hfac, eval_mul]
      nlinarith [sq_nonneg (q.eval x), hpos x hx])
    (by simpa only [eval_mul] using hp.2.2 q hqd)
  apply polynomial_not_zero_on_support μ n hm hG p hp0 hp.2.1.le
  intro x hx
  have he := hz x hx
  rw [eval_mul] at he
  rcases mul_eq_zero.mp he with he | he
  · exact he
  · simp [hfac, eval_mul, he]

lemma orthogonal_root_location (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) (hm : FiniteMoment μ (2 * n)) (hG : (gramMatrix μ n).PosDef)
    (p : ℝ[X]) (hp : IsMonicOrthogonal μ n p) (a : ℝ) (ha : p.IsRoot a) :
    ∃ l ∈ μ.support, ∃ r ∈ μ.support, l < a ∧ a < r := by
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot.mpr ha)
  have hl : ∃ l ∈ μ.support, l < a := by
    by_contra h
    push Not at h
    apply orthogonal_no_nonnegative_factor μ n hm hG p hp (X - C a) q hq
    · simp only [natDegree_X_sub_C]; omega
    · intro x hx
      simpa only [eval_sub, eval_X, eval_C, sub_nonneg] using h x hx
  have hr : ∃ r ∈ μ.support, a < r := by
    by_contra h
    push Not at h
    apply orthogonal_no_nonnegative_factor μ n hm hG p hp (-(X - C a)) (-q)
    · simpa only [neg_mul_neg] using hq
    · simp only [natDegree_neg, natDegree_X_sub_C]; omega
    · intro x hx
      simp only [eval_neg, eval_sub, eval_X, eval_C]
      linarith [h x hx]
  obtain ⟨l, hl, hla⟩ := hl
  obtain ⟨r, hr, har⟩ := hr
  exact ⟨l, hl, r, hr, hla, har⟩

theorem orthogonal_roots : Specs.orthogonalRoots := by
  classical
  intro μ _ n _hn hm hG p hp
  have hs := orthogonal_splits μ n hm hG p hp
  have hnd := orthogonal_roots_nodup μ n hm hG p hp
  let s := p.roots.toFinset
  have hcard : s.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, ← hs.natDegree_eq_card_roots, hp.2.1]
  let e : s ≃ Fin n := s.equivFinOfCardEq hcard
  let x : Fin n → ℝ := fun i => (e.symm i).val
  have hroot (i : Fin n) : p.IsRoot (x i) := by
    apply (mem_roots hp.1.ne_zero).mp
    exact Multiset.mem_toFinset.mp (e.symm i).property
  refine ⟨x, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  · calc
      p = (p.roots.map (X - C ·)).prod := hs.eq_prod_roots_of_monic hp.1
      _ = ∏ a ∈ s, (X - C a) := by
        rw [Finset.prod_eq_multiset_prod]
        dsimp [s]
        rw [Multiset.dedup_eq_self.mpr hnd]
      _ = ∏ a : s, (X - C (a.val)) := (Finset.prod_coe_sort s _).symm
      _ = ∏ i : Fin n, (X - C (x i)) := by
        apply Fintype.prod_equiv e
        intro a
        simp only [x, Equiv.symm_apply_apply]
  · intro y
    constructor
    · intro hy
      have hym : y ∈ s := Multiset.mem_toFinset.mpr ((mem_roots hp.1.ne_zero).mpr hy)
      refine ⟨e ⟨y, hym⟩, ?_⟩
      simp only [x, Equiv.symm_apply_apply]
    · rintro ⟨i, rfl⟩
      exact hroot i
  · intro i
    exact orthogonal_rootMultiplicity μ n hm hG p hp (x i) (hroot i)
  · intro i
    exact orthogonal_root_location μ n hm hG p hp (x i) (hroot i)

end NumAnalysis206.Quadrature
