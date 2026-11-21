import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.GramSupport
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Polynomial Matrix
open scoped BigOperators

namespace NumAnalysis206.Quadrature

theorem lower_moments : Specs.lowerMoments := by
  intro μ _ n hm k hk
  have ha : Integrable (fun x : ℝ => |x| ^ k) μ := by
    simpa only [Real.norm_eq_abs] using
      integrable_norm_pow_of_le (μ := μ) (f := fun x : ℝ => x)
        measurable_id.aestronglyMeasurable hk hm
  refine ⟨ha, ?_⟩
  exact (integrable_norm_iff (by fun_prop)).mp (by simpa [Real.norm_eq_abs, abs_pow] using ha)

theorem polynomial_integrable : Specs.polynomialIntegrable := by
  intro μ _ n hm p hp
  rw [p.as_sum_range_C_mul_X_pow]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  apply integrable_finsetSum
  intro k hk
  apply ((lower_moments μ n hm k ?_).2).const_mul
  have := Finset.mem_range.mp hk
  omega

theorem polynomial_products : Specs.polynomialProducts := by
  intro μ _ n hm p q hpq
  simpa only [eval_mul] using polynomial_integrable μ n hm (p * q)
    (natDegree_mul_le.trans hpq)

theorem closed_support : Specs.closedSupport := by
  intro μ
  refine ⟨?_, μ.isClosed_support, μ.measure_compl_support⟩
  intro x
  rw [μ.support_eq_forall_isOpen]
  rfl

/-- Expansion of the polynomial represented by a vector in the monomial basis. -/
lemma eval_ofFn (n : ℕ) (c : Fin (n + 1) → ℝ) (x : ℝ) :
    (Polynomial.ofFn (n + 1) c).eval x = ∑ j, c j * x ^ j.val := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp [eval_finsetSum, eval_monomial]

theorem gram_identity : Specs.gramIdentity := by
  intro μ _ n hm c
  have hi (i j : Fin (n + 1)) :
      Integrable (fun x : ℝ => c i * c j * x ^ (i.val + j.val)) μ :=
    ((lower_moments μ n hm _ (by omega)).2).const_mul _
  calc
    c ⬝ᵥ ((gramMatrix μ n) *ᵥ c) =
        ∑ i, ∑ j, ∫ x : ℝ, c i * c j * x ^ (i.val + j.val) ∂μ := by
      simp only [dotProduct, mulVec, gramMatrix, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
      ring
    _ = ∫ x : ℝ, ∑ i, ∑ j, c i * c j * x ^ (i.val + j.val) ∂μ := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum]
        exact fun j _ => hi i j
      · intro i _
        exact integrable_finsetSum _ fun j _ => hi i j
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, pow_add]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma integrable_square (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hm : FiniteMoment μ (2 * n)) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    Integrable (fun x : ℝ => (p.eval x) ^ 2) μ := by
  simpa only [pow_two] using polynomial_products μ n hm p p (by omega)

/-- For a continuous polynomial, vanishing almost everywhere is the same as
vanishing on the closed support. -/
lemma square_integral_zero_iff (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hm : FiniteMoment μ (2 * n)) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    (∫ x : ℝ, (p.eval x) ^ 2 ∂μ) = 0 ↔ ∀ x ∈ μ.support, p.eval x = 0 := by
  rw [integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (p.eval x))
    (integrable_square μ n hm p hp)]
  constructor
  · intro h
    have hz : ∀ᵐ x ∂μ, p.eval x = 0 := by
      filter_upwards [h] with x hx
      exact sq_eq_zero_iff.mp hx
    exact μ.support_subset_of_isClosed (isClosed_eq p.continuous continuous_const) hz
  · intro h
    filter_upwards [μ.support_mem_ae] with x hx
    simp [h x hx]

lemma square_integral_pos_of_support_points (μ : Measure ℝ) [IsFiniteMeasure μ] (n : ℕ)
    (hm : FiniteMoment μ (2 * n)) (hs : HasSupportPoints μ n)
    (p : ℝ[X]) (hp0 : p ≠ 0) (hp : p.natDegree ≤ n) :
    0 < ∫ x : ℝ, (p.eval x) ^ 2 ∂μ := by
  have hnonneg : 0 ≤ ∫ x : ℝ, (p.eval x) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg (p.eval x))
  apply lt_of_le_of_ne hnonneg
  intro heq
  have hz := (square_integral_zero_iff μ n hm p hp).mp heq.symm
  obtain ⟨s, hs, hcard⟩ := hs
  apply hp0
  exact p.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' s
    (fun x hx => hz x (hs hx)) (by omega)

theorem polynomial_square_positive : Specs.polynomialSquarePositive := by
  intro μ _ n hm hG p hp0 hp
  let c := Polynomial.toFn (n + 1) p
  have hc : Polynomial.ofFn (n + 1) c = p :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have hc0 : c ≠ 0 := by
    intro hzero
    apply hp0
    simpa only [hzero, map_zero] using hc.symm
  have hpos := hG.dotProduct_mulVec_pos hc0
  simp only [star_trivial] at hpos
  rw [gram_identity μ n hm c] at hpos
  simpa only [← eval_ofFn n c, hc] using hpos

/-- Small support supplies an annihilating polynomial, including the empty
product 1 for the zero measure. -/
lemma annihilator_of_not_support_points (μ : Measure ℝ) (n : ℕ)
    (hs : ¬ HasSupportPoints μ n) :
    ∃ p : ℝ[X], p ≠ 0 ∧ p.natDegree ≤ n ∧ ∀ x ∈ μ.support, p.eval x = 0 := by
  classical
  have hfin : μ.support.Finite := by
    by_contra hinf
    exact hs (Set.Infinite.exists_subset_card_eq hinf (n + 1))
  let s := hfin.toFinset
  have hcard : s.card ≤ n := by
    by_contra hlarge
    obtain ⟨t, hts, htcard⟩ := s.exists_subset_card_eq (show n + 1 ≤ s.card by omega)
    apply hs
    refine ⟨t, ?_, htcard⟩
    intro x hx
    exact hfin.mem_toFinset.mp (hts hx)
  refine ⟨∏ a ∈ s, (X - C a), (monic_prod_X_sub_C id s).ne_zero, ?_, ?_⟩
  · simpa only [natDegree_finsetProd_X_sub_C_eq_card] using hcard
  · intro x hx
    simp only [eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (hfin.mem_toFinset.mpr hx) (sub_self x)

theorem gram_support : Specs.gramSupport := by
  intro μ _ n hm
  constructor
  · intro hG
    by_contra hs
    obtain ⟨p, hp0, hp, hz⟩ := annihilator_of_not_support_points μ n hs
    have hpos := polynomial_square_positive μ n hm hG p hp0 hp
    have hzero := (square_integral_zero_iff μ n hm p hp).mpr hz
    exact (ne_of_gt hpos) hzero
  · intro hs
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      simp [gramMatrix, conjTranspose_apply, add_comm]
    · intro c hc
      have hp0 : Polynomial.ofFn (n + 1) c ≠ 0 := by
        intro hz
        apply hc
        apply Polynomial.injective_ofFn (n + 1)
        simpa only [map_zero] using hz
      have hp : (Polynomial.ofFn (n + 1) c).natDegree ≤ n :=
        Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) c)
      have hpos := square_integral_pos_of_support_points μ n hm hs
        (Polynomial.ofFn (n + 1) c) hp0 hp
      simpa only [star_trivial, gram_identity μ n hm c, eval_ofFn] using hpos

end NumAnalysis206.Quadrature
