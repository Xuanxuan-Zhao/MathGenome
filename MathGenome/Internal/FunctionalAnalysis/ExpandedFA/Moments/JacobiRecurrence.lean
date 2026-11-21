import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.JacobiRecurrence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Moments.PolynomialMomentHilbertSpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.DeficiencyHalfPlaneConstancy
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Tactic.NormNum

noncomputable section
open Polynomial Complex
namespace ExpandedFA.Moments
open Unbounded

theorem HankelPositive.nonnegative {m : ℕ → ℝ} (hs : HankelPositive m) :
    HankelNonnegative m := by
  intro p
  by_cases hp : p = 0
  · simp [hp, momentForm]
  · exact (hs p hp).le

/-- Strict positivity makes the polynomial embedding injective. -/
theorem polynomialClass_injective_of_positive (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hs : HankelPositive m) : Function.Injective (polynomialClass m h) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro p hp
  by_contra hn
  have hpos := hs (rawPolynomial p) hn
  have hz : momentForm m p p = 0 := (nullPolynomials_iff m h p).mp hp
  change 0 < (momentForm m p p).re at hpos
  rw [hz] at hpos
  exact (lt_irrefl 0) hpos

/-- The embedded monomials form a linearly independent family in the strictly positive case. -/
theorem moment_monomials_linearIndependent (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hs : HankelPositive m) : LinearIndependent ℂ
      (fun n : ℕ => polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n))) := by
  let b : Module.Basis ℕ ℂ (MomentPolynomials m h) := Polynomial.basisMonomials ℂ
  have hi := b.linearIndependent.map' (polynomialClass m h)
    (LinearMap.ker_eq_bot.mpr (polynomialClass_injective_of_positive m h hs))
  have he : (fun n : ℕ => polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n))) =
      (polynomialClass m h) ∘ b := by
    funext n
    apply congrArg (polynomialClass m h)
    change (X : ℂ[X]) ^ n = (Polynomial.basisMonomials ℂ) n
    rw [Polynomial.coe_basisMonomials]
    exact (Polynomial.monomial_one_right_eq_X_pow n).symm
  rw [he]
  exact hi

/-- The algebraic span of the embedded monomials is exactly the polynomial domain. -/
theorem span_moment_monomials (m : ℕ → ℝ) (h : HankelNonnegative m) :
    Submodule.span ℂ (Set.range (fun n : ℕ =>
      polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n)))) =
      (polynomialClass m h).range := by
  let b : Module.Basis ℕ ℂ (MomentPolynomials m h) := Polynomial.basisMonomials ℂ
  have hb := congrArg (Submodule.map (polynomialClass m h)) b.span_eq
  rw [Submodule.map_span, ← Set.range_comp] at hb
  have he : (polynomialClass m h) ∘ b =
      (fun n : ℕ => polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n))) := by
    funext n
    apply congrArg (polynomialClass m h)
    change (Polynomial.basisMonomials ℂ) n = (X : ℂ[X]) ^ n
    rw [Polynomial.coe_basisMonomials]
    exact Polynomial.monomial_one_right_eq_X_pow n
  rw [he] at hb
  simpa only [Submodule.map_top] using hb

/-- Gram--Schmidt of the monomial classes, using the moment norm. -/
def momentGramSchmidtFamily (m : ℕ → ℝ) (h : HankelNonnegative m) :
    ℕ → MomentHilbertSpace m h :=
  InnerProductSpace.gramSchmidtNormed ℂ
    (fun n : ℕ => polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n)))

theorem momentGramSchmidt_orthonormal (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hs : HankelPositive m) : Orthonormal ℂ (momentGramSchmidtFamily m h) :=
  InnerProductSpace.gramSchmidtNormed_orthonormal (moment_monomials_linearIndependent m h hs)

theorem span_momentGramSchmidt (m : ℕ → ℝ) (h : HankelNonnegative m) :
    Submodule.span ℂ (Set.range (momentGramSchmidtFamily m h)) =
      (polynomialClass m h).range := by
  unfold momentGramSchmidtFamily
  rw [InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt,
    span_moment_monomials]

/-- The normalized monomial Gram--Schmidt family is a Hilbert basis of the
completion, even when the moment multiplication operator is unbounded. -/
def momentGramSchmidtBasis (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hs : HankelPositive m) : HilbertBasis ℕ ℂ (MomentHilbertSpace m h) :=
  HilbertBasis.mk (momentGramSchmidt_orthonormal m h hs) (by
    rw [span_momentGramSchmidt]
    apply top_le_iff.mpr
    apply SetLike.coe_injective
    change closure (Set.range (polynomialClass m h)) = Set.univ
    exact (polynomialClass_dense m h).closure_eq)

theorem momentGramSchmidtBasis_apply (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hs : HankelPositive m) (n : ℕ) :
    momentGramSchmidtBasis m h hs n = momentGramSchmidtFamily m h n := by
  exact congrFun (HilbertBasis.coe_mk _ _) n

/-- For a Hilbert basis, its algebraic span corresponds exactly to finite-support
coordinates; no finite-dimensionality or boundedness of an operator is used. -/
theorem mem_hilbertBasis_span_iff_finite_support {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (b : HilbertBasis ℕ ℂ H) (x : H) :
    x ∈ Submodule.span ℂ (Set.range b) ↔
      (Function.support (fun n => b.repr x n)).Finite := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, rfl⟩ := hy
      apply (Set.finite_singleton n).subset
      intro j hj
      by_contra hne
      have hz : b.repr (b n) j = 0 := by
        rw [b.repr_self]
        exact lp.single_apply_ne 2 n 1 (by simpa only [Set.mem_singleton_iff] using hne)
      exact hj hz
    | zero => simp
    | add y w _ _ hy hw =>
      apply (hy.union hw).subset
      intro n hn
      simp only [Function.mem_support, map_add, lp.coeFn_add, Pi.add_apply] at hn
      by_cases hny : b.repr y n = 0
      · apply Or.inr
        change b.repr w n ≠ 0
        simpa only [hny, zero_add] using hn
      · exact Or.inl hny
    | smul c y _ hy =>
      apply hy.subset
      intro n hn
      simp only [Function.mem_support, map_smul, lp.coeFn_smul, Pi.smul_apply,
        smul_eq_mul] at hn ⊢
      exact fun hz => hn (by rw [hz, mul_zero])
  · intro hx
    have ht : HasSum (fun n => b.repr x n • b n)
        (∑ n ∈ hx.toFinset, b.repr x n • b n) :=
      hasSum_sum_of_ne_finset_zero (by
        intro n hn
        have hz : b.repr x n = 0 := by
          simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hn
        rw [hz, zero_smul])
    rw [(b.hasSum_repr x).unique ht]
    exact Submodule.sum_mem _ (fun n _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨n, rfl⟩))

/-- The unitary supplied by monomial Gram--Schmidt carries the polynomial
operator domain onto all and only the finite-support sequences. -/
theorem momentGramSchmidt_finite_support_domain (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hs : HankelPositive m) (y : JacobiRecurrenceSpec.SequenceHilbertSpace) :
    (momentGramSchmidtBasis m h hs).repr.symm y ∈
      (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h).domain ↔
      (Function.support (fun n => y n)).Finite := by
  have he : Submodule.span ℂ (Set.range (momentGramSchmidtBasis m h hs)) =
      (polynomialClass m h).range := by
    have hb : (momentGramSchmidtBasis m h hs : ℕ → MomentHilbertSpace m h) =
        momentGramSchmidtFamily m h := funext (momentGramSchmidtBasis_apply m h hs)
    rw [hb, span_momentGramSchmidt]
  change (momentGramSchmidtBasis m h hs).repr.symm y ∈ (polynomialClass m h).range ↔ _
  rw [← he, mem_hilbertBasis_span_iff_finite_support]
  simp only [LinearIsometryEquiv.apply_symm_apply]

theorem complexify_add (p q : ℝ[X]) :
    JacobiRecurrenceSpec.complexify (p + q) =
      JacobiRecurrenceSpec.complexify p + JacobiRecurrenceSpec.complexify q :=
  Polynomial.map_add _

theorem complexify_smul (r : ℝ) (p : ℝ[X]) :
    JacobiRecurrenceSpec.complexify (r • p) =
      (r : ℂ) • JacobiRecurrenceSpec.complexify p := by
  simp only [JacobiRecurrenceSpec.complexify, ← Polynomial.C_mul',
    Polynomial.map_mul, Polynomial.map_C]
  rfl

/-- Assembly of the exact-domain Jacobi model from real recurrence polynomials
identified with the normalized monomial Gram--Schmidt family. -/
theorem jacobi_realization_of_gramSchmidt_system (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hs : HankelPositive m) (d : JacobiRecurrenceSpec.PolynomialJacobiSystem m)
    (halign : ∀ n, polynomialClass m h (ofPolynomial (JacobiRecurrenceSpec.complexify (d.p n))) =
      momentGramSchmidtFamily m h n) :
    JacobiRecurrenceSpec.IsJacobiRealization m h d (momentGramSchmidtBasis m h hs).repr := by
  let B := momentGramSchmidtBasis m h hs
  let S := PolynomialMomentHilbertSpaceSpec.multiplicationValue m h
  have hb (n : ℕ) : polynomialClass m h
      (ofPolynomial (JacobiRecurrenceSpec.complexify (d.p n))) = B n :=
    (halign n).trans (momentGramSchmidtBasis_apply m h hs n).symm
  have hmem (n : ℕ) : B n ∈ S.domain := by
    rw [← hb]
    exact LinearMap.mem_range_self _ _
  have haction (n : ℕ) : S ⟨B n, hmem n⟩ =
      (d.a (n + 1) : ℂ) • B (n + 1) + (d.b n : ℂ) • B n +
      if n = 0 then 0 else (d.a n : ℂ) • B (n - 1) := by
    have hrec := congrArg JacobiRecurrenceSpec.complexify (d.recurrence n)
    simp only [complexify_add, complexify_smul] at hrec
    have hx (p : ℝ[X]) : JacobiRecurrenceSpec.complexify ((X : ℝ[X]) * p) =
        (X : ℂ[X]) * JacobiRecurrenceSpec.complexify p := by
      simp [JacobiRecurrenceSpec.complexify]
    have hz : JacobiRecurrenceSpec.complexify 0 = 0 := by
      simp [JacobiRecurrenceSpec.complexify]
    have hite : JacobiRecurrenceSpec.complexify
        (if n = 0 then 0 else d.a n • d.p (n - 1)) =
        if n = 0 then 0 else (d.a n : ℂ) • JacobiRecurrenceSpec.complexify (d.p (n - 1)) := by
      split_ifs <;> simp only [hz, complexify_smul]
    rw [hx, hite] at hrec
    let F : ℂ[X] →ₗ[ℂ] MomentHilbertSpace m h := polynomialClass m h
    have hr := congrArg F hrec
    simp only [map_add, map_smul] at hr
    change polynomialClass m h
      (ofPolynomial ((X : ℂ[X]) * JacobiRecurrenceSpec.complexify (d.p n))) = _ at hr
    have he : (⟨B n, hmem n⟩ : S.domain) =
        ⟨polynomialClass m h (ofPolynomial (JacobiRecurrenceSpec.complexify (d.p n))),
          LinearMap.mem_range_self _ _⟩ := Subtype.ext (hb n).symm
    rw [he]
    dsimp only [S]
    rw [minimalMultiplication_apply]
    have hFb (j : ℕ) : F (JacobiRecurrenceSpec.complexify (d.p j)) = B j := hb j
    by_cases hn : n = 0
    · simp only [hn, ite_true, map_zero, hFb] at hr ⊢
      exact hr
    · simp only [hn, ite_false, map_smul, hFb] at hr ⊢
      exact hr
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [hb]
    exact B.repr_self n
  · exact momentGramSchmidt_finite_support_domain m h hs
  · intro x n
    change B.repr (S x) n = _
    rw [HilbertBasis.repr_apply_apply]
    have hi := minimalMultiplication_symmetric m h ⟨B n, hmem n⟩ x
    change inner ℂ (S ⟨B n, hmem n⟩) (x : MomentHilbertSpace m h) =
      inner ℂ (B n) (S x) at hi
    rw [← hi, haction]
    have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
    by_cases hn : n = 0
    · simp only [hn, ite_true, add_zero, inner_add_left,
        inner_smul_left (𝕜 := ℂ) (E := MomentHilbertSpace m h),
        starRingEnd_apply, hreal, HilbertBasis.repr_apply_apply]
      rfl
    · simp only [hn, ite_false, inner_add_left,
        inner_smul_left (𝕜 := ℂ) (E := MomentHilbertSpace m h),
        starRingEnd_apply, hreal, HilbertBasis.repr_apply_apply]
      rfl

/-- The exact-domain Jacobi realization follows once the aligned polynomial
construction is supplied. The existence of those polynomials remains separate. -/
theorem jacobi_realization_assembly : JacobiRecurrenceSpec.RealizationAssemblyExpected := by
  intro m h hs d hd
  exact ⟨(momentGramSchmidtBasis m h hs).repr,
    jacobi_realization_of_gramSchmidt_system m h hs d hd⟩

/-- An adjoint eigenvector is determined on the monomials by its constant coordinate. -/
theorem deficiency_monomial_inner (m : ℕ → ℝ) (h : HankelNonnegative m)
    (z : ℂ) (y : deficiencySpace (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h) z) (n : ℕ) :
    inner ℂ (polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n)))
      (y : MomentHilbertSpace m h) =
      z ^ n * inner ℂ (PolynomialMomentHilbertSpaceSpec.constantValue m h) (y : MomentHilbertSpace m h) := by
  obtain ⟨hy, hey⟩ := (mem_deficiencySpace_iff (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h) z
    (y : MomentHilbertSpace m h)).mp y.property
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    rfl
  | succ n ih =>
    have hi := hilbertAdjoint_inner (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h)
      (minimalMultiplication_dense m h) ⟨y, hy⟩
      ⟨polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n)), LinearMap.mem_range_self _ _⟩
    have ha := minimalMultiplication_apply m h (ofPolynomial ((X : ℂ[X]) ^ n))
    change PolynomialMomentHilbertSpaceSpec.multiplicationValue m h _ = _ at ha
    rw [ha, hey, inner_smul_right (𝕜 := ℂ) (E := MomentHilbertSpace m h)] at hi
    have he : (X : ℂ[X]) * X ^ n = X ^ (n + 1) := by rw [pow_succ]; ring
    change inner ℂ (polynomialClass m h (ofPolynomial ((X : ℂ[X]) * X ^ n)))
      (y : MomentHilbertSpace m h) = _ at hi
    rw [he, ih] at hi
    rw [hi, pow_succ]
    ring

/-- Equality of the constant coordinates forces equality of adjoint eigenvectors. -/
theorem deficiency_constant_coordinate_injective (m : ℕ → ℝ) (h : HankelNonnegative m)
    (z : ℂ) : Function.Injective (fun y : deficiencySpace (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h) z =>
      inner ℂ (PolynomialMomentHilbertSpaceSpec.constantValue m h) (y : MomentHilbertSpace m h)) := by
  intro y w he
  change inner ℂ (PolynomialMomentHilbertSpaceSpec.constantValue m h)
    (y : MomentHilbertSpace m h) = inner ℂ
    (PolynomialMomentHilbertSpaceSpec.constantValue m h) (w : MomentHilbertSpace m h) at he
  apply Subtype.ext
  apply Dense.eq_of_inner_right (𝕜 := ℂ) (minimalMultiplication_dense m h)
  rintro _ ⟨p, rfl⟩
  change inner ℂ (polynomialClass m h p) (y : MomentHilbertSpace m h) =
    inner ℂ (polynomialClass m h p) (w : MomentHilbertSpace m h)
  suffices hall : ∀ q : ℂ[X],
      inner ℂ (polynomialClass m h (ofPolynomial q)) (y : MomentHilbertSpace m h) =
      inner ℂ (polynomialClass m h (ofPolynomial q)) (w : MomentHilbertSpace m h) by
    exact hall (rawPolynomial p)
  intro q
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    change inner ℂ (polynomialClass m h
      (ofPolynomial (m := m) (h := h) p + ofPolynomial (m := m) (h := h) q)) _ =
      inner ℂ (polynomialClass m h
      (ofPolynomial (m := m) (h := h) p + ofPolynomial (m := m) (h := h) q)) _
    simp only [map_add, inner_add_left, hp, hq]
  | monomial n c =>
    have hm : (monomial n c : ℂ[X]) = c • X ^ n := by
      rw [← Polynomial.monomial_one_right_eq_X_pow, Polynomial.smul_monomial,
        smul_eq_mul, mul_one]
    rw [hm]
    change inner ℂ (polynomialClass m h (c • ofPolynomial ((X : ℂ[X]) ^ n))) _ =
      inner ℂ (polynomialClass m h (c • ofPolynomial ((X : ℂ[X]) ^ n))) _
    simp only [map_smul]
    calc
      _ = star c * inner ℂ (polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n)))
          (y : MomentHilbertSpace m h) := inner_smul_left (𝕜 := ℂ) (E := MomentHilbertSpace m h) _ _ _
      _ = star c * inner ℂ (polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n)))
          (w : MomentHilbertSpace m h) := by
        rw [deficiency_monomial_inner, deficiency_monomial_inner, he]
      _ = _ := (inner_smul_left (𝕜 := ℂ) (E := MomentHilbertSpace m h)
        (polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n)))
        (w : MomentHilbertSpace m h) c).symm

/-- The constant-coordinate functional is a bounded linear injection of each deficiency space. -/
def deficiencyConstantCoordinate (m : ℕ → ℝ) (h : HankelNonnegative m) (z : ℂ) :
    deficiencySpace (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h) z →L[ℂ] ℂ :=
  (innerSL ℂ (PolynomialMomentHilbertSpaceSpec.constantValue m h)).comp
    (deficiencySpace (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h) z).subtypeL

/-- The one-sided Jacobi boundary leaves at most one free deficiency coordinate.
This proof works directly with the dense cyclic polynomial domain. -/
theorem moment_deficiencyIndex_le_one : JacobiRecurrenceSpec.DeficiencyBoundExpected := by
  intro m h hd z
  let S := PolynomialMomentHilbertSpaceSpec.multiplicationValue m h
  let : CompleteSpace (deficiencySpace S z) :=
    (deficiencySpace_isClosed S hd z).isComplete.completeSpace_coe
  obtain ⟨J, b, hb⟩ := deficiencyIndex_hasBasis S hd z
  change deficiencyIndex S hd z ≤ 1
  rw [hb]
  have hi := hilbertBasis_card_le_of_injective b (stdOrthonormalBasis ℂ ℂ).toHilbertBasis
    (deficiencyConstantCoordinate m h z) (deficiency_constant_coordinate_injective m h z)
  simpa using hi

/-- Coefficient conjugation conjugates the moment form because every moment is real. -/
theorem momentForm_conjugate (m : ℕ → ℝ) (p q : ℂ[X]) :
    momentForm m (p.map (starRingEnd ℂ)) (q.map (starRingEnd ℂ)) =
      star (momentForm m p q) := by
  simp only [momentForm]
  rw [← momentFunctional_conj]
  simp [Polynomial.map_map, mul_comm]

/-- Conjugation on the polynomial vectors, viewed as a semilinear map. -/
def polynomialConjugateClass (m : ℕ → ℝ) (h : HankelNonnegative m) :
    MomentPolynomials m h →ₗ⋆[ℂ] MomentHilbertSpace m h where
  toFun p := polynomialClass m h (ofPolynomial ((rawPolynomial p).map (starRingEnd ℂ)))
  map_add' p q := by
    change polynomialClass m h (ofPolynomial ((rawPolynomial p + rawPolynomial q).map _)) = _
    simp only [Polynomial.map_add]
    exact (polynomialClass m h).map_add _ _
  map_smul' c p := by
    change polynomialClass m h (ofPolynomial ((c • rawPolynomial p).map _)) = _
    have he : (c • rawPolynomial p).map (starRingEnd ℂ) =
        star c • (rawPolynomial p).map (starRingEnd ℂ) := by
      simp only [← Polynomial.C_mul', Polynomial.map_mul, Polynomial.map_C,
        starRingEnd_apply]
    rw [he]
    exact (polynomialClass m h).map_smul (star c) _

theorem polynomialConjugateClass_norm (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p : MomentPolynomials m h) :
    ‖polynomialConjugateClass m h p‖ = ‖polynomialClass m h p‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  congr 1
  change (inner ℂ (polynomialClass m h _) (polynomialClass m h _)).re = _
  rw [polynomialClass_inner, polynomialClass_inner]
  change (momentForm m ((rawPolynomial p).map (starRingEnd ℂ))
    ((rawPolynomial p).map (starRingEnd ℂ))).re = (momentForm m p p).re
  rw [momentForm_conjugate]
  rfl

/-- The canonical anti-linear isometry on the completed moment space. -/
def momentConjugation (m : ℕ → ℝ) (h : HankelNonnegative m) :
    MomentHilbertSpace m h →ₗᵢ⋆[ℂ] MomentHilbertSpace m h :=
  (polynomialConjugateClass m h).extendOfIsometry
    (polynomialClass_dense m h) (polynomialConjugateClass_norm m h)

@[simp] theorem momentConjugation_class (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p : MomentPolynomials m h) :
    momentConjugation m h (polynomialClass m h p) =
      polynomialClass m h (ofPolynomial ((rawPolynomial p).map (starRingEnd ℂ))) :=
  LinearMap.extendOfIsometry_eq _ _ _ p

theorem momentConjugation_involutive (m : ℕ → ℝ) (h : HankelNonnegative m) :
    Function.Involutive (momentConjugation m h) := by
  intro x
  refine (polynomialClass_dense m h).induction_on x
    (isClosed_eq ((momentConjugation m h).continuous.comp
      (momentConjugation m h).continuous) continuous_id) ?_
  intro p
  rw [momentConjugation_class, momentConjugation_class]
  congr 1
  change ofPolynomial (((rawPolynomial p).map (starRingEnd ℂ)).map (starRingEnd ℂ)) = p
  change ((rawPolynomial p).map (starRingEnd ℂ)).map (starRingEnd ℂ) = rawPolynomial p
  ext n
  simp

/-- The extended conjugation reverses the inner product. -/
theorem momentConjugation_inner (m : ℕ → ℝ) (h : HankelNonnegative m)
    (x y : MomentHilbertSpace m h) :
    inner ℂ (momentConjugation m h x) (momentConjugation m h y) = star (inner ℂ x y) := by
  refine (polynomialClass_dense m h).induction_on₂
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro p q
  rw [momentConjugation_class, momentConjugation_class,
    polynomialClass_inner, polynomialClass_inner]
  exact momentForm_conjugate m p q

/-- Moving conjugation across a polynomial test vector. -/
theorem inner_class_momentConjugation (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p : MomentPolynomials m h) (y : MomentHilbertSpace m h) :
    inner ℂ (polynomialClass m h p) (momentConjugation m h y) =
      star (inner ℂ (polynomialClass m h
        (ofPolynomial ((rawPolynomial p).map (starRingEnd ℂ)))) y) := by
  have hi := momentConjugation_inner m h
    (momentConjugation m h (polynomialClass m h p)) y
  rw [momentConjugation_involutive, momentConjugation_class] at hi
  exact hi

/-- Coefficient conjugation carries the z-deficiency space into the conjugate-z space. -/
theorem momentConjugation_mem_deficiency (m : ℕ → ℝ) (h : HankelNonnegative m)
    (z : ℂ) (y : MomentHilbertSpace m h)
    (hy : y ∈ deficiencySpace (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h) z) :
    momentConjugation m h y ∈
      deficiencySpace (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h) (star z) := by
  let S := PolynomialMomentHilbertSpaceSpec.multiplicationValue m h
  obtain ⟨hy, hey⟩ := (mem_deficiencySpace_iff S z y).mp hy
  have hw : ∀ x : S.domain, inner ℂ (S x) (momentConjugation m h y) =
      inner ℂ (x : MomentHilbertSpace m h) (star z • momentConjugation m h y) := by
    intro x
    obtain ⟨p, hp⟩ := x.property
    have hx : x = ⟨polynomialClass m h p, LinearMap.mem_range_self _ p⟩ :=
      Subtype.ext hp.symm
    subst x
    dsimp only [S]
    rw [minimalMultiplication_apply, inner_smul_right (𝕜 := ℂ) (E := MomentHilbertSpace m h), inner_class_momentConjugation,
      inner_class_momentConjugation]
    let q : MomentPolynomials m h := ofPolynomial ((rawPolynomial p).map (starRingEnd ℂ))
    have hq := hilbertAdjoint_inner S (minimalMultiplication_dense m h) ⟨y, hy⟩
      ⟨polynomialClass m h q, LinearMap.mem_range_self _ q⟩
    dsimp only [S] at hq
    rw [minimalMultiplication_apply, hey, inner_smul_right (𝕜 := ℂ) (E := MomentHilbertSpace m h)] at hq
    have he : (((X : ℂ[X]) * rawPolynomial p).map (starRingEnd ℂ)) =
        (X : ℂ[X]) * (rawPolynomial p).map (starRingEnd ℂ) := by simp
    change star (inner ℂ (polynomialClass m h (ofPolynomial
      (((X : ℂ[X]) * rawPolynomial p).map (starRingEnd ℂ)))) y) = _
    rw [he]
    change star (inner ℂ (polynomialClass m h
      (ofPolynomial ((X : ℂ[X]) * rawPolynomial q))) y) = _
    rw [hq, star_mul]
    exact mul_comm _ _
  have hyC := (mem_hilbertAdjoint_domain_iff S (minimalMultiplication_dense m h) _).mpr
    ⟨star z • momentConjugation m h y, hw⟩
  apply (mem_deficiencySpace_iff S (star z) _).mpr
  exact ⟨hyC, hilbertAdjoint_apply_eq S (minimalMultiplication_dense m h) _ _ hw⟩

/-- A zero Hilbert cardinal is equivalent to vanishing of every deficiency vector. -/
theorem moment_deficiencyIndex_zero_iff (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hd : Dense ((PolynomialMomentHilbertSpaceSpec.multiplicationValue m h).domain :
      Set (MomentHilbertSpace m h))) (z : ℂ) :
    deficiencyIndex (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h) hd z = 0 ↔
      ∀ y : deficiencySpace (PolynomialMomentHilbertSpaceSpec.multiplicationValue m h) z,
        y = 0 := by
  let S := PolynomialMomentHilbertSpaceSpec.multiplicationValue m h
  let : CompleteSpace (deficiencySpace S z) :=
    (deficiencySpace_isClosed S hd z).isComplete.completeSpace_coe
  obtain ⟨J, b, hb⟩ := deficiencyIndex_hasBasis S hd z
  change deficiencyIndex S hd z = 0 ↔ _
  rw [hb]
  constructor
  · intro hz y
    have : IsEmpty J := Cardinal.mk_eq_zero_iff.mp hz
    apply b.repr.injective
    apply lp.ext
    funext j
    exact isEmptyElim j
  · intro hall
    have : IsEmpty J := ⟨fun j => b.orthonormal.ne_zero j (hall (b j))⟩
    exact Cardinal.mk_eq_zero J

/-- Equal conjugate deficiencies, and the one-coordinate bound, give the required alternatives. -/
theorem moment_deficiency_alternatives : JacobiRecurrenceSpec.DeficiencyAlternativesExpected := by
  intro m h hd _hs
  let S := PolynomialMomentHilbertSpaceSpec.multiplicationValue m h
  change (deficiencyIndex S hd I = 0 ∧ deficiencyIndex S hd (-I) = 0) ∨
    (deficiencyIndex S hd I = 1 ∧ deficiencyIndex S hd (-I) = 1)
  have hc : deficiencyIndex S hd I = 0 ↔ deficiencyIndex S hd (-I) = 0 := by
    constructor <;> intro hz
    · apply (moment_deficiencyIndex_zero_iff m h hd (-I)).mpr
      intro y
      have hy := momentConjugation_mem_deficiency m h (-I) y y.property
      have he : star (-I : ℂ) = I := by simp
      rw [he] at hy
      have h0 := (moment_deficiencyIndex_zero_iff m h hd I).mp hz ⟨_, hy⟩
      have hval := congrArg Subtype.val h0
      apply Subtype.ext
      exact (momentConjugation m h).injective (by simpa using hval)
    · apply (moment_deficiencyIndex_zero_iff m h hd I).mpr
      intro y
      have hy := momentConjugation_mem_deficiency m h I y y.property
      have he : star (I : ℂ) = -I := by simp
      rw [he] at hy
      have h0 := (moment_deficiencyIndex_zero_iff m h hd (-I)).mp hz ⟨_, hy⟩
      have hval := congrArg Subtype.val h0
      apply Subtype.ext
      exact (momentConjugation m h).injective (by simpa using hval)
  by_cases hz : deficiencyIndex S hd I = 0
  · exact Or.inl ⟨hz, hc.mp hz⟩
  · right
    constructor
    · exact le_antisymm (moment_deficiencyIndex_le_one m h hd I)
        (Cardinal.one_le_iff_ne_zero.mpr hz)
    · exact le_antisymm (moment_deficiencyIndex_le_one m h hd (-I))
        (Cardinal.one_le_iff_ne_zero.mpr (fun he => hz (hc.mpr he)))


@[simp] theorem complexify_conj (p : ℝ[X]) :
    (JacobiRecurrenceSpec.complexify p).map (starRingEnd ℂ) =
      JacobiRecurrenceSpec.complexify p := by
  ext n
  simp [JacobiRecurrenceSpec.complexify]

theorem momentForm_complexify_ofReal_re (m : ℕ → ℝ) (p q : ℝ[X]) :
    ((momentForm m (JacobiRecurrenceSpec.complexify p)
      (JacobiRecurrenceSpec.complexify q)).re : ℂ) =
      momentForm m (JacobiRecurrenceSpec.complexify p)
        (JacobiRecurrenceSpec.complexify q) := by
  have he : star (momentForm m (JacobiRecurrenceSpec.complexify p)
      (JacobiRecurrenceSpec.complexify q)) =
      momentForm m (JacobiRecurrenceSpec.complexify p)
        (JacobiRecurrenceSpec.complexify q) := by
    rw [← momentForm_conjugate, complexify_conj, complexify_conj]
  apply Complex.ext
  · rfl
  · have hi := congrArg Complex.im he
    simp only [star_def, conj_im] at hi
    simp only [ofReal_im]
    linarith


open JacobiRecurrenceSpec

private def rMoment (m : ℕ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap ∘ₗ (momentFunctional m).restrictScalars ℝ ∘ₗ
    (Polynomial.mapAlgHom (Algebra.ofId ℝ ℂ)).toLinearMap

private theorem rMoment_eq (m : ℕ → ℝ) (p q : ℝ[X]) :
    rMoment m (p*q) = (momentForm m (complexify p) (complexify q)).re := by
  have hc : (complexify p).map (starRingEnd ℂ) = complexify p := by
    ext i
    simp [complexify]
  simp only [momentForm, hc]
  simp [rMoment, complexify, Polynomial.map_mul]

private def rPair (m : ℕ → ℝ) (p : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun q := rMoment m (p*q)
  map_add' q r := by simp [mul_add]
  map_smul' c q := by simp

private theorem rPair_symm (m : ℕ → ℝ) (p q : ℝ[X]) :
    rPair m p q = rPair m q p := by dsimp [rPair]; rw [mul_comm]

private theorem rPair_X (m : ℕ → ℝ) (p q : ℝ[X]) :
    rPair m p (X*q) = rPair m (X*p) q := by
  dsimp [rPair]
  congr 1
  ring

private theorem recurrence_basis_coordinates (m : ℕ → ℝ)
    (p : ℕ → ℝ[X]) (hp : ∀ n, (p n).natDegree = n)
    (hl : ∀ n, 0 < (p n).leadingCoeff)
    (ho : ∀ j k, momentForm m (complexify (p j)) (complexify (p k)) =
      if j = k then 1 else 0) :
    ∃ B : Module.Basis ℕ ℝ ℝ[X], (∀ n, B n = p n) ∧
      ∀ q n, B.repr q n = rPair m (p n) q := by
  let S : Polynomial.Sequence ℝ := ⟨p, fun n => by
    rw [Polynomial.degree_eq_natDegree (Polynomial.leadingCoeff_ne_zero.mp (ne_of_gt (hl n))), hp n]⟩
  let B := S.basis (fun n => isUnit_iff_ne_zero.mpr (ne_of_gt (hl n)))
  have he : ∀ n, B n = p n := by intro n; exact S.basis_eq_self _ n
  refine ⟨B, he, ?_⟩
  intro q n
  have hmaps : B.coord n = rPair m (p n) := by
    apply B.ext
    intro j
    rw [Module.Basis.coord_apply, B.repr_self, he]
    change (Finsupp.single j 1) n = rMoment m (p n * p j)
    rw [rMoment_eq, ho]
    by_cases h : n = j <;> simp [h]
  exact LinearMap.congr_fun hmaps q

private theorem recurrence_repr_zero (B : Module.Basis ℕ ℝ ℝ[X])
    (hd : ∀ n, (B n).degree = n) (q : ℝ[X]) (k : ℕ) (hq : q.degree < k) :
    B.repr q k = 0 := by
  let S : Polynomial.Sequence ℝ := ⟨B, hd⟩
  have hsp : q ∈ Submodule.span ℝ (B '' Set.Iio k) := by
    change q ∈ Submodule.span ℝ (S '' Set.Iio k)
    rw [S.span_degreeLT (fun i _hi => isUnit_iff_ne_zero.mpr
      (Polynomial.leadingCoeff_ne_zero.mpr (B.ne_zero i)))]
    exact Polynomial.mem_degreeLT.mpr hq
  apply Finsupp.notMem_support_iff.mp
  intro hk
  have hlt := B.repr_support_subset_of_mem_span (Set.Iio k) hsp hk
  exact (lt_irrefl k) hlt

private theorem recurrence_coordinates_symmetric (m : ℕ → ℝ)
    (B : Module.Basis ℕ ℝ ℝ[X])
    (hc : ∀ q n, B.repr q n = rPair m (B n) q) (j k : ℕ) :
    B.repr (X*B j) k = B.repr (X*B k) j := by
  rw [hc, hc, rPair_X, rPair_symm]

private theorem recurrence_coordinates_tridiagonal (m : ℕ → ℝ)
    (B : Module.Basis ℕ ℝ ℝ[X]) (hd : ∀ n, (B n).degree = n)
    (hc : ∀ q n, B.repr q n = rPair m (B n) q)
    (n k : ℕ) (hk : k ≠ n + 1 ∧ k ≠ n ∧ (n = 0 ∨ k ≠ n - 1)) :
    B.repr (X*B n) k = 0 := by
  have hdeg (j : ℕ) : (X*B j).degree = ((j+1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, Polynomial.degree_X, hd]
    norm_cast
    omega
  by_cases hkn : n + 1 < k
  · exact recurrence_repr_zero B hd _ _ (by rw [hdeg]; exact_mod_cast hkn)
  · rw [recurrence_coordinates_symmetric m B hc]
    apply recurrence_repr_zero B hd
    rw [hdeg]
    exact_mod_cast (show k+1<n by omega)

private theorem recurrence_of_basis (m : ℕ → ℝ)
    (B : Module.Basis ℕ ℝ ℝ[X]) (hd : ∀ n, (B n).degree = n)
    (hc : ∀ q n, B.repr q n = rPair m (B n) q)
    (htop : ∀ n, 0 < B.repr (X*B n) (n+1)) :
    ∃ a b : ℕ → ℝ, a 0 = 0 ∧ (∀ n, 0 < a (n+1)) ∧
      ∀ n, (X : ℝ[X]) * B n =
        a (n+1) • B (n+1) + b n • B n +
          if n=0 then 0 else a n • B (n-1) := by
  let a : ℕ → ℝ := fun n => if n=0 then 0 else B.repr (X*B (n-1)) n
  let b : ℕ → ℝ := fun n => B.repr (X*B n) n
  have haup (n : ℕ) : a (n+1) = B.repr (X*B n) (n+1) := by simp [a]
  have hlow (n : ℕ) (hn : n ≠ 0) : a n = B.repr (X*B n) (n-1) := by
    simp only [a, ite_eq_right hn]
    exact recurrence_coordinates_symmetric m B hc _ _
  refine ⟨a,b,by simp [a],fun n => by rw [haup]; exact htop n, ?_⟩
  intro n
  apply B.repr.injective
  ext k
  by_cases hn : n = 0
  · subst n
    by_cases hk1 : k = 1
    · subst k
      simp [haup, b]
    · by_cases hk0 : k = 0
      · subst k
        simp [b]
      · have hz := recurrence_coordinates_tridiagonal m B hd hc 0 k
          ⟨by simpa using hk1,hk0,Or.inl rfl⟩
        simp [hz,hk1,hk0]
  · simp only [ite_eq_right hn]
    by_cases hk1 : k = n+1
    · subst k
      have hne : n-1 ≠ n+1 := by omega
      simp [haup,b,hne]
    · by_cases hkn : k = n
      · subst k
        have hne : n-1 ≠ n := by omega
        simp [b,hne]
      · by_cases hkp : k = n-1
        · subst k
          have hne : n+1 ≠ n-1 := by omega
          have hne' : n ≠ n-1 := by omega
          simp [hlow n hn,hne']
        · have hz := recurrence_coordinates_tridiagonal m B hd hc n k
            ⟨hk1,hkn,Or.inr hkp⟩
          simp [hz,hk1,hkn,hkp]

/-- The coefficient of the next polynomial in multiplication by `X` is the ratio
of the leading coefficients. -/
theorem polynomial_basis_X_top_coefficient
    (B : Module.Basis ℕ ℝ ℝ[X])
    (hdegree : ∀ n, (B n).degree = (n : WithBot ℕ))
    (hzero : ∀ (q : ℝ[X]) (k : ℕ), q.degree < (k : WithBot ℕ) → B.repr q k = 0)
    (n : ℕ) :
    B.repr ((X : ℝ[X]) * B n) (n + 1) =
      (B n).leadingCoeff / (B (n + 1)).leadingCoeff := by
  let c := (B n).leadingCoeff / (B (n + 1)).leadingCoeff
  have hne : ∀ i, (B i).leadingCoeff ≠ 0 := fun i =>
    Polynomial.leadingCoeff_ne_zero.mpr (B.ne_zero i)
  have hc : c ≠ 0 := div_ne_zero (hne n) (hne (n + 1))
  have hhead : (c • B (n + 1)).degree = ((X : ℝ[X]) * B n).degree := by
    rw [Polynomial.degree_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero hc),
      hdegree (n + 1), Polynomial.degree_mul, Polynomial.degree_X, hdegree n]
    simp [add_comm]
  have hlc : (((X : ℝ[X]) * B n).leadingCoeff) =
      (c • B (n + 1)).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul,
      Polynomial.leadingCoeff_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero hc)]
    simp only [Polynomial.leadingCoeff_X, one_mul, smul_eq_mul]
    exact (div_mul_cancel₀ _ (hne (n + 1))).symm
  have htail : (((X : ℝ[X]) * B n) - c • B (n + 1)).degree < (n + 1 : ℕ) := by
    have hlt := Polynomial.degree_sub_lt_left hhead.symm
      (mul_ne_zero Polynomial.X_ne_zero (B.ne_zero n)) hlc
    convert hlt using 1
    rw [Polynomial.degree_mul, Polynomial.degree_X, hdegree n]
    simp [add_comm]
  have hz := hzero (((X : ℝ[X]) * B n) - c • B (n + 1)) (n + 1) htail
  have hre : B.repr (((X : ℝ[X]) * B n) - c • B (n + 1)) (n + 1) =
      B.repr ((X : ℝ[X]) * B n) (n + 1) - c := by
    simp
  rw [hre] at hz
  exact sub_eq_zero.mp hz


/-- Every real degree-indexed orthonormal polynomial family with positive leading
coefficients obeys the positive symmetric three-term Jacobi recurrence. -/
theorem polynomial_jacobi_recurrence (m : ℕ → ℝ)
    (p : ℕ → ℝ[X]) (hp : ∀ n, (p n).natDegree = n)
    (hl : ∀ n, 0 < (p n).leadingCoeff)
    (ho : ∀ j k, momentForm m (complexify (p j)) (complexify (p k)) =
      if j = k then 1 else 0) :
    ∃ a b : ℕ → ℝ, a 0 = 0 ∧ (∀ n, 0 < a (n+1)) ∧
      ∀ n, (X : ℝ[X]) * p n =
        a (n+1) • p (n+1) + b n • p n +
          if n=0 then 0 else a n • p (n-1) := by
  obtain ⟨B,he,hc⟩ := recurrence_basis_coordinates m p hp hl ho
  have hd (n : ℕ) : (B n).degree = n := by
    rw [he, Polynomial.degree_eq_natDegree
      (Polynomial.leadingCoeff_ne_zero.mp (ne_of_gt (hl n))), hp]
  have hcoord (q : ℝ[X]) (n : ℕ) : B.repr q n = rPair m (B n) q := by
    rw [he]
    exact hc q n
  have htop (n : ℕ) : 0 < B.repr (X*B n) (n+1) := by
    rw [polynomial_basis_X_top_coefficient B hd (recurrence_repr_zero B hd), he, he]
    exact div_pos (hl n) (hl (n+1))
  obtain ⟨a,b,ha0,hapos,hrec⟩ := recurrence_of_basis m B hd hcoord htop
  refine ⟨a,b,ha0,hapos,?_⟩
  intro n
  simpa only [he] using hrec n



/-- The real coefficient for projection onto an unnormalized monomial Gram--Schmidt vector. -/
def realMomentProjectionCoefficient (m : ℕ → ℝ) (h : HankelNonnegative m)
    (n k : ℕ) : ℝ :=
  (inner ℂ
    (InnerProductSpace.gramSchmidt ℂ
      (fun j : ℕ => polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ j))) k)
    (polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n)))).re /
    ‖InnerProductSpace.gramSchmidt ℂ
      (fun j : ℕ => polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ j))) k‖ ^ 2

/-- Real monic Gram--Schmidt polynomials, before normalization. -/
def realMomentOrthogonalPolynomial (m : ℕ → ℝ) (h : HankelNonnegative m) (n : ℕ) : ℝ[X] :=
  (X : ℝ[X]) ^ n - ∑ k : Fin n,
    realMomentProjectionCoefficient m h n k • realMomentOrthogonalPolynomial m h k
termination_by n

theorem realMomentOrthogonalPolynomial_eq (m : ℕ → ℝ) (h : HankelNonnegative m) (n : ℕ) :
    realMomentOrthogonalPolynomial m h n = (X : ℝ[X]) ^ n -
      ∑ k ∈ Finset.range n, realMomentProjectionCoefficient m h n k •
        realMomentOrthogonalPolynomial m h k := by
  rw [realMomentOrthogonalPolynomial]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun k => realMomentProjectionCoefficient m h n k •
    realMomentOrthogonalPolynomial m h k) n

/-- Real polynomial classes, with scalars restricted from complex scalars. -/
def realPolynomialClass (m : ℕ → ℝ) (h : HankelNonnegative m) :
    ℝ[X] →ₗ[ℝ] MomentHilbertSpace m h where
  toFun p := polynomialClass m h (ofPolynomial (JacobiRecurrenceSpec.complexify p))
  map_add' p q := by
    simp only [complexify_add]
    exact (polynomialClass m h).map_add _ _
  map_smul' r p := by
    simp only [complexify_smul]
    exact (polynomialClass m h).map_smul (r : ℂ) _


theorem realMomentOrthogonalPolynomial_class (m : ℕ → ℝ) (h : HankelNonnegative m) (n : ℕ) :
    realPolynomialClass m h (realMomentOrthogonalPolynomial m h n) =
      InnerProductSpace.gramSchmidt ℂ
        (fun j : ℕ => polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ j))) n := by
  let M : ℕ → MomentHilbertSpace m h := fun j =>
    polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ j))
  let G := InnerProductSpace.gramSchmidt ℂ M
  change realPolynomialClass m h (realMomentOrthogonalPolynomial m h n) = G n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    change realPolynomialClass m h (realMomentOrthogonalPolynomial m h n) =
      InnerProductSpace.gramSchmidt ℂ M n
    rw [realMomentOrthogonalPolynomial_eq, map_sub, map_sum,
      InnerProductSpace.gramSchmidt_def, Nat.Iio_eq_range]
    have hm : realPolynomialClass m h ((X : ℝ[X]) ^ n) = M n := by
      simp [realPolynomialClass, JacobiRecurrenceSpec.complexify, M]
    rw [hm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_smul, ih k (Finset.mem_range.mp hk),
      Submodule.starProjection_singleton]
    have hreal : Complex.ofReal (inner ℂ (G k) (M n)).re = inner ℂ (G k) (M n) := by
      rw [← ih k (Finset.mem_range.mp hk)]
      change Complex.ofReal (inner ℂ
        (polynomialClass m h (ofPolynomial (JacobiRecurrenceSpec.complexify
          (realMomentOrthogonalPolynomial m h k))))
        (polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n)))).re =
        inner ℂ
          (polynomialClass m h (ofPolynomial (JacobiRecurrenceSpec.complexify
            (realMomentOrthogonalPolynomial m h k))))
          (polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n)))
      rw [polynomialClass_inner]
      change Complex.ofReal (momentForm m (JacobiRecurrenceSpec.complexify
        (realMomentOrthogonalPolynomial m h k)) ((X : ℂ[X]) ^ n)).re = _
      simpa only [JacobiRecurrenceSpec.complexify, Polynomial.map_pow, Polynomial.map_X, ofPolynomial]
        using momentForm_complexify_ofReal_re m (realMomentOrthogonalPolynomial m h k)
          ((X : ℝ[X]) ^ n)
    change (realMomentProjectionCoefficient m h n k : ℂ) • G k = _
    congr 1
    change Complex.ofReal ((inner ℂ (G k) (M n)).re / ‖G k‖ ^ 2) = _
    rw [Complex.ofReal_div, hreal]
    rfl

/-- Triangular subtraction from monomials leaves their top coefficient unchanged. -/
theorem triangular_polynomial_degree_monic
    (q : ℕ → ℝ[X]) (c : ℕ → ℕ → ℝ)
    (hq : ∀ n, q n = (X : ℝ[X]) ^ n - ∑ i ∈ Finset.range n, c n i • q i) :
    ∀ n, (q n).natDegree = n ∧ (q n).Monic := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hle : (q n).natDegree ≤ n := by
      rw [hq n]
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · apply Polynomial.natDegree_sum_le_of_forall_le
        intro i hi
        exact (Polynomial.natDegree_smul_le _ _).trans ((ih i (Finset.mem_range.mp hi)).1.le.trans (Finset.mem_range.mp hi).le)
    have hcoeff : (q n).coeff n = 1 := by
      rw [hq n, Polynomial.coeff_sub, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_smul, smul_eq_mul]
      have hz : (∑ i ∈ Finset.range n, c n i * (q i).coeff n) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
        · simp
        · rw [(ih i (Finset.mem_range.mp hi)).1]
          exact Finset.mem_range.mp hi
      rw [hz, sub_zero]
      simp
    exact ⟨Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeff]; norm_num),
      Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hle hcoeff⟩

/-- A positive real normalization preserves the degree and gives a positive leading coefficient. -/
theorem positive_smul_monic_polynomial {q : ℝ[X]} {n : ℕ} {r : ℝ}
    (hq : q.Monic) (hd : q.natDegree = n) (hr : 0 < r) :
    (r • q).natDegree = n ∧ 0 < (r • q).leadingCoeff := by
  constructor
  · rw [Polynomial.natDegree_smul _ hr.ne', hd]
  · rw [Polynomial.leadingCoeff_smul_of_smul_regular _ (IsSMulRegular.of_ne_zero hr.ne'), hq.leadingCoeff, smul_eq_mul, mul_one]
    exact hr


/-- The real orthonormal polynomial with positive leading coefficient. -/
def realMomentOrthonormalPolynomial (m : ℕ → ℝ) (h : HankelNonnegative m) (n : ℕ) : ℝ[X] :=
  ‖InnerProductSpace.gramSchmidt ℂ
    (fun j : ℕ => polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ j))) n‖⁻¹ •
    realMomentOrthogonalPolynomial m h n

theorem realMomentOrthonormalPolynomial_class (m : ℕ → ℝ) (h : HankelNonnegative m) (n : ℕ) :
    polynomialClass m h (ofPolynomial (JacobiRecurrenceSpec.complexify
      (realMomentOrthonormalPolynomial m h n))) = momentGramSchmidtFamily m h n := by
  change realPolynomialClass m h (realMomentOrthonormalPolynomial m h n) = _
  rw [realMomentOrthonormalPolynomial, map_smul, realMomentOrthogonalPolynomial_class]
  unfold momentGramSchmidtFamily InnerProductSpace.gramSchmidtNormed
  let G := InnerProductSpace.gramSchmidt ℂ
    (fun j : ℕ => polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ j))) n
  change (↑(‖G‖⁻¹) : ℂ) • G = (‖G‖ : ℂ)⁻¹ • G
  rw [Complex.ofReal_inv]

theorem realMomentOrthonormalPolynomial_degree_leading
    (m : ℕ → ℝ) (h : HankelNonnegative m) (hs : HankelPositive m) (n : ℕ) :
    (realMomentOrthonormalPolynomial m h n).natDegree = n ∧
      0 < (realMomentOrthonormalPolynomial m h n).leadingCoeff := by
  have hd := triangular_polynomial_degree_monic
    (realMomentOrthogonalPolynomial m h) (realMomentProjectionCoefficient m h)
    (realMomentOrthogonalPolynomial_eq m h) n
  have hn : 0 < ‖InnerProductSpace.gramSchmidt ℂ
      (fun j : ℕ => polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ j))) n‖ :=
    norm_pos_iff.mpr (InnerProductSpace.gramSchmidt_ne_zero n
      (moment_monomials_linearIndependent m h hs))
  exact positive_smul_monic_polynomial hd.2 hd.1 (inv_pos.mpr hn)

theorem realMomentOrthonormalPolynomial_orthonormal
    (m : ℕ → ℝ) (h : HankelNonnegative m) (hs : HankelPositive m) (j k : ℕ) :
    momentForm m
      (JacobiRecurrenceSpec.complexify (realMomentOrthonormalPolynomial m h j))
      (JacobiRecurrenceSpec.complexify (realMomentOrthonormalPolynomial m h k)) =
      if j = k then 1 else 0 := by
  have he := (orthonormal_iff_ite.mp (momentGramSchmidt_orthonormal m h hs)) j k
  rw [← realMomentOrthonormalPolynomial_class m h j,
    ← realMomentOrthonormalPolynomial_class m h k, polynomialClass_inner] at he
  exact he

/-- Strict moment positivity constructs real orthonormal polynomials aligned with
monomial Gram--Schmidt, with their degree and leading sign fixed. -/
theorem exists_real_orthonormal_moment_polynomials
    (m : ℕ → ℝ) (h : HankelNonnegative m) (hs : HankelPositive m) :
    ∃ p : ℕ → ℝ[X],
      (∀ n, (p n).natDegree = n) ∧
      (∀ n, 0 < (p n).leadingCoeff) ∧
      (∀ j k, momentForm m (JacobiRecurrenceSpec.complexify (p j))
        (JacobiRecurrenceSpec.complexify (p k)) = if j = k then 1 else 0) ∧
      (∀ n, polynomialClass m h (ofPolynomial (JacobiRecurrenceSpec.complexify (p n))) =
        momentGramSchmidtFamily m h n) := by
  refine ⟨realMomentOrthonormalPolynomial m h, ?_, ?_, ?_,
    realMomentOrthonormalPolynomial_class m h⟩
  · intro n
    exact (realMomentOrthonormalPolynomial_degree_leading m h hs n).1
  · intro n
    exact (realMomentOrthonormalPolynomial_degree_leading m h hs n).2
  · exact realMomentOrthonormalPolynomial_orthonormal m h hs



/-- Strict positivity supplies the real Jacobi polynomials and the identity
with the normalized monomial Gram--Schmidt construction. -/
theorem jacobi_aligned_polynomial_construction :
    JacobiRecurrenceSpec.AlignedPolynomialConstructionExpected := by
  intro m h hs
  obtain ⟨p, hdeg, hlead, hon, halign⟩ :=
    exists_real_orthonormal_moment_polynomials m h hs
  obtain ⟨a, b, ha0, hapos, hrec⟩ :=
    polynomial_jacobi_recurrence m p hdeg hlead hon
  let d : JacobiRecurrenceSpec.PolynomialJacobiSystem m :=
    { p := p
      a := a
      b := b
      degree := hdeg
      leading_positive := hlead
      orthonormal := hon
      a_zero := ha0
      a_positive := hapos
      recurrence := hrec }
  exact ⟨d, halign⟩

/-- Real orthonormal polynomials with positive leading coefficients and the
positive symmetric three-term recurrence, under exactly strict Hankel positivity. -/
theorem jacobi_orthonormal_polynomials :
    JacobiRecurrenceSpec.OrthonormalPolynomialsExpected := by
  intro m hs
  obtain ⟨d, _⟩ := jacobi_aligned_polynomial_construction m hs.nonnegative hs
  exact ⟨d⟩

/-- The completed moment Hilbert space is unitarily identified with ℓ², and
minimal multiplication has exactly the finite-support Jacobi matrix domain. -/
theorem jacobi_realization : JacobiRecurrenceSpec.JacobiRealizationExpected := by
  intro m h hs
  obtain ⟨d, halign⟩ := jacobi_aligned_polynomial_construction m h hs
  obtain ⟨U, hU⟩ := jacobi_realization_assembly m h hs d halign
  exact ⟨d, U, hU⟩

end ExpandedFA.Moments
