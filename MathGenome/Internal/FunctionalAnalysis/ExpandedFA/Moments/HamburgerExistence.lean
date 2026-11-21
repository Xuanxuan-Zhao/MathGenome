import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.HamburgerExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Moments.PolynomialMomentHilbertSpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.ClosedSymmetricExtensions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Polynomial Complex
open scoped ENNReal
namespace ExpandedFA.Moments
open Unbounded Unbounded.OperatorDomainsSpec Unbounded.SymmetryAndDeficienciesSpec
open PolynomialMomentHilbertSpaceSpec

/- The construction helpers have their own namespace so independent moment
problem developments can use their own conjugations without name collisions. -/
namespace HamburgerExistenceProof

/-- All real powers are Bochner integrable, since absolute moments are finite. -/
theorem RepresentsHamburgerMoments.integrable_pow {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (n : ℕ) :
    Integrable (fun t : ℝ => t ^ n) μ := by
  apply (integrable_norm_iff ((continuous_id.pow n).aestronglyMeasurable)).mp
  change Integrable (fun t : ℝ => ‖t ^ n‖) μ
  simpa only [Real.norm_eq_abs, abs_pow] using hμ.2.1 n

theorem RepresentsHamburgerMoments.integrable_complex_pow {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (n : ℕ) :
    Integrable (fun t : ℝ => (t : ℂ) ^ n) μ := by
  apply (integrable_norm_iff ((Complex.continuous_ofReal.pow n).aestronglyMeasurable)).mp
  change Integrable (fun t : ℝ => ‖(t : ℂ) ^ n‖) μ
  simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs] using hμ.2.1 n

theorem RepresentsHamburgerMoments.integral_complex_pow {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : RepresentsHamburgerMoments m μ) (n : ℕ) :
    (∫ t : ℝ, (t : ℂ) ^ n ∂μ) = (m n : ℂ) := by
  simp_rw [← Complex.ofReal_pow]
  rw [integral_complex_ofReal, hμ.2.2 n]

/-- Necessity follows by integrating the squared modulus of each coefficient sum. -/
theorem hamburger_measure_necessity : HamburgerExistenceSpec.MeasureNecessity := by
  intro m μ hμ N c
  let s := Finset.range (N + 1)
  let f : ℝ → ℂ := fun t => ∑ j ∈ s, ∑ k ∈ s,
    (t : ℂ) ^ (j + k) * star (c j) * c k
  have hterm (j k : ℕ) : Integrable
      (fun t : ℝ => (t : ℂ) ^ (j + k) * star (c j) * c k) μ :=
    ((RepresentsHamburgerMoments.integrable_complex_pow hμ (j + k)).mul_const _).mul_const _
  have hf : Integrable f μ :=
    integrable_finsetSum s (fun j _ => integrable_finsetSum s (fun k _ => hterm j k))
  have hform : (∫ t, f t ∂μ) =
      ∑ j ∈ s, ∑ k ∈ s, (m (j + k) : ℂ) * star (c j) * c k := by
    rw [integral_finsetSum s (fun j _ =>
      integrable_finsetSum s (fun k _ => hterm j k))]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finsetSum s (fun k _ => hterm j k)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_mul_const, integral_mul_const,
      RepresentsHamburgerMoments.integral_complex_pow hμ]
  have hpos (t : ℝ) : 0 ≤ (f t).re := by
    have heq : f t = star (∑ j ∈ s, c j * (t : ℂ) ^ j) *
        (∑ k ∈ s, c k * (t : ℂ) ^ k) := by
      simp only [f, map_sum, map_mul, map_pow, Complex.star_def, Complex.conj_ofReal,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_add]
      ring
    rw [heq]
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re]
    nlinarith [sq_nonneg (∑ j ∈ s, c j * (t : ℂ) ^ j).re,
      sq_nonneg (∑ j ∈ s, c j * (t : ℂ) ^ j).im]
  change 0 ≤ (∑ j ∈ s, ∑ k ∈ s, (m (j + k) : ℂ) * star (c j) * c k).re
  rw [← hform]
  change 0 ≤ RCLike.re (∫ t, f t ∂μ)
  rw [← integral_re hf]
  exact integral_nonneg hpos

/-- Inclusion of partial operators carries each existing power graph into the
corresponding extension power graph. -/
theorem powerValue_mono {H : Type*} [AddCommGroup H] [Module ℂ H]
    {S A : Operator ℂ H H} (hSA : S ≤ A) (n : ℕ) :
    powerValue S n ≤ powerValue A n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    refine ⟨?_, ?_⟩
    · rintro x ⟨hx, hsx⟩
      refine ⟨ih.1 hx, ?_⟩
      have hv := ih.2 (x := ⟨x, hx⟩) (y := ⟨x, ih.1 hx⟩) rfl
      change powerValue A n ⟨x, ih.1 hx⟩ ∈ A.domain
      rw [← hv]
      exact hSA.1 hsx
    · intro x y hxy
      change S _ = A _
      apply hSA.2
      exact ih.2 hxy

theorem hamburger_extension_realizes : HamburgerExistenceSpec.ExtensionRealizes := by
  intro m h A hSA hA
  refine ⟨hA, fun n => ?_⟩
  obtain ⟨he, hev⟩ := constantPolynomialVector_powers m h n
  have hpow := powerValue_mono hSA n
  refine ⟨hpow.1 he, ?_⟩
  have heq := hpow.2 (x := ⟨constantValue m h, he⟩)
    (y := ⟨constantValue m h, hpow.1 he⟩) rfl
  rw [← heq, hev]
  exact constantPolynomialVector_moments m h n

/-- Conjugating coefficients, as an actual semilinear involution. -/
def polynomialConjugation (m : ℕ → ℝ) (h : HankelNonnegative m) :
    MomentPolynomials m h ≃ₛₗ[starRingEnd ℂ] MomentPolynomials m h where
  toFun p := ofPolynomial ((rawPolynomial p).map (starRingEnd ℂ))
  invFun p := ofPolynomial ((rawPolynomial p).map (starRingEnd ℂ))
  left_inv p := by
    change Polynomial.map _ (Polynomial.map _ (rawPolynomial p)) = rawPolynomial p
    ext n
    simp only [Polynomial.coeff_map, starRingEnd_apply, star_star]
  right_inv p := by
    change Polynomial.map _ (Polynomial.map _ (rawPolynomial p)) = rawPolynomial p
    ext n
    simp only [Polynomial.coeff_map, starRingEnd_apply, star_star]
  map_add' p q := by
    change Polynomial.map _ (rawPolynomial p + rawPolynomial q) = _
    exact Polynomial.map_add _
  map_smul' c p := by
    dsimp only [MomentPolynomials, rawPolynomial, ofPolynomial] at *
    change Polynomial.map _ (c • rawPolynomial p) = star c • Polynomial.map _ (rawPolynomial p)
    ext n
    simp only [Polynomial.coeff_map, Polynomial.coeff_smul, starRingEnd_apply,
      smul_eq_mul, star_mul]
    erw [Polynomial.coeff_smul]
    simp only [Polynomial.coeff_map, starRingEnd_apply, smul_eq_mul, mul_comm]

theorem momentForm_conjugation (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p q : MomentPolynomials m h) :
    momentForm m (polynomialConjugation m h p) (polynomialConjugation m h q) =
      star (momentForm m p q) := by
  change momentFunctional m (((rawPolynomial p).map (starRingEnd ℂ)).map (starRingEnd ℂ) *
    (rawPolynomial q).map (starRingEnd ℂ)) =
      star (momentFunctional m ((rawPolynomial p).map (starRingEnd ℂ) * rawPolynomial q))
  rw [← momentFunctional_conj]
  simp [Polynomial.map_mul]


theorem polynomialConjugation_norm (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p : MomentPolynomials m h) :
    ‖polynomialClass m h (polynomialConjugation m h p)‖ = ‖polynomialClass m h p‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
    polynomialClass_inner, polynomialClass_inner, momentForm_conjugation]
  rfl

/-- Coefficient conjugation extends across the null quotient and completion. -/
def momentConjugation (m : ℕ → ℝ) (h : HankelNonnegative m) :
    MomentHilbertSpace m h ≃ₛₗᵢ[starRingEnd ℂ] MomentHilbertSpace m h :=
  (polynomialConjugation m h).extendOfIsometry (polynomialClass m h)
    (polynomialClass m h) (polynomialClass_dense m h) (polynomialClass_dense m h)
    (polynomialConjugation_norm m h)

@[simp] theorem momentConjugation_polynomialClass (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p : MomentPolynomials m h) :
    momentConjugation m h (polynomialClass m h p) =
      polynomialClass m h (polynomialConjugation m h p) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ _

theorem momentConjugation_involutive (m : ℕ → ℝ) (h : HankelNonnegative m) :
    Function.Involutive (momentConjugation m h) := by
  have heq : (fun x => momentConjugation m h (momentConjugation m h x)) = id := by
    apply (polynomialClass_dense m h).equalizer
      ((momentConjugation m h).continuous.comp (momentConjugation m h).continuous)
      continuous_id
    funext p
    simp only [Function.comp_apply, momentConjugation_polynomialClass]
    change polynomialClass m h (ofPolynomial
      (((rawPolynomial p).map (starRingEnd ℂ)).map (starRingEnd ℂ))) = polynomialClass m h p
    congr 1
    apply_fun rawPolynomial
    · ext n
      simp only [rawPolynomial_ofPolynomial, Polynomial.coeff_map, starRingEnd_apply, star_star]
    · exact Function.injective_id
  exact fun x => congrFun heq x

theorem momentConjugation_inner (m : ℕ → ℝ) (h : HankelNonnegative m)
    (x y : MomentHilbertSpace m h) :
    inner ℂ (momentConjugation m h x) (momentConjugation m h y) = star (inner ℂ x y) := by
  refine (polynomialClass_dense m h).induction ?_
    (isClosed_eq (by fun_prop) (by fun_prop)) x
  rintro _ ⟨p, rfl⟩
  refine (polynomialClass_dense m h).induction ?_
    (isClosed_eq (by fun_prop) (by fun_prop)) y
  rintro _ ⟨q, rfl⟩
  rw [momentConjugation_polynomialClass, momentConjugation_polynomialClass,
    polynomialClass_inner, polynomialClass_inner, momentForm_conjugation]

section Conjugation
universe u
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An involutive conjugation commuting with an operator also preserves its adjoint graph. -/
theorem adjoint_graph_conjugation (S : Operator ℂ H H) (hd : Dense (S.domain : Set H))
    (J : H ≃ₛₗᵢ[starRingEnd ℂ] H) (hJ : Function.Involutive J)
    (hi : ∀ x y, inner ℂ (J x) (J y) = star (inner ℂ x y))
    (hc : ∀ x y, (x, y) ∈ S.graph → (J x, J y) ∈ S.graph)
    {y z : H} (hyz : (y, z) ∈ (hilbertAdjoint S).graph) :
    (J y, J z) ∈ (hilbertAdjoint S).graph := by
  apply (mem_hilbertAdjoint_graph_iff S hd _ _).mpr
  intro x
  obtain ⟨w, hw, hwv⟩ := S.mem_graph_iff.mp (hc _ _ (S.mem_graph x))
  have htest := (mem_hilbertAdjoint_graph_iff S hd y z).mp hyz w
  have ht : inner ℂ (J (S x)) y = inner ℂ (J (x : H)) z := by
    rw [hw, hwv] at htest
    exact htest
  calc
    inner ℂ (S x) (J y) = star (inner ℂ (J (S x)) y) := by rw [← hi, hJ]
    _ = star (inner ℂ (J (x : H)) z) := congrArg star ht
    _ = inner ℂ (x : H) (J z) := by rw [← hi, hJ]

/-- Conjugation exchanges the nonreal adjoint eigenspaces. -/
theorem conjugation_mem_deficiency (S : Operator ℂ H H) (hd : Dense (S.domain : Set H))
    (J : H ≃ₛₗᵢ[starRingEnd ℂ] H) (hJ : Function.Involutive J)
    (hi : ∀ x y, inner ℂ (J x) (J y) = star (inner ℂ x y))
    (hc : ∀ x y, (x, y) ∈ S.graph → (J x, J y) ∈ S.graph)
    (z : ℂ) {x : H} (hx : x ∈ deficiencySpace S z) :
    J x ∈ deficiencySpace S (star z) := by
  obtain ⟨hx, hv⟩ := (mem_deficiencySpace_iff S z x).mp hx
  have hg : (x, z • x) ∈ (hilbertAdjoint S).graph :=
    (hilbertAdjoint S).mem_graph_iff.mpr ⟨⟨x, hx⟩, rfl, hv⟩
  have hjg := adjoint_graph_conjugation S hd J hJ hi hc hg
  rw [map_smulₛₗ, starRingEnd_apply] at hjg
  obtain ⟨y, hy, hyv⟩ := (hilbertAdjoint S).mem_graph_iff.mp hjg
  apply (mem_deficiencySpace_iff S (star z) (J x)).mpr
  have hval : (y : H) = J x := hy
  refine ⟨hval ▸ y.property, ?_⟩
  have heq : (⟨J x, hval ▸ y.property⟩ : (hilbertAdjoint S).domain) = y := Subtype.ext hval.symm
  rw [heq]
  exact hyv

/-- The isometric equivalence here is conjugate linear, with the correct scalar change. -/
def deficiencyConjugation (S : Operator ℂ H H) (hd : Dense (S.domain : Set H))
    (J : H ≃ₛₗᵢ[starRingEnd ℂ] H) (hJ : Function.Involutive J)
    (hi : ∀ x y, inner ℂ (J x) (J y) = star (inner ℂ x y))
    (hc : ∀ x y, (x, y) ∈ S.graph → (J x, J y) ∈ S.graph) (z : ℂ) :
    deficiencySpace S z ≃ₛₗᵢ[starRingEnd ℂ] deficiencySpace S (star z) where
  toFun x := ⟨J x, conjugation_mem_deficiency S hd J hJ hi hc z x.property⟩
  invFun x := ⟨J x, by
    simpa only [star_star] using
      conjugation_mem_deficiency S hd J hJ hi hc (star z) x.property⟩
  left_inv x := Subtype.ext (hJ x)
  right_inv x := Subtype.ext (hJ x)
  map_add' x y := Subtype.ext (map_add J (x : H) (y : H))
  map_smul' c x := Subtype.ext (map_smulₛₗ J c (x : H))
  norm_map' x := J.norm_map x

/-- Antiunitary equivalence preserves Hilbert cardinal dimension, including zero. -/
theorem hilbertDimension_eq_of_conjugateIsometryEquiv
    {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (J : E ≃ₛₗᵢ[starRingEnd ℂ] F)
    (hi : ∀ x y, inner ℂ (J x) (J y) = star (inner ℂ x y)) :
    hilbertDimensionValue E = hilbertDimensionValue F := by
  classical
  let b := (exists_hilbertBasis ℂ E).choose_spec.choose
  let v := fun i => J (b i)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp [v]
    rw [hi, orthonormal_iff_ite.mp b.orthonormal]
    split_ifs <;> simp
  have hsp : (Submodule.span ℂ (Set.range v)).orthogonal = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have he : J.symm x = 0 := by
      apply b.repr.injective
      ext i
      rw [b.repr_apply_apply]
      simp only [map_zero, lp.coeFn_zero, Pi.zero_apply]
      have hzero : inner ℂ (v i) x = 0 :=
        (Submodule.mem_orthogonal _ _).mp hx _ (Submodule.subset_span ⟨i, rfl⟩)
      have hh := hi (b i) (J.symm x)
      rw [J.apply_symm_apply] at hh
      apply (starRingEnd ℂ).injective
      simpa only [starRingEnd_apply, map_zero] using (hh.symm.trans hzero)
    change x = 0
    rw [← J.apply_symm_apply x, he, map_zero]
  let d := HilbertBasis.mkOfOrthogonalEqBot hv hsp
  exact hilbertDimension_eq_of_linearIsometryEquiv (b.repr.trans d.repr.symm)

/-- Taking the graph closure leaves the adjoint unchanged. -/
theorem symmetric_adjoint_closure (S : Operator ℂ H H) (hS : IsSymmetric S) :
    hilbertAdjoint S.closure = hilbertAdjoint S := by
  have hd : Dense ((hilbertAdjoint S).domain : Set H) := hS.1.mono hS.2.1
  change hilbertAdjoint (closure S hS.isClosable) = _
  rw [closure_eq_hilbertAdjoint_hilbertAdjoint S hS.1 hS.isClosable]
  exact hilbertAdjoint_hilbertAdjoint_of_closed (hilbertAdjoint S) hd
    (hilbertAdjoint_isClosed S hS.1)

theorem symmetric_closure (S : Operator ℂ H H) (hS : IsSymmetric S) :
    IsSymmetric S.closure := by
  refine ⟨hS.1.mono S.le_closure.1, ?_⟩
  change S.closure ≤ hilbertAdjoint S.closure
  rw [symmetric_adjoint_closure S hS]
  apply LinearPMap.le_of_le_graph
  rw [← hS.isClosable.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hS.2)
    (hilbertAdjoint_isClosed S hS.1)

/-- A symmetric operator with a commuting conjugation has a self-adjoint extension. -/
theorem exists_selfAdjoint_extension_of_conjugation (S : Operator ℂ H H)
    (hS : IsSymmetric S) (J : H ≃ₛₗᵢ[starRingEnd ℂ] H)
    (hJ : Function.Involutive J)
    (hi : ∀ x y, inner ℂ (J x) (J y) = star (inner ℂ x y))
    (hc : ∀ x y, (x, y) ∈ S.graph → (J x, J y) ∈ S.graph) :
    ∃ A : Operator ℂ H H, S ≤ A ∧ selfAdjointValue A := by
  have hSc := symmetric_closure S hS
  have hcc : ∀ x y, (x, y) ∈ S.closure.graph → (J x, J y) ∈ S.closure.graph := by
    intro x y hxy
    have hclosed : _root_.IsClosed
        {p : H × H | (J p.1, J p.2) ∈ S.closure.graph} :=
      hS.isClosable.closure_isClosed.preimage
        ((J.continuous.comp continuous_fst).prodMk (J.continuous.comp continuous_snd))
    have hsub : (S.graph : Set (H × H)) ⊆
        {p : H × H | (J p.1, J p.2) ∈ S.closure.graph} := by
      rintro ⟨a, b⟩ hab
      exact LinearPMap.le_graph_of_le S.le_closure (hc a b hab)
    have hm := closure_minimal hsub hclosed
    rw [← hS.isClosable.graph_closure_eq_closure_graph] at hxy
    exact hm hxy
  let : CompleteSpace (deficiencySpaceValue S.closure Complex.I) :=
    (deficiencySpace_closed S.closure hSc.1 Complex.I).isComplete.completeSpace_coe
  let : CompleteSpace (deficiencySpaceValue S.closure (-Complex.I)) :=
    (deficiencySpace_closed S.closure hSc.1 (-Complex.I)).isComplete.completeSpace_coe
  let : CompleteSpace (deficiencySpace S.closure Complex.I) :=
    (deficiencySpace_isClosed S.closure hSc.1 Complex.I).isComplete.completeSpace_coe
  let : CompleteSpace (deficiencySpace S.closure (-Complex.I)) :=
    (deficiencySpace_isClosed S.closure hSc.1 (-Complex.I)).isComplete.completeSpace_coe
  have hstar : star Complex.I = -Complex.I := Complex.conj_I
  let e : deficiencySpace S.closure Complex.I ≃ₛₗᵢ[starRingEnd ℂ]
      deficiencySpace S.closure (-Complex.I) :=
    { toFun x := ⟨J x, by
        have hm := conjugation_mem_deficiency S.closure hSc.1 J hJ hi hcc Complex.I x.property
        rwa [hstar] at hm⟩
      invFun x := ⟨J x, by
        have hm := conjugation_mem_deficiency S.closure hSc.1 J hJ hi hcc (-Complex.I) x.property
        rwa [star_neg, hstar, neg_neg] at hm⟩
      left_inv x := Subtype.ext (hJ x)
      right_inv x := Subtype.ext (hJ x)
      map_add' x y := Subtype.ext (map_add J (x : H) (y : H))
      map_smul' c x := Subtype.ext (map_smulₛₗ J c (x : H))
      norm_map' x := J.norm_map x }
  have he : ∀ x y, inner ℂ (e x) (e y) = star (inner ℂ x y) := by
    intro x y
    change inner ℂ (J (x : H)) (J (y : H)) = star (inner ℂ (x : H) (y : H))
    exact hi x y
  have hidx : deficiencyIndexPlusValue S.closure hSc.1 =
      deficiencyIndexMinusValue S.closure hSc.1 :=
    hilbertDimension_eq_of_conjugateIsometryEquiv e he
  obtain ⟨A, hCA, hA⟩ :=
    (exists_selfAdjoint_extension_iff_deficiencyIndices_eq S.closure
      hS.isClosable.closure_isClosed hSc).mpr hidx
  exact ⟨A, S.le_closure.trans hCA, hA⟩

end Conjugation

theorem minimalMultiplication_graph_conjugation (m : ℕ → ℝ) (h : HankelNonnegative m)
    (x y : MomentHilbertSpace m h) (hxy : (x, y) ∈ (multiplicationValue m h).graph) :
    (momentConjugation m h x, momentConjugation m h y) ∈ (multiplicationValue m h).graph := by
  obtain ⟨x, rfl, rfl⟩ := (multiplicationValue m h).mem_graph_iff.mp hxy
  obtain ⟨p, hp⟩ := x.property
  have heq : x = ⟨polynomialClass m h p, LinearMap.mem_range_self _ p⟩ :=
    Subtype.ext hp.symm
  subst x
  rw [minimalMultiplication_apply, momentConjugation_polynomialClass,
    momentConjugation_polynomialClass]
  apply (multiplicationValue m h).mem_graph_iff.mpr
  refine ⟨⟨polynomialClass m h (polynomialConjugation m h p),
    LinearMap.mem_range_self _ _⟩, rfl, ?_⟩
  rw [minimalMultiplication_apply]
  congr 1
  change ofPolynomial ((X : ℂ[X]) * (rawPolynomial p).map (starRingEnd ℂ)) =
    ofPolynomial (((X : ℂ[X]) * rawPolynomial p).map (starRingEnd ℂ))
  congr 1
  simp

/-- No determinacy or positive-mass premise is needed for the extension. -/
theorem hamburger_polynomial_extension : HamburgerExistenceSpec.PolynomialExtension := by
  intro m h
  have hs : IsSymmetric (multiplicationValue m h) :=
    ⟨minimalMultiplication_dense m h,
      LinearPMap.IsFormalAdjoint.le_adjoint (minimalMultiplication_dense m h)
        (minimalMultiplication_symmetric m h)⟩
  exact exists_selfAdjoint_extension_of_conjugation (multiplicationValue m h) hs
    (momentConjugation m h) (momentConjugation_involutive m h)
    (momentConjugation_inner m h) (minimalMultiplication_graph_conjugation m h)

theorem hamburger_operator_of_nonnegative (m : ℕ → ℝ) (hm : FiniteHankelNonnegative m) :
    HasHamburgerOperator m := by
  let h : HankelNonnegative m := (hankelNonnegative_iff_finite m).mpr hm
  obtain ⟨A, hSA, hA⟩ := hamburger_polynomial_extension m h
  exact ⟨MomentHilbertSpace m h, inferInstance, inferInstance, inferInstance,
    A, constantValue m h, hamburger_extension_realizes m h A hSA hA⟩

namespace SpectralMoments
open SpectralMeasure MeasurableSpectralCalculus
open UnboundedNormalSpectralTheorem.SpectralRepresentation
open Filter Set
variable {S H : Type*} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : ProjectionValuedMeasure S H} (C : BoundedRealization E)

theorem scalar_simple (a : SimpleFunc S ℂ) (x : H) :
    inner ℂ x (C.integral a x) = ∫ s, a s ∂C.measure x := by
  classical
  have := C.finite x
  rw [C.simple, SimpleFunc.integral_eq_sum a a.integrable_of_isFiniteMeasure]
  simp only [SpectralMeasure.Spec.SimpleIntegralValue, sum_apply,
    smul_apply, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro c hc
  have hB := a.measurableSet_fiber c
  have hp := E.coefficient_projection (a ⁻¹' {c}) hB x x
  change inner ℂ x (E (a ⁻¹' {c}) x) = inner ℂ (E (a ⁻¹' {c}) x) (E (a ⁻¹' {c}) x) at hp
  rw [hp, inner_self_eq_norm_sq_to_K, measureReal_def, C.measure_apply x _ hB,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  simp [Complex.real_smul, mul_comm]

theorem scalar_bounded (f : S → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f)
    (x : H) : inner ℂ x (C.integral f x) = ∫ s, f s ∂C.measure x := by
  have := C.finite x
  obtain ⟨a, ha⟩ := SpectralMeasure.exists_uniform_simple_approx f hf
  have hA := C.uniform_limit f hf a ha
  have hAx := (((ContinuousLinearMap.apply ℂ H) x).continuous.tendsto _).comp hA
  have hinner : Tendsto (fun n => inner ℂ x (C.integral (a n) x)) atTop
      (nhds (inner ℂ x (C.integral f x))) := by
    convert (tendsto_const_nhds (x := x)).inner hAx (𝕜 := ℂ) using 1
    · simp only [C.simple]; rfl
    · rfl
  have hInt : Tendsto (fun n => ∫ s, a n s ∂C.measure x) atTop
      (nhds (∫ s, f s ∂C.measure x)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall (fun n => (a n).measurable.aestronglyMeasurable)
    · obtain ⟨M, hM⟩ := hf.2
      refine ⟨M + 1, ?_⟩
      filter_upwards [Metric.tendstoUniformly_iff.mp ha 1 (by norm_num)] with n hn
      apply Eventually.of_forall
      intro s
      have hd := hn s
      rw [dist_eq_norm] at hd
      have htri : ‖a n s‖ ≤ ‖f s‖ + ‖f s - a n s‖ := by
        exact norm_le_norm_add_norm_sub (f s) (a n s)
      linarith [hM s]
    · exact Eventually.of_forall (fun s => ha.tendsto_at s)
  simp only [scalar_simple C] at hinner
  exact tendsto_nhds_unique hinner hInt
/-- Powers localized to a region where the symbol is bounded are bounded symbols. -/
theorem bounded_localized_pow {f : S → ℂ} (hf : Measurable f)
    {B : Set S} (hB : MeasurableSet B) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ s ∈ B, ‖f s‖ ≤ M) (n : ℕ) :
    SpectralMeasure.Spec.IsBoundedMeasurable (B.indicator (fun s => f s ^ n)) := by
  classical
  refine ⟨(hf.pow_const n).indicator hB, M ^ n, fun s => ?_⟩
  by_cases hs : s ∈ B
  · simpa only [Set.indicator_of_mem hs, norm_pow] using
      pow_le_pow_left₀ (norm_nonneg (f s)) (hb s hs) n
  · simp [hs, pow_nonneg hM]

/-- This identity uses the exact product domains, in either finite or infinite dimension. -/
theorem localized_power_identity {f : S → ℂ} (hf : Measurable f)
    {B : Set S} (hB : MeasurableSet B) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ s ∈ B, ‖f s‖ ≤ M) (n : ℕ) :
    ∀ (x : (powerValue (measurableIntegral C f) n).domain) (k : ℕ),
      C.integral (B.indicator (fun s => f s ^ k)) (powerValue (measurableIntegral C f) n x) =
        C.integral (B.indicator (fun s => f s ^ (k + n))) (x : H) := by
  have hbounded := bounded_localized_pow hf hB hM hb
  have hmul (k : ℕ) : f * B.indicator (fun s => f s ^ k) =
      B.indicator (fun s => f s ^ (k + 1)) := by
    classical
    funext s
    by_cases hs : s ∈ B <;> simp [hs, pow_succ, mul_comm]
  induction n with
  | zero => intro x k; simp only [Nat.add_zero]; rfl
  | succ n ih =>
    intro x k
    let hx : (powerValue (measurableIntegral C f) n).domain := ⟨x, x.property.1⟩
    let hy : (measurableIntegral C f).domain :=
      ⟨powerValue (measurableIntegral C f) n hx, x.property.2⟩
    change C.integral _ (measurableIntegral C f hy) = _
    rw [bounded_product_commutes C hf (hbounded k) (by rw [hmul]; exact hbounded (k + 1)),
      hmul, ih hx (k + 1)]
    have hk : k + 1 + n = k + (n + 1) := by omega
    rw [hk]

/-- Localizing the nth power agrees with integrating the localized nth monomial. -/
theorem projected_power {f : S → ℂ} (hf : Measurable f)
    {B : Set S} (hB : MeasurableSet B) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ s ∈ B, ‖f s‖ ≤ M) (n : ℕ)
    (x : (powerValue (measurableIntegral C f) n).domain) :
    C.integral (B.indicator (fun s => f s ^ n)) (x : H) =
      E B (powerValue (measurableIntegral C f) n x) := by
  have ht := localized_power_identity C hf hB hM hb n x 0
  simpa only [pow_zero, Nat.zero_add, integral_indicator_one C B hB] using ht.symm

/-- Localized power norms bound the full nonnegative scalar integral by monotone convergence. -/
theorem power_lintegral_bound {f : S → ℂ} (hf : Measurable f) (n : ℕ)
    (x : (powerValue (measurableIntegral C f) n).domain) :
    (∫⁻ s, ENNReal.ofReal (‖f s ^ n‖ ^ 2) ∂C.measure (x : H)) ≤
      ENNReal.ofReal (‖powerValue (measurableIntegral C f) n x‖ ^ 2) := by
  let B : ℕ → Set S := fun k => {s | ‖f s‖ ≤ (k : ℝ)}
  have hB (k : ℕ) : MeasurableSet (B k) := measurableSet_le hf.norm measurable_const
  let g : ℕ → S → ℂ := fun k => (B k).indicator (fun s => f s ^ n)
  have hg (k : ℕ) : SpectralMeasure.Spec.IsBoundedMeasurable (g k) :=
    bounded_localized_pow hf (hB k) (Nat.cast_nonneg k) (fun _ hs => hs) n
  let G : ℕ → S → ℝ≥0∞ := fun k s => ENNReal.ofReal (‖g k s‖ ^ 2)
  have hG (k : ℕ) : Measurable (G k) :=
    ENNReal.measurable_ofReal.comp (((hg k).1.norm).pow_const 2)
  have hm : ∀ s, Monotone (fun k => G k s) := by
    intro s k l hkl
    classical
    by_cases hk : s ∈ B k
    · have hk' : ‖f s‖ ≤ (k : ℝ) := hk
      have hl : s ∈ B l := hk'.trans (by exact_mod_cast hkl)
      simp only [G, g, Set.indicator_of_mem hk, Set.indicator_of_mem hl, le_refl]
    · simp only [G, g, Set.indicator_of_notMem hk, norm_zero, zero_pow (by decide : 2 ≠ 0),
        ENNReal.ofReal_zero, zero_le]
  have hl : ∀ s, Tendsto (fun k => G k s) atTop
      (nhds (ENNReal.ofReal (‖f s ^ n‖ ^ 2))) := by
    intro s
    obtain ⟨K, hK⟩ := exists_nat_ge ‖f s‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop K] with k hk
    have hmem : s ∈ B k := hK.trans (by exact_mod_cast hk)
    simp only [G, g, Set.indicator_of_mem hmem]
  have ht := lintegral_tendsto_of_tendsto_of_monotone (μ := C.measure (x : H))
    (fun k => (hG k).aemeasurable) (Eventually.of_forall hm) (Eventually.of_forall hl)
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro k
  rw [show (∫⁻ s, G k s ∂C.measure (x : H)) =
      ENNReal.ofReal (‖C.integral (g k) (x : H)‖ ^ 2) from C.lintegral_norm_sq _ (hg k) _]
  rw [projected_power C hf (hB k) (Nat.cast_nonneg k) (fun _ hs => hs) n x]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _)
    (E.norm_apply_le (B k) (hB k) _) 2)

/-- Membership in an operator-power domain gives actual scalar L² integrability. -/
theorem power_integrable_sq_norm {f : S → ℂ} (hf : Measurable f) (n : ℕ)
    (x : (powerValue (measurableIntegral C f) n).domain) :
    Integrable (fun s => ‖f s ^ n‖ ^ 2) (C.measure (x : H)) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((hf.pow_const n).norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall (fun s => sq_nonneg ‖f s ^ n‖))).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (power_lintegral_bound C hf n x)

/-- The finite scalar measure has every moment allowed by the actual operator domain. -/
theorem power_integrable {f : S → ℂ} (hf : Measurable f) (n : ℕ)
    (x : (powerValue (measurableIntegral C f) n).domain) :
    Integrable (fun s => f s ^ n) (C.measure (x : H)) := by
  have := C.finite (x : H)
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((memLp_two_iff_integrable_sq_norm (hf.pow_const n).aestronglyMeasurable).mpr
      (power_integrable_sq_norm C hf n x))

/-- The scalar power-moment formula, without a determinacy or cyclicity assumption. -/
theorem scalar_power {f : S → ℂ} (hf : Measurable f) (n : ℕ)
    (x : (powerValue (measurableIntegral C f) n).domain) :
    inner ℂ (x : H) (powerValue (measurableIntegral C f) n x) =
      ∫ s, f s ^ n ∂C.measure (x : H) := by
  let B : ℕ → Set S := fun k => {s | ‖f s‖ ≤ (k : ℝ)}
  have hB (k : ℕ) : MeasurableSet (B k) := measurableSet_le hf.norm measurable_const
  let g : ℕ → S → ℂ := fun k => (B k).indicator (fun s => f s ^ n)
  have hg (k : ℕ) : SpectralMeasure.Spec.IsBoundedMeasurable (g k) :=
    bounded_localized_pow hf (hB k) (Nat.cast_nonneg k) (fun _ hs => hs) n
  have hvec : Tendsto (fun k => C.integral (g k) (x : H)) atTop
      (nhds (powerValue (measurableIntegral C f) n x)) := by
    have ht := C.cutoff_tendsto hf (powerValue (measurableIntegral C f) n x)
    have heq (k : ℕ) : C.integral (g k) (x : H) =
        C.integral (cutoffIndicator f k) (powerValue (measurableIntegral C f) n x) := by
      rw [projected_power C hf (hB k) (Nat.cast_nonneg k) (fun _ hs => hs) n x]
      rw [cutoffIndicator, integral_indicator_one C _ (hB k)]
    simpa only [heq] using ht
  have hinner := (tendsto_const_nhds (x := (x : H))).inner hvec (𝕜 := ℂ)
  have hInt : Tendsto (fun k => ∫ s, g k s ∂C.measure (x : H)) atTop
      (nhds (∫ s, f s ^ n ∂C.measure (x : H))) := by
    apply tendsto_integral_of_dominated_convergence (fun s => ‖f s ^ n‖)
    · intro k; exact (hg k).1.aestronglyMeasurable
    · exact (power_integrable C hf n x).norm
    · intro k
      apply Eventually.of_forall
      intro s
      classical
      by_cases hs : s ∈ B k
      · simp only [g, Set.indicator_of_mem hs, le_refl]
      · simp only [g, Set.indicator_of_notMem hs, norm_zero, norm_nonneg]
    · apply Eventually.of_forall
      intro s
      obtain ⟨K, hK⟩ := exists_nat_ge ‖f s‖
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop K] with k hk
      have hs : s ∈ B k := hK.trans (by exact_mod_cast hk)
      simp only [g, Set.indicator_of_mem hs]
  simp only [scalar_bounded C _ (hg _)] at hinner
  exact tendsto_nhds_unique hinner hInt

end SpectralMoments

/-- The scalar PVM measure represents all prescribed moments, with finite absolute moments. -/
theorem hamburger_operator_sufficiency : HamburgerExistenceSpec.OperatorSufficiency := by
  intro m
  rintro ⟨H, instNorm, instInner, instComplete, A, e, hA⟩
  have hc : A.IsClosed := by
    have heq : A = hilbertAdjoint A := hA.1.2
    rw [heq]
    exact hilbertAdjoint_isClosed A hA.1.1
  obtain ⟨hreal, _⟩ := UnboundedNormalSpectralTheorem.selfadjoint_spectral H A
    hA.1.1 hc hA.1.2.symm
  obtain ⟨E, C, hC, _⟩ := hreal
  rw [← hC] at hA
  refine ⟨C.measure e, C.finite e, ?_, ?_⟩
  · intro n
    obtain ⟨he, _⟩ := hA.2 n
    have hp := SpectralMoments.power_integrable C Complex.continuous_ofReal.measurable n ⟨e, he⟩
    simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs] using hp.norm
  · intro n
    obtain ⟨he, hev⟩ := hA.2 n
    have hm := (SpectralMoments.scalar_power C Complex.continuous_ofReal.measurable n ⟨e, he⟩).symm.trans hev
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_pow, integral_complex_ofReal] using hm

/-- Logical assembly from the two analytic implications. -/
theorem hamburger_existence_of_extension_and_spectral
    (hext : HamburgerExistenceSpec.PolynomialExtension)
    (hspectral : HamburgerExistenceSpec.OperatorSufficiency) :
    HamburgerExistenceSpec.HamburgerExistence := by
  intro m
  have hpositive_to_operator : FiniteHankelNonnegative m → HasHamburgerOperator m := by
    intro hm
    let h : HankelNonnegative m := (hankelNonnegative_iff_finite m).mpr hm
    obtain ⟨A, hSA, hA⟩ := hext m h
    exact ⟨MomentHilbertSpace m h, inferInstance, inferInstance, inferInstance,
      A, constantValue m h, hamburger_extension_realizes m h A hSA hA⟩
  have hmeasure_to_positive : HasHamburgerMeasure m → FiniteHankelNonnegative m := by
    rintro ⟨μ, hμ⟩
    exact hamburger_measure_necessity m μ hμ
  exact ⟨⟨fun hm => hspectral m (hpositive_to_operator hm), hmeasure_to_positive⟩,
    ⟨hpositive_to_operator, fun hA => hmeasure_to_positive (hspectral m hA)⟩⟩

/-- Hamburger's three-way existence theorem, including zero and degenerate sequences. -/
theorem hamburger_existence : HamburgerExistenceSpec.HamburgerExistence :=
  hamburger_existence_of_extension_and_spectral hamburger_polynomial_extension
    hamburger_operator_sufficiency

end HamburgerExistenceProof

/-- A representing measure makes every finite Hankel form nonnegative. -/
theorem hamburger_measure_necessity : HamburgerExistenceSpec.MeasureNecessity :=
  HamburgerExistenceProof.hamburger_measure_necessity

/-- Equal deficiency indices give a self-adjoint extension on the polynomial completion. -/
theorem hamburger_polynomial_extension : HamburgerExistenceSpec.PolynomialExtension :=
  HamburgerExistenceProof.hamburger_polynomial_extension

/-- Every self-adjoint extension retains the polynomial vector's power moments. -/
theorem hamburger_extension_realizes : HamburgerExistenceSpec.ExtensionRealizes :=
  HamburgerExistenceProof.hamburger_extension_realizes

/-- The scalar spectral measure represents all moments, including absolute moments. -/
theorem hamburger_operator_sufficiency : HamburgerExistenceSpec.OperatorSufficiency :=
  HamburgerExistenceProof.hamburger_operator_sufficiency

/-- Hamburger's three-way existence theorem, including zero and degenerate sequences. -/
theorem hamburger_existence : HamburgerExistenceSpec.HamburgerExistence :=
  HamburgerExistenceProof.hamburger_existence

end ExpandedFA.Moments
