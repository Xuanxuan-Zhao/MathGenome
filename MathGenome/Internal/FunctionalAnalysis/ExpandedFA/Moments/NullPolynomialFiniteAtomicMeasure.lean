import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.NullPolynomialFiniteAtomicMeasure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Moments.HamburgerDeterminacy
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open MeasureTheory Polynomial
namespace ExpandedFA.Moments.NullPolynomialFiniteAtomicMeasure
open PolynomialMomentHilbertSpaceSpec HamburgerDeterminacy

/-- The null space is stable under multiplication by every polynomial. -/
theorem null_mul (m : ℕ → ℝ) (h : HankelNonnegative m) (p : ℂ[X])
    (hp : polynomialClass m h (ofPolynomial p) = 0) (q : ℂ[X]) :
    polynomialClass m h (ofPolynomial (q * p)) = 0 := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    change polynomialClass m h ((q + r) * p) = 0
    rw [add_mul]
    change polynomialClass m h
      (ofPolynomial (m := m) (h := h) (q * p) +
        ofPolynomial (m := m) (h := h) (r * p)) = 0
    rw [map_add, hq, hr, add_zero]
  | monomial n c =>
    have hn : ∀ n : ℕ, polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n * p)) = 0 := by
      intro n
      induction n with
      | zero => simpa using hp
      | succ n ih =>
        have hz := nullPolynomials_multiplyX m h
          (ofPolynomial ((X : ℂ[X]) ^ n * p)) ih
        change polynomialClass m h (ofPolynomial ((X : ℂ[X]) * (X ^ n * p))) = 0 at hz
        simpa only [pow_succ', mul_assoc] using hz
    rw [← C_mul_X_pow_eq_monomial, mul_assoc, C_mul']
    change polynomialClass m h (c • ofPolynomial ((X : ℂ[X]) ^ n * p)) = 0
    rw [map_smul, hn, smul_zero]

/-- Division by a nonzero null polynomial reduces every polynomial class to a
fixed finite-dimensional space of remainders. -/
theorem class_range_finite (m : ℕ → ℝ) (h : HankelNonnegative m) (p : ℂ[X])
    (hp : p ≠ 0) (hn : momentForm m p p = 0) :
    FiniteDimensional ℂ (polynomialClass m h).range := by
  let f : ℂ[X] →ₗ[ℂ] MomentHilbertSpace m h := polynomialClass m h
  have hz : f p = 0 := (nullPolynomials_iff m h (ofPolynomial p)).mpr hn
  let d := degreeLT ℂ (p.natDegree + 1)
  have hd : FiniteDimensional ℂ d := inferInstance
  let g : d →ₗ[ℂ] f.range :=
    { toFun := fun q => ⟨f q, LinearMap.mem_range_self _ _⟩
      map_add' := by intros; apply Subtype.ext; exact f.map_add _ _
      map_smul' := by intros; apply Subtype.ext; exact f.map_smul _ _ }
  apply FiniteDimensional.of_surjective g
  rintro ⟨y, q, rfl⟩
  have hdeg : q % p ∈ d := by
    apply mem_degreeLT.mpr
    exact (degree_mod_lt q hp).trans
      (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self p.natDegree))
  refine ⟨⟨q % p, hdeg⟩, ?_⟩
  apply Subtype.ext
  change f (q % p) = f q
  have he := congrArg f (EuclideanDomain.div_add_mod q p)
  have hmul : f (p * (q / p)) = 0 := by
    change polynomialClass m h (ofPolynomial (p * (q / p))) = 0
    simpa only [mul_comm] using null_mul m h p hz (q / p)
  simpa only [map_add, hmul, zero_add] using he

/-- The finite-dimensional range is closed, so density makes it the full
Hilbert completion. -/
theorem class_range_eq_top (m : ℕ → ℝ) (h : HankelNonnegative m) (p : ℂ[X])
    (hp : p ≠ 0) (hn : momentForm m p p = 0) :
    (polynomialClass m h).range = ⊤ := by
  have := class_range_finite m h p hp hn
  have hd : Dense ((polynomialClass m h).range : Set (MomentHilbertSpace m h)) :=
    polynomialClass_dense m h
  have ht := Submodule.dense_iff_topologicalClosure_eq_top.mp hd
  rwa [(polynomialClass m h).range.closed_of_finiteDimensional.submodule_topologicalClosure_eq] at ht

theorem finite_dimensional : NullPolynomialFiniteAtomicMeasureSpec.FiniteDimension := by
  intro m h p hp hn
  have ht := class_range_eq_top m h p hp hn
  have := class_range_finite m h p hp hn
  have : FiniteDimensional ℂ (MomentHilbertSpace m h) := by
    apply FiniteDimensional.of_surjective (polynomialClass m h).range.subtype
    intro x
    exact ⟨⟨x, by rw [ht]; trivial⟩, rfl⟩
  refine ⟨?_, inferInstance⟩
  exact FiniteDimensional.of_injective
    (UniformSpace.Completion.toComplₗᵢ : PolynomialQuotient m h →ₗᵢ[ℂ]
      MomentHilbertSpace m h).toLinearMap
    UniformSpace.Completion.toComplₗᵢ.injective

/-- Full domain leaves no room for a proper operator extension. -/
theorem multiplication_selfAdjoint (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p : ℂ[X]) (hp : p ≠ 0) (hn : momentForm m p p = 0) :
    Unbounded.SymmetryAndDeficienciesSpec.selfAdjointValue (multiplicationValue m h) := by
  obtain ⟨A, hSA, hA⟩ := hamburger_polynomial_extension m h
  have ht : (multiplicationValue m h).domain = ⊤ := class_range_eq_top m h p hp hn
  have he : multiplicationValue m h = A :=
    LinearPMap.eq_of_le_of_domain_eq hSA
      (le_antisymm hSA.1 (by rw [ht]; exact le_top))
  rwa [he]

theorem null_determinate (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p : ℂ[X]) (hp : p ≠ 0) (hn : momentForm m p p = 0) :
    HamburgerDeterminacySpec.Determinate m := by
  have hs := multiplication_selfAdjoint m h p hp hn
  have hc : (multiplicationValue m h).IsClosed := by
    rw [hs.2]
    exact Unbounded.hilbertAdjoint_isClosed _ hs.1
  have he : (multiplicationValue m h).closure = multiplicationValue m h := by
    apply LinearPMap.eq_of_eq_graph
    rw [← hc.isClosable.graph_closure_eq_closure_graph]
    exact hc.submodule_topologicalClosure_eq
  apply determinate_of_essentiallySelfAdjoint m h
  exact ⟨hs.1, hc.isClosable, he.symm ▸ hs⟩

/-- Every representing measure annihilates the same null polynomial almost
 everywhere, without any polynomial-density assumption on its L² space. -/
theorem null_eval_ae (m : ℕ → ℝ) (h : HankelNonnegative m) (p : ℂ[X])
    (hn : momentForm m p p = 0) (μ : Measure ℝ)
    (hμ : RepresentsHamburgerMoments m μ) :
    ∀ᵐ (t : ℝ) ∂μ, p.eval (t : ℂ) = 0 := by
  have hz : polynomialClass m h (ofPolynomial p) = 0 :=
    (nullPolynomials_iff m h (ofPolynomial p)).mpr hn
  have hv : polynomialEvaluationL2 hμ h (ofPolynomial p) = 0 := by
    rw [← representingIsometry_class, hz, map_zero]
  have hf := (memLp_polynomial_eval hμ p).coeFn_toLp
  change ⇑(polynomialEvaluationL2 hμ h (ofPolynomial p)) =ᵐ[μ]
    (fun t : ℝ => p.eval (t : ℂ)) at hf
  rw [hv] at hf
  filter_upwards [hf, Lp.coeFn_zero ℂ 2 μ] with t ht hz
  exact ht.symm.trans hz

/-- The unique representing measure has finitely many distinct real atoms,
after removing every root with zero mass. -/
theorem unique_atomic_measure : NullPolynomialFiniteAtomicMeasureSpec.UniqueAtomicMeasure := by
  classical
  intro m h p hp hn
  obtain ⟨μ, hμ, hu⟩ := null_determinate m h p hp hn
  letI : IsFiniteMeasure μ := hμ.1
  have hr : Set.Finite {t : ℝ | p.eval (t : ℂ) = 0} :=
    (finite_setOfPred_isRoot hp).preimage Complex.ofReal_injective.injOn
  let r : Finset ℝ := hr.toFinset
  let s := r.filter (fun t => μ {t} ≠ 0)
  have hae : ∀ᵐ t ∂μ, t ∈ r := by
    simpa only [r, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using null_eval_ae m h p hn μ hμ
  have hm : μ = ∑ t ∈ r, μ {t} • Measure.dirac t := Measure.ae_mem_finset_iff.mp hae
  refine ⟨μ, hμ, hu, s, ?_, ?_⟩
  · intro t ht
    obtain ⟨htr, htz⟩ := Finset.mem_filter.mp ht
    refine ⟨bot_lt_iff_ne_bot.mpr htz, measure_lt_top μ _, ?_⟩
    simpa only [r, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using htr
  · have he : (∑ t ∈ s, μ {t} • Measure.dirac t) =
        ∑ t ∈ r, μ {t} • Measure.dirac t := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro t htr hts
      have hz : μ {t} = 0 := by
        by_contra hne
        exact hts (Finset.mem_filter.mpr ⟨htr, hne⟩)
      rw [hz, zero_smul]
    exact hm.trans he.symm

end ExpandedFA.Moments.NullPolynomialFiniteAtomicMeasure
