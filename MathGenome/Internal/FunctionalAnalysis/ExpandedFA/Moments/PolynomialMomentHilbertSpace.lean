import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.PolynomialMomentHilbertSpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.HilbertAdjoint
import Mathlib.Tactic.Ring

noncomputable section
open Polynomial Complex
namespace ExpandedFA.Moments
open PolynomialMomentHilbertSpaceSpec

def polynomialMomentForm : FormTypeExpected := momentForm

abbrev polynomialQuotient : QuotientTypeExpected := PolynomialQuotient

abbrev momentHilbertSpace : HilbertTypeExpected := MomentHilbertSpace

def nullPolynomials : NullTypeExpected := nullSpaceValue

def minimalMultiplication : OperatorTypeExpected := multiplicationValue

def constantPolynomialVector : ConstantTypeExpected := constantValue

theorem polynomialClass_inner : ClassInnerExpected := by
  intro m h p q
  change inner ℂ
    ((SeparationQuotient.mk p : PolynomialQuotient m h) : MomentHilbertSpace m h)
    ((SeparationQuotient.mk q : PolynomialQuotient m h) : MomentHilbertSpace m h) = _
  rw [UniformSpace.Completion.inner_coe, SeparationQuotient.inner_mk_mk]
  rfl

theorem nullPolynomials_iff : NullExpected := by
  intro m h p
  change polynomialClass m h p = 0 ↔ _
  rw [← inner_self_eq_zero (𝕜 := ℂ), polynomialClass_inner]

theorem momentForm_multiplyX (m : ℕ → ℝ) (p q : ℂ[X]) :
    momentForm m ((X : ℂ[X]) * p) q = momentForm m p ((X : ℂ[X]) * q) := by
  simp [momentForm, Polynomial.map_mul, mul_left_comm, mul_assoc]

theorem nullPolynomials_multiplyX : NullMultiplicationExpected := by
  intro m h p hp
  apply (nullPolynomials_iff m h _).mpr
  change momentForm m ((X : ℂ[X]) * rawPolynomial p) ((X : ℂ[X]) * rawPolynomial p) = 0
  rw [momentForm_multiplyX]
  have hi := polynomialClass_inner m h p
    (ofPolynomial ((X : ℂ[X]) * ((X : ℂ[X]) * rawPolynomial p)))
  have hz : polynomialClass m h p = 0 := hp
  rw [hz, inner_zero_left] at hi
  exact hi.symm

theorem minimalMultiplication_domain : DomainExpected := by
  intro m h
  rfl

theorem polynomialClass_dense (m : ℕ → ℝ) (h : HankelNonnegative m) :
    DenseRange (polynomialClass m h) := by
  have h₁ : DenseRange (fun q : PolynomialQuotient m h =>
      (q : MomentHilbertSpace m h)) := UniformSpace.Completion.denseRange_coe
  have h₂ : DenseRange (fun p : MomentPolynomials m h => SeparationQuotient.mk p) :=
    SeparationQuotient.surjective_mk.denseRange
  exact h₁.comp h₂ (UniformSpace.Completion.continuous_coe _)

theorem minimalMultiplication_dense : DenseExpected := by
  intro m h
  exact polynomialClass_dense m h

private theorem multiplyX_class_eq (m : ℕ → ℝ) (h : HankelNonnegative m)
    (p q : MomentPolynomials m h) (hpq : polynomialClass m h p = polynomialClass m h q) :
    polynomialClass m h (multiplyX m h p) = polynomialClass m h (multiplyX m h q) := by
  apply sub_eq_zero.mp
  rw [← map_sub, ← map_sub]
  exact nullPolynomials_multiplyX m h (p - q) (by
    change polynomialClass m h (p - q) = 0
    rw [map_sub, hpq, sub_self])

theorem minimalMultiplication_apply : MultiplicationExpected := by
  intro m h p
  change polynomialClass m h (multiplyX m h (representative m h _)) = _
  apply multiplyX_class_eq
  have hr := Classical.choose_spec
    ((polynomialClass m h).rangeRestrict.exists_rightInverse_of_surjective
      (polynomialClass m h).range_rangeRestrict)
  have hh := LinearMap.congr_fun hr
    (⟨polynomialClass m h p, LinearMap.mem_range_self _ p⟩ : (polynomialClass m h).range)
  exact congrArg Subtype.val hh

theorem minimalMultiplication_symmetric : SymmetricExpected := by
  intro m h x y
  obtain ⟨p, hp⟩ := x.property
  obtain ⟨q, hq⟩ := y.property
  have hx : x = ⟨polynomialClass m h p, LinearMap.mem_range_self _ p⟩ := Subtype.ext hp.symm
  have hy : y = ⟨polynomialClass m h q, LinearMap.mem_range_self _ q⟩ := Subtype.ext hq.symm
  subst x
  subst y
  rw [minimalMultiplication_apply, minimalMultiplication_apply]
  change inner ℂ (polynomialClass m h (multiplyX m h p)) (polynomialClass m h q) =
    inner ℂ (polynomialClass m h p) (polynomialClass m h (multiplyX m h q))
  rw [polynomialClass_inner m h _ _, polynomialClass_inner m h _ _]
  exact momentForm_multiplyX m p q

theorem polynomialMomentForm_formula : FormFormulaExpected := by
  intro m p q
  have hp : p.map (starRingEnd ℂ) =
      ∑ j ∈ p.support, monomial j (star (p.coeff j)) := by
    conv_lhs => rw [← p.sum_monomial_eq]
    simp only [Polynomial.sum, Polynomial.map_sum, Polynomial.map_monomial,
      starRingEnd_apply]
  have hq : q = ∑ k ∈ q.support, monomial k (q.coeff k) :=
    q.sum_monomial_eq.symm
  unfold momentForm
  rw [hp]
  have he : (∑ j ∈ p.support, monomial j (star (p.coeff j))) * q =
      (∑ j ∈ p.support, monomial j (star (p.coeff j))) *
        (∑ k ∈ q.support, monomial k (q.coeff k)) := congrArg _ hq
  rw [he]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, monomial_mul_monomial,
    momentFunctional_monomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem minimalMultiplication_powers : PowersExpected := by
  intro m h n
  induction n with
  | zero =>
    intro p
    refine ⟨Submodule.mem_top, ?_⟩
    change polynomialClass m h p = polynomialClass m h ((X : ℂ[X]) ^ 0 * rawPolynomial p)
    congr 1
    change rawPolynomial p = (X : ℂ[X]) ^ 0 * rawPolynomial p
    simp
  | succ n ih =>
    intro p
    obtain ⟨hp, hev⟩ := ih p
    let q : MomentPolynomials m h := ofPolynomial ((X : ℂ[X]) ^ n * rawPolynomial p)
    have hq : polynomialClass m h q ∈ (multiplicationValue m h).domain :=
      LinearMap.mem_range_self _ q
    have hs : Unbounded.OperatorDomainsSpec.powerValue (multiplicationValue m h) n
        ⟨polynomialClass m h p, hp⟩ ∈ (multiplicationValue m h).domain := by
      rw [hev]
      exact hq
    refine ⟨⟨hp, hs⟩, ?_⟩
    change multiplicationValue m h
      ⟨Unbounded.OperatorDomainsSpec.powerValue (multiplicationValue m h) n
        ⟨polynomialClass m h p, hp⟩, hs⟩ = _
    have heq : (⟨Unbounded.OperatorDomainsSpec.powerValue (multiplicationValue m h) n
        ⟨polynomialClass m h p, hp⟩, hs⟩ : (multiplicationValue m h).domain) =
        ⟨polynomialClass m h q, hq⟩ := Subtype.ext hev
    rw [heq, minimalMultiplication_apply]
    congr 1
    change (X : ℂ[X]) * ((X : ℂ[X]) ^ n * rawPolynomial p) =
      (X : ℂ[X]) ^ (n + 1) * rawPolynomial p
    rw [pow_succ]
    ring

theorem constantPolynomialVector_powers : ConstantPowersExpected := by
  intro m h n
  obtain ⟨he, hev⟩ := minimalMultiplication_powers m h n 1
  refine ⟨he, ?_⟩
  calc
    _ = polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n * rawPolynomial (1 : MomentPolynomials m h))) := hev
    _ = polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n)) := by
      congr 2
      change (X : ℂ[X]) ^ n * (1 : ℂ[X]) = (X : ℂ[X]) ^ n
      exact mul_one _

theorem constantPolynomialVector_moments : MomentsExpected := by
  intro m h n
  change inner ℂ (polynomialClass m h 1)
    (polynomialClass m h (ofPolynomial ((X : ℂ[X]) ^ n))) = _
  rw [polynomialClass_inner m h]
  change momentForm m (1 : ℂ[X]) ((X : ℂ[X]) ^ n) = _
  simp [momentForm]

/-- The form of arbitrary finite coefficient sums, without a support restriction. -/
theorem momentForm_sum_monomials (m : ℕ → ℝ) (s t : Finset ℕ)
    (c d : ℕ → ℂ) :
    momentForm m (∑ j ∈ s, monomial j (c j)) (∑ k ∈ t, monomial k (d k)) =
      ∑ j ∈ s, ∑ k ∈ t, (m (j + k) : ℂ) * star (c j) * d k := by
  simp only [momentForm, Polynomial.map_sum, Polynomial.map_monomial,
    starRingEnd_apply, Finset.sum_mul, Finset.mul_sum, map_sum,
    monomial_mul_monomial, momentFunctional_monomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem hankelNonnegative_iff_finite : PositivityExpected := by
  intro m
  constructor
  · intro h N c
    have hp := h (∑ j ∈ Finset.range (N + 1), monomial j (c j))
    rwa [momentForm_sum_monomials] at hp
  · intro h p
    have he : momentForm m p p =
        ∑ j ∈ Finset.range (p.natDegree + 1), ∑ k ∈ Finset.range (p.natDegree + 1),
          (m (j + k) : ℂ) * star (p.coeff j) * p.coeff k := by
      calc
        _ = momentForm m (∑ j ∈ Finset.range (p.natDegree + 1), monomial j (p.coeff j))
            (∑ k ∈ Finset.range (p.natDegree + 1), monomial k (p.coeff k)) := by
          conv_lhs => arg 2; rw [p.as_sum_range]
          conv_lhs => arg 3; rw [p.as_sum_range]
        _ = _ := momentForm_sum_monomials m _ _ _ _
    rw [he]
    exact h p.natDegree p.coeff

theorem zero_mass_moments : ZeroMassExpected := by
  intro m h h0
  have he : constantValue m h = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    have hi := constantPolynomialVector_moments m h 0
    have hone : (ofPolynomial ((X : ℂ[X]) ^ 0) : MomentPolynomials m h) = 1 := by
      change (X : ℂ[X]) ^ 0 = 1
      exact pow_zero _
    rw [hone, ← constantValue, h0, Complex.ofReal_zero] at hi
    exact hi
  refine ⟨he, fun n => ?_⟩
  have hi := constantPolynomialVector_moments m h n
  rw [he, inner_zero_left] at hi
  exact Complex.ofReal_injective hi.symm

end ExpandedFA.Moments
