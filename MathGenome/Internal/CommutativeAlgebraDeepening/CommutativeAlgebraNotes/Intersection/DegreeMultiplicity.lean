import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity
import MathGenome.Internal.AlgebraCore.P103.Ch07.HilbertSamuelDimension

/-! The cumulative Hilbert–Samuel polynomial and multiplicity in a specified degree. -/

namespace CommutativeAlgebraNotes.Intersection.DegreeMultiplicity

open Polynomial
open P103.HilbertSamuelPolynomial (EventuallyPolynomial Quotient quotientLength)
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)
open P103.HilbertSamuelDimension (backwardDifference backwardDifference_coeff
  backwardDifference_degree eventuallyPolynomial_unique)
open Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity hiding
  hilbertSamuelPolynomial degreeMultiplicity hilbertSamuelMultiplicity

universe u v

section Definitions

variable {A : Type u} [CommRing A] (J : Ideal A)
variable (E : Type v) [AddCommGroup E] [Module A E]

noncomputable abbrev hilbertSamuelPolynomial : Polynomial ℚ :=
  Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity.hilbertSamuelPolynomial J E

noncomputable abbrev degreeMultiplicity (r : ℕ) : ℚ :=
  Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity.degreeMultiplicity J E r

noncomputable abbrev hilbertSamuelMultiplicity : ℚ :=
  Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity.hilbertSamuelMultiplicity J E

end Definitions

private theorem eventuallyPolynomial_zero_of_subsingleton {A : Type u} [CommRing A]
    (E : Type v) [AddCommGroup E] [Module A E] [Subsingleton E] (J : Ideal A) :
    EventuallyPolynomial (quotientLength J E) 0 := by
  exact ⟨0, fun n _ => by simp [quotientLength]⟩

theorem quotientLengthsFinite : quotientLengthsFiniteType.{u,v} := by
  intro A _ _ _ E _ _ _ J hJ hLength n
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact Module.length_ne_top_iff.mp (by simp)
  · exact (P103.HilbertSamuelPolynomial.finite_lengths A E J hJ hLength n).2

theorem hilbertSamuelPolynomialEventually : hilbertSamuelPolynomialEventuallyType.{u,v} := by
  intro A _ _ _ E _ _ _ J hJ hLength
  apply Classical.epsilon_spec
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨0, eventuallyPolynomial_zero_of_subsingleton E J⟩
  · obtain ⟨p, hp, _, _⟩ := P103.HilbertSamuelPolynomial.quotient_polynomial A E J hJ hLength
    exact ⟨p, hp⟩

theorem hilbertSamuelPolynomialUnique : hilbertSamuelPolynomialUniqueType.{u,v} := by
  intro A _ E _ _ J p hp
  exact eventuallyPolynomial_unique _ _ _ hp (Classical.epsilon_spec ⟨p, hp⟩)

theorem hilbertSamuelPolynomialDegree : hilbertSamuelPolynomialDegreeType.{u,v} := by
  intro A _ _ _ E _ _ _ _ J hJ hLength
  obtain ⟨d, hd, _, _⟩ := P103.Ch06.SystemsParameters.parameter_count A E
  obtain ⟨p, hp, hp0, hpd⟩ :=
    P103.HilbertSamuelDimension.quotient_degree A E J hJ hLength d hd
  have hpos : 0 < p.leadingCoeff :=
    P103.HilbertSamuelDimension.leadingCoeff_pos_of_eventuallyPolynomial _ p hp hp0
      (P103.HilbertSamuelPolynomial.leadingCoeff_pos_of_eventuallyPolynomial _ p hp)
  have heq := hilbertSamuelPolynomialUnique A E J p hp
  exact ⟨heq ▸ hpos, heq ▸ (hpd.symm ▸ hd)⟩

theorem hilbertSamuelPolynomialDimensionZero : hilbertSamuelPolynomialDimensionZeroType.{u,v} := by
  intro A _ _ _ E _ _ _ _ J hJ _ hd
  have hE := (P103.Ch06.SystemsParameters.dimension_zero_iff A E).mp hd
  obtain ⟨N, hN⟩ := P103.HilbertSamuelDimension.powerSubmodule_eventually_zero A E J hJ hE
  apply (hilbertSamuelPolynomialUnique A E J _ ?_).symm
  refine ⟨N, fun n hn => ?_⟩
  rw [eval_C, (P103.HilbertSamuelDimension.lengths_of_powerSubmodule_zero A E J n
    (hN n hn) (hN (n + 1) (hn.trans (Nat.le_succ n)))).2]

theorem hilbertSamuelPolynomialZero : hilbertSamuelPolynomialZeroType.{u,v} := by
  intro A _ E _ _ _ J
  exact (hilbertSamuelPolynomialUnique A E J 0 (eventuallyPolynomial_zero_of_subsingleton E J)).symm

theorem degreeMultiplicityZero : degreeMultiplicityZeroType.{u,v} := by
  intro A _ E _ _ _ J r
  change (r.factorial : ℚ) * (hilbertSamuelPolynomial J E).coeff r = 0
  simp only [hilbertSamuelPolynomial, hilbertSamuelPolynomialZero A E J, coeff_zero, mul_zero]

theorem degreeMultiplicityZeroOfDimensionLT : degreeMultiplicityZeroOfDimensionLTType.{u,v} := by
  intro A _ _ _ E _ _ _ J hJ hLength r hr
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact degreeMultiplicityZero A E J r
  · have hd := (hilbertSamuelPolynomialDegree A E J hJ hLength).2
    rw [hd] at hr
    have hr' : (hilbertSamuelPolynomial J E).natDegree < r := by exact_mod_cast hr
    change (r.factorial : ℚ) * (hilbertSamuelPolynomial J E).coeff r = 0
    rw [coeff_eq_zero_of_natDegree_lt hr', mul_zero]

private theorem backwardDifference_eventually_integer {p : Polynomial ℚ}
    (hp : ∃ N : ℕ, ∀ n ≥ N, ∃ z : ℤ, p.eval (n : ℚ) = (z : ℚ)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z : ℤ, (backwardDifference p).eval (n : ℚ) = (z : ℚ) := by
  obtain ⟨N, hN⟩ := hp
  refine ⟨N + 1, fun n hn => ?_⟩
  obtain ⟨a, ha⟩ := hN n (by omega)
  obtain ⟨b, hb⟩ := hN (n - 1) (by omega)
  have hcast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  refine ⟨a - b, ?_⟩
  simp only [backwardDifference, eval_sub, taylor_apply, eval_comp,
    eval_add, eval_X, eval_C, ← sub_eq_add_neg]
  rw [← hcast, ha, hb, Int.cast_sub]

private theorem factorial_mul_coeff_integral (r : ℕ) (p : Polynomial ℚ)
    (hp : ∃ N : ℕ, ∀ n ≥ N, ∃ z : ℤ, p.eval (n : ℚ) = (z : ℚ))
    (hd : p.natDegree ≤ r) : ∃ z : ℤ, (r.factorial : ℚ) * p.coeff r = (z : ℚ) := by
  induction r generalizing p with
  | zero =>
    have hconst := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hd)
    obtain ⟨N, hN⟩ := hp
    obtain ⟨z, hz⟩ := hN N le_rfl
    rw [hconst, eval_C] at hz
    exact ⟨z, by simpa only [Nat.factorial_zero, Nat.cast_one, one_mul] using hz⟩
  | succ r ih =>
    by_cases hlt : p.natDegree < r + 1
    · exact ⟨0, by simp [coeff_eq_zero_of_natDegree_lt hlt]⟩
    · have heq : p.natDegree = r + 1 := by omega
      have hpos : 0 < p.natDegree := by omega
      have hd' := (backwardDifference_degree p hpos).2
      rw [heq, Nat.add_sub_cancel] at hd'
      obtain ⟨z, hz⟩ := ih _ (backwardDifference_eventually_integer hp) hd'.le
      have hc := backwardDifference_coeff p hpos
      rw [← coeff_natDegree, heq, Nat.add_sub_cancel] at hc
      rw [hc] at hz
      refine ⟨z, ?_⟩
      rw [Nat.factorial_succ, Nat.cast_mul, mul_comm ((r + 1 : ℕ) : ℚ), mul_assoc]
      exact hz

theorem degreeMultiplicityIntegral : degreeMultiplicityIntegralType.{u,v} := by
  intro A _ _ _ E _ _ _ J hJ hLength r hr
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨0, by rw [degreeMultiplicityZero A E J r, Int.cast_zero]⟩
  · have hd := (hilbertSamuelPolynomialDegree A E J hJ hLength).2
    rw [hd] at hr
    have hr' : (hilbertSamuelPolynomial J E).natDegree ≤ r := by exact_mod_cast hr
    obtain ⟨N, hN⟩ := hilbertSamuelPolynomialEventually A E J hJ hLength
    refine factorial_mul_coeff_integral r (hilbertSamuelPolynomial J E) ⟨N, ?_⟩ hr'
    intro n hn
    exact ⟨(quotientLength J E n : ℤ), by simpa only [Int.cast_natCast] using (hN n hn).symm⟩

theorem hilbertSamuelMultiplicityAtDimension : hilbertSamuelMultiplicityAtDimensionType.{u,v} := by
  intro A _ E _ _ J d hd
  change degreeMultiplicity J E ((moduleDimensionValue A E).unbotD 0).toNat =
    degreeMultiplicity J E d
  rw [hd]
  simp

theorem hilbertSamuelMultiplicityPositive : hilbertSamuelMultiplicityPositiveType.{u,v} := by
  intro A _ _ _ E _ _ _ _ J hJ hLength
  obtain ⟨hpos, hd⟩ := hilbertSamuelPolynomialDegree A E J hJ hLength
  rw [hilbertSamuelMultiplicityAtDimension A E J _ hd]
  change 0 < ((hilbertSamuelPolynomial J E).natDegree.factorial : ℚ) *
    (hilbertSamuelPolynomial J E).coeff (hilbertSamuelPolynomial J E).natDegree
  rw [coeff_natDegree]
  exact mul_pos (by exact_mod_cast Nat.factorial_pos _) hpos

end CommutativeAlgebraNotes.Intersection.DegreeMultiplicity
