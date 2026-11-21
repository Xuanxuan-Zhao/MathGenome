import MathGenome.Internal.Specs.D07.Ch11.DegreeConventions

/-!
K07.11.degree_conventions: canonical degree, natural degree, leading
coefficient and monicity, with all zero and nonzero cases kept separate.
The definitions are aliases for Mathlib's operations on formal polynomials;
their specified values expose the support maximum and coefficient formulas.
-/

universe u

namespace D07.Ch11.DegreeConventions

open Specs.D07.Ch11.DegreeConventions

noncomputable def degree : DegreeType.{u} :=
  fun f => Polynomial.degree f

noncomputable def natDegree : NatDegreeType.{u} :=
  fun f => Polynomial.natDegree f

noncomputable def leadingCoeff : LeadingCoefficientType.{u} :=
  fun f => Polynomial.leadingCoeff f

noncomputable def Monic : MonicType.{u} :=
  fun f => Polynomial.Monic f

theorem degreeCharacterization : DegreeCharacterization.{u} := by
  intro R _ f n
  constructor
  · intro h
    refine ⟨Polynomial.coeff_ne_zero_of_eq_degree h, ?_⟩
    intro i hi
    have hle : (i : WithBot ℕ) ≤ (n : WithBot ℕ) := by
      rw [← h]
      exact Polynomial.le_degree_of_ne_zero hi
    exact WithBot.coe_le_coe.mp hle
  · rintro ⟨hn, hmax⟩
    apply le_antisymm _ (Polynomial.le_degree_of_ne_zero hn)
    apply (Polynomial.degree_le_iff_coeff_zero f (n : WithBot ℕ)).mpr
    intro i hi
    by_contra hne
    exact (not_le_of_gt (WithBot.coe_lt_coe.mp hi)) (hmax i hne)

theorem degreeZero : DegreeZero.{u} := by
  intro R _
  exact Polynomial.degree_zero

theorem degreeBottomIff : DegreeBottomIff.{u} := by
  intro R _ f
  exact Polynomial.degree_eq_bot

theorem bottomAddition : BottomAddition := by
  intro n
  simp

theorem natDegreeAgreement : NatDegreeAgreement.{u} := by
  intro R _ f hf
  exact Polynomial.degree_eq_natDegree hf

theorem natDegreeZero : NatDegreeZero.{u} := by
  intro R _
  exact Polynomial.natDegree_zero

theorem leadingCoefficientAtDegree : LeadingCoefficientAtDegree.{u} := by
  intro R _ f
  exact Polynomial.coeff_natDegree

theorem leadingCoefficientZero : LeadingCoefficientZero.{u} := by
  intro R _
  exact Polynomial.leadingCoeff_zero

theorem nonzeroLeadingCoefficient : NonzeroLeadingCoefficient.{u} := by
  intro R _ f hf
  exact Polynomial.leadingCoeff_ne_zero.mpr hf

theorem monicCharacterization : MonicCharacterization.{u} := by
  intro R _ f
  exact Polynomial.Monic.def

theorem monicNonzero : MonicNonzero.{u} := by
  intro R _ _ f hf
  exact Polynomial.Monic.ne_zero hf

theorem zeroMonicIff : ZeroMonicIff.{u} := by
  intro R _
  rw [Polynomial.Monic.def, Polynomial.leadingCoeff_zero]

theorem zeroRingMonic : ZeroRingMonic.{u} := by
  intro R _ _
  exact (zeroMonicIff R).mpr (Subsingleton.elim _ _)

theorem constantDegree : ConstantDegree.{u} := by
  intro R _ a ha
  exact Polynomial.degree_C ha

theorem constantNatDegree : ConstantNatDegree.{u} := by
  intro R _ a
  exact Polynomial.natDegree_C a

end D07.Ch11.DegreeConventions
