import MathGenome.Internal.Specs.D07.Ch11.QuotientNormalForm
import MathGenome.Internal.D07.Ch09.QuotientProjection
import MathGenome.Internal.D07.Ch11.DegreeArithmetic
import MathGenome.Internal.D07.Ch11.FieldDivision

/-!
K07.11.quotient_normal_form. `AdjoinRoot f` is definitionally the same
ideal quotient as the accepted quotient construction. Its power basis
requires only f ≠ 0, even though some library docstrings mention
irreducibility. Remainders and their uniqueness use polynomial division.
-/

universe u

namespace D07.Ch11.QuotientNormalForm

open Polynomial Module
open Specs.D07.Ch11.QuotientNormalForm

theorem uniqueRepresentative : UniqueRepresentative.{u} := by
  intro F _ f hf x
  change ∃! r : Polynomial F, r.degree < f.degree ∧ AdjoinRoot.mk f r = x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨g % f, ⟨Polynomial.degree_mod_lt g hf, ?_⟩, ?_⟩
  · apply AdjoinRoot.mk_eq_mk.mpr
    rw [EuclideanDomain.mod_eq_sub_mul_div]
    have : g - f * (g / f) - g = -(f * (g / f)) := by abel
    rw [this]
    exact dvd_neg.mpr (dvd_mul_right _ _)
  · intro r hr
    have h := Polynomial.mod_eq_of_dvd_sub (AdjoinRoot.mk_eq_mk.mp hr.2)
    rwa [(Polynomial.mod_eq_self_iff hf).mpr hr.1] at h

theorem scalarAction : ScalarAction.{u} := by
  intro F _ f a x
  exact Algebra.smul_def a x

theorem quotientBasis : QuotientBasis.{u} := by
  intro F _ f hf
  refine ⟨(AdjoinRoot.powerBasis hf).basis, ?_⟩
  intro i
  exact ((AdjoinRoot.powerBasis hf).basis_eq_pow i).trans
    (map_pow (AdjoinRoot.mk f) X (i : ℕ)).symm

theorem quotientDimension : QuotientDimension.{u} := by
  intro F _ f hf
  obtain ⟨b, _⟩ := quotientBasis F f hf
  exact ⟨Module.Finite.of_basis b, by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]⟩

theorem finiteCardinality : FiniteCardinality.{u} := by
  intro F _ _ f hf
  obtain ⟨b, _⟩ := quotientBasis F f hf
  refine ⟨Finite.of_equiv (Fin f.natDegree → F) b.equivFun.toEquiv.symm, ?_⟩
  rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_fin]

theorem degreeZeroCase : DegreeZeroCase.{u} := by
  intro F _ f hf hn
  obtain ⟨b, _⟩ := quotientBasis F f hf
  have he : IsEmpty (Fin f.natDegree) := by rw [hn]; infer_instance
  let := he
  have hs : Subsingleton (Polynomial F ⧸ Ideal.span {f}) :=
    b.equivFun.toEquiv.subsingleton
  let := hs
  refine ⟨hs, Nat.card_unique, ?_⟩
  rw [hn] at b
  exact ⟨b⟩

theorem constantCase : ConstantCase.{u} := by
  intro F _ a ha x r
  have hs := (degreeZeroCase F (C a) (C_ne_zero.mpr ha) (natDegree_C a)).1
  let := hs
  constructor
  · intro hr
    rw [degree_C ha] at hr
    exact degree_eq_bot.mp ((WithBot.lt_zero_iff_eq_bot r.degree).mp hr.1)
  · rintro rfl
    refine ⟨?_, Subsingleton.elim _ _⟩
    rw [degree_zero, degree_C ha]
    exact WithBot.bot_lt_coe 0

theorem zeroPolynomialCase : ZeroPolynomialCase.{u} := by
  intro F _
  have hI : Ideal.span {(0 : Polynomial F)} = ⊥ := by simp
  let e : (Polynomial F ⧸ Ideal.span {(0 : Polynomial F)}) ≃ₐ[F] Polynomial F :=
    (Ideal.quotientEquivAlgOfEq F hI).trans (AlgEquiv.quotientBot F (Polynomial F))
  refine ⟨degree_zero, ?_, ⟨e, ?_⟩, ?_, Polynomial.not_finite, ?_⟩
  · intro n
    simp
  · intro p
    simp [e]
  · refine ⟨Polynomial.basisMonomials F, ?_⟩
    intro i
    simp [Polynomial.coe_basisMonomials, ← C_mul_X_pow_eq_monomial]
  · intro h
    let := h
    exact Polynomial.not_finite (Module.Finite.equiv e.toLinearEquiv)

theorem irreducibleExtension : IrreducibleExtension.{u} := by
  intro F _ f hf
  have : Fact (Irreducible f) := ⟨hf⟩
  have : Nontrivial (AdjoinRoot f) := inferInstance
  refine ⟨AdjoinRoot.isField_iff_irreducible.mpr hf, ?_, quotientDimension F f hf.ne_zero⟩
  exact (algebraMap F (AdjoinRoot f)).injective

end D07.Ch11.QuotientNormalForm
