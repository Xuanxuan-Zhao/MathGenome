import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.Polynomial
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.MonomialBasis
import Mathlib.Data.Sym.NatCard
import Mathlib.RingTheory.MvPolynomial.Basic

namespace Alg01SymmetricWitt.Symmetric.MonomialBasis

open Module
open Alg01SymmetricWitt.Symmetric.Algebra (degree)

abbrev Exponent := Specs.Alg01SymmetricWitt.Symmetric.MonomialBasis.Exponent

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {r : ℕ}

private theorem restrictSupport_eq_homogeneous (r n : ℕ) :
    MvPolynomial.restrictSupport R {a : Fin r →₀ ℕ | ∑ i, a i = n} =
      MvPolynomial.homogeneousSubmodule (Fin r) R n := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  simp_rw [Finsupp.degree_eq_sum]
  rfl

private noncomputable def homogeneousBasis (r n : ℕ) :
    Basis (Exponent r n) R (MvPolynomial.homogeneousSubmodule (Fin r) R n) :=
  (MvPolynomial.basisRestrictSupport R {a : Fin r →₀ ℕ | ∑ i, a i = n}).map
    (LinearEquiv.ofEq _ _ (restrictSupport_eq_homogeneous r n))

private theorem homogeneousBasis_coe (a : Exponent r n) :
    (homogeneousBasis (R := R) r n a : MvPolynomial (Fin r) R) =
      MvPolynomial.monomial a.val 1 := by
  classical
  rw [homogeneousBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply]
  rw [← Basis.repr_symm_single_one]
  change (((AddMonoidAlgebra.supportedEquivFinsupp
    {a : Fin r →₀ ℕ | ∑ i, a i = n}).symm (Finsupp.single a (1 : R))) :
      MvPolynomial (Fin r) R) = _
  simp [AddMonoidAlgebra.supportedEquivFinsupp, MvPolynomial.monomial]

/-- The degree-`n` basis consists of all products of the prescribed basis generators
with exponents summing to `n`. -/
theorem exists_monomialBasis (b : Basis (Fin r) R M) (n : ℕ) :
    ∃ c : Basis (Exponent r n) R (degree R M n), ∀ a : Exponent r n,
      (c a : SymmetricAlgebra R M) = ∏ i, SymmetricAlgebra.ι R M (b i) ^ a.val i ∧
      Polynomial.equivMvPolynomial b (c a : SymmetricAlgebra R M) =
        MvPolynomial.monomial a.val 1 := by
  refine ⟨(homogeneousBasis r n).map (Polynomial.degreeEquiv b n).symm, fun a => ?_⟩
  have h : Polynomial.equivMvPolynomial b
      (∏ i, SymmetricAlgebra.ι R M (b i) ^ a.val i) = MvPolynomial.monomial a.val 1 := by
    rw [map_prod]
    simp only [map_pow, Polynomial.equivMvPolynomial_ι]
    rw [← Finsupp.prod_fintype _ (fun i e => MvPolynomial.X i ^ e) (fun _ => pow_zero _)]
    exact MvPolynomial.prod_X_pow_eq_monomial
  have himage : Polynomial.equivMvPolynomial b
      (((homogeneousBasis r n).map (Polynomial.degreeEquiv b n).symm a : degree R M n) :
        SymmetricAlgebra R M) = MvPolynomial.monomial a.val 1 := by
    rw [Basis.map_apply, ← Polynomial.degreeEquiv_apply, LinearEquiv.apply_symm_apply]
    exact homogeneousBasis_coe a
  exact ⟨(Polynomial.equivMvPolynomial b).injective (himage.trans h.symm), himage⟩

/-- Exponents of a given total degree are counted by multisets of that size. -/
private def exponentEquivSym (r n : ℕ) : Exponent r n ≃ Sym (Fin r) n :=
  Multiset.toFinsupp.toEquiv.symm.subtypeEquiv fun a => by
    change (∑ i, a i = n) ↔ Multiset.card a.toMultiset = n
    rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
    rfl

theorem exponentCard (r n : ℕ) :
    Finite (Exponent r n) ∧ (0 < r → Nat.card (Exponent r n) = (n + r - 1).choose n) := by
  refine ⟨Finite.of_equiv _ (exponentEquivSym r n).symm, fun _ => ?_⟩
  rw [Nat.card_congr (exponentEquivSym r n), Sym.natCard_sym_eq_choose, Nat.card_fin, Nat.add_comm]

theorem rankZeroDegreeZero (b : Basis (Fin 0) R M) :
    Nonempty (Unique (Exponent 0 0)) ∧
      ∃ c : Basis (Exponent 0 0) R (degree R M 0),
        ∀ a : Exponent 0 0, (c a : SymmetricAlgebra R M) = 1 := by
  obtain ⟨c, hc⟩ := exists_monomialBasis b 0
  refine ⟨⟨(exponentEquivSym 0 0).unique⟩, c, fun a => ?_⟩
  simpa using (hc a).1

theorem rankZeroPositiveDegree (b : Basis (Fin 0) R M) (n : ℕ) (hn : 0 < n) :
    IsEmpty (Exponent 0 n) ∧ degree R M n = ⊥ := by
  have : IsEmpty (Exponent 0 n) := ⟨fun a => hn.ne' (by simpa using a.property.symm)⟩
  obtain ⟨c, _⟩ := exists_monomialBasis b n
  have : Subsingleton (degree R M n) := c.repr.injective.subsingleton
  exact ⟨inferInstance, Submodule.eq_bot_of_subsingleton⟩

end Alg01SymmetricWitt.Symmetric.MonomialBasis
