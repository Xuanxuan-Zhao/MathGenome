import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.AssociativePrimePowers
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.JacobsonPolynomials
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RestrictedOperationBoundary
import Batteries.Tactic.OpenPrivate

/-! Associative p-power identities and Jacobson polynomials. -/

namespace LieNotes.SuperRestricted.AssociativePrimePowers

open _root_.Specs.LieNotes.SuperRestricted.JacobsonPolynomials (jacobsonTermValue)
open _root_.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary (jacobsonCorrectionValue)
open Polynomial (C X)

open private ad_pow_apply coeff_ad_polynomial associative_pow_add from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RestrictedOperationBoundary

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Taking the associative `p`-th power induces the `p`-fold adjoint. -/
theorem ad_pow {k : Type*} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {B : Type*} [Ring B] [Algebra k B] (x : B) :
    (LieAlgebra.ad k B x) ^ p = LieAlgebra.ad k B (x ^ p) := by
  ext a
  exact ad_pow_apply (k := k) (p := p) x a

/-- The canonical Jacobson term gives the corresponding adjoint coefficient in `B[X]`. -/
theorem jacobsonTerm_polynomial {k : Type*} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {B : Type*} [Ring B] [Algebra k B] (x y : B) {i : ℕ} (hi : 1 ≤ i) (hip : i < p) :
    (i : k) • jacobsonTermValue k p i x y =
      (((LieAlgebra.ad k (Polynomial B) (C x * X + C y)) ^ (p - 1)) (C x)).coeff (i - 1) := by
  have hcast : (i : k) ≠ 0 := by
    intro h
    exact (Nat.not_dvd_of_pos_of_lt hi hip) ((CharP.cast_eq_zero_iff k p i).mp h)
  rw [coeff_ad_polynomial (k := k), jacobsonTermValue, smul_smul,
    mul_inv_cancel₀ hcast, one_smul]

/-- The mixed terms in the associative `p`-th power are the individual Jacobson terms. -/
theorem pow_add {k : Type*} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {B : Type*} [Ring B] [Algebra k B] (x y : B) :
    (x + y) ^ p = x ^ p + y ^ p + ∑ i ∈ Finset.Ico 1 p, jacobsonTermValue k p i x y := by
  have hsum : (∑ i ∈ Finset.Ico 1 p, jacobsonTermValue k p i x y) =
      jacobsonCorrectionValue k p x y := JacobsonPolynomials.sum_jacobsonTerm k p x y
  rw [hsum]
  exact associative_pow_add (k := k) (p := p) x y

end LieNotes.SuperRestricted.AssociativePrimePowers
