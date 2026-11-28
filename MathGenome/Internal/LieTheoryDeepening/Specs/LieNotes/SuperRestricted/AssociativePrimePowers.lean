import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.JacobsonPolynomials
import Mathlib.Algebra.Lie.OfAssociative

/-! Specifications for the `p`-power identities in an associative algebra. -/

namespace Specs.LieNotes.SuperRestricted.AssociativePrimePowers

open _root_.Specs.LieNotes.SuperRestricted.JacobsonPolynomials (jacobsonTermValue)
open Polynomial (C X)

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

/-- The adjoint of the associative `p`-th power is the `p`-fold composition. -/
def ad_powType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {B : Type v} [Ring B] [Algebra k B] (x : B),
    (LieAlgebra.ad k B x) ^ p = LieAlgebra.ad k B (x ^ p)

/-- Each Jacobson term is specified by the adjoint coefficient in the
central-variable polynomial ring over the associative algebra. -/
def jacobsonTerm_polynomialType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {B : Type v} [Ring B] [Algebra k B] (x y : B) {i : ℕ},
    1 ≤ i → i < p →
    (i : k) • jacobsonTermValue k p i x y =
      (((LieAlgebra.ad k (Polynomial B) (C x * X + C y)) ^ (p - 1)) (C x)).coeff (i - 1)

/-- The cross terms in the associative `p`-th power of a sum. -/
def pow_addType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {B : Type v} [Ring B] [Algebra k B] (x y : B),
    (x + y) ^ p = x ^ p + y ^ p + ∑ i ∈ Finset.Ico 1 p, jacobsonTermValue k p i x y

end Specs.LieNotes.SuperRestricted.AssociativePrimePowers
