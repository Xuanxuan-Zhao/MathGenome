import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.JacobsonPolynomials
import Mathlib.Algebra.Lie.Subalgebra

/-! Specifications for restricted Lie algebras and restriction to Lie subalgebras. -/

namespace Specs.LieNotes.SuperRestricted.RestrictedLie

open _root_.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary
open _root_.Specs.LieNotes.SuperRestricted.JacobsonPolynomials (jacobsonTermValue)

universe u v

set_option linter.checkUnivs false in
abbrev restrictedPowerType :=
  _root_.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary.restrictedPowerType.{u, v}

/-- The canonical restricted-power data used by the restricted enveloping algebra. -/
abbrev restrictedPowerValue :=
  _root_.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary.restrictedPowerValue.{u, v}

/-- The three axioms, with the sum indexed by the individual Jacobson polynomials. -/
def isRestrictedPower_iffType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G] (power : G → G),
    isRestrictedPowerValue k p power ↔
      (∀ x, LieAlgebra.ad k G (power x) = LieAlgebra.ad k G x ^ p) ∧
      (∀ (a : k) x, power (a • x) = a ^ p • power x) ∧
      (∀ x y, power (x + y) = power x + power y +
        ∑ i ∈ Finset.Ico 1 p, jacobsonTermValue k p i x y)

/-- The subalgebra inherits the operation given by restricting the ambient map. -/
def subalgebra_inheritsType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G]
    (power : restrictedPowerValue k p G) (S : LieSubalgebra k G),
    (∀ x : S, power.val (x : G) ∈ S) →
      ∃ inherited : restrictedPowerValue k p S,
        ∀ x : S, (inherited.val x : G) = power.val (x : G)

end Specs.LieNotes.SuperRestricted.RestrictedLie
