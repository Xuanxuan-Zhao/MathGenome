import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.ReducedEnveloping
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-! The polynomial p-center and the free basis of the ordinary enveloping algebra. -/

namespace Specs.LieNotes.SuperRestricted.RestrictedPolynomialBasis

open _root_.Shared.Lie (U inclusion)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.ReducedEnveloping (pCenterValue pCenterElementValue)

universe u v

variable {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
  {n p : ℕ}

/-- The product of enveloping generators in increasing basis order, with exponents below p. -/
noncomputable def restrictedMonomialValue (b : Module.Basis (Fin n) k G) (r : Fin n → Fin p) : U k G :=
  ((List.finRange n).map fun i => inclusion k G (b i) ^ (r i).val).prod

set_option linter.checkUnivs false in
def restrictedMonomialType :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G] {n p : ℕ},
    Module.Basis (Fin n) k G → (Fin n → Fin p) → U k G

/-- The variables map to the actual p-center generators. Via this equivalence and
the inclusion of the p-center, the bounded ordered words are a module basis. -/
def polynomialBasisType : Prop :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {n p : ℕ} [CharP k p] [NeZero p] (power : restrictedPowerValue k p G)
    (b : Module.Basis (Fin n) k G),
    ∃ e : MvPolynomial (Fin n) k ≃ₐ[k] pCenterValue power,
      (∀ i, (e (MvPolynomial.X i) : U k G) = pCenterElementValue power (b i)) ∧
      letI : Module (MvPolynomial (Fin n) k) (U k G) :=
        ((pCenterValue power).val.comp e.toAlgHom).toRingHom.toModule
      ∃ B : Module.Basis (Fin n → Fin p) (MvPolynomial (Fin n) k) (U k G),
        ∀ r, B r = restrictedMonomialValue b r

/-- The same products are a basis directly over the p-center acting by left multiplication. -/
def centerBasisType : Prop :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    {n p : ℕ} [CharP k p] [NeZero p] (power : restrictedPowerValue k p G)
    (b : Module.Basis (Fin n) k G),
    letI : Module (pCenterValue power) (U k G) := (pCenterValue power).val.toRingHom.toModule
    ∃ B : Module.Basis (Fin n → Fin p) (pCenterValue power) (U k G),
      ∀ r, B r = restrictedMonomialValue b r

end Specs.LieNotes.SuperRestricted.RestrictedPolynomialBasis
