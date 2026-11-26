import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.BorelProper
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.Stabilizers

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.LeviConjugacy

open BorelProper (IsParabolic)
open GeometricRadicals (IsUnipotentRadical)
open Unipotent (closedSubgroupAlgebraicGroup)

variable {k : Type u} [Field k]

/-- The two inclusions of closed subschemes that express equality with the
conjugate over the test scheme. -/
def Transports {P : GroupScheme k} (L L' : ClosedSubgroup P)
    {X : SchemeOver k} (g : X ⟶ P.X) : Prop :=
  (∃ f : L.group.X ⊗ X ⟶ L'.group.X,
    f ≫ L'.inclusion.hom.hom = conjugateFamily L.inclusion g) ∧
  (∃ f : L'.group.X ⊗ X ⟶ L.group.X,
    f ≫ L.inclusion.hom.hom = conjugateFamily L'.inclusion g⁻¹)

/-- The transporter between two Levi complements of the unipotent radical
is represented by the ground field scheme, with the displayed point as its
inclusion in the radical. The Levi condition is the isomorphism with the
quotient by the radical, expressed using a quotient with that scheme kernel. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    IsParabolic G P →
    ∀ (U : ClosedSubgroup P.group), IsUnipotentRadical (closedSubgroupAlgebraicGroup P) U →
    ∀ (Q : AffineAlgebraicGroup k) (q : P.group ⟶ Q.val), IsSchemeKernel q U →
    ∀ (L L' : ClosedSubgroup P.group),
      IsIso (L.inclusion ≫ q) → IsIso (L'.inclusion ≫ q) →
      ∃ a : 𝟙_ (SchemeOver k) ⟶ U.group.X,
        ∀ (X : SchemeOver k) (g : X ⟶ U.group.X),
          Transports L L' (g ≫ U.inclusion.hom.hom) ↔ g = toUnit X ≫ a

end LinearAlgebraicGroups.Specs.LeviConjugacy
