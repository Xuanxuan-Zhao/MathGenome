import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.QuotientEmbedding
import Mathlib.AlgebraicGeometry.Morphisms.Proper

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.BorelProper

open GeometricBorelConjugacy (IsBorel)
open GeometricRadicals (GeometricGroup IsReductive baseChangedSubgroup)
open SchemeDerivedGroup (IsSubgroupOf)

variable {k : Type u} [Field k]

/-- The base-changed closed subgroup contains a Borel as a subgroup scheme. -/
def ContainsGeometricBorel {G : GroupScheme k} (P : ClosedSubgroup G) : Prop :=
  ∃ h : IsClosedImmersion
      ((groupBaseChange k (AlgebraicClosure k)).map P.inclusion).hom.hom.left,
    ∃ B : ClosedSubgroup ((groupBaseChange k (AlgebraicClosure k)).obj G),
      IsBorel B ∧ IsSubgroupOf B (baseChangedSubgroup (AlgebraicClosure k) P h)

/-- A parabolic of a connected reductive group is a smooth closed subgroup
whose base change to an algebraic closure contains a Borel. -/
def IsParabolic (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val) : Prop :=
  IsReductive G ∧ Smooth P.group.X.hom ∧ ContainsGeometricBorel P

/-- The canonical right fppf quotient by any geometric Borel is proper over
the algebraic closure of the ground field. -/
def GeometricBorelQuotientProper : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ (B : ClosedSubgroup (GeometricGroup G).val), IsBorel B →
    ∀ Q : QuotientEmbedding.Presentation B, IsProper Q.scheme.hom

/-- For a smooth closed subgroup of a smooth connected affine algebraic
group, the canonical right fppf quotient is proper exactly when the subgroup
contains a Borel after extension to the algebraic closure. -/
def QuotientProperIff : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ (P : ClosedSubgroup G.val), Smooth P.group.X.hom →
    ∀ Q : QuotientEmbedding.Presentation P,
      IsProper Q.scheme.hom ↔ ContainsGeometricBorel P

end LinearAlgebraicGroups.Specs.BorelProper
