import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.UnipotentRadicalIntersection

open GeometricBorelConjugacy (IsBorel IsReducedIdentityComponent subgroupOfSubgroup)
open GeometricRadicals (IsMaximalTorus IsSolvableRadical IsUnipotentRadical)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (IsUnipotent closedSubgroupAlgebraicGroup)

variable {k : Type u} [Field k] {G : GroupScheme k}

/-- The scheme intersection is characterized by simultaneous factorization on
every test scheme over the ground field. -/
def IsSchemeIntersection (family : Set (ClosedSubgroup G)) (I : ClosedSubgroup G) : Prop :=
  ∀ (Y : SchemeOver k) (y : Y ⟶ G.X),
    y ∈ SubgroupSections I Y ↔ ∀ H ∈ family, y ∈ SubgroupSections H Y

/-- The unipotent radicals of the Borels containing the given torus, viewed
as closed subgroups of the ambient group. -/
def borelUnipotentRadicals {G : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val) :
    Set (ClosedSubgroup G.val) :=
  {H | ∃ (B : ClosedSubgroup G.val) (U : ClosedSubgroup B.group),
    IsBorel B ∧ IsSubgroupOf T B ∧
      IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U ∧ H = subgroupOfSubgroup B U}

/-- Over an algebraically closed field, the reduced identity component of the
scheme intersection of the unipotent radicals of the Borels through a maximal
torus is the largest smooth connected normal unipotent subgroup. -/
def UnipotentRadicalFromBorelIntersection : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ T : ClosedSubgroup G.val, IsMaximalTorus T →
      ∃ (I : ClosedSubgroup G.val) (J : ClosedSubgroup I.group),
        IsSchemeIntersection (borelUnipotentRadicals T) I ∧
          IsReducedIdentityComponent J ∧ IsUnipotentRadical G (subgroupOfSubgroup I J)

/-- Over an algebraically closed field, the reduced identity component of the
scheme intersection of all Borels is the largest smooth connected normal
solvable subgroup. -/
def SolvableRadicalFromBorelIntersection : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
      ∃ (I : ClosedSubgroup G.val) (J : ClosedSubgroup I.group),
        IsSchemeIntersection {B | IsBorel B} I ∧
          IsReducedIdentityComponent J ∧ IsSolvableRadical G (subgroupOfSubgroup I J)

/-- Every geometric orbit of a smooth unipotent group on an affine variety
is closed. The orbit is the underlying image of its orbit morphism. -/
def UnipotentOrbitsClosed : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (U : AffineAlgebraicGroup k) (X : SchemeOver k)
    (a : ModObj U.val.X X),
    Smooth U.val.X.hom → IsUnipotent U →
      IsAffine X.left → IsReduced X.left → LocallyOfFiniteType X.hom →
        ∀ x : 𝟙_ (SchemeOver k) ⟶ X, IsClosed (SmoothOrbit.orbitSet a x)

end LinearAlgebraicGroups.Specs.UnipotentRadicalIntersection
