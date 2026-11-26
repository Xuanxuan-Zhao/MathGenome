import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SmoothDiagonalKernel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.GeometricTorusSplitting

open EquivariantUnipotentSeries (IsSplitTorus)
open SchemeDerivedGroup (IsSolvable IsSubgroupOf)
open SmoothDiagonalKernel (IsTorusGroup)
open Unipotent (IsUnipotent IsFppfGroupQuotient closedSubgroupAlgebraicGroup)

variable {k : Type u} [Field k]

/-- The radical is smooth, connected, normal and unipotent, and contains every
closed unipotent subgroup scheme, including nonsmooth ones. -/
def IsUnipotentRadical {G : AffineAlgebraicGroup k} (U : ClosedSubgroup G.val) : Prop :=
  Smooth U.group.X.hom ∧ ConnectedSpace U.group.X.left ∧
    IsNormalSubgroup U.inclusion ∧ IsUnipotent (closedSubgroupAlgebraicGroup U) ∧
    ∀ V : ClosedSubgroup G.val, IsUnipotent (closedSubgroupAlgebraicGroup V) →
      IsSubgroupOf V U

/-- A maximal torus is maximal by inclusion among the closed torus subgroup schemes. -/
def IsMaximalTorus {G : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val) : Prop :=
  IsTorusGroup (closedSubgroupAlgebraicGroup T) ∧
    ∀ S : ClosedSubgroup G.val, IsTorusGroup (closedSubgroupAlgebraicGroup S) →
      IsSubgroupOf T S → IsSubgroupOf S T

/-- Multiplication on the two subgroup factors, in the order radical then torus.
For a normal first factor its isomorphism property expresses the internal
semidirect product, with the action given by conjugation. -/
noncomputable def subgroupProduct {G : GroupScheme k} (U T : ClosedSubgroup G) :
    U.group.X ⊗ T.group.X ⟶ G.X :=
  (fst U.group.X T.group.X ≫ U.inclusion.hom.hom) *
    (snd U.group.X T.group.X ≫ T.inclusion.hom.hom)

/-- Over an algebraically closed field a smooth connected solvable affine algebraic
group has a maximal torus. Its maximal tori are exactly the closed subgroups on
which the quotient by the unipotent radical restricts to an isomorphism.
Multiplication by any such torus gives the internal semidirect product. -/
def Splitting : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left → IsSolvable G.val →
    ∃ (U : ClosedSubgroup G.val) (D : AffineAlgebraicGroup k) (p : G.val ⟶ D.val),
      IsUnipotentRadical U ∧ IsFppfGroupQuotient U p ∧ IsSplitTorus D.val ∧
      (∃ T : ClosedSubgroup G.val, IsMaximalTorus T) ∧
      ∀ T : ClosedSubgroup G.val,
        (IsMaximalTorus T ↔ IsIso (T.inclusion ≫ p)) ∧
        (IsMaximalTorus T → IsIso (subgroupProduct U T))

/-- Any two maximal tori are conjugate as subgroup schemes by a rational
point of the unipotent radical. The isomorphism intertwines their inclusions
with conjugation by the image of that point in the ambient group. -/
def Conjugacy : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left → IsSolvable G.val →
    ∀ U : ClosedSubgroup G.val, IsUnipotentRadical U →
      ∀ T₁ T₂ : ClosedSubgroup G.val, IsMaximalTorus T₁ → IsMaximalTorus T₂ →
        ∃ (a : 𝟙_ (SchemeOver k) ⟶ U.group.X) (e : T₁.group ≅ T₂.group),
          let g : T₁.group.X ⟶ G.val.X := toUnit T₁.group.X ≫ a ≫ U.inclusion.hom.hom
          (e.hom ≫ T₂.inclusion).hom.hom = g * T₁.inclusion.hom.hom * g⁻¹

end LinearAlgebraicGroups.Specs.GeometricTorusSplitting
