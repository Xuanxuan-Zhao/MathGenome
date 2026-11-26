import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.SplitTorusConjugacy

open GeometricRadicals (IsSplitTorus IsTorus IsMaximalTorus baseChangedSubgroup)
open GeometricTorusSplitting (IsUnipotentRadical subgroupProduct)
open SchemeDerivedGroup (IsSplitSolvable IsSubgroupOf)
open Unipotent (IsFppfGroupQuotient)

variable {k : Type u} [Field k]

/-- A split torus maximal among the closed split tori over the given field. -/
def IsMaximalSplitTorus {G : GroupScheme k} (T : ClosedSubgroup G) : Prop :=
  IsSplitTorus T.group ∧
    ∀ S : ClosedSubgroup G, IsSplitTorus S.group →
      IsSubgroupOf T S → IsSubgroupOf S T

/-- A torus defined over the given field whose base change is maximal over the
algebraic closure. -/
def IsGeometricallyMaximalTorus {G : GroupScheme k} (T : ClosedSubgroup G) : Prop :=
  IsTorus T.group ∧
    ∃ h : IsClosedImmersion
        ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
      IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h)

/-- The radical quotient of a split solvable group over any field is a split
torus. The maximal split tori are exactly the complements, and multiplication
gives the internal semidirect product for each of them. Every split torus
lies in a geometrically maximal torus, and every geometrically maximal torus
maps isomorphically onto the quotient. -/
def Splitting : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsSplitSolvable G.val →
    ∃ (U : ClosedSubgroup G.val) (D : AffineAlgebraicGroup k) (p : G.val ⟶ D.val),
      IsUnipotentRadical U ∧ IsFppfGroupQuotient U p ∧ IsSplitTorus D.val ∧
      (∃ T : ClosedSubgroup G.val, IsMaximalSplitTorus T) ∧
      (∀ T : ClosedSubgroup G.val,
        (IsMaximalSplitTorus T ↔ IsIso (T.inclusion ≫ p)) ∧
        (IsMaximalSplitTorus T → IsIso (subgroupProduct U T))) ∧
      (∀ T : ClosedSubgroup G.val,
        IsGeometricallyMaximalTorus T → IsIso (T.inclusion ≫ p)) ∧
      (∀ S : ClosedSubgroup G.val, IsSplitTorus S.group →
        ∃ T : ClosedSubgroup G.val, IsGeometricallyMaximalTorus T ∧ IsSubgroupOf S T)

/-- Two maximal split tori are conjugate as subgroup schemes by a rational
point of the unipotent radical. -/
def Conjugacy : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsSplitSolvable G.val →
    ∀ U : ClosedSubgroup G.val, IsUnipotentRadical U →
      ∀ T₁ T₂ : ClosedSubgroup G.val, IsMaximalSplitTorus T₁ → IsMaximalSplitTorus T₂ →
        ∃ (a : 𝟙_ (SchemeOver k) ⟶ U.group.X) (e : T₁.group ≅ T₂.group),
          let g : T₁.group.X ⟶ G.val.X := toUnit T₁.group.X ≫ a ≫ U.inclusion.hom.hom
          (e.hom ≫ T₂.inclusion).hom.hom = g * T₁.inclusion.hom.hom * g⁻¹

end LinearAlgebraicGroups.Specs.SplitTorusConjugacy
