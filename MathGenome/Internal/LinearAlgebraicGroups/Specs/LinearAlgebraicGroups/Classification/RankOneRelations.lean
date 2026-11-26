import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.OrderedRootProducts

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.RankOneRelations

open AdjointRepresentation (GroupPoints)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open CharacterPairing (absoluteRoots)
open RootGroups (AdditiveLine CorootReflection HasScalarAction IsRootSubgroup Proportional
  rankOneWord rootPoint)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

noncomputable section

/-- The opposite-root Gauss identity, the square of the Weyl representative,
and its action on the positive coordinate. The statement uses the rank-one
word of the linked coordinates and holds over every test algebra. -/
def OppositeRootRelations : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ α ∈ absoluteRoots T,
    ∀ {A : AdditiveLine k} (xpos xneg : A.group ⟶ G.val)
      (r : CorootReflection T α xpos xneg),
      HasScalarAction T α xpos → HasScalarAction T α⁻¹ xneg →
      ∀ (R : TestAlgebra k),
        (∀ (u v : R) (c : Rˣ), (c : R) = 1 + u * v →
          rootPoint xpos R u * rootPoint xneg R v =
            rootPoint xneg R (v * (↑c⁻¹ : R)) *
              ((groupPointsFunctor k).map T.inclusion).app R (cocharacterPoint r.coroot R c) *
              rootPoint xpos R (u * (↑c⁻¹ : R))) ∧
        let n : GroupPoints G.val R := toUnit _ ≫ r.representative
        n ^ 2 = cocharacterPoint r.coroot R (-1) ≫ T.inclusion.hom.hom ∧
        ∀ u : R, n * rootPoint xpos R u * n⁻¹ = rootPoint xneg R (-u)

/-- Root subgroups of independent roots commute if their strict positive
cone contains no root of the form iα + jβ with i,j positive integers. -/
def IndependentRootCommutation : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ α ∈ absoluteRoots T, ∀ β ∈ absoluteRoots T,
      ¬ Proportional α β →
      (∀ i j : ℕ, 0 < i → 0 < j → α ^ i * β ^ j ∉ absoluteRoots T) →
      ∀ (U V : ClosedSubgroup G.val), IsRootSubgroup T U α → IsRootSubgroup T V β →
        ∀ (R : TestAlgebra k) (p : GroupPoints U.group R) (q : GroupPoints V.group R),
          Commute (p ≫ U.inclusion.hom.hom : GroupPoints G.val R)
            (q ≫ V.inclusion.hom.hom : GroupPoints G.val R)

end

end LinearAlgebraicGroups.Specs.RankOneRelations
