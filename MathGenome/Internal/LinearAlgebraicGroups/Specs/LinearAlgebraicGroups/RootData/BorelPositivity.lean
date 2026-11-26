import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.DatumAndWeyl
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.OrderedRootProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.BorelPositivity

open AbstractPairing (Datum Root)
open BorelsAndChambers (IsPositiveSystem subgroupRoots)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (GeometricGroup IsReductive IsSplitTorus IsUnipotentRadical
  baseChangedSubgroup)
open OrderedRootProducts (Enumerates Parametrizes RootSubgroupFamily)
open RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (multiplyFactors)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- Taking the Lie roots gives a bijection from Borel subgroups through the
torus, up to equality as ambient closed subgroups, to positive systems. -/
def BorelCorrespondence (T : ClosedSubgroup G.val) : Prop :=
  (∀ B : ClosedSubgroup G.val, IsKBorel B → IsSubgroupOf T B →
    IsPositiveSystem T (subgroupRoots T B)) ∧
  (∀ S : Set (Root T), IsPositiveSystem T S →
    ∃ B : ClosedSubgroup G.val, IsKBorel B ∧ IsSubgroupOf T B ∧ subgroupRoots T B = S) ∧
  ∀ B B' : ClosedSubgroup G.val, IsKBorel B → IsKBorel B' →
    IsSubgroupOf T B → IsSubgroupOf T B' →
    (subgroupRoots T B = subgroupRoots T B' ↔ SameSubgroup B B')

/-- The action on the positive systems is the image action of the Weyl
permutations of the actual root indices. -/
def WeylAction {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] (D : Datum T) : Prop :=
  (∃ S : Set (Root T), IsPositiveSystem T S) ∧
  (∀ (w : D.rootDatum.weylGroup) (S : Set (Root T)), IsPositiveSystem T S →
    IsPositiveSystem T ((D.rootDatum.weylGroupToPerm w) '' S)) ∧
  ∀ S S' : Set (Root T), IsPositiveSystem T S → IsPositiveSystem T S' →
    ∃! w : D.rootDatum.weylGroup, (D.rootDatum.weylGroupToPerm w) '' S = S'

/-- The torus splits the radical quotient of the Borel, and multiplication
gives the scheme factorization and every ordered positive-root parametrization
of the same unipotent radical. -/
def RadicalDecomposition (T B : ClosedSubgroup G.val) : Prop :=
  let B₀ := closedSubgroupAlgebraicGroup B
  ∃ (R : ClosedSubgroup B.group) (j : T.group ⟶ B.group) (q : B.group ⟶ T.group),
    IsUnipotentRadical B₀ R ∧
    (∃ hR : IsClosedImmersion
        ((groupBaseChange k (AlgebraicClosure k)).map R.inclusion).hom.hom.left,
      IsUnipotentRadical (GeometricGroup B₀) (baseChangedSubgroup (AlgebraicClosure k) R hR)) ∧
    j ≫ B.inclusion = T.inclusion ∧ j ≫ q = 𝟙 T.group ∧
    IsPullback R.inclusion.hom.hom (toUnit _) q.hom.hom η[T.group.X] ∧
    IsIso (multiplyFactors j R.inclusion) ∧
    ∀ (U : RootSubgroupFamily T) (l : List (Root T)),
      Enumerates l (subgroupRoots T B) →
      Parametrizes U l (R.inclusion.hom.hom ≫ B.inclusion.hom.hom)

/-- For a split maximal torus in a connected reductive group, the Borels
through the torus correspond to positive systems of the actual root datum.
The scheme Weyl group acts simply transitively, and the Borel is the split
extension of the torus by its ordered product of positive root groups. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
      ∃ h : IsCommMonObj T.group.X, letI := h
        ∃ D : Datum T,
          Nonempty (DatumAndWeyl.Identification D) ∧
          BorelCorrespondence T ∧ WeylAction D ∧ Nonempty (RootSubgroupFamily T) ∧
          ∀ B : ClosedSubgroup G.val, IsKBorel B → IsSubgroupOf T B →
            RadicalDecomposition T B

end LinearAlgebraicGroups.Specs.BorelPositivity
