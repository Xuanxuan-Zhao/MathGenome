import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRootRelations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbstractPairing

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.PinnedDatumFromMarkedRootGroups

open AdjointRepresentation (GroupPoints)
open AbstractPairing (Root)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Character)
open CharacterPairing (characterValue)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open IntegralRootRelations (upper lower diagonal)
open OrderedRootProducts (RootSubgroupFamily)
open Pinning (AttachedDatum BasedIso BasedRootDatum Pinning RootCoordinate SplitBorelPair)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (AdditiveLine rootPoint)
open SchemeDerivedGroup (IsSubgroupOf)

noncomputable section

variable {k : Type u} [Field k]

/-- The determinant-one matrices, functorial in the commutative test algebra. -/
def rankOnePoints : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Matrix.SpecialLinearGroup (Fin 2) R)
  map f := GrpCat.ofHom (Matrix.SpecialLinearGroup.map f.hom.toRingHom)
  map_id _ := by apply GrpCat.ext; intro x; ext i j; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; ext i j; rfl

/-- Root subgroups and their marked additive coordinates, indexed via the
bijection with the actual absolute roots. -/
structure Marking (D : BasedRootDatum.{u}) (H : AffineAlgebraicGroup k)
    (T : ClosedSubgroup H.val) (A : AdditiveLine k) where
  character : D.X ≃ₗ[ℤ] Additive (Character T.group)
  index : D.I ≃ Root T
  rootCharacter : ∀ a, (index a).val = Additive.toMul (character (D.datum.root a))
  roots : RootSubgroupFamily T
  coordinate : ∀ α : Root T, RootCoordinate A T (roots α).val α.val

abbrev Marking.rootMap {D : BasedRootDatum.{u}} {H : AffineAlgebraicGroup k}
    {T : ClosedSubgroup H.val} {A : AdditiveLine k} (M : Marking D H T A) (a : D.I) :
    A.group ⟶ H.val :=
  (M.coordinate (M.index a)).val.hom ≫ (M.roots (M.index a)).val.inclusion

/-- The marked rank-one homomorphisms have the prescribed upper, lower and
diagonal values over every commutative test algebra. -/
structure RankOneRelations {D : BasedRootDatum.{u}} {H : AffineAlgebraicGroup k}
    {T : ClosedSubgroup H.val} {A : AdditiveLine k} (M : Marking D H T A) where
  hom : D.I → (rankOnePoints ⟶ (groupPointsFunctor k).obj H.val)
  upper_eq : ∀ a (R : TestAlgebra k) (r : R),
    (hom a).app R (upper r) = rootPoint (M.rootMap a) R r
  lower_eq : ∀ a (R : TestAlgebra k) (r : R),
    (hom a).app R (lower r) = rootPoint (M.rootMap (D.datum.reflectionPerm a a)) R r
  diagonal_eq : ∀ a (R : TestAlgebra k) (s : Rˣ),
    ∃ t : GroupPoints T.group R,
      (hom a).app R (diagonal s) = t ≫ T.inclusion.hom.hom ∧
      ∀ x : D.X, characterValue (Additive.toMul (M.character x)) R t =
        (↑(s ^ D.datum.coroot' a x) : R)

/-- The specified ambient group and torus, together with the Borel selected
by the marked positive system. -/
abbrev markedBorelPair {H : AffineAlgebraicGroup k} (hH : IsReductive H)
    {T : ClosedSubgroup H.val} (hT : IsSplitTorus T.group) (hMax : IsGeometricallyMaximal T)
    (B : ClosedSubgroup H.val) (hB : IsKBorel B) (hTB : IsSubgroupOf T B) :
    SplitBorelPair k :=
  ⟨H, hH, T, hT, hMax, B, hB, hTB⟩

/-- The positive system selects a Borel. Its attached datum has the exact
character and root markings, and the marked coordinates induce the pinning
while retaining the ambient root morphisms at every root. -/
def Statement : Prop :=
  ∀ (D : BasedRootDatum.{u}) (k : Type u) [Field k]
    (H : AffineAlgebraicGroup k) (hH : IsReductive H)
    (T : ClosedSubgroup H.val) (hT : IsSplitTorus T.group) (hMax : IsGeometricallyMaximal T)
    (A : AdditiveLine k) (M : Marking D H T A), RankOneRelations M →
    ∃ (B : ClosedSubgroup H.val) (hB : IsKBorel B) (hTB : IsSubgroupOf T B),
      let P := markedBorelPair hH hT hMax B hB hTB
      ∃ (E : AttachedDatum P) (e : BasedIso D E.toBased)
        (pin : Pinning A P M.roots)
        (z : ∀ α : Root T, RootCoordinate A T (M.roots α).val α.val),
        (∀ a, M.index a ∈ subgroupRoots T B ↔ D.base.IsPos a) ∧
        e.val.weightEquiv = M.character ∧
        e.val.indexEquiv = M.index ∧
        (∀ α, pin α = z α.val) ∧
        ∀ α, z α = M.coordinate α

end

end LinearAlgebraicGroups.Specs.PinnedDatumFromMarkedRootGroups
