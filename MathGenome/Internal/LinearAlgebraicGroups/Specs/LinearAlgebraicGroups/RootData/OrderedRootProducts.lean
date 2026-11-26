import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbstractPairing
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelsAndChambers

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.OrderedRootProducts

open AbstractPairing (Root)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open CharacterDescent (Cocharacter)
open CharacterPairing (absoluteRoots)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (IsRootSubgroup)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition oppositeCocharacter)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- An enumeration lists each element of the set exactly once. -/
def Enumerates {I : Type u} (l : List I) (S : Set I) : Prop :=
  l.Nodup ∧ ∀ i, i ∈ l ↔ i ∈ S

/-- An ambient closed root subgroup at each absolute root. -/
abbrev RootSubgroupFamily (T : ClosedSubgroup G.val) :=
  ∀ α : Root T, {U : ClosedSubgroup G.val // IsRootSubgroup T U α.val}

/-- The product over the ground field with factors in list order.
The empty product is the base scheme. -/
def product {I : Type u} (X : I → SchemeOver k) : List I → SchemeOver k
  | [] => 𝟙_ (SchemeOver k)
  | i :: l => X i ⊗ product X l

/-- Multiply the inclusions of the root group factors from left to right. -/
def rootProduct {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T) :
    (l : List (Root T)) → product (fun α => (U α).val.group.X) l ⟶ G.val.X
  | [] => 1
  | α :: l =>
    (fst _ _ ≫ (U α).val.inclusion.hom.hom) * (snd _ _ ≫ rootProduct U l)

/-- The root product identifies its domain with a subgroup via the given
inclusion into the ambient group. -/
def Parametrizes {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T) (l : List (Root T))
    {X : SchemeOver k} (i : X ⟶ G.val.X) : Prop :=
  ∃ e : product (fun α => (U α).val.group.X) l ≅ X, e.hom ≫ i = rootProduct U l

/-- For every cocharacter of the split maximal torus, each ordering of the
strictly positive roots gives a scheme isomorphism onto its contracting group. -/
def ContractingProduct : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
    (absoluteRoots T).Finite ∧ Nonempty (RootSubgroupFamily T) ∧
    ∀ cochar : Cocharacter T.group,
      Nonempty (LimitDecomposition (cochar ≫ T.inclusion)) ∧
      ∀ (D : LimitDecomposition (cochar ≫ T.inclusion))
        (U : RootSubgroupFamily T) (l : List (Root T)),
        Enumerates l (positiveRoots T cochar) →
        Parametrizes U l D.contracting.inclusion.hom.hom

/-- For a Borel through the split torus, the ordered product of its positive
root groups parametrizes the unipotent radical as a scheme. -/
def BorelRadicalProduct : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ B : ClosedSubgroup G.val, IsKBorel B → IsSubgroupOf T B →
      ∃ R : ClosedSubgroup B.group,
        IsUnipotentRadical (closedSubgroupAlgebraicGroup B) R ∧
        ∀ (U : RootSubgroupFamily T) (l : List (Root T)),
          Enumerates l (subgroupRoots T B) →
          Parametrizes U l (R.inclusion.hom.hom ≫ B.inclusion.hom.hom)

/-- Multiplication in the order negative root groups, torus, positive root
groups, with each of the two root orders specified by a list. -/
def rootCellMap (T : ClosedSubgroup G.val) (U : RootSubgroupFamily T)
    (negative positive : List (Root T)) :
    product (fun α => (U α).val.group.X) negative ⊗
      (T.group.X ⊗ product (fun α => (U α).val.group.X) positive) ⟶ G.val.X :=
  (fst _ _ ≫ rootProduct U negative) *
    (snd _ _ ≫
      ((fst _ _ ≫ T.inclusion.hom.hom) * (snd _ _ ≫ rootProduct U positive)))

/-- For a regular cocharacter the negative root product, torus and positive
root product multiply into the ambient group by an open immersion. -/
def RegularRootCell : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ cochar : Cocharacter T.group, IsRegular T cochar →
    ∀ (U : RootSubgroupFamily T) (negative positive : List (Root T)),
      Enumerates negative (positiveRoots T (oppositeCocharacter cochar)) →
      Enumerates positive (positiveRoots T cochar) →
      IsOpenImmersion (rootCellMap T U negative positive).left

end

end LinearAlgebraicGroups.Specs.OrderedRootProducts
