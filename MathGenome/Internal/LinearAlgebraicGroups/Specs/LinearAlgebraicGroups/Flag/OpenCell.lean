import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelsAndChambers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SimpleRoots

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.OpenCell

open AbstractPairing (Datum Root)
open BorelsAndChambers (subgroupRoots)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open SimpleRoots (wordLength)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (multiplyFactors)

noncomputable section

variable {k : Type u} [Field k] {G : GroupScheme k}

/-- For Borels through the same split maximal torus, opposition means that
their Lie root sets are complementary in the actual absolute root system. -/
def AreOpposite (T B Bneg : ClosedSubgroup G) : Prop :=
  subgroupRoots T Bneg = (subgroupRoots T B)ᶜ

/-- The canonical product over the ground field of the two radicals and the
torus, multiplied in the order negative radical, torus, positive radical. -/
def cellMap (T : ClosedSubgroup G) {B Bneg : ClosedSubgroup G}
    (Uneg : ClosedSubgroup Bneg.group) (Upos : ClosedSubgroup B.group) :
    Uneg.group.X ⊗ (T.group.X ⊗ Upos.group.X) ⟶ G.X :=
  (fst _ _ ≫ (Uneg.inclusion ≫ Bneg.inclusion).hom.hom) *
    (snd _ _ ≫ multiplyFactors T.inclusion (Upos.inclusion ≫ B.inclusion))

/-- Left multiplication by the indicated rational point on the cell. -/
def translatedCellMap (T : ClosedSubgroup G) {B Bneg : ClosedSubgroup G}
    (Uneg : ClosedSubgroup Bneg.group) (Upos : ClosedSubgroup B.group)
    (n : 𝟙_ (SchemeOver k) ⟶ G.X) :
    Uneg.group.X ⊗ (T.group.X ⊗ Upos.group.X) ⟶ G.X :=
  (toUnit _ ≫ n) * cellMap T Uneg Upos

/-- The double orbit map sends the pair of Borel factors to (b_1 n b_2). -/
def doubleOrbitMap (B : ClosedSubgroup G) (n : 𝟙_ (SchemeOver k) ⟶ G.X) :
    B.group.X ⊗ B.group.X ⟶ G.X :=
  (fst _ _ ≫ B.inclusion.hom.hom) * (toUnit _ ≫ n) *
    (snd _ _ ≫ B.inclusion.hom.hom)

/-- Membership in the fppf image of the double orbit map. The covering
sieve consists of the base changes on which the section has Borel factors. -/
def InFppfDoubleOrbit (B : ClosedSubgroup G) (n : 𝟙_ (SchemeOver k) ⟶ G.X)
    {Y : SchemeOver k} (g : Y ⟶ G.X) : Prop :=
  (Sieve.generate (Presieve.singleton (doubleOrbitMap B n))).pullback g ∈ Fppf.schemeTopology k Y

/-- The open cell and its longest-element translate for a split connected
reductive pair. The translated open represents the fppf double orbit on
every test scheme over the ground field. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
    ∀ B Bneg : ClosedSubgroup G.val,
      IsKBorel B → IsKBorel Bneg → IsSubgroupOf T B → IsSubgroupOf T Bneg →
        AreOpposite T B Bneg →
    ∀ (Uneg : ClosedSubgroup Bneg.group) (Upos : ClosedSubgroup B.group),
      IsUnipotentRadical (closedSubgroupAlgebraicGroup Bneg) Uneg →
      IsUnipotentRadical (closedSubgroupAlgebraicGroup B) Upos →
      IsOpenImmersion (cellMap T Uneg Upos).left ∧
      (∀ (K : Type u) [Field K] [Algebra k K],
        DenseRange ((baseChange k K).map (cellMap T Uneg Upos)).left) ∧
      ∀ (comm : IsCommMonObj T.group.X), letI := comm
        ∀ (D : Datum T) (e : DatumAndWeyl.Identification D) (b : D.rootDatum.Base),
          (∀ α : Root T, b.IsPos α ↔ α ∈ subgroupRoots T B) →
          ∀ w : D.rootDatum.weylGroup,
            (∀ v : D.rootDatum.weylGroup,
              wordLength D.rootDatum b v ≤ wordLength D.rootDatum b w) →
            ∀ n : 𝟙_ (SchemeOver k) ⟶ e.normalizer.group.X,
              n ≫ e.quotient.hom.hom = e.image.constantGroup.sectionPoint (e.labelEquiv w) →
              let nG := n ≫ e.normalizer.inclusion.hom.hom
              let m := translatedCellMap T Uneg Upos nG
              IsOpenImmersion m.left ∧
                ∀ {Y : SchemeOver k} (g : Y ⟶ G.val.X),
                  (∃ y, y ≫ m = g) ↔ InFppfDoubleOrbit B nG g

end

end LinearAlgebraicGroups.Specs.OpenCell
