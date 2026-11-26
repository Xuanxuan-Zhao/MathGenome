import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRootRelations

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.IntegralFibreDatum

open Pinning (BasedRootDatum SplitBorelPair AttachedDatum BasedIso RootCoordinate)
open RationalRealization (diagonalTorus Realization)
open RootGroups (AdditiveLine HasScalarAction rootPoint)
open AbstractPairing (Root)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (characterValue)
open DiagonalizableGroups (groupAlgebraMap IntegerCharacters)
open AdjointRepresentation (GroupPoints)
open OrderedRootProducts (Enumerates RootSubgroupFamily product)
open RankOneFlag (IsGeometricallyMaximal)
open GeometricRadicals (IsReductive IsSplitTorus)
open GeometricBorelConjugacy (IsKBorel)
open SchemeDerivedGroup (IsSubgroupOf)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

noncomputable section

variable {k : Type u} [Field k]

/-- The character given by a lattice monomial in the full character algebra. -/
def markedCharacter (D : BasedRootDatum.{u}) (x : D.X) :
    Character (diagonalTorus k D).val :=
  specGroupMap (groupAlgebraMap k ((zpowersHom (Multiplicative D.X)
    (Multiplicative.ofAdd x)).comp MulEquiv.ulift.toMonoidHom))

/-- The cocharacter is specified by the original integral pairing on every monomial. -/
def markedCocharacter (D : BasedRootDatum.{u}) (y : D.Y) :
    Cocharacter (diagonalTorus k D).val :=
  specGroupMap (groupAlgebraMap k (show Multiplicative D.X →* IntegerCharacters from
    { toFun := fun x => ⟨Multiplicative.ofAdd (D.datum.toLinearMap x.toAdd y)⟩
      map_one' := by change ULift.up (Multiplicative.ofAdd (D.datum.toLinearMap 0 y)) = _; simp; rfl
      map_mul' := by
        intro x x'
        change ULift.up (Multiplicative.ofAdd (D.datum.toLinearMap (x.toAdd + x'.toAdd) y)) =
          ULift.up (Multiplicative.ofAdd
            (D.datum.toLinearMap x.toAdd y + D.datum.toLinearMap x'.toAdd y))
        simp }))

abbrev oppositeIndex (D : BasedRootDatum.{u}) (i : D.I) : D.I := D.datum.reflectionPerm i i

/-- The product of the marked additive factors in the supplied list order. -/
def rootProduct {D : BasedRootDatum.{u}} {A : AdditiveLine k} {G : GroupScheme k}
    (x : D.I → (A.group ⟶ G)) :
    (l : List D.I) → product (fun _ : D.I => A.group.X) l ⟶ G.X
  | [] => 1
  | i :: l => (fst _ _ ≫ (x i).hom.hom) * (snd _ _ ≫ rootProduct x l)

/-- Multiplication of the negative factors, the full marked torus and the positive factors. -/
def cellMap {D : BasedRootDatum.{u}} {A : AdditiveLine k} {G : GroupScheme k}
    (t : (diagonalTorus k D).val ⟶ G) (x : D.I → (A.group ⟶ G))
    (negative positive : List D.I) :
    product (fun _ : D.I => A.group.X) negative ⊗
      ((diagonalTorus k D).val.X ⊗ product (fun _ : D.I => A.group.X) positive) ⟶ G.X :=
  (fst _ _ ≫ rootProduct x negative) *
    (snd _ _ ≫ ((fst _ _ ≫ t.hom.hom) * (snd _ _ ≫ rootProduct x positive)))

/-- The determinant-one matrix functor over the ground field. -/
def rankOnePoints (k : Type u) [Field k] : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Matrix.SpecialLinearGroup (Fin 2) R)
  map f := GrpCat.ofHom (Matrix.SpecialLinearGroup.map f.hom.toRingHom)
  map_id _ := by apply GrpCat.ext; intro x; ext i j; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; ext i j; rfl

/-- The scheme maps given on a field fibre of the integral construction. -/
structure Marking (D : BasedRootDatum.{u}) (G : AffineAlgebraicGroup k)
    (A : AdditiveLine k) where
  torus : (diagonalTorus k D).val ⟶ G.val
  torusClosed : IsClosedImmersion torus.hom.hom.left
  maximal : IsGeometricallyMaximal ⟨_, torus, torusClosed⟩
  root : D.I → (A.group ⟶ G.val)
  rootClosed : ∀ i, IsClosedImmersion (root i).hom.hom.left
  scalar : ∀ i, HasScalarAction ⟨_, torus, torusClosed⟩ (markedCharacter D (D.datum.root i)) (root i)
  openCell : ∃ negative positive : List D.I,
    Enumerates negative {i | ¬ D.base.IsPos i} ∧ Enumerates positive {i | D.base.IsPos i} ∧
      IsOpenImmersion (cellMap torus root negative positive).left
  rankOne : D.I → (rankOnePoints k ⟶ (groupPointsFunctor k).obj G.val)
  upper : ∀ i (R : TestAlgebra k) (z : R),
    (rankOne i).app R (IntegralRootRelations.upper z) = rootPoint (root i) R z
  lower : ∀ i (R : TestAlgebra k) (z : R),
    (rankOne i).app R (IntegralRootRelations.lower z) = rootPoint (root (oppositeIndex D i)) R z
  diagonal : ∀ i (R : TestAlgebra k) (s : Rˣ),
    (rankOne i).app R (IntegralRootRelations.diagonal s) =
      cocharacterPoint (markedCocharacter D (D.datum.coroot i)) R s ≫ torus.hom.hom

variable {D : BasedRootDatum.{u}} {G : AffineAlgebraicGroup k} {A : AdditiveLine k}

/-- The marked torus, with the original morphism as its ambient inclusion. -/
def Marking.T (M : Marking D G A) : ClosedSubgroup G.val := ⟨_, M.torus, M.torusClosed⟩

/-- The pair uses the given group and torus and the Borel chosen in their positive chamber. -/
def Marking.pair (M : Marking D G A) (hG : IsReductive G) (hT : IsSplitTorus M.T.group)
    (B : ClosedSubgroup G.val) (hB : IsKBorel B) (hTB : IsSubgroupOf M.T B) : SplitBorelPair k :=
  ⟨G, hG, M.T, hT, M.maximal, B, hB, hTB⟩

/-- Comparison with the actual based datum on the marked group. -/
structure FibreRealization (M : Marking D G A) (hG : IsReductive G) where
  split : IsSplitTorus M.T.group
  B : ClosedSubgroup G.val
  borel : IsKBorel B
  containsTorus : IsSubgroupOf M.T B
  roots : RootSubgroupFamily M.T
  coordinates : ∀ α : Root M.T, RootCoordinate A M.T (roots α).val α.val
  attached : AttachedDatum (M.pair hG split B borel containsTorus)
  datumIso : BasedIso D attached.toBased
  character : ∀ x : D.X, Additive.toMul (datumIso.val.weightEquiv x) = markedCharacter D x
  cocharacter : ∀ y : D.Y,
    Additive.toMul (datumIso.val.coweightEquiv.symm y) = markedCocharacter D y
  positive : ∀ i : D.I, datumIso.val.indexEquiv i ∈ BorelsAndChambers.subgroupRoots M.T B ↔
    D.base.IsPos i
  rootCoordinate : ∀ i : D.I,
    let α := datumIso.val.indexEquiv i
    (coordinates α).val.hom ≫ (roots α).val.inclusion = M.root i

/-- Pin the actual Borel pair by the marked coordinates at its simple roots. -/
def FibreRealization.realization {M : Marking D G A} {hG : IsReductive G}
    (F : FibreRealization M hG) : Realization D A :=
  ⟨⟨M.pair hG F.split F.B F.borel F.containsTorus, F.roots, fun α => F.coordinates α.val⟩,
    F.attached, F.datumIso⟩

/-- The marked open cell and rank-one maps identify the actual roots, coroots and pinning
of this field fibre. The morphism comparisons apply to all test algebras. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (D : BasedRootDatum.{u}) (G : AffineAlgebraicGroup k)
    (hG : IsReductive G) (A : AdditiveLine k) (M : Marking D G A),
    Nonempty (FibreRealization M hG)

end

end LinearAlgebraicGroups.Specs.IntegralFibreDatum
