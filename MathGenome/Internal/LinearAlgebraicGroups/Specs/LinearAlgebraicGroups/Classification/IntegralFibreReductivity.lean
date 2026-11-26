import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRootRelations
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.OrderedRootProducts

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.IntegralFibreReductivity

open AdjointRepresentation (GroupPoints)
open Pinning (BasedRootDatum)
open RationalRealization (diagonalTorus)
open RootGroups (AdditiveLine rootPoint)
open OrderedRootProducts (Enumerates product)

noncomputable section

variable {k : Type u} [Field k] (D : BasedRootDatum.{u})

abbrev TorusValues (R : TestAlgebra k) := Multiplicative D.X →* Rˣ

/-- Evaluate the group algebra of the full character lattice. -/
def torusPoint (R : TestAlgebra k) (t : TorusValues D R) :
    GroupPoints (diagonalTorus k D).val R :=
  (testSpec k).map (CommAlgCat.ofHom
    (MonoidAlgebra.lift k R (Multiplicative D.X) ((Units.coeHom R).comp t))).op

/-- Evaluation of a marked cocharacter under the original perfect pairing. -/
def cocharacter (y : D.Y) (R : TestAlgebra k) (s : Rˣ) : TorusValues D R where
  toFun x := s ^ D.datum.toLinearMap x.toAdd y
  map_one' := by simp
  map_mul' x z := by
    change s ^ D.datum.toLinearMap (x.toAdd + z.toAdd) y = _
    rw [map_add, LinearMap.add_apply, zpow_add]

/-- The determinant-one matrix group functor with its standard size-two indexing. -/
def rankOnePoints (k : Type u) [Field k] : TestAlgebra k ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Matrix.SpecialLinearGroup (Fin 2) R)
  map f := GrpCat.ofHom (Matrix.SpecialLinearGroup.map f.hom.toRingHom)
  map_id _ := by apply GrpCat.ext; intro x; ext i j; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; ext i j; rfl

variable {D} {G : GroupScheme k}

/-- Multiply the successive additive factors of the chart. -/
def rootProduct (A : AdditiveLine k) (root : D.I → (A.group ⟶ G)) :
    (l : List D.I) → product (fun _ : D.I => A.group.X) l ⟶ G.X
  | [] => 1
  | i :: l => (fst _ _ ≫ (root i).hom.hom) * (snd _ _ ≫ rootProduct A root l)

/-- The chart multiplies the negative factors, the marked torus and the positive factors. -/
def cellMap (A : AdditiveLine k) (torus : (diagonalTorus k D).val ⟶ G)
    (root : D.I → (A.group ⟶ G)) (negative positive : List D.I) :
    product (fun _ : D.I => A.group.X) negative ⊗
      ((diagonalTorus k D).val.X ⊗ product (fun _ : D.I => A.group.X) positive) ⟶ G.X :=
  (fst _ _ ≫ rootProduct A root negative) *
    (snd _ _ ≫ ((fst _ _ ≫ torus.hom.hom) * (snd _ _ ≫ rootProduct A root positive)))

/-- The root, torus and rank-one markings on the field fibre. -/
structure Marking (D : BasedRootDatum.{u}) (G : GroupScheme k) where
  line : AdditiveLine k
  torus : (diagonalTorus k D).val ⟶ G
  torusClosed : IsClosedImmersion torus.hom.hom.left
  root : D.I → (line.group ⟶ G)
  rootClosed : ∀ a, IsClosedImmersion (root a).hom.hom.left
  conjugation : ∀ (R : TestAlgebra k) (t : TorusValues D R) (a : D.I) (z : R),
    let g : GroupPoints G R := torusPoint D R t ≫ torus.hom.hom
    g * rootPoint (root a) R z * g⁻¹ =
      rootPoint (root a) R ((t (Multiplicative.ofAdd (D.datum.root a)) : R) * z)
  negative : List D.I
  positive : List D.I
  negativeOrder : Enumerates negative {i | ¬ D.base.IsPos i}
  positiveOrder : Enumerates positive {i | D.base.IsPos i}
  openCell : IsOpenImmersion (cellMap line torus root negative positive).left
  rankOne : D.I → (rankOnePoints k ⟶ (groupPointsFunctor k).obj G)
  rankOneUpper : ∀ a (R : TestAlgebra k) (z : R),
    (rankOne a).app R (IntegralRootRelations.upper z) = rootPoint (root a) R z
  rankOneLower : ∀ a (R : TestAlgebra k) (z : R),
    (rankOne a).app R (IntegralRootRelations.lower z) =
      rootPoint (root (D.datum.reflectionPerm a a)) R z
  rankOneDiagonal : ∀ a (R : TestAlgebra k) (s : Rˣ),
    (rankOne a).app R (IntegralRootRelations.diagonal s) =
      torusPoint D R (cocharacter D (D.datum.coroot a) R s) ≫ torus.hom.hom

def Marking.subgroup (M : Marking D G) : ClosedSubgroup G :=
  ⟨_, M.torus, M.torusClosed⟩

/-- Each coroot has a character pairing to one when the coroots generate the cocharacter lattice. -/
def PrimitiveCoroots : Prop :=
  ∀ (D : BasedRootDatum.{u}), Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    ∀ a : D.I, ∃ w : D.X, D.datum.coroot' a w = 1

/-- The marked fibre is reductive, with the specified geometrically maximal torus. -/
def Statement : Prop :=
  ∀ (k : Type u) [Field k] (D : BasedRootDatum.{u}),
    RootData.rationalRootAnnihilator D.datum = ⊥ →
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    ∀ (G : AffineAlgebraicGroup k), Smooth G.val.X.hom →
      GeometricallyConnected G.val.X.hom → ∀ M : Marking D G.val,
      GeometricRadicals.IsReductive G ∧ RankOneFlag.IsGeometricallyMaximal M.subgroup

end

end LinearAlgebraicGroups.Specs.IntegralFibreReductivity
