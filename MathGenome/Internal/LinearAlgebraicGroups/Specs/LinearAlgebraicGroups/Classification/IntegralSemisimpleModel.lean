import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRootRelations
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.MonoidalCategory TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.IntegralSemisimpleModel

open Pinning (BasedRootDatum RootCoordinate)
open RationalRealization (Realization)
open OrderedRootProducts (Enumerates)
open CharacterPairing (characterValue)

noncomputable section

/-- A lift of the integers to the universe of the datum and schemes. -/
abbrev Integers := ULift.{u} ℤ

abbrev Base := Spec (CommRingCat.of Integers.{u})
abbrev IntegralScheme := Over Base.{u}
abbrev IntegralGroup := Grp IntegralScheme.{u}
abbrev IntegralAlgebra := CommAlgCat.{u} Integers.{u}

abbrev integralSpec : IntegralAlgebra.{u}ᵒᵖ ⥤ IntegralScheme.{u} :=
  algSpec (CommRingCat.of Integers.{u})

abbrev IntegralPoints (G : IntegralGroup.{u}) (R : IntegralAlgebra.{u}) :=
  integralSpec.obj (op R) ⟶ G.X

abbrev integralPointFunctor (G : IntegralGroup.{u}) : IntegralAlgebra.{u} ⥤ GrpCat.{u} :=
  integralSpec.rightOp ⋙ yonedaGrp.obj G

abbrev additiveScheme : IntegralScheme.{u} :=
  integralSpec.obj (op (CommAlgCat.of Integers.{u} (Polynomial Integers.{u})))

abbrev additivePoint (R : IntegralAlgebra.{u}) (a : R) :
    integralSpec.obj (op R) ⟶ additiveScheme :=
  integralSpec.map (CommAlgCat.ofHom (Polynomial.aeval a : Polynomial Integers.{u} →ₐ[_] R)).op

/-- The additive group with its standard polynomial coordinate over the integers. -/
structure AdditiveLine where
  operations : GrpObj additiveScheme.{u}
  add : ∀ (R : IntegralAlgebra.{u}) (a b : R),
    letI := operations
    additivePoint R a * additivePoint R b = additivePoint R (a + b)

abbrev AdditiveLine.group (L : AdditiveLine.{u}) : IntegralGroup.{u} :=
  { X := additiveScheme, grp := L.operations }

abbrev AdditiveLine.point (L : AdditiveLine.{u}) (R : IntegralAlgebra.{u}) (a : R) :
    IntegralPoints L.group R :=
  additivePoint R a

/-- The marked split torus has the group algebra of the full character lattice. -/
abbrev splitTorus (D : BasedRootDatum.{u}) : IntegralGroup.{u} :=
  (hopfSpec (CommRingCat.of Integers.{u})).obj
    (op (CommHopfAlgCat.of Integers.{u} (MonoidAlgebra Integers.{u} (Multiplicative D.X))))

abbrev TorusValues (D : BasedRootDatum.{u}) (R : IntegralAlgebra.{u}) :=
  Multiplicative D.X →* Rˣ

def torusPoint (D : BasedRootDatum.{u}) (R : IntegralAlgebra.{u}) (t : TorusValues D R) :
    IntegralPoints (splitTorus D) R :=
  integralSpec.map (CommAlgCat.ofHom
    (MonoidAlgebra.lift Integers.{u} R (Multiplicative D.X)
      ((Units.coeHom R).comp t))).op

/-- The cocharacter associated to the given element of the cocharacter lattice. -/
def cocharacter (D : BasedRootDatum.{u}) (y : D.Y) (R : IntegralAlgebra.{u}) (s : Rˣ) :
    TorusValues D R where
  toFun x := s ^ D.datum.toLinearMap (Multiplicative.toAdd x) y
  map_one' := by simp
  map_mul' x z := by
    change s ^ D.datum.toLinearMap (x.toAdd + z.toAdd) y = _
    rw [map_add, LinearMap.add_apply, zpow_add]

/-- The integral group functor represented by determinant-one matrices of size two. -/
def rankOnePoints : IntegralAlgebra.{u} ⥤ GrpCat.{u} where
  obj R := GrpCat.of (Matrix.SpecialLinearGroup (Fin 2) R)
  map f := GrpCat.ofHom (Matrix.SpecialLinearGroup.map f.hom.toRingHom)
  map_id _ := by apply GrpCat.ext; intro x; ext i j; rfl
  map_comp _ _ := by apply GrpCat.ext; intro x; ext i j; rfl

/-- The product of a list of schemes over the integers. -/
def product {I : Type u} (X : I → IntegralScheme.{u}) : List I → IntegralScheme.{u}
  | [] => 𝟙_ IntegralScheme.{u}
  | i :: l => X i ⊗ product X l

/-- Write the integral root factors in the given order. -/
def rootProduct {G : IntegralGroup.{u}} (L : AdditiveLine.{u})
    {I : Type u} (root : I → (L.group ⟶ G)) :
    (l : List I) → product (fun _ : I => L.group.X) l ⟶ G.X
  | [] => 1
  | i :: l => (fst _ _ ≫ (root i).hom.hom) * (snd _ _ ≫ rootProduct L root l)

/-- The ordered negative and positive root groups, separated by the marked torus. -/
def cellMap {D : BasedRootDatum.{u}} {G : IntegralGroup.{u}} (L : AdditiveLine.{u})
    (torus : splitTorus D ⟶ G) (root : D.I → (L.group ⟶ G)) (negative positive : List D.I) :
    product (fun _ : D.I => L.group.X) negative ⊗
      ((splitTorus D).X ⊗ product (fun _ : D.I => L.group.X) positive) ⟶ G.X :=
  (fst _ _ ≫ rootProduct L root negative) *
    (snd _ _ ≫ ((fst _ _ ≫ torus.hom.hom) * (snd _ _ ≫ rootProduct L root positive)))

/-- All fields, in every characteristic, carry their canonical algebra structure over the integers. -/
abbrev integerAlgebra (k : Type u) [CommRing k] : Algebra Integers.{u} k :=
  ((Int.castRingHom k).comp ULift.ringEquiv.toRingHom).toAlgebra

attribute [local instance] integerAlgebra

abbrev fibre (k : Type u) [Field k] : IntegralGroup.{u} ⥤ GroupScheme k :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k)))).mapGrp

/-- Regard a point of a scalar extension as a point on the integral scheme. -/
def forgetFibrePoint {k : Type u} [Field k] (G : IntegralGroup.{u}) (R : TestAlgebra k)
    (p : AdjointRepresentation.GroupPoints ((fibre k).obj G) R) :
    IntegralPoints G (CommAlgCat.of Integers.{u} R) := by
  let p' : (testSpec k).obj (op R) ⟶ ((fibre k).obj G).X := p
  refine Over.homMk (p'.left ≫ pullback.fst _ _) ?_
  change (p'.left ≫ pullback.fst G.X.hom _) ≫ G.X.hom =
    Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} R))
  erw [Category.assoc, pullback.condition, ← Category.assoc]
  have hp : p'.left ≫ ((fibre k).obj G).X.hom = ((testSpec k).obj (op R)).hom :=
    Over.w p'
  erw [hp]
  change Spec.map (CommRingCat.ofHom (algebraMap k R)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} k)) =
    Spec.map (CommRingCat.ofHom (algebraMap Integers.{u} R))
  rw [← Spec.map_comp]
  congr 2
  ext x
  exact map_intCast (algebraMap k R) x.down

/-- The integral group, its marked torus, root parametrizations and rank-one homomorphisms. -/
structure IntegralMarking (D : BasedRootDatum.{u}) where
  group : IntegralGroup.{u}
  affine : IsAffine group.X.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation group.X.hom
  quasiCompact : QuasiCompact group.X.hom
  smooth : Smooth group.X.hom
  connected : GeometricallyConnected group.X.hom
  line : AdditiveLine.{u}
  torus : splitTorus D ⟶ group
  torusClosed : IsClosedImmersion torus.hom.hom.left
  root : D.I → (line.group ⟶ group)
  rootClosed : ∀ a, IsClosedImmersion (root a).hom.hom.left
  conjugation : ∀ (R : IntegralAlgebra.{u}) (t : TorusValues D R) (a : D.I) (z : R),
    let g := torusPoint D R t ≫ torus.hom.hom
    g * (line.point R z ≫ (root a).hom.hom) * g⁻¹ =
      line.point R ((t (Multiplicative.ofAdd (D.datum.root a)) : R) * z) ≫ (root a).hom.hom
  openCell : ∀ (negative positive : List D.I),
    Enumerates negative {i | ¬ D.base.IsPos i} → Enumerates positive {i | D.base.IsPos i} →
    IsOpenImmersion (cellMap line torus root negative positive).left
  rankOne : D.I → (rankOnePoints.{u} ⟶ integralPointFunctor group)
  rankOneUpper : ∀ a (R : IntegralAlgebra.{u}) (z : R),
    (rankOne a).app R (IntegralRootRelations.upper z) = line.point R z ≫ (root a).hom.hom
  rankOneLower : ∀ a (R : IntegralAlgebra.{u}) (z : R),
    (rankOne a).app R (IntegralRootRelations.lower z) =
      line.point R z ≫ (root (D.datum.reflectionPerm a a)).hom.hom
  rankOneDiagonal : ∀ a (R : IntegralAlgebra.{u}) (s : Rˣ),
    (rankOne a).app R (IntegralRootRelations.diagonal s) =
      torusPoint D R (cocharacter D (D.datum.coroot a) R s) ≫ torus.hom.hom

/-- The integral marking identifies the actual pinned based datum in every field fibre. -/
structure Model (D : BasedRootDatum.{u}) extends IntegralMarking D where
  fieldFibre : ∀ (k : Type u) [Field k],
    ∃ (A : RootGroups.AdditiveLine k) (F : Realization D A)
      (e : (fibre k).obj group ≅ F.pinned.pair.G.val)
      (t : (fibre k).obj (splitTorus D) ≅ F.pinned.pair.T.group)
      (z : ∀ a : D.I, RootCoordinate A F.pinned.pair.T
        (F.pinned.roots (F.datumIso.val.indexEquiv a)).val (F.datumIso.val.indexEquiv a).val),
      ((fibre k).map torus) ≫ e.hom = t.hom ≫ F.pinned.pair.T.inclusion ∧
      (∀ a : D.base.support, z a.val = F.pinned.pin (F.simpleRoot a)) ∧
      (∀ (R : TestAlgebra k) (s : AdjointRepresentation.GroupPoints ((fibre k).obj (splitTorus D)) R)
          (v : TorusValues D (CommAlgCat.of Integers.{u} R)),
        forgetFibrePoint (splitTorus D) R s = torusPoint D (CommAlgCat.of Integers.{u} R) v →
        ∀ x : D.X, characterValue (Additive.toMul (F.datumIso.val.weightEquiv x)) R
          (s ≫ t.hom.hom.hom) = (v (Multiplicative.ofAdd x) : R)) ∧
      ∀ (a : D.I) (R : TestAlgebra k) (r : R),
        forgetFibrePoint group R
          (RootGroups.rootPoint ((z a).val.hom ≫
            (F.pinned.roots (F.datumIso.val.indexEquiv a)).val.inclusion ≫ e.inv) R r) =
          line.point (CommAlgCat.of Integers.{u} R) r ≫ (root a).hom.hom

/-- Every finite based reduced semisimple datum whose cocharacter lattice is
generated by its coroots is realized by a split model over the integers. -/
def Statement : Prop :=
  ∀ (D : BasedRootDatum.{u}), RootData.rationalRootAnnihilator D.datum = ⊥ →
    Submodule.span ℤ (Set.range D.datum.coroot) = ⊤ →
    (∀ a : D.I, ∃ w : D.X, D.datum.coroot' a w = 1) ∧ Nonempty (Model D)

end

end LinearAlgebraicGroups.Specs.IntegralSemisimpleModel
