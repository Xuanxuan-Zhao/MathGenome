import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups

noncomputable section

variable (k : Type u) [Field k]

/-- The category of schemes over the field. -/
abbrev SchemeOver := Over (Spec (CommRingCat.of k))

namespace Specs

/-- A group scheme over a field, with no affineness or finiteness condition. -/
abbrev GroupScheme := Grp (SchemeOver k)

/-- An affine group scheme over a field. -/
abbrev AffineGroupScheme := {G : GroupScheme k // IsAffine G.X.left}

/-- An affine group scheme of finite type over a field. -/
abbrev AffineAlgebraicGroup :=
  {G : GroupScheme k // IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom}

def GroupSchemeType := ∀ (k : Type u) [Field k], Type (u + 1)
def AffineGroupSchemeType := ∀ (k : Type u) [Field k], Type (u + 1)
def AffineAlgebraicGroupType := ∀ (k : Type u) [Field k], Type (u + 1)

end Specs

open Specs (GroupScheme)

abbrev TestAlgebra := CommAlgCat.{u} k

/-- Taking the spectrum of a test algebra as a scheme over the field. -/
abbrev testSpec : (TestAlgebra k)ᵒᵖ ⥤ SchemeOver k :=
  AlgebraicGeometry.algSpec (CommRingCat.of k)

variable {k}

/-- The points of a scheme over a commutative test algebra. -/
abbrev Points (X : SchemeOver k) (R : TestAlgebra k) : Type u :=
  (testSpec k).obj (op R) ⟶ X

/-- Change of test algebra on points. -/
abbrev mapPoints {X : SchemeOver k} {R S : TestAlgebra k} (a : R ⟶ S) (p : Points X R) :
    Points X S :=
  (testSpec k).map a.op ≫ p

/-- The set-valued functor of points on test algebras. -/
def pointsFunctor (X : SchemeOver k) : TestAlgebra k ⥤ Type u :=
  (testSpec k).rightOp ⋙ yoneda.obj X

/-- The group-valued functor of points, functorial in the group scheme. -/
def groupPointsFunctor (k : Type u) [Field k] :
    GroupScheme k ⥤ TestAlgebra k ⥤ GrpCat.{u} :=
  yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (testSpec k).rightOp

/-- Group laws on every set of points, for which change of test algebra is a homomorphism. -/
structure NaturalGroupLaw (X : SchemeOver k) where
  group : ∀ R : TestAlgebra k, Group (Points X R)
  map_one : ∀ {R S : TestAlgebra k} (a : R ⟶ S),
    mapPoints a (group R).one = (group S).one
  map_mul : ∀ {R S : TestAlgebra k} (a : R ⟶ S) (p q : Points X R),
    mapPoints a ((group R).mul p q) = (group S).mul (mapPoints a p) (mapPoints a q)

/-- A group scheme structure induces the pointwise group law by precomposition. -/
def inducedGroupLaw (X : SchemeOver k) (s : GrpObj X) : NaturalGroupLaw X :=
  letI := s
  { group := fun _ ↦ Hom.group
    map_one := fun a ↦ MonObj.comp_one ((testSpec k).map a.op)
    map_mul := fun a p q ↦ MonObj.comp_mul ((testSpec k).map a.op) p q }

/-- The ordinary pair description of the points of a fibre product. -/
abbrev CompatiblePoints {X Y Z : SchemeOver k} (f : X ⟶ Z) (g : Y ⟶ Z)
    (R : TestAlgebra k) :=
  {p : Points X R × Points Y R // p.1 ≫ f = p.2 ≫ g}

def pullbackPointPair {X Y Z : SchemeOver k} (f : X ⟶ Z) (g : Y ⟶ Z) (R : TestAlgebra k)
    (p : Points (pullback f g) R) : CompatiblePoints f g R :=
  ⟨(p ≫ pullback.fst f g, p ≫ pullback.snd f g), by simp [pullback.condition]⟩

def mapCompatiblePoints {X Y Z : SchemeOver k} {f : X ⟶ Z} {g : Y ⟶ Z}
    {R S : TestAlgebra k} (a : R ⟶ S) (p : CompatiblePoints f g R) :
    CompatiblePoints f g S :=
  ⟨(mapPoints a p.1.1, mapPoints a p.1.2), by
    simpa only [mapPoints, Category.assoc] using
      congrArg ((testSpec k).map a.op ≫ ·) p.2⟩

/-- The points of a pullback of group schemes map to the two projected points. -/
def groupPullbackPointPair {G H L : GroupScheme k} (f : G ⟶ H) (g : L ⟶ H)
    (R : TestAlgebra k) (p : Points (pullback f g).X R) :
    CompatiblePoints f.hom.hom g.hom.hom R :=
  ⟨(p ≫ (pullback.fst f g).hom.hom, p ≫ (pullback.snd f g).hom.hom), by
    have h := congrArg (fun h ↦ p ≫ (Grp.forget (SchemeOver k)).map h)
      (pullback.condition (f := f) (g := g))
    simp only [Functor.map_comp, Category.assoc] at h ⊢
    exact h⟩

section ScalarExtension

variable (k) (K : Type u) [Field K] [Algebra k K]

/-- The morphism of field spectra associated with a field extension. -/
abbrev fieldSpecMap : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- Extension of scalars of schemes is pullback along the morphism of field spectra. -/
abbrev baseChange : SchemeOver k ⥤ SchemeOver K :=
  Over.pullback (fieldSpecMap k K)

/-- Extension of scalars of a group scheme uses the finite-product-preserving pullback. -/
abbrev groupBaseChange : GroupScheme k ⥤ GroupScheme K :=
  (baseChange k K).mapGrp

abbrev restrictTestAlgebraObj (R : TestAlgebra K) : TestAlgebra k :=
  letI : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
  CommAlgCat.of k R

/-- View a commutative algebra over the extension field as an algebra over the base field. -/
abbrev restrictTestAlgebra : TestAlgebra K ⥤ TestAlgebra k where
  obj := restrictTestAlgebraObj k K
  map {R S} a := ConcreteCategory.ofHom (C := CommAlgCat k)
    ({ toRingHom := a.hom.toRingHom
       commutes' := fun x ↦ a.hom.commutes (algebraMap k K x) } :
      restrictTestAlgebraObj k K R →ₐ[k] restrictTestAlgebraObj k K S)
  map_id R := by ext; rfl
  map_comp a b := by ext; rfl

theorem restrictTestAlgebra_spec_hom (R : TestAlgebra K) :
    ((testSpec k).obj (op ((restrictTestAlgebra k K).obj R))).hom =
      ((testSpec K).obj (op R)).hom ≫ fieldSpecMap k K :=
  Spec.map_comp (CommRingCat.ofHom (algebraMap k K)) (CommRingCat.ofHom (algebraMap K R))

/-- On points over the extension field, forget the factorization over that field. -/
def baseChangePoint (X : SchemeOver k) (R : TestAlgebra K)
    (p : Points ((baseChange k K).obj X) R) :
    Points X ((restrictTestAlgebra k K).obj R) :=
  Over.homMk (p.left ≫ pullback.fst X.hom (fieldSpecMap k K)) (by
    change (p.left ≫ pullback.fst X.hom (fieldSpecMap k K)) ≫ X.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap K R).comp (algebraMap k K)))
    erw [Category.assoc, pullback.condition]
    change p.left ≫ ((baseChange k K).obj X).hom ≫ fieldSpecMap k K = _
    rw [← Category.assoc, Over.w p]
    exact (restrictTestAlgebra_spec_hom k K R).symm)

end ScalarExtension

namespace Specs

def GroupLawComparison : Prop :=
  ∀ (k : Type u) [Field k] (X : SchemeOver k), IsAffine X.left →
    Function.Bijective (inducedGroupLaw X)

def GroupHomComparison : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme k), IsAffine G.X.left →
    Function.Bijective (fun f : G ⟶ H ↦ (groupPointsFunctor k).map f)

def PullbackPoints : Prop :=
  ∀ (k : Type u) [Field k] {X Y Z : SchemeOver k} (f : X ⟶ Z) (g : Y ⟶ Z)
    (R : TestAlgebra k), Function.Bijective (pullbackPointPair f g R)

def PullbackPointsNaturality : Prop :=
  ∀ (k : Type u) [Field k] {X Y Z : SchemeOver k} (f : X ⟶ Z) (g : Y ⟶ Z)
    {R S : TestAlgebra k} (a : R ⟶ S) (p : Points (pullback f g) R),
    pullbackPointPair f g S (mapPoints a p) =
      mapCompatiblePoints a (pullbackPointPair f g R p)

def GroupPullbackPoints : Prop :=
  ∀ (k : Type u) [Field k] {G H L : GroupScheme k} (f : G ⟶ H) (g : L ⟶ H)
    (R : TestAlgebra k), Function.Bijective (groupPullbackPointPair f g R)

def GroupPullbackPointsNaturality : Prop :=
  ∀ (k : Type u) [Field k] {G H L : GroupScheme k} (f : G ⟶ H) (g : L ⟶ H)
    {R S : TestAlgebra k} (a : R ⟶ S) (p : Points (pullback f g).X R),
    groupPullbackPointPair f g S (mapPoints a p) =
      mapCompatiblePoints a (groupPullbackPointPair f g R p)

def GroupPullbackPointsMultiplication : Prop :=
  ∀ (k : Type u) [Field k] {G H L : GroupScheme k} (f : G ⟶ H) (g : L ⟶ H)
    (R : TestAlgebra k) (p q : Points (pullback f g).X R),
    (groupPullbackPointPair f g R (p * q)).1 =
      (groupPullbackPointPair f g R p).1 * (groupPullbackPointPair f g R q).1

def BaseChangePoints : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] (X : SchemeOver k)
    (R : TestAlgebra K), Function.Bijective (baseChangePoint k K X R)

def BaseChangePointsNaturality : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] (X : SchemeOver k)
    {R S : TestAlgebra K} (a : R ⟶ S) (p : Points ((baseChange k K).obj X) R),
    baseChangePoint k K X S (mapPoints a p) =
      mapPoints ((restrictTestAlgebra k K).map a) (baseChangePoint k K X R p)

def BaseChangePointsSchemeNaturality : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] {X Y : SchemeOver k} (f : X ⟶ Y)
    (R : TestAlgebra K) (p : Points ((baseChange k K).obj X) R),
    baseChangePoint k K Y R (p ≫ (baseChange k K).map f) =
      baseChangePoint k K X R p ≫ f

def BaseChangePointsGroupLaw : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] (G : GroupScheme k)
    (R : TestAlgebra K) (p q : Points ((groupBaseChange k K).obj G).X R),
    baseChangePoint k K G.X R (p * q) =
      baseChangePoint k K G.X R p * baseChangePoint k K G.X R q

end Specs

end

end LinearAlgebraicGroups
