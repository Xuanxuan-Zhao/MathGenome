import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.StandardGroups
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Norm.Defs
import Mathlib.AlgebraicGeometry.OpenImmersion

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups
namespace WeilRestriction

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]

/-- Tensor a map of test algebras with the identity of the scalar algebra. -/
def tensorMap {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) : R ⊗[k] B →ₐ[B] S ⊗[k] B :=
  { (Algebra.TensorProduct.map f (AlgHom.id k B)).toRingHom with
    commutes' b := by
      change Algebra.TensorProduct.map f (AlgHom.id k B) (1 ⊗ₜ b) = 1 ⊗ₜ b
      simp }

/-- Extension of a test algebra by the scalar algebra, acting on the right tensor factor. -/
abbrev extendScalars : CommAlgCat.{u} k ⥤ CommAlgCat.{u} B where
  obj R := CommAlgCat.of B (R ⊗[k] B)
  map f := CommAlgCat.ofHom (tensorMap k B f.hom)
  map_id R := by
    ext : 2
    exact DFunLike.congr_fun (Algebra.TensorProduct.map_id (R := k) (A := R) (B := B)) _
  map_comp f g := by
    ext : 2
    exact DFunLike.congr_fun
      (Algebra.TensorProduct.map_comp g.hom f.hom (AlgHom.id k B) (AlgHom.id k B)) _

/-- Points of the restriction, in affine coordinates over the scalar algebra. -/
abbrev restrictionFunctor (A : CommAlgCat.{u} B) : CommAlgCat.{u} k ⥤ Type u :=
  extendScalars k B ⋙ coyoneda.obj (op A)

/-- A finite-type coordinate algebra and its natural representing isomorphism. -/
structure Representation (A : CommAlgCat.{u} B) where
  coordinate : CommAlgCat.{u} k
  finiteType : Algebra.FiniteType k coordinate
  points : coyoneda.obj (op coordinate) ≅ restrictionFunctor k B A

variable {k B}

/-- Two representations agree if their coordinate comparison induces the specified point maps. -/
def Compatible {A : CommAlgCat.{u} B} (P Q : Representation k B A)
    (e : P.coordinate ≅ Q.coordinate) : Prop :=
  ∀ (R : CommAlgCat.{u} k) (f : Q.coordinate ⟶ R),
    P.points.hom.app R (e.hom ≫ f) = Q.points.hom.app R f

variable (k B)

/-- A finite-type affine scheme over the spectrum of a commutative ring. -/
abbrev AffineFiniteTypeScheme (F : Type u) [CommRing F] :=
  {X : Over (Spec (CommRingCat.of F)) //
    IsAffine X.left ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom}

/-- The points on commutative algebras of a scheme over an affine base. -/
abbrev schemePoints (F : Type u) [CommRing F] (X : Over (Spec (CommRingCat.of F))) :
    CommAlgCat.{u} F ⥤ Type u :=
  (algSpec (CommRingCat.of F)).rightOp ⋙ yoneda.obj X

/-- The restricted functor of scheme points. -/
abbrev schemeRestrictionFunctor (F L : Type u) [CommRing F] [CommRing L] [Algebra F L]
    (X : Over (Spec (CommRingCat.of L))) : CommAlgCat.{u} F ⥤ Type u :=
  extendScalars F L ⋙ schemePoints L X

/-- Geometric base change along the spectrum of an algebra map. -/
abbrev pullbackScalars (F L : Type u) [CommRing F] [CommRing L] [Algebra F L] :
    Over (Spec (CommRingCat.of F)) ⥤ Over (Spec (CommRingCat.of L)) :=
  Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))

/-- Units in the scalar-extended test algebra. -/
def extendedUnits : CommAlgCat.{u} k ⥤ GrpCat.{u} where
  obj R := GrpCat.of ((extendScalars k B).obj R)ˣ
  map f := GrpCat.ofHom (Units.map (((extendScalars k B).map f).hom.toMonoidHom))
  map_id R := by
    rw [(extendScalars k B).map_id]
    ext x : 2
    rfl
  map_comp f g := by
    rw [(extendScalars k B).map_comp]
    ext x : 2
    rfl

/-- Determinant of multiplication in the extended test algebra. -/
def pointNorm (R : CommAlgCat.{u} k) : (R ⊗[k] B) →* R :=
  Algebra.norm R

private abbrev restrictScalarsObj (k L : Type u) [CommRing k] [CommRing L] [Algebra k L]
    (R : CommAlgCat.{u} L) : CommAlgCat.{u} k :=
  letI : Algebra k R := ((algebraMap L R).comp (algebraMap k L)).toAlgebra
  CommAlgCat.of k R

/-- Regard a test algebra over a commutative scalar extension as an algebra over the base. -/
abbrev restrictScalars (k L : Type u) [CommRing k] [CommRing L] [Algebra k L] :
    CommAlgCat.{u} L ⥤ CommAlgCat.{u} k where
  obj := restrictScalarsObj k L
  map {R S} a := ConcreteCategory.ofHom (C := CommAlgCat k)
    ({ toRingHom := a.hom.toRingHom
       commutes' := fun x => a.hom.commutes (algebraMap k L x) } :
      restrictScalarsObj k L R →ₐ[k] restrictScalarsObj k L S)
  map_id R := by ext; rfl
  map_comp a b := by ext; rfl

/-- Restrict a point of the base-changed coordinate algebra along `c ↦ 1 ⊗ₜ c`. -/
abbrev restrictCoordinatePoint (k L : Type u) [CommRing k] [CommRing L] [Algebra k L]
    {C : CommAlgCat.{u} k} {R : CommAlgCat.{u} L}
    (f : CommAlgCat.of L (L ⊗[k] C) ⟶ R) : C ⟶ (restrictScalars k L).obj R :=
  letI : Algebra k R := ((restrictScalars k L).obj R).algebra
  letI : IsScalarTower k L R := IsScalarTower.of_algebraMap_eq' rfl
  CommAlgCat.ofHom ((AlgHom.liftEquiv k L C R).symm f.hom)

/-- Reassociate the scalar extension of a test algebra after changing the base. -/
def tensorCancellation (k B L : Type u) [CommRing k] [CommRing B] [CommRing L]
    [Algebra k B] [Algebra k L] (R : CommAlgCat.{u} L) :
    (R ⊗[L] (L ⊗[k] B)) ≃ₐ[L] ((restrictScalars k L).obj R) ⊗[k] B :=
  letI : Algebra k R := ((restrictScalars k L).obj R).algebra
  letI : IsScalarTower k L R := IsScalarTower.of_algebraMap_eq' rfl
  Algebra.TensorProduct.cancelBaseChange k L L R B

/-- Coordinates of the base-changed scheme over the base-changed scalar algebra. -/
abbrev changedCoordinates (k B L : Type u) [CommRing k] [CommRing B] [CommRing L]
    [Algebra k B] [Algebra k L] (A : CommAlgCat.{u} B) : CommAlgCat.{u} (L ⊗[k] B) :=
  CommAlgCat.of (L ⊗[k] B) ((L ⊗[k] B) ⊗[B] A)

/-- The element with universal coordinates in the scalar algebra. -/
def genericElement {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
    {ι : Type u} [Fintype ι] (b : Module.Basis ι k B) : MvPolynomial ι k ⊗[k] B :=
  ∑ i, MvPolynomial.X i ⊗ₜ b i

/-- The equation inverted to obtain the open subscheme of units. -/
def normPolynomial {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
    {ι : Type u} [Fintype ι] (b : Module.Basis ι k B) : MvPolynomial ι k :=
  Algebra.norm (MvPolynomial ι k) (genericElement b)

abbrev NormCoordinates {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
    {ι : Type u} [Fintype ι] (b : Module.Basis ι k B) :=
  Localization.Away (normPolynomial b)

end
end WeilRestriction

namespace Specs
namespace WeilRestriction

open LinearAlgebraicGroups.WeilRestriction
attribute [local instance] Algebra.TensorProduct.rightAlgebra

def PresentationCoordinatesType :=
  ∀ {k B : Type u} [CommRing k] [CommRing B] [Algebra k B] {ι σ : Type u} [Fintype ι],
    Module.Basis ι k B → Ideal (MvPolynomial σ B) → CommAlgCat.{u} k

/-- The coefficient quotient for a polynomial presentation over the scalar algebra. -/
noncomputable def presentationCoordinates {k B : Type u} [CommRing k] [CommRing B] [Algebra k B]
    {ι σ : Type u} [Fintype ι] (b : Module.Basis ι k B) (I : Ideal (MvPolynomial σ B)) :
    CommAlgCat.{u} k :=
  let P := MvPolynomial (σ × ι) k
  let substitute : MvPolynomial σ B →ₐ[B] P ⊗[k] B :=
    MvPolynomial.aeval fun i => ∑ j, MvPolynomial.X (i, j) ⊗ₜ b j
  let relations : Ideal P := Ideal.span (Set.range fun p : I × ι =>
    (b.baseChange P).repr (substitute p.1) p.2)
  CommAlgCat.of k (P ⧸ relations)

def Representability : Prop :=
  ∀ (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]
    [Module.Free k B] [Module.Finite k B] (A : CommAlgCat.{u} B) [Algebra.FiniteType B A],
    Nonempty (Representation k B A)

def BasisIndependence : Prop :=
  ∀ (k B : Type u) [CommRing k] [CommRing B] [Algebra k B] (A : CommAlgCat.{u} B)
    (P Q : Representation k B A),
    ∃! e : P.coordinate ≅ Q.coordinate, Compatible P Q e

def SchemeRepresentability : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (X : AffineFiniteTypeScheme K),
    ∃ Y : AffineFiniteTypeScheme k,
      Nonempty (pointsFunctor Y.val ≅ schemeRestrictionFunctor k K X.val)

def GroupRepresentability : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (G : Specs.AffineAlgebraicGroup K),
    ∃ H : Specs.AffineAlgebraicGroup k,
      Nonempty ((groupPointsFunctor k).obj H.val ≅
        extendScalars k K ⋙ (groupPointsFunctor K).obj G.val)

def NormNaturality : Prop :=
  ∀ (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]
    [Module.Free k B] [Module.Finite k B] {R S : CommAlgCat.{u} k} (f : R ⟶ S)
    (x : R ⊗[k] B),
    f.hom (pointNorm k B R x) = pointNorm k B S (((extendScalars k B).map f).hom x)

def NormDetectsUnits : Prop :=
  ∀ (k B : Type u) [CommRing k] [CommRing B] [Algebra k B]
    [Module.Free k B] [Module.Finite k B] (R : CommAlgCat.{u} k) (x : R ⊗[k] B),
    IsUnit (pointNorm k B R x) ↔ IsUnit x

def FiniteFreeAfterBaseChange : Prop :=
  ∀ (k B L : Type u) [CommRing k] [CommRing B] [CommRing L] [Algebra k B] [Algebra k L]
    [Module.Free k B] [Module.Finite k B], Module.Free L (L ⊗[k] B) ∧ Module.Finite L (L ⊗[k] B)

def CoordinateBaseChange : Prop :=
  ∀ (k B L : Type u) [CommRing k] [CommRing B] [CommRing L] [Algebra k B] [Algebra k L]
    (A : CommAlgCat.{u} B) (P : Representation k B A),
    let C := CommAlgCat.of L (L ⊗[k] P.coordinate)
    Algebra.FiniteType L C ∧
      ∃ e : coyoneda.obj (op C) ≅ restrictionFunctor L (L ⊗[k] B) (changedCoordinates k B L A),
        ∀ (R : CommAlgCat.{u} L) (f : C ⟶ R) (a : A),
          tensorCancellation k B L R ((e.hom.app R f).hom ((1 : L ⊗[k] B) ⊗ₜ[B] a)) =
            (P.points.hom.app ((restrictScalars k L).obj R) (restrictCoordinatePoint k L f)).hom a

def SchemeBaseChange : Prop :=
  ∀ (k B L : Type u) [Field k] [CommRing B] [Field L] [Algebra k B] [Algebra k L]
    (A : CommAlgCat.{u} B) (Y : AffineFiniteTypeScheme k)
    (e : pointsFunctor Y.val ≅ restrictionFunctor k B A),
    let Z := (baseChange k L).obj Y.val
    IsAffine Z.left ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧
      ∃ α : pointsFunctor Z ≅ restrictionFunctor L (L ⊗[k] B) (changedCoordinates k B L A),
        ∀ (R : TestAlgebra L) (p : Points Z R) (a : A),
          tensorCancellation k B L R ((α.hom.app R p).hom ((1 : L ⊗[k] B) ⊗ₜ[B] a)) =
            (e.hom.app ((restrictTestAlgebra k L).obj R) (baseChangePoint k L Y.val R p)).hom a

def SchemePullbackRepresentability : Prop :=
  ∀ (k B L : Type u) [CommRing k] [CommRing B] [CommRing L] [Algebra k B] [Algebra k L]
    (X : AffineFiniteTypeScheme B) (Y : AffineFiniteTypeScheme k),
    (schemePoints k Y.val ≅ schemeRestrictionFunctor k B X.val) →
    let Z := (pullbackScalars k L).obj Y.val
    let X' := (pullbackScalars B (L ⊗[k] B)).obj X.val
    IsAffine Z.left ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧
      Nonempty (schemePoints L Z ≅ schemeRestrictionFunctor L (L ⊗[k] B) X')

def NormOpenImmersion : Prop :=
  ∀ (k K ι : Type u) [Field k] [Field K] [Algebra k K] [Fintype ι]
    (b : Module.Basis ι k K),
    let f := Spec.map (CommRingCat.ofHom (algebraMap (MvPolynomial ι k) (NormCoordinates b)))
    ∃ h : IsOpenImmersion f, @Scheme.Hom.opensRange _ _ f h =
      PrimeSpectrum.basicOpen (normPolynomial b)

def OpenNormLocus : Prop :=
  ∀ (k K ι : Type u) [Field k] [Field K] [Algebra k K] [Fintype ι]
    (b : Module.Basis ι k K),
    ∃ (G : Specs.AffineAlgebraicGroup k)
      (e : (groupPointsFunctor k).obj G.val ≅ extendedUnits k K)
      (i : (testSpec k).obj (op (CommAlgCat.of k (NormCoordinates b))) ≅ G.val.X),
      ∀ (R : TestAlgebra k) (f : NormCoordinates b →ₐ[k] R) (j : ι),
        (b.baseChange R).repr
          (e.hom.app R ((testSpec k).map (CommAlgCat.ofHom f).op ≫ i.hom) :
            (R ⊗[k] K)ˣ).val j =
          f (algebraMap (MvPolynomial ι k) (NormCoordinates b) (MvPolynomial.X j))

def NormHomomorphism : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (G H : Specs.AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj G.val ≅ extendedUnits k K)
    (t : (groupPointsFunctor k).obj H.val ≅ Specs.StandardGroups.multiplicativePoints k),
    ∃ f : G.val ⟶ H.val, ∀ (R : TestAlgebra k)
      (x : ((groupPointsFunctor k).obj G.val).obj R),
      (t.hom.app R (((groupPointsFunctor k).map f).app R x) : Rˣ).val =
        pointNorm k K R (e.hom.app R x : (R ⊗[k] K)ˣ).val

def MultiplicativeRestrictionNorm : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (G : Specs.AffineAlgebraicGroup K) (H : Specs.AffineAlgebraicGroup k)
    (s : (groupPointsFunctor K).obj G.val ≅ Specs.StandardGroups.multiplicativePoints K)
    (t : (groupPointsFunctor k).obj H.val ≅ Specs.StandardGroups.multiplicativePoints k),
    ∃ (W : Specs.AffineAlgebraicGroup k)
      (e : (groupPointsFunctor k).obj W.val ≅ extendScalars k K ⋙
        (groupPointsFunctor K).obj G.val)
      (n : W.val ⟶ H.val),
      ∀ (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj W.val).obj R),
        (t.hom.app R (((groupPointsFunctor k).map n).app R x) : Rˣ).val =
          pointNorm k K R
            (s.hom.app ((extendScalars k K).obj R) (e.hom.app R x) : (R ⊗[k] K)ˣ).val

end WeilRestriction
end Specs
end LinearAlgebraicGroups
