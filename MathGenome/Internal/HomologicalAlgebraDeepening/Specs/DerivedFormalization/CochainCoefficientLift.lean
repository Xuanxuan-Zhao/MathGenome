import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Cochains
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Independent statements for the cochain coefficient-universe lift. -/

namespace Specs.DerivedFormalization.CochainCoefficientLift

open CategoryTheory CategoryTheory.Limits

universe t v u s w j k

variable {R : Type u} [Ring R]

noncomputable section

attribute [local instance] HasDerivedCategory.standard

-- The levels in each bound are independent parameters of the specified type.
set_option linter.checkUnivs false

abbrev lift (R : Type u) [Ring R] : Cochains.compValue.{v} R ⥤ Cochains.compValue.{max v t} R :=
  (ModuleCat.uliftFunctor.{t, v} R).mapHomologicalComplex (.up ℤ)

def liftType :=
  ∀ (R : Type u) [Ring R],
    Cochains.compValue.{v} R ⥤ Cochains.compValue.{max v t} R

def termEquiv (X : Cochains.compValue.{v} R) (i : ℤ) : X.X i ≃ₗ[R] ((lift.{t} R).obj X).X i :=
  ULift.moduleEquiv.symm

def termEquivType :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ),
    X.X i ≃ₗ[R] ((lift.{t} R).obj X).X i

def termEquiv_applyType : Prop :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ) (x : X.X i),
    termEquiv.{t} X i x = ULift.up x

def termEquiv_symm_applyType : Prop :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ) (x : ((lift.{t} R).obj X).X i),
    (termEquiv.{t} X i).symm x = x.down

def lift_smulType : Prop :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ) (r : R) (x : X.X i),
    r • termEquiv.{t} X i x = termEquiv.{t} X i (r • x)

def lift_dType : Prop :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i j : ℤ) (x : X.X i),
    ((lift.{t} R).obj X).d i j (termEquiv.{t} X i x) = termEquiv.{t} X j (X.d i j x)

def lift_fType : Prop :=
  ∀ {R : Type u} [Ring R] {X Y : Cochains.compValue.{v} R} (f : X ⟶ Y) (i : ℤ) (x : X.X i),
    ((lift.{t} R).map f).f i (termEquiv.{t} X i x) = termEquiv.{t} Y i (f.f i x)

def liftHomotopy {X Y : Cochains.compValue.{v} R} {f g : X ⟶ Y} (h : Homotopy f g) :
    Homotopy ((lift.{t} R).map f) ((lift.{t} R).map g) :=
  (ModuleCat.uliftFunctor.{t, v} R).mapHomotopy h

def liftHomotopyType :=
  ∀ {R : Type u} [Ring R] {X Y : Cochains.compValue.{v} R} {f g : X ⟶ Y} (_h : Homotopy f g),
    Homotopy ((lift.{t} R).map f) ((lift.{t} R).map g)

def liftHomotopy_homType : Prop :=
  ∀ {R : Type u} [Ring R] {X Y : Cochains.compValue.{v} R} {f g : X ⟶ Y} (h : Homotopy f g) (i j :
    ℤ) (x : X.X i),
    (liftHomotopy.{t} h).hom i j (termEquiv.{t} X i x) = termEquiv.{t} Y j (h.hom i j x)

def fullyFaithful (R : Type u) [Ring R] : (lift.{t, v} R).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (lift.{t, v} R)

def fullyFaithfulType :=
  ∀ (R : Type u) [Ring R],
    (lift.{t, v} R).FullyFaithful

def liftK (R : Type u) [Ring R] : Cochains.homotopyValue.{v} R ⥤ Cochains.homotopyValue.{max v t} R :=
  (ModuleCat.uliftFunctor.{t, v} R).mapHomotopyCategory (.up ℤ)

def liftKType :=
  ∀ (R : Type u) [Ring R],
    Cochains.homotopyValue.{v} R ⥤ Cochains.homotopyValue.{max v t} R

def liftKFactors (R : Type u) [Ring R] :
    Cochains.quotientValue.{v} R ⋙ liftK.{t, v} R ≅
      lift.{t, v} R ⋙ Cochains.quotientValue.{max v t} R :=
  (ModuleCat.uliftFunctor.{t, v} R).mapHomotopyCategoryFactors (.up ℤ)

def liftKFactorsType :=
  ∀ (R : Type u) [Ring R],
    Cochains.quotientValue.{v} R ⋙ liftK.{t, v} R ≅ lift.{t, v} R ⋙ Cochains.quotientValue.{max v t}
      R

def fullyFaithfulK (R : Type u) [Ring R] : (liftK.{t, v} R).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful
    ((ModuleCat.uliftFunctor.{t, v} R).mapHomotopyCategory (.up ℤ))

def fullyFaithfulKType :=
  ∀ (R : Type u) [Ring R],
    (liftK.{t, v} R).FullyFaithful

def shiftIso (R : Type u) [Ring R] (n : ℤ) :
    Cochains.shiftValue.{v} R n ⋙ lift.{t, v} R ≅ lift.{t, v} R ⋙ Cochains.shiftValue.{max v t} R n :=
  (ModuleCat.uliftFunctor.{t, v} R).mapCochainComplexShiftIso n

def shiftIsoType :=
  ∀ (R : Type u) [Ring R] (n : ℤ),
    Cochains.shiftValue.{v} R n ⋙ lift.{t, v} R ≅ lift.{t, v} R ⋙ Cochains.shiftValue.{max v t} R n

def coneIso {X Y : Cochains.compValue.{v} R} (f : X ⟶ Y) :
    (lift.{t} R).obj (CochainComplex.mappingCone f) ≅
      CochainComplex.mappingCone ((lift.{t} R).map f) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso f (ModuleCat.uliftFunctor.{t, v} R)

def coneIsoType :=
  ∀ {R : Type u} [Ring R] {X Y : Cochains.compValue.{v} R} (f : X ⟶ Y),
    (lift.{t} R).obj (CochainComplex.mappingCone f) ≅ CochainComplex.mappingCone ((lift.{t} R).map
      f)

def preservesLimitsType : Prop :=
  ∀ (R : Type u) [Ring R] (J : Type j) [Category.{k} J] [Small.{v} J],
    PreservesLimitsOfShape J (lift.{t, v} R)

def preservesColimitsType : Prop :=
  ∀ (R : Type u) [Ring R] (J : Type j) [Category.{k} J] [Small.{v} J],
    PreservesColimitsOfShape J (lift.{t, v} R)

def liftD (R : Type u) [Ring R] : Cochains.derivedValue.{v} R ⥤ Cochains.derivedValue.{max v t} R :=
  (ModuleCat.uliftFunctor.{t, v} R).mapDerivedCategory

def liftDType :=
  ∀ (R : Type u) [Ring R],
    Cochains.derivedValue.{v} R ⥤ Cochains.derivedValue.{max v t} R

def liftDFactors (R : Type u) [Ring R] :
    Cochains.qValue.{v} R ⋙ liftD.{t, v} R ≅ lift.{t, v} R ⋙ Cochains.qValue.{max v t} R :=
  (ModuleCat.uliftFunctor.{t, v} R).mapDerivedCategoryFactors

def liftDFactorsType :=
  ∀ (R : Type u) [Ring R],
    Cochains.qValue.{v} R ⋙ liftD.{t, v} R ≅ lift.{t, v} R ⋙ Cochains.qValue.{max v t} R

def liftDFactorsh (R : Type u) [Ring R] :
    Cochains.qhValue.{v} R ⋙ liftD.{t, v} R ≅ liftK.{t, v} R ⋙ Cochains.qhValue.{max v t} R :=
  (ModuleCat.uliftFunctor.{t, v} R).mapDerivedCategoryFactorsh

def liftDFactorshType :=
  ∀ (R : Type u) [Ring R],
    Cochains.qhValue.{v} R ⋙ liftD.{t, v} R ≅ liftK.{t, v} R ⋙ Cochains.qhValue.{max v t} R

def cyclesIso (R : Type u) [Ring R] (i : ℤ) :
    lift.{t, v} R ⋙ HomologicalComplex.cyclesFunctor (ModuleCat.{max v t} R) (.up ℤ) i ≅
      HomologicalComplex.cyclesFunctor (ModuleCat.{v} R) (.up ℤ) i ⋙
        ModuleCat.uliftFunctor.{t, v} R :=
  Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor _ _ i)
    (ShortComplex.cyclesFunctorIso (ModuleCat.uliftFunctor.{t, v} R))

def cyclesIsoType :=
  ∀ (R : Type u) [Ring R] (i : ℤ),
    lift.{t, v} R ⋙ HomologicalComplex.cyclesFunctor (ModuleCat.{max v t} R) (.up ℤ) i ≅
      HomologicalComplex.cyclesFunctor (ModuleCat.{v} R) (.up ℤ) i ⋙ ModuleCat.uliftFunctor.{t, v} R

def cohomologyIso (R : Type u) [Ring R] (i : ℤ) :
    lift.{t, v} R ⋙ Cochains.cohomologyValue.{max v t} R i ≅
      Cochains.cohomologyValue.{v} R i ⋙ ModuleCat.uliftFunctor.{t, v} R :=
  Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor _ _ i)
    (ShortComplex.homologyFunctorIso (ModuleCat.uliftFunctor.{t, v} R))

def cohomologyIsoType :=
  ∀ (R : Type u) [Ring R] (i : ℤ),
    lift.{t, v} R ⋙ Cochains.cohomologyValue.{max v t} R i ≅ Cochains.cohomologyValue.{v} R i ⋙
      ModuleCat.uliftFunctor.{t, v} R

def cyclesEquiv (X : Cochains.compValue.{v} R) (i : ℤ) :
    X.cycles i ≃ₗ[R] ((lift.{t} R).obj X).cycles i :=
  ULift.moduleEquiv.symm.trans (((cyclesIso.{t} R i).app X).symm.toLinearEquiv)

def cyclesEquivType :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ),
    X.cycles i ≃ₗ[R] ((lift.{t} R).obj X).cycles i

def cohomologyEquiv (X : Cochains.compValue.{v} R) (i : ℤ) :
    X.homology i ≃ₗ[R] ((lift.{t} R).obj X).homology i :=
  ULift.moduleEquiv.symm.trans (((cohomologyIso.{t} R i).app X).symm.toLinearEquiv)

def cohomologyEquivType :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ),
    X.homology i ≃ₗ[R] ((lift.{t} R).obj X).homology i

def cyclesEquiv_iCyclesType : Prop :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ) (x : X.cycles i),
    ((lift.{t} R).obj X).iCycles i (cyclesEquiv.{t} X i x) = termEquiv.{t} X i (X.iCycles i x)

def quasiIso_iffType : Prop :=
  ∀ {R : Type u} [Ring R] {X Y : Cochains.compValue.{v} R} (f : X ⟶ Y),
    QuasiIso ((lift.{t} R).map f) ↔ QuasiIso f

def acyclic_iffType : Prop :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R),
    ((lift.{t} R).obj X).Acyclic ↔ X.Acyclic

def injective_iffType : Prop :=
  ∀ {R : Type u} [Ring R] {X Y : Cochains.compValue.{v} R} (f : X ⟶ Y) (i : ℤ),
    Function.Injective (((lift.{t} R).map f).f i) ↔ Function.Injective (f.f i)

def surjective_iffType : Prop :=
  ∀ {R : Type u} [Ring R] {X Y : Cochains.compValue.{v} R} (f : X ⟶ Y) (i : ℤ),
    Function.Surjective (((lift.{t} R).map f).f i) ↔ Function.Surjective (f.f i)

def mono_iffType : Prop :=
  ∀ {R : Type u} [Ring R] {X Y : Cochains.compValue.{v} R} (f : X ⟶ Y) (i : ℤ),
    Mono (((lift.{t} R).map f).f i) ↔ Mono (f.f i)

private theorem map_boundary (X : Cochains.compValue.{v} R) (i : ℤ) :
    (LinearMap.range (X.d ((ComplexShape.up ℤ).prev i) i).hom).map
        (termEquiv.{t} X i).toLinearMap =
      LinearMap.range (((lift.{t} R).obj X).d ((ComplexShape.up ℤ).prev i) i).hom := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨ULift.up x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x.down, rfl⟩, rfl⟩

def map_boundaryType : Prop :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ),
    (LinearMap.range (X.d ((ComplexShape.up ℤ).prev i) i).hom).map (termEquiv.{t} X i).toLinearMap =
      LinearMap.range (((lift.{t} R).obj X).d ((ComplexShape.up ℤ).prev i) i).hom

def boundariesEquiv (X : Cochains.compValue.{v} R) (i : ℤ) :
    LinearMap.range (X.d ((ComplexShape.up ℤ).prev i) i).hom ≃ₗ[R]
      LinearMap.range (((lift.{t} R).obj X).d ((ComplexShape.up ℤ).prev i) i).hom :=
  (termEquiv.{t} X i).ofSubmodules _ _ (map_boundary.{t} X i)

def boundariesEquivType :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ),
    LinearMap.range (X.d ((ComplexShape.up ℤ).prev i) i).hom ≃ₗ[R]
      LinearMap.range (((lift.{t} R).obj X).d ((ComplexShape.up ℤ).prev i) i).hom

def boundariesEquiv_applyType : Prop :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ) (x : LinearMap.range (X.d
    ((ComplexShape.up ℤ).prev i) i).hom),
    (boundariesEquiv.{t} X i x).val = termEquiv.{t} X i x.val

def cohomologyEquiv_homologyπType : Prop :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ) (x : X.cycles i),
    cohomologyEquiv.{t} X i (X.homologyπ i x) =
      ((lift.{t} R).obj X).homologyπ i (cyclesEquiv.{t} X i x)

structure MixedHom (X : Cochains.compValue.{v} R) (Y : Cochains.compValue.{w} R) where
  f (i : ℤ) : X.X i →ₗ[R] Y.X i
  comm (i j : ℤ) (x : X.X i) : Y.d i j (f i x) = f j (X.d i j x)

def MixedHomType :=
  ∀ {R : Type u} [Ring R], Cochains.compValue.{v} R → Cochains.compValue.{w} R → Type (max v w)

abbrev mixedHomValue (X : Cochains.compValue.{v} R) (Y : Cochains.compValue.{w} R) :=
  MixedHom X Y

def fromOriginal {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R}
    (f : (lift.{t} R).obj X ⟶ Y) : MixedHom X Y where
  f i := (f.f i).hom.comp (termEquiv.{t} X i).toLinearMap
  comm i j x :=
    congrArg (fun g => g (termEquiv.{t} X i x)) (ModuleCat.hom_ext_iff.mp (f.comm i j))

def fromOriginalType :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R} (_f :
    (lift.{t} R).obj X ⟶ Y),
    MixedHom X Y

def toOriginal {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R}
    (f : X ⟶ (lift.{t} R).obj Y) : MixedHom X Y where
  f i := (termEquiv.{t} Y i).symm.toLinearMap.comp (f.f i).hom
  comm i j x :=
    congrArg ULift.down (congrArg (fun g => g x) (ModuleCat.hom_ext_iff.mp (f.comm i j)))

def toOriginalType :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R} (_f :
    X ⟶ (lift.{t} R).obj Y),
    MixedHom X Y

def fromOriginalEquiv {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R} :
    ((lift.{t} R).obj X ⟶ Y) ≃ MixedHom X Y where
  toFun := fromOriginal
  invFun f :=
    { f := fun i => ModuleCat.ofHom ((f.f i).comp (termEquiv.{t} X i).symm.toLinearMap)
      comm' := fun i j _ => by
        apply ModuleCat.hom_ext
        ext x
        exact f.comm i j x.down }
  left_inv f := by ext i x; rfl
  right_inv := by rintro ⟨f, h⟩; rfl

def fromOriginalEquivType :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R},
    ((lift.{t} R).obj X ⟶ Y) ≃ MixedHom X Y

def toOriginalEquiv {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R} :
    (X ⟶ (lift.{t} R).obj Y) ≃ MixedHom X Y where
  toFun := toOriginal
  invFun f :=
    { f := fun i => ModuleCat.ofHom ((termEquiv.{t} Y i).toLinearMap.comp (f.f i))
      comm' := fun i j _ => by
        apply ModuleCat.hom_ext
        ext x
        exact congrArg ULift.up (f.comm i j x) }
  left_inv f := by ext i x; rfl
  right_inv := by rintro ⟨f, h⟩; rfl

def toOriginalEquivType :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R},
    (X ⟶ (lift.{t} R).obj Y) ≃ MixedHom X Y

def fromOriginal_injectiveType : Prop :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R} (f :
    (lift.{t} R).obj X ⟶ Y) (i : ℤ),
    Function.Injective ((fromOriginal.{t} f).f i) ↔ Mono (f.f i)

def fromOriginal_surjectiveType : Prop :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R} (f :
    (lift.{t} R).obj X ⟶ Y) (i : ℤ),
    Function.Surjective ((fromOriginal.{t} f).f i) ↔ Function.Surjective (f.f i)

def toOriginal_injectiveType : Prop :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R} (f : X
    ⟶ (lift.{t} R).obj Y) (i : ℤ),
    Function.Injective ((toOriginal.{t} f).f i) ↔ Mono (f.f i)

def toOriginal_surjectiveType : Prop :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R} (f : X
    ⟶ (lift.{t} R).obj Y) (i : ℤ),
    Function.Surjective ((toOriginal.{t} f).f i) ↔ Function.Surjective (f.f i)

def fromOriginalCycles {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R}
    (f : (lift.{t} R).obj X ⟶ Y) (i : ℤ) : X.cycles i →ₗ[R] Y.cycles i :=
  (HomologicalComplex.cyclesMap f i).hom.comp (cyclesEquiv.{t} X i).toLinearMap

def fromOriginalCyclesType :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R} (_f :
    (lift.{t} R).obj X ⟶ Y) (i : ℤ),
    X.cycles i →ₗ[R] Y.cycles i

def toOriginalCycles {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R}
    (f : X ⟶ (lift.{t} R).obj Y) (i : ℤ) : X.cycles i →ₗ[R] Y.cycles i :=
  (cyclesEquiv.{t} Y i).symm.toLinearMap.comp (HomologicalComplex.cyclesMap f i).hom

def toOriginalCyclesType :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R} (_f :
    X ⟶ (lift.{t} R).obj Y) (i : ℤ),
    X.cycles i →ₗ[R] Y.cycles i

def fromOriginalCohomology {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R}
    (f : (lift.{t} R).obj X ⟶ Y) (i : ℤ) : X.homology i →ₗ[R] Y.homology i :=
  (HomologicalComplex.homologyMap f i).hom.comp (cohomologyEquiv.{t} X i).toLinearMap

def fromOriginalCohomologyType :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R} (_f :
    (lift.{t} R).obj X ⟶ Y) (i : ℤ),
    X.homology i →ₗ[R] Y.homology i

def toOriginalCohomology {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R}
    (f : X ⟶ (lift.{t} R).obj Y) (i : ℤ) : X.homology i →ₗ[R] Y.homology i :=
  (cohomologyEquiv.{t} Y i).symm.toLinearMap.comp (HomologicalComplex.homologyMap f i).hom

def toOriginalCohomologyType :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R} (_f :
    X ⟶ (lift.{t} R).obj Y) (i : ℤ),
    X.homology i →ₗ[R] Y.homology i

def fromOriginalCycles_iCyclesType : Prop :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R} (f :
    (lift.{t} R).obj X ⟶ Y) (i : ℤ) (x : X.cycles i),
    Y.iCycles i (fromOriginalCycles.{t} f i x) = (fromOriginal.{t} f).f i (X.iCycles i x)

def toOriginalCycles_iCyclesType : Prop :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R} (f : X
    ⟶ (lift.{t} R).obj Y) (i : ℤ) (x : X.cycles i),
    Y.iCycles i (toOriginalCycles.{t} f i x) = (toOriginal.{t} f).f i (X.iCycles i x)

def fromOriginalCohomology_homologyπType : Prop :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R} (f :
    (lift.{t} R).obj X ⟶ Y) (i : ℤ) (x : X.cycles i),
    fromOriginalCohomology.{t} f i (X.homologyπ i x) = Y.homologyπ i (fromOriginalCycles.{t} f i x)

def toOriginalCohomology_homologyπType : Prop :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R} (f : X
    ⟶ (lift.{t} R).obj Y) (i : ℤ) (x : X.cycles i),
    toOriginalCohomology.{t} f i (X.homologyπ i x) = Y.homologyπ i (toOriginalCycles.{t} f i x)

def fromOriginal_quasiIso_iffType : Prop :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{v} R} {Y : Cochains.compValue.{max v t} R} (f :
    (lift.{t} R).obj X ⟶ Y),
    QuasiIso f ↔ ∀ i, Function.Bijective (fromOriginalCohomology.{t} f i)

def toOriginal_quasiIso_iffType : Prop :=
  ∀ {R : Type u} [Ring R] {X : Cochains.compValue.{max v t} R} {Y : Cochains.compValue.{v} R} (f : X
    ⟶ (lift.{t} R).obj Y),
    QuasiIso f ↔ ∀ i, Function.Bijective (toOriginalCohomology.{t} f i)

def compIso (R : Type u) [Ring R] :
    lift.{t, v} R ⋙ lift.{s, max v t} R ≅ lift.{max t s, v} R :=
  Functor.mapHomologicalComplexCompIso
    (NatIso.ofComponents
      (fun M : ModuleCat.{v} R =>
        let first : M ≃ₗ[R] ((ModuleCat.uliftFunctor.{t, v} R).obj M : Type _) :=
          ULift.moduleEquiv.symm
        let second : ((ModuleCat.uliftFunctor.{t, v} R).obj M : Type _) ≃ₗ[R]
            ((ModuleCat.uliftFunctor.{t, v} R ⋙
              ModuleCat.uliftFunctor.{s, max v t} R).obj M : Type _) := ULift.moduleEquiv.symm
        let single : M ≃ₗ[R] ((ModuleCat.uliftFunctor.{max t s, v} R).obj M : Type _) :=
          ULift.moduleEquiv.symm
        ((first.trans second).symm.trans single).toModuleIso)
      (fun _ => by ext; rfl)) (.up ℤ)

def compIsoType :=
  ∀ (R : Type u) [Ring R],
    lift.{t, v} R ⋙ lift.{s, max v t} R ≅ lift.{max t s, v} R

def sameLevelIso (R : Type u) [Ring R] : lift.{v, v} R ≅ 𝟭 (Cochains.compValue.{v} R) :=
  let e : ModuleCat.uliftFunctor.{v, v} R ≅ 𝟭 (ModuleCat.{v} R) :=
    NatIso.ofComponents
      (fun M : ModuleCat.{v} R =>
        (ULift.moduleEquiv : ((ModuleCat.uliftFunctor.{v, v} R).obj M : Type v) ≃ₗ[R]
          M).toModuleIso)
      (fun _ => by ext; rfl)
  NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (ModuleCat.{v} R) (ComplexShape.up ℤ)

def sameLevelIsoType :=
  ∀ (R : Type u) [Ring R],
    lift.{v, v} R ≅ 𝟭 (Cochains.compValue.{v} R)

def restrictScalarsIso {S : Type s} [Ring S] (a : R →+* S) :
    (ModuleCat.restrictScalars.{v} a).mapHomologicalComplex (.up ℤ) ⋙ lift.{t, v} R ≅
      lift.{t, v} S ⋙ (ModuleCat.restrictScalars.{max v t} a).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.restrictScalars.{v} a ⋙ ModuleCat.uliftFunctor.{t, v} R))
      (.up ℤ)).symm

def restrictScalarsIsoType :=
  ∀ {R : Type u} [Ring R] {S : Type s} [Ring S] (a : R →+* S),
    (ModuleCat.restrictScalars.{v} a).mapHomologicalComplex (.up ℤ) ⋙ lift.{t, v} R ≅ lift.{t, v} S
      ⋙ (ModuleCat.restrictScalars.{max v t} a).mapHomologicalComplex (.up ℤ)

def compIso_applyType : Prop :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ)
    (x : (((lift.{t, v} R) ⋙ lift.{s, max v t} R).obj X).X i),
    ((compIso.{t, v, u, s} R).hom.app X).f i x = ULift.up x.down.down

def sameLevelIso_applyType : Prop :=
  ∀ {R : Type u} [Ring R] (X : Cochains.compValue.{v} R) (i : ℤ) (x : ((lift.{v, v} R).obj X).X i),
    ((sameLevelIso.{v} R).hom.app X).f i x = x.down

def restrictScalarsIso_applyType : Prop :=
  ∀ {R : Type u} [Ring R] {S : Type s} [Ring S] (a : R →+* S) (X : Cochains.compValue.{v} S) (i : ℤ)
    (x : X.X i),
    ((restrictScalarsIso.{t, v} a).hom.app X).f i (ULift.up x) = ULift.up x

def restrictScalars_smulType : Prop :=
  ∀ {R : Type u} [Ring R] {S : Type s} [Ring S] (a : R →+* S) (X : Cochains.compValue.{v} S) (i : ℤ)
    (r : R) (x : X.X i),
    let M := ((lift.{t, v} S ⋙
      (ModuleCat.restrictScalars.{max v t} a).mapHomologicalComplex (.up ℤ)).obj X).X i
    @SMul.smul R M (inferInstanceAs (SMul R M)) r (ULift.up x) = ULift.up (a r • x)

end

end Specs.DerivedFormalization.CochainCoefficientLift
