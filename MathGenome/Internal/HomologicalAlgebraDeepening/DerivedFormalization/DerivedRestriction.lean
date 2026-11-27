import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Cochains
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! Restriction of scalars on modules, cochains and derived categories. -/

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u w

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] (f : R →+* S)

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- Restriction along `f` acts on a module by letting `r` act as `f r`. -/
abbrev restrictScalars : ModuleCat.{v} S ⥤ ModuleCat.{v} R :=
  ModuleCat.restrictScalars f

theorem restrictScalars_smul (M : ModuleCat.{v} S) (r : R)
    (x : (restrictScalars f).obj M) :
    r • x = f r • (show M from x) :=
  ModuleCat.restrictScalars.smul_def f r x

theorem restrictScalars_map_apply {M N : ModuleCat.{v} S} (g : M ⟶ N) (x : M) :
    (restrictScalars f).map g x = g x :=
  ModuleCat.restrictScalars.map_apply f g x

/-- Restriction of scalars applied degreewise to an unbounded cochain complex. -/
abbrev restrictScalarsComplex : Comp.{v} S ⥤ Comp.{v} R :=
  (restrictScalars.{v} f).mapHomologicalComplex (.up ℤ)

@[simp] theorem restrictScalarsComplex_X (X : Comp.{v} S) (i : ℤ) :
    ((restrictScalarsComplex f).obj X).X i = (restrictScalars f).obj (X.X i) :=
  rfl

@[simp] theorem restrictScalarsComplex_d (X : Comp.{v} S) (i j : ℤ) :
    ((restrictScalarsComplex f).obj X).d i j = (restrictScalars f).map (X.d i j) :=
  rfl

@[simp] theorem restrictScalarsComplex_map_f {X Y : Comp.{v} S} (g : X ⟶ Y) (i : ℤ) :
    ((restrictScalarsComplex f).map g).f i = (restrictScalars f).map (g.f i) :=
  rfl

theorem restrictScalars_exact (C : ShortComplex (ModuleCat.{v} S)) (hC : C.Exact) :
    (C.map (restrictScalars f)).Exact :=
  ModuleCat.restrictScalars_map_exact f C hC

theorem restrictScalarsComplex_shortExact (C : ShortComplex (Comp.{v} S))
    (hC : C.ShortExact) :
    (C.map (restrictScalarsComplex f)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  exact ((HomologicalComplex.shortExact_iff_degreewise_shortExact C).mp hC i).map_of_exact
    (restrictScalars f)

/-- Cohomology of the restricted complex is restriction of the original cohomology. -/
def restrictScalarsCohomologyIso (i : ℤ) :
    restrictScalarsComplex.{v} f ⋙ cohomologyFunctor.{v} R i ≅
      cohomologyFunctor.{v} S i ⋙ restrictScalars.{v} f :=
  Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} S) (.up ℤ) i)
    (ShortComplex.homologyFunctorIso (restrictScalars.{v} f))

theorem restrictScalarsComplex_quasiIso {X Y : Comp.{v} S} (g : X ⟶ Y) (hg : QuasiIso g) :
    QuasiIso ((restrictScalarsComplex f).map g) := by
  let _ := hg
  infer_instance

/-- Exact restriction of scalars induces restriction on the unbounded derived categories. -/
abbrev derivedRestrictScalars : D.{v} S ⥤ D.{v} R :=
  (restrictScalars.{v} f).mapDerivedCategory

/-- The comparison of derived restriction with restriction on arbitrary cochain models. -/
def derivedRestrictScalarsFactors :
    Q.{v} S ⋙ derivedRestrictScalars.{v} f ≅ restrictScalarsComplex.{v} f ⋙ Q.{v} R :=
  (restrictScalars.{v} f).mapDerivedCategoryFactors

@[reassoc]
theorem derivedRestrictScalarsFactors_naturality {X Y : Comp.{v} S} (g : X ⟶ Y) :
    (derivedRestrictScalars f).map ((Q S).map g) ≫ (derivedRestrictScalarsFactors f).hom.app Y =
      (derivedRestrictScalarsFactors f).hom.app X ≫ (Q R).map ((restrictScalarsComplex f).map g) :=
  (restrictScalars.{v} f).mapDerivedCategoryFactors_hom_naturality g

theorem derivedRestrictScalars_isTriangulated : (derivedRestrictScalars.{v} f).IsTriangulated :=
  inferInstance

/-- The cochain cohomology comparison descends to the derived category. -/
def derivedRestrictScalarsCohomologyIso (i : ℤ) :
    derivedRestrictScalars.{v} f ⋙ derivedCohomologyFunctor.{v} R i ≅
      derivedCohomologyFunctor.{v} S i ⋙ restrictScalars.{v} f :=
  Localization.liftNatIso (Q.{v} S) (HomologicalComplex.quasiIso (ModuleCat.{v} S) (.up ℤ))
    _ _ _ _
    (Functor.isoWhiskerRight (derivedRestrictScalarsFactors.{v} f) _ ≪≫
      Functor.isoWhiskerLeft (restrictScalarsComplex.{v} f) (cohomologyFactors.{v} R i) ≪≫
      restrictScalarsCohomologyIso.{v} f i ≪≫
      Functor.isoWhiskerRight (cohomologyFactors.{v} S i).symm _)

end

end DerivedFormalization
