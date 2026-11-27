import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Transfer

namespace Specs.DerivedFormalization.AffineModuleSheaves

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

/-- The full subcategory of quasi-coherent modules on the affine scheme. -/
abbrev qcValue (A : CommRingCat.{u}) :=
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory

def qcType := CommRingCat.{u} → Type (u + 1)

abbrev inclusion (A : CommRingCat.{u}) : qcValue A ⥤ (Spec A).Modules :=
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).ι

abbrev affineEquivValue (A : CommRingCat.{u}) : ModuleCat.{u} A ≌ qcValue A :=
  AlgebraicGeometry.tildeEquiv (R := A)

def affineEquivType := ∀ A : CommRingCat.{u}, ModuleCat.{u} A ≌ qcValue A

instance qcFiniteProducts (A : CommRingCat.{u}) : HasFiniteProducts (qcValue A) :=
  ⟨fun _ => hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (affineEquivValue A).inverse⟩

/-- Use the inherited preadditive structure of the full subcategory. -/
instance qcAbelian (A : CommRingCat.{u}) : Abelian (qcValue A) :=
  abelianOfEquivalence (affineEquivValue A).inverse

instance inclusionAdditive (A : CommRingCat.{u}) : (inclusion A).Additive where
  map_add := rfl

instance tildeAdditive (A : CommRingCat.{u}) : (affineEquivValue A).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

instance gammaAdditive (A : CommRingCat.{u}) : (affineEquivValue A).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] HasDerivedCategory.standard

abbrev qcDerivedValue (A : CommRingCat.{u}) := DerivedCategory (qcValue A)

def qcDerivedType := CommRingCat.{u} → Type (u + 1)

def exactAffineEquivType : Prop :=
  ∀ A : CommRingCat.{u},
    PreservesFiniteLimits (affineEquivValue A).functor ∧
    PreservesFiniteColimits (affineEquivValue A).functor ∧
    PreservesFiniteLimits (affineEquivValue A).inverse ∧
    PreservesFiniteColimits (affineEquivValue A).inverse

def tildeExactType : Prop :=
  ∀ A : CommRingCat.{u},
    PreservesFiniteLimits (tilde.functor A) ∧ PreservesFiniteColimits (tilde.functor A)

def tildeSectionsLocalizedType : Prop :=
  ∀ (A : CommRingCat.{u}) (M : ModuleCat.{u} A) (a : A),
    IsLocalizedModule.Away a (tilde.toOpen M (PrimeSpectrum.basicOpen a)).hom

def qcSectionsLocalizedType : Prop :=
  ∀ (A : CommRingCat.{u}) (F : qcValue A) (a : A),
    IsLocalizedModule.Away a
      ((modulesSpecToSheaf.obj F.obj).obj.map (PrimeSpectrum.basicOpen a).leTop.op).hom

def preimageBasicOpenType : Prop :=
  ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B) (a : A),
    (Opens.map (Spec.map φ).base).obj (PrimeSpectrum.basicOpen a) =
      PrimeSpectrum.basicOpen (φ a)

def pushforwardGammaType : Prop :=
  ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B),
    Nonempty (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := A) ≅
      moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars φ.hom)

def pushforwardPreservesQCType : Prop :=
  ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B) (F : qcValue B),
    ((Scheme.Modules.pushforward (Spec.map φ)).obj F.obj).IsQuasicoherent

def pullbackPreservesQCType : Prop :=
  ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B) (F : qcValue A),
    ((Scheme.Modules.pullback (Spec.map φ)).obj F.obj).IsQuasicoherent

def qcPushforwardComparisonType : Prop :=
  ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B) (h : ∀ F : qcValue B,
      ((Scheme.Modules.pushforward (Spec.map φ)).obj F.obj).IsQuasicoherent),
    Nonempty ((affineEquivValue B).functor ⋙
        ObjectProperty.lift (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf)
          (inclusion B ⋙ Scheme.Modules.pushforward (Spec.map φ)) h ≅
      ModuleCat.restrictScalars φ.hom ⋙ (affineEquivValue A).functor)

def qcPullbackComparisonType : Prop :=
  ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B) (h : ∀ F : qcValue A,
      ((Scheme.Modules.pullback (Spec.map φ)).obj F.obj).IsQuasicoherent),
    Nonempty ((affineEquivValue A).functor ⋙
        ObjectProperty.lift (SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf)
          (inclusion A ⋙ Scheme.Modules.pullback (Spec.map φ)) h ≅
      ModuleCat.extendScalars φ.hom ⋙ (affineEquivValue B).functor)

def derivedEquivalenceType : Prop :=
  ∀ A : CommRingCat.{u},
    ∃ e : DerivedCategory (ModuleCat.{u} A) ≌ qcDerivedValue A,
      e.functor = (affineEquivValue A).functor.mapDerivedCategory ∧
      e.inverse = (affineEquivValue A).inverse.mapDerivedCategory ∧
      (affineEquivValue A).functor.mapDerivedCategory.IsTriangulated ∧
      (affineEquivValue A).inverse.mapDerivedCategory.IsTriangulated

def derivedTildeFactorsType : Prop :=
  ∀ A : CommRingCat.{u},
    Nonempty (DerivedCategory.Q ⋙ (affineEquivValue A).functor.mapDerivedCategory ≅
      (affineEquivValue A).functor.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

def derivedGammaFactorsType : Prop :=
  ∀ A : CommRingCat.{u},
    Nonempty (DerivedCategory.Q ⋙ (affineEquivValue A).inverse.mapDerivedCategory ≅
      (affineEquivValue A).inverse.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

end

end Specs.DerivedFormalization.AffineModuleSheaves
