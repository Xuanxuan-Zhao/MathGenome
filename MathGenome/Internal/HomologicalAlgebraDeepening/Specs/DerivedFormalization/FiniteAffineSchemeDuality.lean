import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.AffineModuleSheaves
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedScalarExtension
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedCoinduction
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

namespace Specs.DerivedFormalization.FiniteAffineSchemeDuality

open CategoryTheory AlgebraicGeometry
open AffineModuleSheaves (qcValue qcDerivedValue inclusion affineEquivValue)
open Cochains (compValue derivedValue qValue)
open CochainModels (isKInjectiveValue)
open CochainRingTransport (adjunctionCompatible)
open DerivedCoinduction (Coinduction evaluation)
open DerivedRestriction (derivedRestrictScalarsValue)
open DerivedScalarExtension (NativeExtension)

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)

abbrev CochainsQC (A : CommRingCat.{u}) := CochainComplex (qcValue A) ℤ

abbrev affine (A : CommRingCat.{u}) := (affineEquivValue A).functor.mapDerivedCategory

abbrev pushforward (h : ∀ F : qcValue B,
    ((Scheme.Modules.pushforward (Spec.map φ)).obj F.obj).IsQuasicoherent) :
    qcValue B ⥤ qcValue A :=
  ObjectProperty.lift _ (inclusion B ⋙ Scheme.Modules.pushforward (Spec.map φ)) h

/-- The ordinary sheaf functors restrict to the full quasi-coherent subcategories,
and this direct image is exact. -/
structure Ordinary where
  pushforwardQC : ∀ F : qcValue B,
    ((Scheme.Modules.pushforward (Spec.map φ)).obj F.obj).IsQuasicoherent
  pullbackQC : ∀ F : qcValue A,
    ((Scheme.Modules.pullback (Spec.map φ)).obj F.obj).IsQuasicoherent
  additive : (pushforward φ pushforwardQC).Additive
  finiteLimits : Limits.PreservesFiniteLimits (pushforward φ pushforwardQC)
  finiteColimits : Limits.PreservesFiniteColimits (pushforward φ pushforwardQC)

variable (O : Ordinary φ)

abbrev pullback : qcValue A ⥤ qcValue B :=
  ObjectProperty.lift _ (inclusion A ⋙ Scheme.Modules.pullback (Spec.map φ)) O.pullbackQC

/-- The ordinary adjunction restricted from the scheme pullback and direct image. -/
def sheafAdjunction : pullback φ O ⊣ pushforward φ O.pushforwardQC :=
  (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).restrictFullyFaithful
    (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).fullyFaithfulι
    (SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

theorem pullbackAdditive : (pullback φ O).Additive := by
  have : (pullback φ O).IsLeftAdjoint := (sheafAdjunction φ O).isLeftAdjoint
  exact rightExactFunctor_le_additiveFunctor _ _ _ ⟨inferInstance⟩

abbrev pullbackComplex : CochainsQC A ⥤ CochainsQC B :=
  letI := pullbackAdditive φ O
  (pullback φ O).mapHomologicalComplex (.up ℤ)

abbrev pushforwardComplex : CochainsQC B ⥤ CochainsQC A :=
  letI := O.additive
  (pushforward φ O.pushforwardQC).mapHomologicalComplex (.up ℤ)

abbrev cochainAdjunction : pullbackComplex φ O ⊣ pushforwardComplex φ O :=
  letI := pullbackAdditive φ O
  letI := O.additive
  ScalarExtensionTransport.cochainAdjunction (sheafAdjunction φ O)

/-- Exact direct image is obtained by applying the ordinary direct image termwise. -/
abbrev directImage : qcDerivedValue B ⥤ qcDerivedValue A :=
  letI := O.additive
  letI := O.finiteLimits
  letI := O.finiteColimits
  (pushforward φ O.pushforwardQC).mapDerivedCategory

def directImageFactors :
    (DerivedCategory.Q : CochainsQC B ⥤ qcDerivedValue B) ⋙ directImage φ O ≅
      pushforwardComplex φ O ⋙ (DerivedCategory.Q : CochainsQC A ⥤ qcDerivedValue A) :=
  letI := O.additive
  letI := O.finiteLimits
  letI := O.finiteColimits
  Functor.mapDerivedCategoryFactors (pushforward φ O.pushforwardQC)

/-- The comparison map for derived pullback is the mate of the exact direct-image
factorization for the ordinary and derived adjunctions. -/
def pullbackComparison {L : qcDerivedValue A ⥤ qcDerivedValue B}
    (adj : L ⊣ directImage φ O) :
    (DerivedCategory.Q : CochainsQC A ⥤ qcDerivedValue A) ⋙ L ⟶
      pullbackComplex φ O ⋙ (DerivedCategory.Q : CochainsQC B ⥤ qcDerivedValue B) :=
  (mateEquiv (cochainAdjunction φ O) adj).symm (directImageFactors φ O).inv

/-- The ordinary direct-image comparison is induced by the comparison on global sections. -/
def ordinaryDirectImageComparison :
    (affineEquivValue B).functor ⋙ pushforward φ O.pushforwardQC ≅
      ModuleCat.restrictScalars φ.hom ⋙ (affineEquivValue A).functor := by
  let E := affineEquivValue A
  let H := affineEquivValue B
  let P := pushforward φ O.pushforwardQC
  let R := ModuleCat.restrictScalars φ.hom
  let γ : P ⋙ E.inverse ≅ H.inverse ⋙ R :=
    Functor.isoWhiskerLeft (inclusion B)
      (Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
        (TopCat.Sheaf.forget _ _ ⋙ (CategoryTheory.evaluation _ _).obj (Opposite.op ⊤)))
  exact (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ E.counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator H.functor P E.inverse ≪≫ Functor.isoWhiskerLeft H.functor γ ≪≫
        (Functor.associator H.functor H.inverse R).symm ≪≫
        Functor.isoWhiskerRight H.unitIso.symm R ≪≫ Functor.leftUnitor R)
      E.functor

/-- Localize the ordinary comparison at quasi-isomorphisms. -/
def directImageComparison :
    affine B ⋙ directImage φ O ≅ derivedRestrictScalarsValue.{u} φ.hom ⋙ affine A :=
  letI := O.additive
  letI := O.finiteLimits
  letI := O.finiteColimits
  Functor.mapDerivedCategoryCompIso (affineEquivValue B).functor
      (pushforward φ O.pushforwardQC) ≪≫
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (.up ℤ)) _ _ _ _
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex (ordinaryDirectImageComparison φ O) (.up ℤ))
        DerivedCategory.Q) ≪≫
    (Functor.mapDerivedCategoryCompIso (ModuleCat.restrictScalars φ.hom)
      (affineEquivValue A).functor).symm

abbrev ScalarExtension := NativeExtension (RingEquiv.refl A) (RingEquiv.refl B) φ.hom

/-- The two geometric adjunctions and their comparisons in affine module coordinates. -/
structure Comparison (M : ScalarExtension φ) (N : Coinduction.{u} φ.hom) where
  ordinary : Ordinary φ
  pullback : qcDerivedValue A ⥤ qcDerivedValue B
  exceptionalPullback : qcDerivedValue A ⥤ qcDerivedValue B
  pullbackAdjunction : pullback ⊣ directImage φ ordinary
  exceptionalAdjunction : directImage φ ordinary ⊣ exceptionalPullback
  isDerivedPullback : pullback.IsLeftDerivedFunctor
    (pullbackComparison φ ordinary pullbackAdjunction) (HomologicalComplex.quasiIso (qcValue A) (.up ℤ))
  pullbackIso : affine A ⋙ pullback ≅ M.derived ⋙ affine B
  exceptionalIso : N.functor ⋙ affine B ≅ affine A ⋙ exceptionalPullback
  pullbackMate : adjunctionCompatible M.adj pullbackAdjunction
    pullbackIso.hom (directImageComparison φ ordinary).inv
  exceptionalMate : adjunctionCompatible N.adjunction exceptionalAdjunction
    (directImageComparison φ ordinary).hom exceptionalIso.hom
  trace_on_model : ∀ (Y : derivedValue.{u} A) (I : compValue.{u} A)
    (i : Y ≅ (qValue A).obj I) (hI : isKInjectiveValue I),
    (directImage φ ordinary).map ((affine B).map (N.modelIso φ.hom I i hI).inv ≫
      exceptionalIso.hom.app Y) ≫ exceptionalAdjunction.counit.app ((affine A).obj Y) =
      (directImageComparison φ ordinary).hom.app
        ((qValue B).obj ((CoinductionComplex.coinduceValue.{u} φ.hom).obj I)) ≫
        (affine A).map (evaluation.{u} φ.hom I ≫ i.inv)

def comparisonType : Prop :=
  ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B) [IsFinite (Spec.map φ)]
    (M : ScalarExtension φ) (N : Coinduction.{u} φ.hom), Nonempty (Comparison φ M N)

def finiteAffineDualityType : Prop :=
  ∀ {A B : CommRingCat.{u}} (f : Spec B ⟶ Spec A) [IsFinite f],
    let φ := Spec.preimage f
    Spec.map φ = f ∧
      ∃ (M : ScalarExtension φ) (N : Coinduction.{u} φ.hom), Nonempty (Comparison φ M N)

end

end Specs.DerivedFormalization.FiniteAffineSchemeDuality
