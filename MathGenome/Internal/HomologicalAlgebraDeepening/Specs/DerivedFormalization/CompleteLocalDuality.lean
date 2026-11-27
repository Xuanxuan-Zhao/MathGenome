import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.NormalizedRegularCoverDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompleteLocalDuality

/-! Complete local duality for the normalized object coming from a regular local cover. -/

namespace Specs.DerivedFormalization.CompleteLocalDuality

open CategoryTheory Opposite CochainComplex.HomComplex
open IsLocalRing (maximalIdeal)
open Cochains (compValue derivedValue stalkValue derivedStalkValue qValue derivedCohomologyValue)
open CoinductionComplex (coinduceValue evaluationValue restrictedHomValue)
open DerivedCoinduction (Coinduction)
open DerivedRestriction (restrictScalarsComplexValue derivedRestrictScalarsValue)
open DerivedHomModels (Models rHomValue)
open DerivedHomAdjunction (Presentation homComparison)
open NormalizedRegularCoverDuality (normalizedObjectValue modelIso)
open _root_.Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel
  (ShiftedRingResolution shiftedRing)
open _root_.Specs.CommutativeAlgebraNotes.CompleteLocalDuality
  (finiteModules homFromModule)
open _root_.Specs.CommutativeAlgebraNotes.IdealTorsion (localCohomology)
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs
  (residueFieldEnvelopeValue matlisDualValue)

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {S R : Type u} [CommRing S] [CommRing R]

/-- Compute signed Hom into an (S)-complex from a restricted module in degree zero.
The terms carry the (R)-action by precomposition, and maps are induced by
precomposition with the map of stalk complexes. -/
structure RestrictedHomModel (f : S →+* R) (I : compValue.{u} S) where
  functor : (ModuleCat.{u} R)ᵒᵖ ⥤ compValue.{u} R
  obj_eq (M : ModuleCat.{u} R) :
    functor.obj (op M) = restrictedHomValue.{u} f ((stalkValue R).obj M) I
  map_apply {M M' : ModuleCat.{u} R} (a : M' ⟶ M)
      (n i j : ℤ) (h : i + n = j)
      (z : (restrictedHomValue.{u} f ((stalkValue R).obj M) I).X n)
      (x : ((stalkValue R).obj M').X i) :
    (show Cochain ((restrictScalarsComplexValue.{u} f).obj ((stalkValue R).obj M')) I n from
      (eqToHom (obj_eq M).symm ≫ functor.map a.op ≫ eqToHom (obj_eq M')).f n z).v i j h x =
      (show Cochain ((restrictScalarsComplexValue.{u} f).obj ((stalkValue R).obj M)) I n from
        z).v i j h (((stalkValue R).map a).f i x)

/-- Derived Hom from a module in degree zero, with the contravariant map on
that argument and the target held fixed. -/
def derivedHomFromModule (H : Models.{u,u} R) (D : derivedValue.{u} R) :
    (ModuleCat.{u} R)ᵒᵖ ⥤ derivedValue.{u} R :=
  ((derivedStalkValue R).op.prod' ((Functor.const _).obj D)) ⋙ rHomValue H

/-- After forgetting the (R)-action, the right side of the comparison is
the ordinary derived Hom over (S) on the restricted module. -/
def derivedHomFromRestrictedModule (f : S →+* R) (H : Models.{u,u} S)
    (Y : derivedValue.{u} S) : (ModuleCat.{u} R)ᵒᵖ ⥤ derivedValue.{u} S :=
  ((derivedStalkValue R ⋙ derivedRestrictScalarsValue.{u} f).op.prod'
    ((Functor.const _).obj Y)) ⋙ rHomValue H

/-- The regular cover and normalization are those of U19a. For every bounded
injective resolution of the shifted regular module, the comparison computes
both derived Hom functors with the indicated action. The Matlis comparison
is natural on the full subcategory of finite modules, in all integer degrees. -/
def CompleteLocalDualityType : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsRegularLocalRing S]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal S) S] [IsAdicComplete (maximalIdeal R) R]
    (f : S →+* R) [IsLocalHom f], Function.Surjective f →
    ∀ (d : ℕ), ringKrullDim S = (d : WithBot ℕ∞) →
    ∀ (G : Coinduction.{u} f) (HS : Models.{u,u} S) (HR : Models.{u,u} R)
      (J : ShiftedRingResolution S d) (E : residueFieldEnvelopeValue R),
    let Y := (qValue S).obj (shiftedRing S d)
    let D := normalizedObjectValue f G d
    let C := (coinduceValue.{u} f).obj J.complex
    let L := derivedRestrictScalarsValue.{u} f
    let H := derivedHomFromModule HR D
    ∃ (hJ : J.complex.IsKInjective) (F : RestrictedHomModel f J.complex)
      (a : homFromModule C ≅ F.functor) (e : H ≅ F.functor ⋙ qValue R),
      (∀ (M : ModuleCat.{u} R) (n i j : ℤ) (h : i + n = j)
          (z : Cochain ((stalkValue R).obj M) C n) (x : ((stalkValue R).obj M).X i),
        (show Cochain ((restrictScalarsComplexValue.{u} f).obj ((stalkValue R).obj M))
          J.complex n from
          ((a.hom.app (op M) ≫ eqToHom (F.obj_eq M)).f n z)).v i j h x =
          ModuleCat.CoextendScalars.equiv f (J.complex.X j) (z.v i j h x) (1 : R)) ∧
      (∀ M : ModuleCat.{u} R,
        e.inv.app (op M) = (qValue R).map (a.inv.app (op M)) ≫
          homComparison HR
            (⟨(stalkValue R).obj M, Iso.refl _⟩ : Presentation ((derivedStalkValue R).obj M))
            (⟨C, (modelIso f G J hJ).symm⟩ : Presentation D)) ∧
      Nonempty ((F.functor ⋙ qValue R) ⋙ L ≅ derivedHomFromRestrictedModule f HS Y) ∧
      (∀ q : ℤ, Nonempty
        ((finiteModules R).ι.op ⋙ H ⋙ derivedCohomologyValue R (-q) ≅
          (finiteModules R).ι.op ⋙ (localCohomology.{u} (maximalIdeal R) q).op ⋙
            matlisDualValue E)) ∧
      (L.map (modelIso f G J hJ).inv ≫ G.adjunction.counit.app Y =
        DerivedCoinduction.evaluation.{u} f J.complex ≫
          (letI := J.quasiIso; (asIso ((qValue S).map J.ι)).inv)) ∧
      (∀ (n : ℤ) (z : C.X n),
        (evaluationValue.{u} f J.complex).f n z =
          ModuleCat.CoextendScalars.equiv f (J.complex.X n) z (1 : R))

end

end Specs.DerivedFormalization.CompleteLocalDuality
