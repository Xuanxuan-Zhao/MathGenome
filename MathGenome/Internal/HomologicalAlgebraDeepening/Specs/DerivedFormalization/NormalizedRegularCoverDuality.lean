import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedCoinduction
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomAdjunction
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.DualizingComplexHomothety

/-! Normalized duality for complete local rings, using the cohomological shift. -/

namespace Specs.DerivedFormalization.NormalizedRegularCoverDuality

open CategoryTheory Opposite
open IsLocalRing (ResidueField maximalIdeal residue)
open Cochains (derivedValue qValue stalkValue derivedStalkValue derivedCohomologyValue)
open DerivedCoinduction (Coinduction)
open DerivedHomModels (Models rHomValue)
open DerivedHomAdjunction (Presentation homComparison)
open DerivedRestriction (derivedRestrictScalarsValue)
open CoinductionComplex (coinduceValue)
open _root_.Specs.CommutativeAlgebraNotes.RegularCoverDualizingModel
  (ShiftedRingResolution shiftedRing dualizingObject)

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- Cohen's regular cover, with the identification of the residue fields. -/
def RegularCoverExists : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R],
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S)
      (d : ℕ), ringKrullDim S = (d : WithBot ℕ∞) ∧
      IsAdicComplete (maximalIdeal S) S ∧
      ∃ f : S →+* R, IsLocalHom f ∧ Function.Surjective f ∧
        ∃ e : ResidueField S ≃+* ResidueField R,
          (residue R).comp f = e.toRingHom.comp (residue S)

/-- The local quotient induces the residue-field identification. -/
def ResidueIdentification : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsLocalRing S] [IsLocalRing R]
    (f : S →+* R) [IsLocalHom f], Function.Surjective f →
    ∃ e : ResidueField S ≃+* ResidueField R,
      e.toRingHom = ResidueField.map f ∧
      (residue R).comp f = e.toRingHom.comp (residue S)

section Cover

variable {S R : Type u} [CommRing S] [CommRing R] (f : S →+* R)

/-- The canonical localized object is obtained by applying the right adjoint to
restriction to the shifted regular module. -/
def normalizedObjectType :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] (f : S →+* R),
    Coinduction.{u} f → ℕ → derivedValue.{u} R

def normalizedObjectValue : normalizedObjectType.{u} :=
  fun {S} {_} [_] [_] _ G d => G.functor.obj ((qValue S).obj (shiftedRing S d))

/-- Compare the actual coinduced complex with the localized object using
the transpose of evaluation at one and the resolution augmentation. -/
def modelIso (G : Coinduction.{u} f) {d : ℕ}
    (J : ShiftedRingResolution S d) (hJ : J.complex.IsKInjective) :
    normalizedObjectValue f G d ≅ dualizingObject f J :=
  letI := J.quasiIso
  G.modelIso f J.complex (asIso ((qValue S).map J.ι)) hJ

/-- The homothety in derived Hom is induced by the degree-zero cocycle given
by scalar multiplication on the coinduced model. -/
def homothety (G : Coinduction.{u} f) (H : Models.{u,u} R) {d : ℕ}
    (J : ShiftedRingResolution S d) (hJ : J.complex.IsKInjective) :
    (qValue R).obj ((stalkValue R).obj (ModuleCat.of R R)) ⟶
      (rHomValue H).obj (op (normalizedObjectValue f G d), normalizedObjectValue f G d) :=
  let P : Presentation (normalizedObjectValue f G d) :=
    ⟨(coinduceValue.{u} f).obj J.complex, (modelIso f G J hJ).symm⟩
  _root_.Specs.CommutativeAlgebraNotes.DualizingComplexHomothety.derivedHomothety f J ≫
    homComparison H P P

end Cover

/-- For every complete regular local cover, the canonical object has finite
cohomology and is normalized. Its restriction is the internal derived Hom
from the restricted regular target module. Every bounded injective resolution
computes it with the original target action. -/
def NormalizedDualizing : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsRegularLocalRing S]
    [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal S) S]
    [IsAdicComplete (maximalIdeal R) R]
    (f : S →+* R) [IsLocalHom f], Function.Surjective f →
    ∀ (d : ℕ), ringKrullDim S = (d : WithBot ℕ∞) →
    ∀ (G : Coinduction.{u} f) (HS : Models.{u,u} S) (HR : Models.{u,u} R),
    let D := normalizedObjectValue f G d
    let k := (derivedStalkValue R).obj (ModuleCat.of R (ResidueField R))
    let RS := (derivedRestrictScalarsValue.{u} f).obj
      ((derivedStalkValue R).obj (ModuleCat.of R R))
    Nonempty (ShiftedRingResolution S d) ∧
      Nonempty ((derivedRestrictScalarsValue.{u} f).obj D ≅
        (rHomValue HS).obj (op RS, (qValue S).obj (shiftedRing S d))) ∧
      (∀ q : ℤ, Module.Finite R ((derivedCohomologyValue R q).obj D)) ∧
      (∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q →
        Limits.IsZero ((derivedCohomologyValue R q).obj D)) ∧
      Nonempty ((rHomValue HR).obj (op k, D) ≅ k) ∧
      ∀ J : ShiftedRingResolution S d,
        let C := (coinduceValue.{u} f).obj J.complex
        Nonempty (D ≅ dualizingObject f J) ∧
        (∃ hJ : J.complex.IsKInjective, IsIso (homothety f G HR J hJ)) ∧
        (∀ q : ℤ, Injective (C.X q)) ∧ C.IsStrictlyGE J.lower ∧ C.IsStrictlyLE J.upper ∧
        C.IsKInjective

end

end Specs.DerivedFormalization.NormalizedRegularCoverDuality
