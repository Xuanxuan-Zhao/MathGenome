import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions

/-! Independent statements for the localization assertions of FL-10,
paper.tex:683–710. All rings may be zero; the submonoids are arbitrary.
The source-localization statements construct the localized-base action from
the stated unit hypothesis, so no additional algebra structure is assumed.
-/
namespace Specs.AdvCommAlg.FormalLifting.Localization

universe u v w

/-- Any localization, including one inverting zero, is formally étale. -/
def localizationEtale : Prop :=
  ∀ (B : Type u) (L : Type v) [CommRing B] [CommRing L]
    [Algebra B L] (S : Submonoid B) [IsLocalization S L],
    formallyEtaleValue B L

/-- Target localization preserves formal smoothness. -/
def smoothTargetLocalization : Prop :=
  ∀ (A : Type u) (B : Type v) (L : Type w)
    [CommRing A] [CommRing B] [CommRing L]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    (S : Submonoid B) [IsLocalization S L],
    formallySmoothValue A B → formallySmoothValue A L

/-- Target localization preserves formal unramifiedness. -/
def unramifiedTargetLocalization : Prop :=
  ∀ (A : Type u) (B : Type v) (L : Type w)
    [CommRing A] [CommRing B] [CommRing L]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    (S : Submonoid B) [IsLocalization S L],
    formallyUnramifiedValue A B → formallyUnramifiedValue A L

/-- Target localization preserves formal étaleness. -/
def etaleTargetLocalization : Prop :=
  ∀ (A : Type u) (B : Type v) (L : Type w)
    [CommRing A] [CommRing B] [CommRing L]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    (S : Submonoid B) [IsLocalization S L],
    formallyEtaleValue A B → formallyEtaleValue A L

/-- Localizing the base at elements mapping to units preserves and reflects
formal smoothness. -/
def smoothSourceLocalizationIff : Prop :=
  ∀ (A : Type u) (B : Type v) (L : Type w)
    [CommRing A] [CommRing B] [CommRing L] [Algebra A B] [Algebra A L]
    (U : Submonoid A) [IsLocalization U L]
    (hU : ∀ s : U, IsUnit (algebraMap A B s)),
    letI : Algebra L B := (IsLocalization.lift (S := L) hU).toAlgebra
    formallySmoothValue A B ↔ formallySmoothValue L B

/-- Localizing the base at elements mapping to units preserves and reflects
formal unramifiedness. -/
def unramifiedSourceLocalizationIff : Prop :=
  ∀ (A : Type u) (B : Type v) (L : Type w)
    [CommRing A] [CommRing B] [CommRing L] [Algebra A B] [Algebra A L]
    (U : Submonoid A) [IsLocalization U L]
    (hU : ∀ s : U, IsUnit (algebraMap A B s)),
    letI : Algebra L B := (IsLocalization.lift (S := L) hU).toAlgebra
    formallyUnramifiedValue A B ↔ formallyUnramifiedValue L B

/-- Localizing the base at elements mapping to units preserves and reflects
formal étaleness. -/
def etaleSourceLocalizationIff : Prop :=
  ∀ (A : Type u) (B : Type v) (L : Type w)
    [CommRing A] [CommRing B] [CommRing L] [Algebra A B] [Algebra A L]
    (U : Submonoid A) [IsLocalization U L]
    (hU : ∀ s : U, IsUnit (algebraMap A B s)),
    letI : Algebra L B := (IsLocalization.lift (S := L) hU).toAlgebra
    formallyEtaleValue A B ↔ formallyEtaleValue L B

end Specs.AdvCommAlg.FormalLifting.Localization
