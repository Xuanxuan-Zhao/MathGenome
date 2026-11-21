import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.Definitions

/-! Independent specifications for SN-03, paper.tex:4081–4102.
The chapter assumes commutative Noetherian rings, and allows the zero ring.
The Serre conditions are the unchanged SN-01 and CM-11a predicates.
-/
universe u
namespace AdvCommAlg.Normality.Specs

def isField_localization_minimalPrimeType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A]
    (p : PrimeSpectrum A), p.asIdeal ∈ minimalPrimes A →
      IsField (Localization.AtPrime p.asIdeal)

def regularInCodimension_zero_of_isReducedType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A],
    RegularInCodimensionValue A 0

def ringSerreCondition_one_of_isReducedType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A],
    CohenMacaulay.Specs.RingSerreConditionValue A 1

def depth_pos_localization_of_isReducedType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A]
    (p : PrimeSpectrum A), 0 < ringKrullDim (Localization.AtPrime p.asIdeal) →
      0 < IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal))

def isReduced_iff_regularInCodimension_zero_and_serreCondition_oneType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A],
    IsReduced A ↔ RegularInCodimensionValue A 0 ∧
      CohenMacaulay.Specs.RingSerreConditionValue A 1

end AdvCommAlg.Normality.Specs
