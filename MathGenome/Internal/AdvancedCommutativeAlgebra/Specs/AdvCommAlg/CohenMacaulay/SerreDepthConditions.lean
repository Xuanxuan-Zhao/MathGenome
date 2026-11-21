import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-! Independent CM-11a specifications (paper.tex:3600–3633).
The same all-prime module predicate is used for the ring specialization and
for the conditions of chapter 8. Support dimensions use `WithBot ℕ∞`;
only nonzero localizations are tested. -/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def SerreConditionType := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M], ℕ → Prop

noncomputable def SerreConditionValue : SerreConditionType.{u} :=
  fun R _ _ M _ _ _ k => ∀ p : PrimeSpectrum R, p ∈ Module.support R M →
    min (k : WithBot ℕ∞)
      (Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)) ≤
    (IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M)) : WithBot ℕ∞)

def RingSerreConditionType := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R], ℕ → Prop

noncomputable def RingSerreConditionValue : RingSerreConditionType.{u} :=
  fun R _ _ k => SerreConditionValue R R k

def NoEmbeddedAssociatedPrimesType := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M], Prop

noncomputable def NoEmbeddedAssociatedPrimesValue : NoEmbeddedAssociatedPrimesType.{u} :=
  fun R _ _ M _ _ _ => ∀ p : PrimeSpectrum R, p.asIdeal ∈ associatedPrimes R M →
    Minimal (fun q => q ∈ Module.support R M) p

def serreCondition_of_subsingletonType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Subsingleton M]
    (k : ℕ), SerreConditionValue R M k

def cohenMacaulay_iff_forall_serreConditionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    IsCohenMacaulayValue R M ↔ ∀ k : ℕ, SerreConditionValue R M k

def serreCondition_one_iff_noEmbeddedAssociatedPrimesType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    SerreConditionValue R M 1 ↔ NoEmbeddedAssociatedPrimesValue R M

def serreCondition_one_iff_associatedPrimes_eq_minimalPrimesType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    SerreConditionValue R M 1 ↔
      associatedPrimes R M = (Module.annihilator R M).minimalPrimes

end AdvCommAlg.CohenMacaulay.Specs
