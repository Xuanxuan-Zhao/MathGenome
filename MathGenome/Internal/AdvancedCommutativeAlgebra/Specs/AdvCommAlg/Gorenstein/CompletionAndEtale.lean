import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.FlatLocalMaps
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! GC-08, completion and étale consequences (paper.tex:4626–4650).
The local condition remains finite self-injective dimension. For the completion
we use the proved Noetherianness interface, with no extra hypothesis.
Global Gorensteinness uses all prime localizations, including the empty spectrum.
-/
universe u
namespace AdvCommAlg.Gorenstein.CompletionAndEtaleSpecs

noncomputable def completion_gorensteinType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    letI := CohenMacaulay.Specs.completionNoetherian R
    Specs.LocalGorensteinValue R ↔
      Specs.LocalGorensteinValue (AdicCompletion (IsLocalRing.maximalIdeal R) R)

/-- The hypotheses needed to use the flat-local theorem for completion. -/
noncomputable def completion_applicabilityType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) ∧
    IsLocalHom (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) ∧
    IsField ((AdicCompletion (IsLocalRing.maximalIdeal R) R) ⧸
      (IsLocalRing.maximalIdeal R).map
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)))

noncomputable def etale_stalk_gorensteinType : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B],
    Specs.AdvCommAlg.Etale.etaleValue A B → ∀ q : PrimeSpectrum B,
    Specs.LocalGorensteinValue (Localization.AtPrime q.asIdeal) ↔
      Specs.LocalGorensteinValue (Localization.AtPrime (q.asIdeal.under A))

noncomputable def etale_ascentType : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B],
    Specs.AdvCommAlg.Etale.etaleValue A B →
    Specs.GorensteinRingValue A → Specs.GorensteinRingValue B

noncomputable def etale_descentType : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B],
    Specs.AdvCommAlg.Etale.etaleValue A B → Module.FaithfullyFlat A B →
    Specs.GorensteinRingValue B → Specs.GorensteinRingValue A

end AdvCommAlg.Gorenstein.CompletionAndEtaleSpecs
