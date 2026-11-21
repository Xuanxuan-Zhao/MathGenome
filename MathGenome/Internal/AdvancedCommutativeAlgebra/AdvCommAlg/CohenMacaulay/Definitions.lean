import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExtCharacterization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions

/-! CM-01: local and global Cohen–Macaulay conditions.
`dimension` retains Mathlib's support dimension, including bottom for the
zero module. Local CM and maximal CM explicitly admit the zero module.
The global module condition is imposed only at primes in its support.
-/
universe u
namespace AdvCommAlg.CohenMacaulay

noncomputable def dimension (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] : WithBot ℕ∞ :=
  Module.supportDim R M

noncomputable def LocalCohenMacaulay (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : Prop :=
  Subsingleton M ∨
    (IsLocalRing.depth (ModuleCat.of R M) : WithBot ℕ∞) = dimension R M

noncomputable def MaximalCohenMacaulay (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : Prop :=
  Subsingleton M ∨
    (IsLocalRing.depth (ModuleCat.of R M) : WithBot ℕ∞) = ringKrullDim R

noncomputable def IsCohenMacaulay (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : Prop :=
  ∀ p : PrimeSpectrum R, p ∈ Module.support R M →
    LocalCohenMacaulay (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M)

noncomputable def CohenMacaulayAt (R : Type u) [CommRing R] [IsNoetherianRing R] (p : PrimeSpectrum R) : Prop :=
  LocalCohenMacaulay (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)

noncomputable def CohenMacaulayRing (R : Type u) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ p : PrimeSpectrum R, CohenMacaulayAt R p

theorem dimension_eq_quotient_annihilator (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    dimension R M = ringKrullDim (R ⧸ Module.annihilator R M) :=
  Module.supportDim_eq_ringKrullDim_quotient_annihilator R M

theorem localCohenMacaulay_iff_depth_eq (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    LocalCohenMacaulay R M ↔
      (IsLocalRing.depth (ModuleCat.of R M) : WithBot ℕ∞) = dimension R M := by
  simp only [LocalCohenMacaulay, (not_subsingleton M), false_or]

theorem maximalCohenMacaulay_iff_depth_eq (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    MaximalCohenMacaulay R M ↔
      (IsLocalRing.depth (ModuleCat.of R M) : WithBot ℕ∞) = ringKrullDim R := by
  simp only [MaximalCohenMacaulay, (not_subsingleton M), false_or]

theorem localCohenMacaulay_iff_sourceDepth (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    LocalCohenMacaulay R M ↔
      (Depth.depth R M : WithBot ℕ∞) = dimension R M := by
  rw [localCohenMacaulay_iff_depth_eq, Depth.depth_eq_libraryDepth (ModuleCat.of R M)]

theorem maximalCohenMacaulay_iff_sourceDepth (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    MaximalCohenMacaulay R M ↔
      (Depth.depth R M : WithBot ℕ∞) = ringKrullDim R := by
  rw [maximalCohenMacaulay_iff_depth_eq, Depth.depth_eq_libraryDepth (ModuleCat.of R M)]

theorem localCohenMacaulay_of_subsingleton (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Subsingleton M] :
    LocalCohenMacaulay R M :=
  Or.inl inferInstance

theorem maximalCohenMacaulay_of_subsingleton (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Subsingleton M] :
    MaximalCohenMacaulay R M :=
  Or.inl inferInstance

theorem cohenMacaulay_of_subsingleton (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Subsingleton M] :
    IsCohenMacaulay R M := by
  intro p hp
  rw [Module.support_eq_empty_iff.mpr (inferInstance : Subsingleton M)] at hp
  exact False.elim hp

theorem localCohenMacaulay_self_iff (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    LocalCohenMacaulay R R ↔
      (IsLocalRing.depth (ModuleCat.of R R) : WithBot ℕ∞) = ringKrullDim R := by
  rw [localCohenMacaulay_iff_depth_eq]
  exact Iff.of_eq (congrArg _ (Module.supportDim_self_eq_ringKrullDim R))

theorem cohenMacaulayAt_iff_depth_eq (R : Type u) [CommRing R] [IsNoetherianRing R] (p : PrimeSpectrum R) :
    CohenMacaulayAt R p ↔
      (IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal)) : WithBot ℕ∞) =
          ringKrullDim (Localization.AtPrime p.asIdeal) :=
  localCohenMacaulay_self_iff (Localization.AtPrime p.asIdeal)

end AdvCommAlg.CohenMacaulay
