import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.Depth.Basic
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Localization.Finiteness

/-! Independent specifications for CM-01, paper.tex:3235–3250.
The zero module is included by a separate disjunct, never by equating its
infinite depth with the dimension of its empty support. All rings and modules
may be placed in a common universe. Local numerical equalities compare the
canonical ℕ∞ depth, explicitly coerced to WithBot ℕ∞, with support dimension.
-/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def dimensionType := ∀ (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M], WithBot ℕ∞

noncomputable def dimensionValue : dimensionType.{u} :=
  fun R _ M _ _ => Module.supportDim R M

def LocalCohenMacaulayType := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M], Prop

noncomputable def LocalCohenMacaulayValue : LocalCohenMacaulayType.{u} :=
  fun R _ _ _ M _ _ _ => Subsingleton M ∨
    (IsLocalRing.depth (ModuleCat.of R M) : WithBot ℕ∞) = dimensionValue R M

def MaximalCohenMacaulayType := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M], Prop

noncomputable def MaximalCohenMacaulayValue : MaximalCohenMacaulayType.{u} :=
  fun R _ _ _ M _ _ _ => Subsingleton M ∨
    (IsLocalRing.depth (ModuleCat.of R M) : WithBot ℕ∞) = ringKrullDim R

def IsCohenMacaulayType := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M], Prop

noncomputable def IsCohenMacaulayValue : IsCohenMacaulayType.{u} :=
  fun R _ _ M _ _ _ => ∀ p : PrimeSpectrum R, p ∈ Module.support R M →
    LocalCohenMacaulayValue (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M)

def CohenMacaulayAtType := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (p : PrimeSpectrum R), Prop

noncomputable def CohenMacaulayAtValue : CohenMacaulayAtType.{u} :=
  fun R _ _ p => LocalCohenMacaulayValue (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)

def CohenMacaulayRingType := ∀ (R : Type u) [CommRing R] [IsNoetherianRing R], Prop

noncomputable def CohenMacaulayRingValue : CohenMacaulayRingType.{u} :=
  fun R _ _ => ∀ p : PrimeSpectrum R, CohenMacaulayAtValue R p

def dimension_eq_quotient_annihilatorType : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M],
    dimensionValue R M = ringKrullDim (R ⧸ Module.annihilator R M)

def localCohenMacaulay_iff_depth_eqType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M],
    LocalCohenMacaulayValue R M ↔
      (IsLocalRing.depth (ModuleCat.of R M) : WithBot ℕ∞) = dimensionValue R M

def maximalCohenMacaulay_iff_depth_eqType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M],
    MaximalCohenMacaulayValue R M ↔
      (IsLocalRing.depth (ModuleCat.of R M) : WithBot ℕ∞) = ringKrullDim R

def localCohenMacaulay_iff_sourceDepthType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M],
    LocalCohenMacaulayValue R M ↔
      (AdvCommAlg.Depth.Specs.depthValue R M : WithBot ℕ∞) = dimensionValue R M

def maximalCohenMacaulay_iff_sourceDepthType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M],
    MaximalCohenMacaulayValue R M ↔
      (AdvCommAlg.Depth.Specs.depthValue R M : WithBot ℕ∞) = ringKrullDim R

def localCohenMacaulay_of_subsingletonType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Subsingleton M],
    LocalCohenMacaulayValue R M

def maximalCohenMacaulay_of_subsingletonType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Subsingleton M],
    MaximalCohenMacaulayValue R M

def cohenMacaulay_of_subsingletonType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Subsingleton M],
    IsCohenMacaulayValue R M

def localCohenMacaulay_self_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    LocalCohenMacaulayValue R R ↔
      (IsLocalRing.depth (ModuleCat.of R R) : WithBot ℕ∞) = ringKrullDim R

def cohenMacaulayAt_iff_depth_eqType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (p : PrimeSpectrum R),
    CohenMacaulayAtValue R p ↔
      (IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal)) : WithBot ℕ∞) =
          ringKrullDim (Localization.AtPrime p.asIdeal)

end AdvCommAlg.CohenMacaulay.Specs
