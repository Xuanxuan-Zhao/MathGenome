import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Definitions
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! The closed fiber is the actual quotient N/mN, with its canonical S-action
and S/mS-action. The sequence hypothesis uses the images of arbitrary lifts
in the actual closed-fiber ring S/mS. -/
namespace Specs.AdvCommAlg.CohenMacaulay
universe u v w

abbrev ClosedFiber (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing R] (N : Type w) [AddCommGroup N] [Module S N] :=
  N ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R S) • ⊤ : Submodule S N)

def fiberRegularLiftingType : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (N : Type w) [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.Finite S N] [Nontrivial N] [Module.Flat R N]
    (y : S), y ∈ IsLocalRing.maximalIdeal S →
    IsSMulRegular (ClosedFiber R S N) y →
    IsSMulRegular N y ∧ Module.Flat R (QuotSMulTop y N) ∧
      Nontrivial (QuotSMulTop y N)

def fiberRegularSequenceLiftingType : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (N : Type w) [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.Finite S N] [Nontrivial N] [Module.Flat R N]
    (ys : List S), (∀ y ∈ ys, y ∈ IsLocalRing.maximalIdeal S) →
    RingTheory.Sequence.IsRegular (ClosedFiber R S N)
      (ys.map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R S)))) →
    RingTheory.Sequence.IsRegular N ys ∧
      ∀ j : ℕ, Module.Flat R
        (N ⧸ (Ideal.ofList (ys.take j) • ⊤ : Submodule S N)) ∧
      Nontrivial (N ⧸ (Ideal.ofList (ys.take j) • ⊤ : Submodule S N))
end Specs.AdvCommAlg.CohenMacaulay
