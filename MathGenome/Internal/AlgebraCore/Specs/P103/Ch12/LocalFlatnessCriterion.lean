import MathGenome.Internal.AlgebraCore.Specs.P103.Ch12.FiniteLengthTorVanishing
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.VanishingAndFlatness
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! The relative local criterion, paper.tex 3266–3315. The algebra structure
encodes an arbitrary unital local map of commutative Noetherian local rings.
The R-action on M is restriction of its S-action. Only finiteness over S is
assumed. The equivalence holds for every ordinary projective residue resolution. -/
namespace P103.Specs.Ch12.LocalFlatnessCriterion
open P103.BalancedTensor P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
universe u v w

def local_flatness_criterionType : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (M : Type w) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] [Module.Finite S M],
    letI := commRightModule R (R ⧸ IsLocalRing.maximalIdeal R)
    ∀ (Pk : LeftResolution Rᵐᵒᵖ (R ⧸ IsLocalRing.maximalIdeal R)),
      Pk.IsProjective → (Module.Flat R M ↔ Subsingleton (TorWith Pk M 1))

end P103.Specs.Ch12.LocalFlatnessCriterion
