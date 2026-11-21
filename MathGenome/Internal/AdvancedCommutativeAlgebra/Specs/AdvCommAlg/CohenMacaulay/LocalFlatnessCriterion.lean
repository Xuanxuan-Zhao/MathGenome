import MathGenome.Internal.AlgebraCore.Specs.P103.Ch12.FiniteLengthTorVanishing
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
The local criterion used in paper.tex, CM-10 (3574–3577) and CM-13 (3723–3726).
The residue field is the actual quotient R/m. Tor is the homology of the ordinary
projective right-R-resolution tensored with M, using the shared balanced tensor.
The compatible R-action on M is restriction of its S-action. Finiteness is only
over S; neither S-flatness nor R-finiteness of M is imposed. The theorem also
holds for the zero module, so it specializes to both nonzero modules in the source.
-/
namespace Specs.AdvCommAlg.CohenMacaulay

open P103.BalancedTensor P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions

universe u v w

/-- An independent full proposition, with every projective residue resolution. -/
def localFlatnessCriterionType : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Finite S M],
    letI := commRightModule R (R ⧸ IsLocalRing.maximalIdeal R)
    ∀ (P : LeftResolution Rᵐᵒᵖ (R ⧸ IsLocalRing.maximalIdeal R)),
      P.IsProjective → (Subsingleton (TorWith P M 1) ↔ Module.Flat R M)

end Specs.AdvCommAlg.CohenMacaulay
