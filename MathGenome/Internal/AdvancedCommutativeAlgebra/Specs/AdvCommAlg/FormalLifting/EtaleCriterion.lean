import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal

/-! Independent statement of the first assertion of FL-11
(paper.tex, Theorem "Formally étale intermediate maps").
The formal properties are the square-zero lifting definitions of FL-01.
Vanishing of the differential module means that its underlying type is a
subsingleton. No finiteness or nonzero-ring hypothesis is imposed. -/
namespace Specs.AdvCommAlg.FormalLifting

universe u v

/-- Formal étaleness is equivalent to formal smoothness and vanishing
of the module of relative Kähler differentials. -/
def etaleCriterion : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    formallyEtaleValue A B ↔
      formallySmoothValue A B ∧
        Subsingleton (Specs.AdvCommAlg.Differentials.omegaValue A B)

end Specs.AdvCommAlg.FormalLifting
