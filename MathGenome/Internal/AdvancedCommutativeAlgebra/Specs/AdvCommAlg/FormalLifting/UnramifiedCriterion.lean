import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal

/-! Independent statement of FL-04, paper.tex, Proposition "The unramified
criterion". A module is zero precisely when its underlying type is a
subsingleton. The lifting property here is the square-zero definition of
FL-01, not an assumed condition on differentials. -/
namespace Specs.AdvCommAlg.FormalLifting

universe u v

/-- For every commutative algebra, uniqueness of square-zero lifts is
equivalent to vanishing of its relative differential module. -/
def unramifiedCriterion : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    formallyUnramifiedValue A B ↔
      Subsingleton (Specs.AdvCommAlg.Differentials.omegaValue A B)

end Specs.AdvCommAlg.FormalLifting
