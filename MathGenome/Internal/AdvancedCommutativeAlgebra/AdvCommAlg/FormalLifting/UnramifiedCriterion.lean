import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Universal
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.UnramifiedCriterion

/-! FL-04: the unramified criterion, without finiteness or nonzero hypotheses. -/
namespace AdvCommAlg.FormalLifting

universe u v

/-- Formal unramifiedness in the square-zero lifting sense is equivalent
to the relative Kähler differential module being zero. -/
theorem formallyUnramified_iff_subsingleton_omega
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    FormallyUnramified A B ↔ Subsingleton (Differentials.Omega A B) := by
  constructor
  · intro h
    exact ((formallyUnramified_iff A B).mp h).subsingleton_kaehlerDifferential
  · intro h
    exact (formallyUnramified_iff A B).mpr ⟨h⟩

end AdvCommAlg.FormalLifting
