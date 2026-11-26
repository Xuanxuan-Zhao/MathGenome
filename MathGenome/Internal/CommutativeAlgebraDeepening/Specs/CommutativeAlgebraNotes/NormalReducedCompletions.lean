import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ExcellenceDefinitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.Definitions

/-! Independent specifications for Corollary 5.10. -/

universe u

namespace CommutativeAlgebraNotes.Specs

/-- The maximal-ideal adic completion of a Noetherian local normal G-ring is normal. -/
def normalCompletionType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A],
    Excellence.Specs.IsGRingValue A → AdvCommAlg.Normality.Specs.IsNormalValue A →
    letI := P103.Ch07.CompletedNoetherian.completed_noetherian A (IsLocalRing.maximalIdeal A)
    AdvCommAlg.Normality.Specs.IsNormalValue (AdicCompletion (IsLocalRing.maximalIdeal A) A)

/-- The maximal-ideal adic completion of a Noetherian local reduced G-ring is reduced. -/
def reducedCompletionType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A],
    Excellence.Specs.IsGRingValue A → IsReduced A →
    IsReduced (AdicCompletion (IsLocalRing.maximalIdeal A) A)

end CommutativeAlgebraNotes.Specs
