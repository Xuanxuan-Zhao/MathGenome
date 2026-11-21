import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.Definitions

/-! SN-09, paper.tex:4265–4280. All prime localizations are tested, with
no domain or nonzero hypothesis on the ambient Noetherian ring. -/
universe u
namespace AdvCommAlg.Normality.Specs

def serreCriterionType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A],
    IsNormalValue A ↔ RegularInCodimensionValue A 1 ∧
      CohenMacaulay.Specs.RingSerreConditionValue A 2

end AdvCommAlg.Normality.Specs
