import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.NormalizedStieltjes
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcDefinition

/-! Global initial variation in the forward implication at paper.tex:4055–4056.
The variation is the accepted supremum of classical partition variations.
The positive-generator conditions and the exact measure equality are conclusions.
All measures carry the Borel measurable space on ℝ. -/

open Set MeasureTheory

namespace Specs.D11.Ch12.AcGlobalVariation
open Specs.D11.Ch12.ScalarStieltjesCorrespondence
open Specs.D11.Ch12.PositiveStieltjes

/-- One AC modulus works on all of ℝ for the genuine initial variation. -/
def variation_ac : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] (F : ℝ → 𝕂), NBV_value F →
    Specs.D11.Ch12.absolutelyContinuousValue F →
    Specs.D11.Ch12.absolutelyContinuousValue
      (fun x => (initialVariation_value F x).toReal)

/-- Includes monotonicity, right continuity, boundedness and limit zero at −∞. -/
def positiveGenerator : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] (F : ℝ → 𝕂), NBV_value F →
    positiveGenerator_value (fun x => (initialVariation_value F x).toReal)

/-- Any proof of the established generator conditions gives the same measure. -/
def stieltjesMeasure_eq : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] (F : ℝ → 𝕂), NBV_value F →
    ∀ hV : positiveGenerator_value (fun x => (initialVariation_value F x).toReal),
      (stieltjesMeasure_value F).variation =
        Specs.D11.Ch12.PositiveStieltjes.stieltjesMeasure_value
          (fun x => (initialVariation_value F x).toReal) hV

/-- Full package from the original NBV and uniform AC hypotheses alone. -/
def global_variation : Prop :=
  ∀ {𝕂 : Type*} [RCLike 𝕂] (F : ℝ → 𝕂), NBV_value F →
    Specs.D11.Ch12.absolutelyContinuousValue F →
    Specs.D11.Ch12.absolutelyContinuousValue
      (fun x => (initialVariation_value F x).toReal) ∧
    ∃ hV : positiveGenerator_value (fun x => (initialVariation_value F x).toReal),
      (stieltjesMeasure_value F).variation =
        Specs.D11.Ch12.PositiveStieltjes.stieltjesMeasure_value
          (fun x => (initialVariation_value F x).toReal) hV

end Specs.D11.Ch12.AcGlobalVariation
