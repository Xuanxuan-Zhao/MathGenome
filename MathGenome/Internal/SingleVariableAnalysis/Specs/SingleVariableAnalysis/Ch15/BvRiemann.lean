import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.OneSided
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Regulated

/-! K03.15.bv_riemann (paper.tex:3622–3630). Variation uses strict endpoint
partitions, regulatedness uses finite limits on every available side, and
integrability is the bounded proper Darboux predicate. All values at nodes and
endpoints are retained. The ordered interval may be a singleton. -/
namespace Specs.SingleVariableAnalysis.Ch15.BvRiemann
open _root_.SingleVariableAnalysis

/-- Each component increment is bounded by the complex increment, including
when the total variation is infinite. -/
def componentVariations : Prop :=
  ∀ (f : ℝ → ℂ) (a b : ℝ),
    Variation.totalVariationValue (fun x => (f x).re) a b ≤
      Variation.totalVariationValue f a b ∧
    Variation.totalVariationValue (fun x => (f x).im) a b ≤
      Variation.totalVariationValue f a b

def realBvRegulated : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    Variation.boundedVariationValue f a b → RegulatedOn f a b

def realBvRiemann : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
    Variation.boundedVariationValue f a b →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc a b, |f x| ≤ M) ∧
      RegulatedOn f a b ∧ Ch08.Integral.realIntegrableValue f a b

def complexBvRegulated : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    Variation.boundedVariationValue f a b → RegulatedOn f a b

def complexBvRiemann : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    Variation.boundedVariationValue f a b →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M) ∧
      RegulatedOn f a b ∧ Ch08.Integral.complexIntegrableValue f a b

/-- Relative continuity on the original closed interval includes endpoints. -/
def complexCountableDiscontinuities : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
    Variation.boundedVariationValue f a b →
    Set.Countable {c ∈ Set.Icc a b | ¬ ContinuousWithinAt f (Set.Icc a b) c}

end Specs.SingleVariableAnalysis.Ch15.BvRiemann
