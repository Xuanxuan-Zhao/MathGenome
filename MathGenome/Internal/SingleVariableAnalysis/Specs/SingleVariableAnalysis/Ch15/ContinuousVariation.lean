import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Jordan
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Continuity

/-! Independent specifications for K03.15.continuous_variation,
paper.tex:3642–3661. Continuity is relative to the closed interval, hence
includes both endpoints and the singleton case. Normed-group generality includes
both real and complex scalars. Variation is the original strict-partition
supremum; real conversion is used only under the stated finite-variation
hypothesis. The one-sided statements require continuity only on that side.
-/
namespace Specs.SingleVariableAnalysis.Ch15.ContinuousVariation
open scoped Topology
universe u

def continuousVariation : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) {a b : ℝ}, a ≤ b → Variation.boundedVariationValue f a b →
  ContinuousOn f (Set.Icc a b) →
  ContinuousOn (fun x => (Variation.totalVariationValue f a x).toReal) (Set.Icc a b)

def rightContinuousVariationAt : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) {a b c : ℝ}, a ≤ b → Variation.boundedVariationValue f a b →
  c ∈ Set.Icc a b → ContinuousWithinAt f (Set.Icc a b ∩ Set.Ici c) c →
  ContinuousWithinAt (fun x => (Variation.totalVariationValue f a x).toReal)
    (Set.Icc a b ∩ Set.Ici c) c

def leftContinuousVariationAt : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) {a b c : ℝ}, a ≤ b → Variation.boundedVariationValue f a b →
  c ∈ Set.Icc a b → ContinuousWithinAt f (Set.Icc a b ∩ Set.Iic c) c →
  ContinuousWithinAt (fun x => (Variation.totalVariationValue f a x).toReal)
    (Set.Icc a b ∩ Set.Iic c) c

def continuousJordan : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
  Variation.boundedVariationValue f a b → ContinuousOn f (Set.Icc a b) →
  ContinuousOn (Jordan.positiveComponentValue f a) (Set.Icc a b) ∧
  ContinuousOn (Jordan.negativeComponentValue f a) (Set.Icc a b) ∧
  MonotoneOn (Jordan.positiveComponentValue f a) (Set.Icc a b) ∧
  MonotoneOn (Jordan.negativeComponentValue f a) (Set.Icc a b) ∧
  (∀ x ∈ Set.Icc a b,
    f x = f a + Jordan.positiveComponentValue f a x - Jordan.negativeComponentValue f a x) ∧
  Jordan.positiveComponentValue f a a = 0 ∧ Jordan.negativeComponentValue f a a = 0

abbrev stepType := ℝ → ℝ

/-- The jump is assigned its right-hand value, including at zero. -/
noncomputable def stepValue : stepType := fun x => if 0 ≤ x then 1 else 0

def stepVariation : Prop := ∀ x ∈ Set.Icc (-1 : ℝ) 1,
  (Variation.totalVariationValue stepValue (-1) x).toReal = stepValue x

/-- A concrete BV counterexample with a left jump, and right continuity of
both the function and its variation. Full continuity of its variation fails
even relative to the original interval. -/
def rightContinuityCounterexample : Prop :=
  Variation.boundedVariationValue stepValue (-1) 1 ∧
  (∀ c : ℝ, ContinuousWithinAt stepValue (Set.Ici c) c) ∧
  Filter.Tendsto stepValue (𝓝[<] (0 : ℝ)) (𝓝 0) ∧ stepValue 0 = 1 ∧
  ¬ ContinuousWithinAt stepValue (Set.Icc (-1) 1) 0 ∧
  (∀ c ∈ Set.Icc (-1 : ℝ) 1,
    ContinuousWithinAt (fun x => (Variation.totalVariationValue stepValue (-1) x).toReal)
      (Set.Icc (-1) 1 ∩ Set.Ici c) c) ∧
  ¬ ContinuousWithinAt (fun x => (Variation.totalVariationValue stepValue (-1) x).toReal)
    (Set.Icc (-1) 1) 0

end Specs.SingleVariableAnalysis.Ch15.ContinuousVariation
