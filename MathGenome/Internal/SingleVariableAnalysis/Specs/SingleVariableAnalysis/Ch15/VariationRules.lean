import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Variation
import Mathlib.Analysis.Normed.Module.Basic

/-! Independent statements for K03.15.variation_rules (paper.tex:3574–3585).
Variation is the upstream supremum over strict endpoint partitions, with values
in `ℝ≥0∞`. Additivity and the sum inequality retain infinite values. Finite
variation is converted to a real number only with the explicit BV hypothesis.
Normed-space generality includes real and complex scalar functions and scaling
by scalars of the same field. -/
namespace Specs.SingleVariableAnalysis.Ch15.VariationRules
open scoped ENNReal
universe u v

def additive : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) {a c b : ℝ}, a ≤ c → c ≤ b →
  Variation.totalVariationValue f a b =
    Variation.totalVariationValue f a c + Variation.totalVariationValue f c b

def subadditive : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f g : ℝ → E) {a b : ℝ}, a ≤ b →
  Variation.totalVariationValue (fun x => f x + g x) a b ≤
    Variation.totalVariationValue f a b + Variation.totalVariationValue g a b

/-- The extended identity is also meaningful for infinite variation, with
`0 * ⊤ = 0`. In particular it includes every finite-variation scalar identity. -/
def homogeneous : Prop := ∀ {𝕜 : Type v} [NormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (c : 𝕜) (f : ℝ → E) {a b : ℝ}, a ≤ b →
  Variation.totalVariationValue (fun x => c • f x) a b =
    ENNReal.ofReal ‖c‖ * Variation.totalVariationValue f a b

/-- Both finiteness of the scaled function and homogeneity of the real finite
value, including c = 0, without a division by the scalar. -/
def finiteHomogeneous : Prop := ∀ {𝕜 : Type v} [NormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (c : 𝕜) (f : ℝ → E) {a b : ℝ}, a ≤ b →
  Variation.boundedVariationValue f a b →
  Variation.boundedVariationValue (fun x => c • f x) a b ∧
    (Variation.totalVariationValue (fun x => c • f x) a b).toReal =
      ‖c‖ * (Variation.totalVariationValue f a b).toReal

def boundedness : Prop := ∀ {E : Type u} [NormedAddCommGroup E]
  (f : ℝ → E) {a b : ℝ}, a ≤ b → Variation.boundedVariationValue f a b →
  ∀ x ∈ Set.Icc a b,
    ‖f x‖ ≤ ‖f a‖ + (Variation.totalVariationValue f a b).toReal

end Specs.SingleVariableAnalysis.Ch15.VariationRules
