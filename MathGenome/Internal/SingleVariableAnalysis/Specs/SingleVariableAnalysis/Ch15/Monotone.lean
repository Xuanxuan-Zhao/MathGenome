import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.VariationRules

/-! Independent statements of K03.15.monotone, paper.tex:3584–3591.
Monotonicity is required only on the closed interval, in either direction;
no continuity is imposed. The total variation is the upstream supremum over
strict endpoint partitions. Its finite value is represented in `ℝ≥0∞` by
`ENNReal.ofReal`. The singleton case is included.

The finite linear-combination statement is given for normed spaces, including
scalar-valued functions over ℝ and ℂ by taking `E = 𝕜`. In those cases scalar
multiplication is ordinary multiplication. The finite index set may be empty. -/
namespace Specs.SingleVariableAnalysis.Ch15.Monotone
open scoped BigOperators ENNReal
universe u v w

def nondecreasingVariation : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
  MonotoneOn f (Set.Icc a b) →
  Variation.totalVariationValue f a b = ENNReal.ofReal |f b - f a|

def nonincreasingVariation : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
  AntitoneOn f (Set.Icc a b) →
  Variation.totalVariationValue f a b = ENNReal.ofReal |f b - f a|

/-- Both directions of real monotonicity imply BV, and the real finite value
is exactly the absolute endpoint increment. -/
def monotoneBoundedVariation : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
  (MonotoneOn f (Set.Icc a b) ∨ AntitoneOn f (Set.Icc a b)) →
  Variation.boundedVariationValue f a b ∧
    (Variation.totalVariationValue f a b).toReal = |f b - f a|

def finiteLinearCombination : Prop := ∀ {𝕜 : Type v} [NormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {ι : Type w} (s : Finset ι) (c : ι → 𝕜) (f : ι → ℝ → E) {a b : ℝ},
  a ≤ b → (∀ i ∈ s, Variation.boundedVariationValue (f i) a b) →
  Variation.boundedVariationValue (fun x => ∑ i ∈ s, c i • f i x) a b

end Specs.SingleVariableAnalysis.Ch15.Monotone
