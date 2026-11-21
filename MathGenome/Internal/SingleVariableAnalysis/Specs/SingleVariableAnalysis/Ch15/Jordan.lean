import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Monotone

/-! Independent specification of K03.15.jordan (paper.tex:3592–3604).
The functions are real valued and all monotonicity and equality assertions are
on the original closed interval, with no continuity or endpoint conventions added.
The real variation function uses the upstream strict-partition variation. Its
`toReal` is finite on every relevant subinterval under the BV hypothesis.
The singleton interval is included. -/
namespace Specs.SingleVariableAnalysis.Ch15.Jordan

abbrev variationFunctionType := (ℝ → ℝ) → ℝ → ℝ → ℝ

noncomputable def variationFunctionValue : variationFunctionType :=
  fun f a x => (Variation.totalVariationValue f a x).toReal

abbrev componentType := (ℝ → ℝ) → ℝ → ℝ → ℝ

noncomputable def positiveComponentValue : componentType :=
  fun f a x => (variationFunctionValue f a x + f x - f a) / 2

noncomputable def negativeComponentValue : componentType :=
  fun f a x => (variationFunctionValue f a x - f x + f a) / 2

/-- The finite variation increment is precisely the variation on the intervening
closed interval. Individual point values, including both endpoints, are counted. -/
def variationIncrement : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
  Variation.boundedVariationValue f a b →
  ∀ {x y : ℝ}, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
    variationFunctionValue f a y - variationFunctionValue f a x =
      (Variation.totalVariationValue f x y).toReal

/-- The key estimate for the explicit Jordan components. -/
def absoluteIncrementBound : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
  Variation.boundedVariationValue f a b →
  ∀ {x y : ℝ}, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
    |f y - f x| ≤ variationFunctionValue f a y - variationFunctionValue f a x

/-- The manuscript's particular formulas give nondecreasing components and the
pointwise reconstruction f = f(a) + p - q. Their initial values are zero. -/
def canonicalDecomposition : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
  Variation.boundedVariationValue f a b →
  MonotoneOn (positiveComponentValue f a) (Set.Icc a b) ∧
  MonotoneOn (negativeComponentValue f a) (Set.Icc a b) ∧
  (∀ x ∈ Set.Icc a b,
    f x = f a + positiveComponentValue f a x - negativeComponentValue f a x) ∧
  positiveComponentValue f a a = 0 ∧ negativeComponentValue f a a = 0

/-- A real function is BV exactly when it is a difference of nondecreasing real
functions on the same interval. The constant f(a) in the canonical construction
can be absorbed into the first component. -/
def jordanIff : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
  (Variation.boundedVariationValue f a b ↔
    ∃ g h : ℝ → ℝ, MonotoneOn g (Set.Icc a b) ∧ MonotoneOn h (Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, f x = g x - h x)

end Specs.SingleVariableAnalysis.Ch15.Jordan
