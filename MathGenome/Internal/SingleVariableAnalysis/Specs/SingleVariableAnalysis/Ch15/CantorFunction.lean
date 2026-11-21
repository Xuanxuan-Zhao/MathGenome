import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.CantorStaircaseLimit
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.CantorSet
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Variation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-! The remaining conclusions of K03.15.cantor_function, paper.tex:3630–3646.
The function is exactly the previously constructed limit, and D is exactly the
previously constructed middle-thirds set. No certificate is a hypothesis.
Constancy is stated on every preconnected subset of the relative complement;
this includes every complementary interval. Derivatives are at actual points
of [0,1] outside D, which are necessarily interior points. -/
namespace Specs.SingleVariableAnalysis.Ch15.CantorFunction
open Set Filter
open scoped Topology

noncomputable abbrev C := CantorStaircaseLimit.limit
noncomputable abbrev D := Ch08.CantorSet.setValue

/-- The named function is exactly the limit of the prescribed iterates. -/
def functionType := ℝ → ℝ
noncomputable def functionValue : functionType := CantorStaircaseLimit.limit

def regularity : Prop :=
  ContinuousOn C (Icc 0 1) ∧ MonotoneOn C (Icc 0 1) ∧
  C 0 = 0 ∧ C 1 = 1 ∧ MapsTo C (Icc 0 1) (Icc 0 1)

def constantOnComplementaryIntervals : Prop :=
  ∀ S : Set ℝ, IsPreconnected S → S ⊆ Icc 0 1 \ D →
    ∀ x ∈ S, ∀ y ∈ S, C x = C y

def locallyConstantOff : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1 \ D, ∀ᶠ y in 𝓝 x, C y = C x

def derivativeZeroOff : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1 \ D, HasDerivAt C 0 x ∧
    Ch04.Derivative.hasRealIncrementDerivativeValue C 0 x ∧ deriv C x = 0

def exceptionalLengthZero : Prop := Ch08.ZeroCovers.lengthZeroValue D

def nonconstant : Prop := ¬ ∃ c : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, C x = c

def variationOne : Prop :=
  Variation.boundedVariationValue C 0 1 ∧
  Variation.totalVariationValue C 0 1 = 1 ∧
  (Variation.totalVariationValue C 0 1).toReal = 1

end Specs.SingleVariableAnalysis.Ch15.CantorFunction
