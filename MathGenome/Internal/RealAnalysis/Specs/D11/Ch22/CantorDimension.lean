import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.CantorDigitSurjection
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.DimensionDefinition

/-! Independent statements for paper.tex:6148–6150, the elementary
middle-thirds Cantor dimension theorem. All objects are the canonical shared
ones. The nonnegative exponent is just the positive real exponent coerced to
`ℝ≥0`; the masses are outer masses in the usual metric on `ℝ`.
Lebesgue nullity uses the earlier completed Euclidean line measure, with the
canonical identification of `ℝ` and Euclidean `ℝ¹`. -/

noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal

namespace Specs.D11.Ch22.CantorDimension

def mass_bounds : Prop :=
  0 < HausdorffOuterMeasure.outerMeasureValue
    (Real.toNNReal CantorDigitSurjection.alpha_value) Ch03.CantorSet.C_value ∧
  HausdorffOuterMeasure.outerMeasureValue
    (Real.toNNReal CantorDigitSurjection.alpha_value) Ch03.CantorSet.C_value ≤ 1

def dimension : Prop :=
  DimensionDefinition.dimensionValue Ch03.CantorSet.C_value =
    ENNReal.ofReal CantorDigitSurjection.alpha_value

def lebesgue_null : Prop :=
  MeasurableSet[Ch03.LebesgueMeasures.lebesgueSpace_value 1]
    (_root_.D11.Ch03.CantorConstruction.linePoint '' Ch03.CantorSet.C_value) ∧
  Ch03.LebesgueMeasures.lebesgue_value 1
    (_root_.D11.Ch03.CantorConstruction.linePoint '' Ch03.CantorSet.C_value) = 0

end Specs.D11.Ch22.CantorDimension
