import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Radius
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch11.CauchyProduct

/-! Independent statements for K03.13.products, paper.tex:1407–1418.
The coefficients, ordinary inclusive partial sums, and root-limsup radii
are the canonical upstream objects. No convergence hypothesis is imposed
beyond the two strict interior inequalities and the specified factor values.
The examples verify coefficient cancellation, all three radii, and the
numerical identity on the original common disk. -/
namespace Specs.SingleVariableAnalysis.Ch13.Products
open PowerSeries
open Specs.SingleVariableAnalysis.Ch11.CauchyProduct
open scoped ENNReal

def realProductHasSum : Prop := ∀ (a b : ℕ → ℝ) (c x : ℝ) (A B : ℝ),
  ENNReal.ofReal |x-c| < min (realPowerSeriesRadiusValue a) (realPowerSeriesRadiusValue b) →
  RealPowerSeriesHasSumValue a c x A → RealPowerSeriesHasSumValue b c x B →
  RealPowerSeriesHasSumValue (realCauchyProductValue a b) c x (A * B)

def realProductAbsolute : Prop := ∀ (a b : ℕ → ℝ) (c x : ℝ),
  ENNReal.ofReal |x-c| < min (realPowerSeriesRadiusValue a) (realPowerSeriesRadiusValue b) →
  RealPowerSeriesAbsolutelyConvergesValue (realCauchyProductValue a b) c x

def realProductRadius : Prop := ∀ (a b : ℕ → ℝ),
  min (realPowerSeriesRadiusValue a) (realPowerSeriesRadiusValue b) ≤ realPowerSeriesRadiusValue (realCauchyProductValue a b)

def realProductEnlargement : Prop :=
  let a : ℕ → ℝ := fun _ => 1
  let b : ℕ → ℝ := fun n => if n = 0 then 1 else if n = 1 then -1 else 0
  realPowerSeriesRadiusValue a = 1 ∧
  realPowerSeriesRadiusValue b = ⊤ ∧
  realCauchyProductValue a b = (fun n => if n = 0 then 1 else 0) ∧
  realPowerSeriesRadiusValue (realCauchyProductValue a b) = ⊤ ∧
  min (realPowerSeriesRadiusValue a) (realPowerSeriesRadiusValue b) < realPowerSeriesRadiusValue (realCauchyProductValue a b) ∧
  ∀ x : ℝ, |x| < 1 →
    RealPowerSeriesHasSumValue a 0 x (1 / (1-x)) ∧
    RealPowerSeriesHasSumValue b 0 x (1-x) ∧
    RealPowerSeriesHasSumValue (realCauchyProductValue a b) 0 x 1 ∧
    (1 / (1-x)) * (1-x) = 1

def complexProductHasSum : Prop := ∀ (a b : ℕ → ℂ) (c : ℝ) (x : ℂ) (A B : ℂ),
  ENNReal.ofReal ‖x-(c : ℂ)‖ < min (complexPowerSeriesRadiusValue a) (complexPowerSeriesRadiusValue b) →
  ComplexPowerSeriesHasSumValue a c x A → ComplexPowerSeriesHasSumValue b c x B →
  ComplexPowerSeriesHasSumValue (complexCauchyProductValue a b) c x (A * B)

def complexProductAbsolute : Prop := ∀ (a b : ℕ → ℂ) (c : ℝ) (x : ℂ),
  ENNReal.ofReal ‖x-(c : ℂ)‖ < min (complexPowerSeriesRadiusValue a) (complexPowerSeriesRadiusValue b) →
  ComplexPowerSeriesAbsolutelyConvergesValue (complexCauchyProductValue a b) c x

def complexProductRadius : Prop := ∀ (a b : ℕ → ℂ),
  min (complexPowerSeriesRadiusValue a) (complexPowerSeriesRadiusValue b) ≤ complexPowerSeriesRadiusValue (complexCauchyProductValue a b)

def complexProductEnlargement : Prop :=
  let a : ℕ → ℂ := fun _ => 1
  let b : ℕ → ℂ := fun n => if n = 0 then 1 else if n = 1 then -1 else 0
  complexPowerSeriesRadiusValue a = 1 ∧
  complexPowerSeriesRadiusValue b = ⊤ ∧
  complexCauchyProductValue a b = (fun n => if n = 0 then 1 else 0) ∧
  complexPowerSeriesRadiusValue (complexCauchyProductValue a b) = ⊤ ∧
  min (complexPowerSeriesRadiusValue a) (complexPowerSeriesRadiusValue b) < complexPowerSeriesRadiusValue (complexCauchyProductValue a b) ∧
  ∀ x : ℂ, ‖x‖ < 1 →
    ComplexPowerSeriesHasSumValue a 0 x (1 / (1-x)) ∧
    ComplexPowerSeriesHasSumValue b 0 x (1-x) ∧
    ComplexPowerSeriesHasSumValue (complexCauchyProductValue a b) 0 x 1 ∧
    (1 / (1-x)) * (1-x) = 1

end Specs.SingleVariableAnalysis.Ch13.Products
