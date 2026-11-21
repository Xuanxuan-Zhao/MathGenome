import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.ProductSigma
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Count

/-! Independent specification of paper.tex:2865–2878. The index type is
`ℕ+ = {n : ℕ // 0 < n}`, so the first row is literally row 1. The factors
carry their ordinary discrete sigma-algebras and counting measures. The
product below is the ordinary product, with no completion. Scalar integral
formulas are accompanied by section and outer integrability assertions. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace Specs.D11.Ch08.SignedFubiniFailure

/-- The source equips the positive integers with their full power-set sigma-algebra. -/
instance positiveIntegersMeasurableSpace : MeasurableSpace ℕ+ := ⊤

/-- The displayed real-valued function, on positive integers. -/
def exampleFunction_type := ℕ+ → ℕ+ → ℝ

def exampleFunction_value : exampleFunction_type := fun m n =>
  if m = n then 1 else if m = n + 1 then -1 else 0

def product_full : Prop :=
  (inferInstance : MeasurableSpace ℕ+).prod (inferInstance : MeasurableSpace ℕ+) = ⊤

def measurable_function : Prop :=
  Measurable (fun p : ℕ+ × ℕ+ => exampleFunction_value p.1 p.2)

def sections_finite_support : Prop :=
  (∀ m : ℕ+, (Function.support (exampleFunction_value m)).Finite) ∧
  (∀ n : ℕ+, (Function.support (fun m => exampleFunction_value m n)).Finite)

def sections_integrable : Prop :=
  (∀ m : ℕ+, Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
    Measure.count (exampleFunction_value m)) ∧
  (∀ n : ℕ+, Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
    Measure.count (fun m => exampleFunction_value m n))

def row_sums : Prop :=
  ∀ m : ℕ+, (∑' n : ℕ+, exampleFunction_value m n) = if m = 1 then 1 else 0

def column_sums : Prop :=
  ∀ n : ℕ+, (∑' m : ℕ+, exampleFunction_value m n) = 0

def iterated_sums : Prop :=
  (∑' m : ℕ+, ∑' n : ℕ+, exampleFunction_value m n) = 1 ∧
  (∑' n : ℕ+, ∑' m : ℕ+, exampleFunction_value m n) = 0

def outer_integrable : Prop :=
  Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value Measure.count
    (fun m : ℕ+ => ∫ n : ℕ+, exampleFunction_value m n ∂Measure.count) ∧
  Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value Measure.count
    (fun n : ℕ+ => ∫ m : ℕ+, exampleFunction_value m n ∂Measure.count)

def iterated_integrals : Prop :=
  (∫ m : ℕ+, ∫ n : ℕ+, exampleFunction_value m n ∂Measure.count ∂Measure.count) = 1 ∧
  (∫ n : ℕ+, ∫ m : ℕ+, exampleFunction_value m n ∂Measure.count ∂Measure.count) = 0

def absolute_sum : Prop :=
  (∑' p : ℕ+ × ℕ+, ENNReal.ofReal |exampleFunction_value p.1 p.2|) = ∞

def absolute_product_integral : Prop :=
  Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value
    ((Measure.count : Measure ℕ+).prod Measure.count)
    (fun p : ℕ+ × ℕ+ => ENNReal.ofReal |exampleFunction_value p.1 p.2|) = ∞

def not_integrable : Prop :=
  ¬ Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
    ((Measure.count : Measure ℕ+).prod Measure.count)
    (fun p : ℕ+ × ℕ+ => exampleFunction_value p.1 p.2)

def interchange_failure : Prop :=
  (∫ m : ℕ+, ∫ n : ℕ+, exampleFunction_value m n ∂Measure.count ∂Measure.count) ≠
  (∫ n : ℕ+, ∫ m : ℕ+, exampleFunction_value m n ∂Measure.count ∂Measure.count)

end Specs.D11.Ch08.SignedFubiniFailure
