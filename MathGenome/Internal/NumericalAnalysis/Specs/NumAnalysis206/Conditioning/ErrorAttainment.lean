import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Conditioning.Errors
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.RCLike.Basic

/-! Independent specification of the attainment paragraph following W12.
The norm on `X` is arbitrary and is the chosen perturbation-size norm.
Closedness is required of the whole feasible set, with no regularity
assumption on `f` or on the admissible set separately. The output space
needs no topology. This includes zero-dimensional input spaces.
-/

open scoped NNReal ENNReal

universe u v w

namespace Specs.NumAnalysis206.Conditioning.ErrorAttainment

open Specs.NumAnalysis206.Conditioning.Errors

/-- A feasible perturbation minimizes the chosen norm and realizes the finite
extended-valued backward error. -/
def normwiseBackwardError_attainedStatement : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X),
    (∃ v, feasiblePerturbation f x yhat D v) →
    IsClosed {v | feasiblePerturbation f x yhat D v} →
    ∃ v, feasiblePerturbation f x yhat D v ∧
      (∀ w, feasiblePerturbation f x yhat D w → ‖v‖ ≤ ‖w‖) ∧
      normwiseBackwardError f x yhat D = normwiseSize v ∧
      normwiseBackwardError f x yhat D < ⊤

/-- The same assertion for an explicitly supplied size functional that is the
chosen norm, embedded into the extended nonnegative reals. No assertion of
attainment for arbitrary nonnegative functionals is made. -/
def backwardError_attained_of_normStatement : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v} {Y : Type w}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    {U : Set X} (f : U → Y) (x : U) (yhat : Y) (D : Set X)
    (size : X → ℝ≥0∞),
    (∀ v, size v = (‖v‖₊ : ℝ≥0∞)) →
    (∃ v, feasiblePerturbation f x yhat D v) →
    IsClosed {v | feasiblePerturbation f x yhat D v} →
    ∃ v, feasiblePerturbation f x yhat D v ∧
      (∀ w, feasiblePerturbation f x yhat D w → size v ≤ size w) ∧
      backwardError f x yhat D size = size v ∧
      backwardError f x yhat D size < ⊤

end Specs.NumAnalysis206.Conditioning.ErrorAttainment
