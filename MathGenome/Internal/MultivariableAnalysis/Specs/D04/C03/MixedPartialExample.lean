import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces

/-! The scalar example d04:03:mixed-counterexample on the canonical Euclidean plane.
Division in ℝ gives the stipulated value zero at the origin. Existence of
partial derivatives is asserted using line derivatives, separately from selectors. -/
noncomputable section
open Set
namespace Specs.D04.C03.MixedPartialExample
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C03.HigherInterfaces.Model

namespace Model
/-- f(x,y)=xy(x²-y²)/(x²+y²), with f(0,0)=0. -/
def mixedPartialExample (z : E 2) : ℝ :=
  z 0 * z 1 * (z 0 ^ 2 - z 1 ^ 2) / (z 0 ^ 2 + z 1 ^ 2)
end Model
open Model

abbrev mixedPartialExampleType := E 2 → ℝ
def mixedPartialExampleValue : mixedPartialExampleType := mixedPartialExample

def mixedPartialExample_zeroType : Prop := mixedPartialExample 0 = 0

def mixedPartialExample_boundType : Prop :=
  ∀ z : E 2, |mixedPartialExample z| ≤ |z 0 * z 1| ∧
    |z 0 * z 1| ≤ ‖z‖ ^ 2 / 2

def mixedPartialExample_derivative_zeroType : Prop :=
  HasTotalDerivative univ mixedPartialExample 0 0 ∧ totalDerivative mixedPartialExample 0 = 0

def mixedPartialExample_c1Type : Prop := CrOn 1 univ mixedPartialExample

def mixedPartialExample_partials_continuousType : Prop :=
  ∀ i : Fin 2, Continuous (fun z => scalarPartialDerivative mixedPartialExample z i)

def mixedPartialExample_axis_partialsType : Prop :=
  (∀ y : ℝ, HasDirectionalDerivative mixedPartialExample
    (y • standardBasis 2 1) (standardBasis 2 0) (-y) ∧
    scalarPartialDerivative mixedPartialExample (y • standardBasis 2 1) 0 = -y) ∧
  (∀ x : ℝ, HasDirectionalDerivative mixedPartialExample
    (x • standardBasis 2 0) (standardBasis 2 1) x ∧
    scalarPartialDerivative mixedPartialExample (x • standardBasis 2 0) 1 = x)

def mixedPartialExample_mixed_partialsType : Prop :=
  HasDirectionalDerivative (fun z => scalarPartialDerivative mixedPartialExample z 0)
      0 (standardBasis 2 1) (-1) ∧
  HasDirectionalDerivative (fun z => scalarPartialDerivative mixedPartialExample z 1)
      0 (standardBasis 2 0) 1 ∧
  scalarPartialDerivative (fun z => scalarPartialDerivative mixedPartialExample z 0) 0 1 = -1 ∧
  scalarPartialDerivative (fun z => scalarPartialDerivative mixedPartialExample z 1) 0 0 = 1

def mixedPartialExample_not_all_partials_differentiableType : Prop :=
  ¬ ∀ i : Fin 2, TotalDifferentiableAt univ
    (fun z => scalarPartialDerivative mixedPartialExample z i) 0

def mixedPartialExample_not_twice_differentiableType : Prop :=
  ¬ TimesDifferentiableAt 2 univ mixedPartialExample 0

end Specs.D04.C03.MixedPartialExample
