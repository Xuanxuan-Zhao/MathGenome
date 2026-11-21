import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces

/-! Independent statements for example d04:02:relative-derivative.
Coordinates 0 and 1 represent the paper's first and second coordinates.
No open-domain derivative or uniqueness condition is imposed. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C02.RelativeDerivativeExample
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

namespace Model
def horizontalAxis : Set (E 2) := {x | x 1 = 0}
def axisFunction (x : E 2) : ℝ := x 0
def axisFirstMap : E 2 →L[ℝ] ℝ := EuclideanSpace.proj 0
def axisSecondMap : E 2 →L[ℝ] ℝ := EuclideanSpace.proj 0 + EuclideanSpace.proj 1
end Model

abbrev horizontalAxisType := Set (E 2)
def horizontalAxisValue : horizontalAxisType := Model.horizontalAxis
abbrev axisFunctionType := E 2 → ℝ
def axisFunctionValue : axisFunctionType := Model.axisFunction
abbrev axisFirstMapType := E 2 →L[ℝ] ℝ
def axisFirstMapValue : axisFirstMapType := Model.axisFirstMap
abbrev axisSecondMapType := E 2 →L[ℝ] ℝ
def axisSecondMapValue : axisSecondMapType := Model.axisSecondMap

open Model

def horizontalAxis_eq_rangeType : Prop :=
  horizontalAxis = Set.range (fun t : ℝ => WithLp.toLp 2 ![t, 0])

def axis_maps_applyType : Prop :=
  (∀ h : E 2, axisFirstMap h = h 0) ∧
  (∀ h : E 2, axisSecondMap h = h 0 + h 1)

def axis_relative_approximationsType : Prop :=
  RelativeApproximation horizontalAxis axisFunction axisFirstMap 0 ∧
  RelativeApproximation horizontalAxis axisFunction axisSecondMap 0 ∧
  axisFirstMap ≠ axisSecondMap

def axis_relative_not_uniqueType : Prop :=
  ¬ (∀ A B : E 2 →L[ℝ] ℝ,
    RelativeApproximation horizontalAxis axisFunction A 0 →
    RelativeApproximation horizontalAxis axisFunction B 0 → A = B)

/-- All target dimensions, including zero, and arbitrary functions and maps. -/
def relativeApproximation_at_isolatedType : Prop :=
  ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set (E n)) (f : E n → Y) (a : U)
    (ha : IsolatedPoint U a) (A : E n →L[ℝ] Y),
    RelativeApproximation U f A a

/-- Literal functions on the relative domain and arbitrary algebraic ambient maps. -/
def relativeApproximation_subtype_at_isolatedType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : U → E m) (a : U)
    (ha : IsolatedPoint U a) (A : E n →ₗ[ℝ] E m),
    RelativeApproximation U (domainExtension U f) A.toContinuousLinearMap a

def relativeApproximation_singletonType : Prop :=
  ∀ {n m : ℕ} (a : E n) (f : ({a} : Set (E n)) → E m)
    (A : E n →ₗ[ℝ] E m),
    RelativeApproximation {a} (domainExtension {a} f) A.toContinuousLinearMap a

end Specs.D04.C02.RelativeDerivativeExample
