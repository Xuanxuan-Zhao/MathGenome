import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.EuclideanInterfaces
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent statements for the distance-function part of
`chapters/01.tex`, `d04:01:distance`. The domain of the definition includes
a proof that the set is nonempty; no distance to the empty set is used.
There is no closedness, boundedness, or positive-dimension assumption. -/

noncomputable section
open Set

namespace Specs.D04.C01.DistanceFunction.Model
open Specs.D04.C01.EuclideanInterfaces.Model

/-- The real infimum of the nonempty set of Euclidean distances. -/
def distanceToSet {n : ℕ} (A : Set (E n)) (_hA : A.Nonempty) (x : E n) : ℝ :=
  sInf ((fun a => ‖x - a‖) '' A)

end Specs.D04.C01.DistanceFunction.Model

namespace Specs.D04.C01.DistanceFunction
open Specs.D04.C01.EuclideanInterfaces.Model

def distanceToSetType :=
  {n : ℕ} → (A : Set (E n)) → A.Nonempty → E n → ℝ

def distanceToSetValue : distanceToSetType := @Model.distanceToSet

def distanceToSet_eq_infDistType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (hA : A.Nonempty) (x : E n),
    Model.distanceToSet A hA x = Metric.infDist x A

def distanceToSet_abs_sub_leType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (hA : A.Nonempty) (x y : E n),
    |Model.distanceToSet A hA x - Model.distanceToSet A hA y| ≤ ‖x - y‖

def distanceToSet_eq_zero_iffType : Prop :=
  ∀ {n : ℕ} (A : Set (E n)) (hA : A.Nonempty) (x : E n),
    Model.distanceToSet A hA x = 0 ↔ x ∈ Closure A

end Specs.D04.C01.DistanceFunction
