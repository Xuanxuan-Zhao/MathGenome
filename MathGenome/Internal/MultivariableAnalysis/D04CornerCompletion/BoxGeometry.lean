import MathGenome.Internal.MultivariableAnalysis.Specs.D04CornerCompletion.BoxGeometry

/-! Canonical box and vertex objects for the D04 corner supplement. -/

namespace D04CornerCompletion

open Specs.D04.C01.EuclideanInterfaces.Model

/-- The coordinatewise closed box, in every dimension and without additional bounds. -/
def box {n : ℕ} (a b : E n) : Set (E n) :=
  Specs.D04CornerCompletion.BoxGeometry.Model.box a b

/-- Each coordinate of a box vertex is one of the corresponding two endpoints. -/
def IsBoxVertex {n : ℕ} (a b v : E n) : Prop :=
  Specs.D04CornerCompletion.BoxGeometry.Model.IsBoxVertex a b v

end D04CornerCompletion
