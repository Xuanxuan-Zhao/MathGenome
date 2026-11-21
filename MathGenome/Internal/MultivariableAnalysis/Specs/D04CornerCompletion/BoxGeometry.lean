import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.EmbeddedManifoldCharts

/-! Canonical box objects for the targeted D04 corner supplement.
The Euclidean model and embedded-chart notions are the unchanged archived ones.
No geometric or analytic theorem is assumed by this interface. -/
noncomputable section
open Set
namespace Specs.D04CornerCompletion.BoxGeometry
open Specs.D04.C01.EuclideanInterfaces.Model

namespace Model

/-- The coordinatewise closed box, without a nondegeneracy convention. -/
def box {n : ℕ} (a b : E n) : Set (E n) :=
  {x | ∀ i : Fin n, a i ≤ x i ∧ x i ≤ b i}

/-- Coordinate endpoint selection; membership follows under the stated box bounds. -/
def IsBoxVertex {n : ℕ} (a b v : E n) : Prop :=
  ∀ i : Fin n, v i = a i ∨ v i = b i

end Model

def boxType := {n : ℕ} → E n → E n → Set (E n)
def boxValue : boxType := @Model.box

def IsBoxVertexType := {n : ℕ} → E n → E n → E n → Prop
def IsBoxVertexValue : IsBoxVertexType := @Model.IsBoxVertex

end Specs.D04CornerCompletion.BoxGeometry
