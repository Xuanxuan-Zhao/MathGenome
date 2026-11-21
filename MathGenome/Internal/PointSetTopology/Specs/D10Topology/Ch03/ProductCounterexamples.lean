import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.Products
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.MapCounterexamples
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch02.SeparateContinuityCounterexample
import Mathlib.Data.PNat.Basic

/-! Independent statements for paper.tex, `d10:03:product-cautions`.
Positive natural indices are exactly the paper's indices n ≥ 1. Bool is
the discrete two-point set, with false and true representing 0 and 1.
All product and box topologies use the canonical upstream constructions. -/

open Set
open scoped Topology

namespace Specs.D10Topology.Ch03.ProductCounterexamples

def diagonalType := ℝ → (ℕ+ → ℝ)
def diagonalValue : diagonalType := fun t _ => t

def shrinkingBoxType := Set (ℕ+ → ℝ)
def shrinkingBoxValue : shrinkingBoxType :=
  univ.pi (fun n => Ioo (-(1 / (n : ℝ))) (1 / (n : ℝ)))

def diagonal_product_continuous : Prop :=
  Continuous[inferInstance, Products.productTopologyValue (fun _ : ℕ+ => inferInstance)]
    diagonalValue

def shrinkingBox_box_open : Prop :=
  IsOpen[Products.boxTopologyValue (fun _ : ℕ+ => inferInstance)] shrinkingBoxValue

def diagonal_preimage_shrinkingBox : Prop :=
  diagonalValue ⁻¹' shrinkingBoxValue = ({0} : Set ℝ)

def diagonal_box_not_continuous : Prop :=
  ¬ Continuous[inferInstance, Products.boxTopologyValue (fun _ : ℕ+ => inferInstance)]
    diagonalValue

/-- Every nonempty finite-coordinate basic neighborhood contains a second point,
including cylinders with no restrictions. -/
def binary_basic_neighborhood_has_second_point : Prop :=
  ∀ B ∈ Products.productBasisValue (fun _ : ℕ+ => (⊥ : TopologicalSpace Bool)),
    ∀ x ∈ B, ∃ y ∈ B, y ≠ x

def binary_singleton_not_open : Prop :=
  ∀ x : ℕ+ → Bool,
    ¬ IsOpen[Products.productTopologyValue (fun _ : ℕ+ => (⊥ : TopologicalSpace Bool))]
      ({x} : Set (ℕ+ → Bool))

def binary_product_not_discrete : Prop :=
  ¬ @DiscreteTopology (ℕ+ → Bool)
    (Products.productTopologyValue (fun _ : ℕ+ => (⊥ : TopologicalSpace Bool)))

/-- The cited closed hyperbola has nonclosed first projection. -/
def projection_closed_counterexample : Prop :=
  IsClosed {z : ℝ × ℝ | z.1 * z.2 = 1} ∧
    Prod.fst '' {z : ℝ × ℝ | z.1 * z.2 = 1} = (univ : Set ℝ) \ {0} ∧
    ¬ IsClosed (Prod.fst '' {z : ℝ × ℝ | z.1 * z.2 = 1}) ∧
    ¬ IsClosedMap (Prod.fst : ℝ × ℝ → ℝ)

/-- The cited h, with its actual prescribed origin value and quotient formula,
is continuous on each horizontal and vertical slice but not at the origin. -/
def separate_continuity_counterexample : Prop :=
  let h := Ch02.SeparateContinuityCounterexample.exampleMap
  h (0, 0) = 0 ∧
    (∀ p : ℝ × ℝ, p ≠ (0, 0) → h p = p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)) ∧
    (∀ y : ℝ, Continuous (fun x : ℝ => h (x, y))) ∧
    (∀ x : ℝ, Continuous (fun y : ℝ => h (x, y))) ∧
    ¬ ContinuousAt h (0, 0)

end Specs.D10Topology.Ch03.ProductCounterexamples
