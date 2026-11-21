import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.QuotientMaps
import Mathlib.Topology.Instances.Rat

/-! The exact quotient and product in paper.tex, d10:03:quotient-product-failure.
The rationals have their metric topology induced by the inclusion into ℝ.
The quotient carries the final topology of the class map; products use the
standard product instances. No theorem about the product map is assumed. -/

open Set Topology

namespace D10Topology.Ch03.IntegerCollapse

/-- The strictly positive integers, viewed as real numbers. -/
def positiveIntegers : Set ℝ := {x | ∃ n : ℕ, x = (n : ℝ) + 1}

/-- Precisely one nonsingleton equivalence class is collapsed. -/
def collapseSetoid : Setoid ℝ where
  r x y := x = y ∨ (x ∈ positiveIntegers ∧ y ∈ positiveIntegers)
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by
      intro x y h
      exact h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
    trans := by
      intro x y z hxy hyz
      rcases hxy with rfl | ⟨hx, hy⟩
      · exact hyz
      rcases hyz with rfl | ⟨_, hz⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hz⟩ }

abbrev Space := Quotient collapseSetoid

instance : TopologicalSpace Space :=
  QuotientData.equivalenceQuotientTopology collapseSetoid

def q : ℝ → Space := Quotient.mk collapseSetoid

def productMap : ℝ × ℚ → Space × ℚ := Prod.map q id

end D10Topology.Ch03.IntegerCollapse

namespace Specs.D10Topology.Ch03.QuotientProductCounterexample
open _root_.D10Topology.Ch03.IntegerCollapse
open _root_.D10Topology.Ch03.QuotientData

/-- Explicitly records which points, and only which points, are identified. -/
def class_eq : Prop := ∀ x y : ℝ,
  q x = q y ↔ x = y ∨ (x ∈ positiveIntegers ∧ y ∈ positiveIntegers)

/-- Both factors are quotient; their displayed product, with its ordinary
product topology and rational subspace factor, is not quotient. -/
def counterexample : Prop :=
  QuotientMap q ∧ QuotientMap (id : ℚ → ℚ) ∧ ¬ QuotientMap productMap

end Specs.D10Topology.Ch03.QuotientProductCounterexample
