import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import Mathlib.Topology.GDelta.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-! Independent specification of the prescribed-mass conclusion in
paper.tex:1025–1061. The real line is represented by the project's Euclidean
`Point 1`; its unit interval is the closed coordinate box from 0 to 1.
The measure in the conclusion is the full Carathéodory Lebesgue measure.
The expected construction removes a small open neighborhood of a countable
dense set and rescales the closed remainder. Its definition uses only library
existence results for dense sets and outer approximation, not the conclusion. -/

noncomputable section

open Set MeasureTheory
open scoped Pointwise

namespace Specs.D11.Ch03.FatCantor

open _root_.D11.Ch03

/-- Fix a countable dense set in the Euclidean real line. -/
def denseSet : Set (Point 1) :=
  Classical.choose (TopologicalSpace.exists_countable_dense (Point 1))

/-- Outer approximation of the null dense set with the prescribed small cost. -/
theorem smallOpen_exists (α : ℝ) (hα1 : α < 1) :
    ∃ U : Set (Point 1), denseSet ⊆ U ∧ IsOpen U ∧
      volume U < ENNReal.ofReal (1 - α) := by
  have hDc := (Classical.choose_spec
    (TopologicalSpace.exists_countable_dense (Point 1))).1
  have hDz : volume denseSet = 0 := hDc.measure_zero volume
  apply denseSet.exists_isOpen_lt_of_lt
  rw [hDz]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hα1)

def smallOpen (α : ℝ) (hα1 : α < 1) : Set (Point 1) :=
  Classical.choose (smallOpen_exists α hα1)

def precursor (α : ℝ) (hα1 : α < 1) : Set (Point 1) :=
  closedBox (fun _ => 0) (fun _ => 1) \ smallOpen α hα1

def fatCantor_type := (α : ℝ) → 0 < α → α < 1 → Set (Point 1)

def fatCantor_value : fatCantor_type := fun α _ hα1 =>
  (α / (volume (precursor α hα1)).toReal) • precursor α hα1

def fatCantor_properties : Prop :=
  ∀ (α : ℝ) (hα : 0 < α) (hα1 : α < 1),
    let C := fatCantor_value α hα hα1
    C ⊆ closedBox (fun _ => 0) (fun _ => 1) ∧
      IsClosed C ∧ IsNowhereDense C ∧
      MeasurableSet[LebesgueMeasures.lebesgueSpace_value 1] C ∧
      LebesgueMeasures.lebesgue_value 1 C = ENNReal.ofReal α

def exists_fatCantor : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 →
    ∃ C : Set (Point 1),
      C ⊆ closedBox (fun _ => 0) (fun _ => 1) ∧
      IsClosed C ∧ IsNowhereDense C ∧
      MeasurableSet[LebesgueMeasures.lebesgueSpace_value 1] C ∧
      LebesgueMeasures.lebesgue_value 1 C = ENNReal.ofReal α

end Specs.D11.Ch03.FatCantor
