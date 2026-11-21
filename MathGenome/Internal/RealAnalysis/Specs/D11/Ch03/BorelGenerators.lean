import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-! Independent statements for paper.tex:771–800. The ambient space has the
Euclidean `ℓ²` norm. Boxes are products of bounded real intervals, and rational
boxes have rational endpoints. All sigma-algebras here are Borel structures,
without completion. The native `borel` and `generateFrom` are the canonical
objects of Chapter 1. -/

open Set MeasurableSpace

namespace D11.Ch03.BorelGenerators

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- All coordinate boxes with each side drawn from `C`. -/
def boxes (d : ℕ) (C : Set (Set ℝ)) : Set (Set (Space d)) :=
  {s | ∃ U : Fin d → Set ℝ, (∀ i, U i ∈ C) ∧ s = {x | ∀ i, x i ∈ U i}}

def rationalOpenIntervals : Set (Set ℝ) :=
  ⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) (b : ℝ)}

def leftClosedIntervals : Set (Set ℝ) :=
  {s | ∃ a b : ℝ, a < b ∧ Ico a b = s}

def rightClosedIntervals : Set (Set ℝ) :=
  {s | ∃ a b : ℝ, a < b ∧ Ioc a b = s}

def rationalOpenBoxes (d : ℕ) := boxes d rationalOpenIntervals

def leftClosedBoxes (d : ℕ) := boxes d leftClosedIntervals

def rightClosedBoxes (d : ℕ) := boxes d rightClosedIntervals

def rationalCoordinateHalfspaces (d : ℕ) : Set (Set (Space d)) :=
  {s | ∃ (j : Fin d) (q : ℚ), s = {x | x j ≤ (q : ℝ)}}

end D11.Ch03.BorelGenerators

namespace Specs.D11.Ch03.BorelGenerators

open _root_.D11.Ch03.BorelGenerators

def euclideanBorel_type := (d : ℕ) → MeasurableSpace (Space d)
def euclideanBorel_value : euclideanBorel_type := fun d => borel (Space d)

def borel_open : Prop := ∀ d : ℕ, 0 < d →
  borel (Space d) = generateFrom {s : Set (Space d) | IsOpen s}

def rational_open_boxes : Prop := ∀ d : ℕ, 0 < d →
  borel (Space d) = generateFrom (rationalOpenBoxes d)

def left_closed_boxes : Prop := ∀ d : ℕ, 0 < d →
  borel (Space d) = generateFrom (leftClosedBoxes d)

def right_closed_boxes : Prop := ∀ d : ℕ, 0 < d →
  borel (Space d) = generateFrom (rightClosedBoxes d)

def rational_coordinate_halfspaces : Prop := ∀ d : ℕ, 0 < d →
  borel (Space d) = generateFrom (rationalCoordinateHalfspaces d)

def real_open_intervals : Prop :=
  borel ℝ = generateFrom {s : Set ℝ | ∃ a b : ℝ, a < b ∧ Ioo a b = s}

def real_closed_intervals : Prop :=
  borel ℝ = generateFrom {s : Set ℝ | ∃ a b : ℝ, a ≤ b ∧ Icc a b = s}

def real_left_closed_intervals : Prop :=
  borel ℝ = generateFrom leftClosedIntervals

def real_right_closed_intervals : Prop :=
  borel ℝ = generateFrom rightClosedIntervals

def real_left_open_rays : Prop := borel ℝ = generateFrom (range (Iio : ℝ → Set ℝ))
def real_right_open_rays : Prop := borel ℝ = generateFrom (range (Ioi : ℝ → Set ℝ))
def real_left_closed_rays : Prop := borel ℝ = generateFrom (range (Iic : ℝ → Set ℝ))
def real_right_closed_rays : Prop := borel ℝ = generateFrom (range (Ici : ℝ → Set ℝ))

end Specs.D11.Ch03.BorelGenerators
