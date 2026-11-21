import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Bounded

/-! Independent statements of the finite-dimensional examples in
`paper.tex`, “Why the hypotheses matter”, lines 4777–4782.
The real unit circle is expressed by its Euclidean coordinate equation;
ℝ × ℝ has its usual real vector space structure and product topology. -/

noncomputable section

namespace VariationalNotes.FixedPoints

/-- The Euclidean unit circle in the real plane. -/
def realUnitCircle : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 = 1}

/-- The antipodal rotation of the real plane. -/
def antipodal (p : ℝ × ℝ) : ℝ × ℝ := -p

/-- The open interval in the second example. -/
def openUnitInterval : Set ℝ := Set.Ioo 0 1

/-- The affine map whose unique ambient fixed point is the endpoint 1. -/
def intervalAffine (x : ℝ) : ℝ := (1 + x) / 2

end VariationalNotes.FixedPoints

namespace Specs.VariationalNotes.FixedPoints.FiniteBoundaryExamples

open _root_.VariationalNotes.FixedPoints

/-- The circle is nonempty and compact, but fails convexity. -/
def CircleGeometry : Prop :=
  realUnitCircle.Nonempty ∧ IsCompact realUnitCircle ∧ ¬ Convex ℝ realUnitCircle

/-- A continuous self-map of the circle with no fixed point on the circle. -/
def AntipodalProperties : Prop :=
  Continuous antipodal ∧ Set.MapsTo antipodal realUnitCircle realUnitCircle ∧
    ¬ ∃ p ∈ realUnitCircle, antipodal p = p

/-- The interval is nonempty, bounded, open and convex. -/
def IntervalGeometry : Prop :=
  openUnitInterval.Nonempty ∧ Bornology.IsBounded openUnitInterval ∧
    IsOpen openUnitInterval ∧ Convex ℝ openUnitInterval

/-- The affine map preserves the interval and is continuous. It has exactly
one ambient real fixed point, 1, and therefore none in the interval. -/
def IntervalProperties : Prop :=
  Continuous intervalAffine ∧ Set.MapsTo intervalAffine openUnitInterval openUnitInterval ∧
    (∀ x : ℝ, intervalAffine x = x ↔ x = 1) ∧
    ¬ ∃ x ∈ openUnitInterval, intervalAffine x = x

end Specs.VariationalNotes.FixedPoints.FiniteBoundaryExamples
