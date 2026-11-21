import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.GreenAreaBridge

/-! Theorem v07-08-02. The area is Lebesgue area of the bounded
Jordan component, and the length is the polygonal geometric length of
the original embedding. The equality condition concerns only its image. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Specs.VariationalNotes.Classical.IsoperimetricInequality
open Specs.D13Unified.Ch21.Collar
open Specs.D13Unified.Ch21.SmoothJordan
open Specs.VariationalNotes.Classical.GreenAreaBridge

/-- A circle of strictly positive radius, irrespective of parametrization. -/
def IsCircle (c : Circle → ℂ) : Prop :=
  ∃ (z : ℂ) (r : ℝ), 0 < r ∧ range c = Metric.sphere z r

/-- The bounded interior, its actual area and length, the sharp estimate,
and both directions of its geometric equality characterization. -/
def Statement : Prop :=
  ∀ (c : Circle → ℂ), RegularEmbeddedLoop c → ∃ (Ω E : Set ℂ) (T : ℝ),
    TwoComponents (range c)ᶜ Ω E ∧ IsOpen Ω ∧ IsOpen E ∧
    IsPathConnected Ω ∧ IsPathConnected E ∧
    Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded E ∧
    frontier Ω = range c ∧ frontier E = range c ∧
    closure Ω = Ω ∪ range c ∧ HasC1Boundary Ω ∧
    0 < volume Ω ∧ volume Ω < ⊤ ∧ 0 < area Ω ∧
    0 < T ∧ curveLength c = ENNReal.ofReal T ∧
    4 * Real.pi * area Ω ≤ T ^ 2 ∧
    (4 * Real.pi * area Ω = T ^ 2 ↔ IsCircle c)

end Specs.VariationalNotes.Classical.IsoperimetricInequality
