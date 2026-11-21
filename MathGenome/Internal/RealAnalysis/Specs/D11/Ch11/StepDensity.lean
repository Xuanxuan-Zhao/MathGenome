import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueMeasures
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.LinearAlgebra.Span.Defs

/-! Independent statements for paper.tex:3636–3654. The measure is the full
completed Euclidean Lebesgue measure fixed in Chapter 3. A rectangle has finite
real endpoints and the convention [a_j,b_j) in every coordinate. The span below
is the algebraic span, so its members are actual finite linear combinations.
`Lp` is the ordinary a.e. quotient, identified with the source quotient by the
upstream quotient-construction interface. Scalars include both ℝ and ℂ.
The restriction assertion holds on every measurable subset, in particular on
an interval in dimension one, with arbitrary endpoint conventions. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace D11.Ch11.StepDensity
open D11.Ch03

abbrev rectangle {d : ℕ} (a b : Fin d → ℝ) : Set (Point d) :=
  endpointBox a b (fun _ => true) (fun _ => false)

def rectangleSteps (d : ℕ) (𝕜 : Type*) [RCLike 𝕜] : Submodule 𝕜 (Point d → 𝕜) :=
  Submodule.span 𝕜 {g | ∃ (a b : Fin d → ℝ) (c : 𝕜),
    g = (rectangle a b).indicator (fun _ => c)}
end D11.Ch11.StepDensity

namespace Specs.D11.Ch11.StepDensity
open _root_.D11.Ch03 _root_.D11.Ch11.StepDensity
open Specs.D11.Ch03.LebesgueMeasures

def step_density : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    letI := lebesgueSpace_value d
    ∀ f : Lp 𝕜 p (lebesgue_value d), ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ rectangleSteps d 𝕜, ∃ hg : MemLp g p (lebesgue_value d),
        ‖f - hg.toLp g‖ < ε

/-- Restricting the approximating rectangle functions gives step functions on
any measurable domain. For d=1 this includes every bounded or unbounded interval,
empty intervals, and all choices of including its endpoints. -/
def restricted_step_density : Prop :=
  ∀ (d : ℕ) [NeZero d] (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    letI := lebesgueSpace_value d
    ∀ I : Set (Point d), MeasurableSet I →
    ∀ f : Lp 𝕜 p ((lebesgue_value d).restrict I), ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ rectangleSteps d 𝕜, ∃ hg : MemLp g p ((lebesgue_value d).restrict I),
        ‖f - hg.toLp g‖ < ε
end Specs.D11.Ch11.StepDensity
