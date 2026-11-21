import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.Bernstein
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
The open-half-line Bernstein theorem, `paper.tex`,
`fa2:p1:bernstein-open-half-line` (5597–5643).

The function really has domain `(0,∞)` and finite nonnegative values.
`realExtension` assigns zero outside that domain solely to use the ordinary
one-variable calculus API. Smoothness and derivative signs are tested only
on the open positive half-line, so this extension imposes no endpoint condition.
All representing measures are positive Borel measures on the finite rate space;
no finiteness or sigma-finiteness assumption is imposed on them.
-/
noncomputable section
namespace ExpandedFA.P1.BernsteinOpenHalfLine
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

abbrev PositiveTime := Ioi (0 : ℝ)
abbrev OpenFunction := PositiveTime → ℝ≥0

def realExtension (f : OpenFunction) (t : ℝ) : ℝ :=
  if ht : 0 < t then (f ⟨t, ht⟩ : ℝ) else 0

def advance (t : PositiveTime) (h : ℝ≥0) : PositiveTime :=
  ⟨t.val + h, add_pos_of_pos_of_nonneg t.property h.coe_nonneg⟩

/-- The alternating sign is built into the independent forward differences. -/
def openDifference : List ℝ≥0 → OpenFunction → PositiveTime → ℝ
  | [], f, t => f t
  | h :: hs, f, t => openDifference hs f t - openDifference hs f (advance t h)

def FiniteDifferenceCondition (f : OpenFunction) : Prop :=
  ∀ hs : List ℝ≥0, (∀ h ∈ hs, 0 < h) → ∀ t, 0 ≤ openDifference hs f t

def SmoothCondition (f : OpenFunction) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (realExtension f) (Ioi 0) ∧
    ∀ (m : ℕ) (t : ℝ), 0 < t → 0 ≤ (-1 : ℝ) ^ m * iteratedDeriv m (realExtension f) t

def openKernel (t : ℝ) (rate : ℝ≥0) : ℝ := Real.exp (-(rate : ℝ) * t)

def openLaplaceTransform (ν : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ rate, openKernel t rate ∂ν

/-- Integrability is explicit: a Bochner integral alone does not assert finiteness. -/
def Represents (f : OpenFunction) (ν : Measure ℝ≥0) : Prop :=
  (∀ t : PositiveTime, Integrable (openKernel t.val) ν) ∧
  ∀ t : PositiveTime, (f t : ℝ) = openLaplaceTransform ν t.val

def FiniteAtZero (f : OpenFunction) : Prop :=
  ∃ L : ℝ≥0, Tendsto (realExtension f) (𝓝[>] (0 : ℝ)) (𝓝 (L : ℝ))

end ExpandedFA.P1.BernsteinOpenHalfLine

namespace Specs.ExpandedFA.P1.BernsteinOpenHalfLine
open _root_.ExpandedFA.P1.BernsteinOpenHalfLine Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

/-- All three source conditions, including uniqueness among arbitrary measures. -/
def Equivalence : Prop :=
  ∀ f : OpenFunction,
    (FiniteDifferenceCondition f ↔ SmoothCondition f) ∧
    (FiniteDifferenceCondition f ↔ ∃! ν : Measure ℝ≥0, Represents f ν)

/-- Local finiteness is a conclusion, not an extra representation hypothesis. -/
def LocalFiniteness : Prop :=
  ∀ (f : OpenFunction) (ν : Measure ℝ≥0), Represents f ν →
    ∀ R : ℝ≥0, ν (Icc 0 R) < ∞

/-- The first limit includes infinite mass. The remaining clauses give the
finite-limit criterion and the exact mass whenever that limit is finite. -/
def EndpointMass : Prop :=
  ∀ (f : OpenFunction) (ν : Measure ℝ≥0), Represents f ν →
    Tendsto (fun t : ℝ => ENNReal.ofReal (realExtension f t))
      (𝓝[>] (0 : ℝ)) (𝓝 (ν univ)) ∧
    (IsFiniteMeasure ν ↔ FiniteAtZero f) ∧
    ∀ L : ℝ≥0, Tendsto (realExtension f) (𝓝[>] (0 : ℝ)) (𝓝 (L : ℝ)) →
      ν univ = (L : ℝ≥0∞)

end Specs.ExpandedFA.P1.BernsteinOpenHalfLine
