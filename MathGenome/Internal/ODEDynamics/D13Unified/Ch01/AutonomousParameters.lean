import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.SolutionConcepts
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.AutonomousParameters

/-! Autonomous and parameter-dependent equations (paper.tex, d13:01:autonomous).
All solution predicates retain the original interval, graph-domain condition,
regularity, and equation. A parameter is a single fixed value, not a curve.
No solution map is selected here: existence and uniqueness are later results.
-/

noncomputable section
open Set

namespace D13Unified
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]

open Specs.D13Unified.Ch01.AutonomousParameters

def AutonomousODE.eval : AutonomousODE E → E → E := autonomousEvalValue

def ParameterODE.eval : ParameterODE E P → ℝ → E → P → E := parameterEvalValue

def AutonomousODE.toODE : AutonomousODE E → ODE E := autonomousToODEValue

def ParameterODE.atParameter : ParameterODE E P → P → ODE E := atParameterValue

def IsAutonomousSolutionOn : AutonomousODE E → TimeInterval → (ℝ → E) → Prop := autonomousSolutionOnValue

def IsClassicalAutonomousSolutionOn : AutonomousODE E → OpenTimeInterval → (ℝ → E) → Prop := classicalAutonomousSolutionOnValue

def IsAutonomousIVPOn : AutonomousODE E → TimeInterval → (ℝ → E) → ℝ → E → Prop := autonomousIVPOnValue

def IsClassicalAutonomousIVPOn : AutonomousODE E → OpenTimeInterval → (ℝ → E) → ℝ → E → Prop := classicalAutonomousIVPOnValue

def IsParameterSolutionOn : ParameterODE E P → P → TimeInterval → (ℝ → E) → Prop := parameterSolutionOnValue

def IsClassicalParameterSolutionOn : ParameterODE E P → P → OpenTimeInterval → (ℝ → E) → Prop := classicalParameterSolutionOnValue

def IsParameterIVPOn : ParameterODE E P → P → TimeInterval → (ℝ → E) → ℝ → E → Prop := parameterIVPOnValue

def IsClassicalParameterIVPOn : ParameterODE E P → P → OpenTimeInterval → (ℝ → E) → ℝ → E → Prop := classicalParameterIVPOnValue

/-- The autonomous conversion preserves exactly the state domain. -/
@[simp] theorem AutonomousODE.mem_toODE_domain (F : AutonomousODE E) (t : ℝ) (x : E) :
    (t, x) ∈ F.toODE.domain ↔ x ∈ F.domain := Iff.rfl

@[simp] theorem AutonomousODE.toODE_eval (F : AutonomousODE E) (t : ℝ) (x : E) :
    F.toODE.eval t x = F.eval x := by
  rfl

/-- At parameter `p`, admissibility is exactly membership in the original joint
open domain. In particular, a varying slice is never replaced by a product. -/
@[simp] theorem ParameterODE.mem_atParameter_domain (F : ParameterODE E P)
    (p : P) (t : ℝ) (x : E) :
    (t, x) ∈ (F.atParameter p).domain ↔ ((t, x), p) ∈ F.domain := Iff.rfl

@[simp] theorem ParameterODE.atParameter_eval (F : ParameterODE E P)
    (p : P) (t : ℝ) (x : E) :
    (F.atParameter p).eval t x = F.eval t x p := by
  rfl

theorem autonomousSolutionOn_iff (F : AutonomousODE E) (I : TimeInterval) (x : ℝ → E) :
    IsAutonomousSolutionOn F I x ↔
      IsSolutionOn (F.toODE) I x := by
  rfl

theorem autonomousIVPOn_iff (F : AutonomousODE E) (I : TimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E) :
    IsAutonomousIVPOn F I x s ξ ↔
      IsIVPOn (F.toODE) I x s ξ := by
  exact and_congr_left fun _ => autonomousSolutionOn_iff F I x

theorem classicalAutonomousSolutionOn_iff (F : AutonomousODE E) (I : OpenTimeInterval) (x : ℝ → E) :
    IsClassicalAutonomousSolutionOn F I x ↔
      IsClassicalSolutionOn (F.toODE) I x := by
  rfl

theorem classicalAutonomousIVPOn_iff (F : AutonomousODE E) (I : OpenTimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E) :
    IsClassicalAutonomousIVPOn F I x s ξ ↔
      IsClassicalIVPOn (F.toODE) I x s ξ := by
  exact and_congr_left fun _ => classicalAutonomousSolutionOn_iff F I x

theorem parameterSolutionOn_iff (F : ParameterODE E P) (p : P) (I : TimeInterval) (x : ℝ → E) :
    IsParameterSolutionOn F p I x ↔
      IsSolutionOn (F.atParameter p) I x := by
  rfl

theorem parameterIVPOn_iff (F : ParameterODE E P) (p : P) (I : TimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E) :
    IsParameterIVPOn F p I x s ξ ↔
      IsIVPOn (F.atParameter p) I x s ξ := by
  exact and_congr_left fun _ => parameterSolutionOn_iff F p I x

theorem classicalParameterSolutionOn_iff (F : ParameterODE E P) (p : P) (I : OpenTimeInterval) (x : ℝ → E) :
    IsClassicalParameterSolutionOn F p I x ↔
      IsClassicalSolutionOn (F.atParameter p) I x := by
  rfl

theorem classicalParameterIVPOn_iff (F : ParameterODE E P) (p : P) (I : OpenTimeInterval) (x : ℝ → E) (s : ℝ) (ξ : E) :
    IsClassicalParameterIVPOn F p I x s ξ ↔
      IsClassicalIVPOn (F.atParameter p) I x s ξ := by
  exact and_congr_left fun _ => classicalParameterSolutionOn_iff F p I x

/-- The initial datum belongs to the same joint domain, at the fixed parameter. -/
theorem IsParameterIVPOn.initial_mem {F : ParameterODE E P} {p : P}
    {I : TimeInterval} {x : ℝ → E} {s : ℝ} {ξ : E}
    (h : IsParameterIVPOn F p I x s ξ) : ((s, ξ), p) ∈ F.domain := by
  have hg := h.1.2.1 s h.2.1
  simpa only [h.2.2] using hg

/-- On open intervals the classical and endpoint-aware descriptions agree. -/
theorem classicalAutonomous_iff_solutionOn (F : AutonomousODE E)
    (I : OpenTimeInterval) (x : ℝ → E) :
    IsClassicalAutonomousSolutionOn F I x ↔
      IsAutonomousSolutionOn F I.toTimeInterval x :=
  (classicalAutonomousSolutionOn_iff F I x).trans
    ((classical_iff_solutionOn F.toODE I x).trans
      (autonomousSolutionOn_iff F I.toTimeInterval x).symm)

theorem classicalParameter_iff_solutionOn (F : ParameterODE E P) (p : P)
    (I : OpenTimeInterval) (x : ℝ → E) :
    IsClassicalParameterSolutionOn F p I x ↔
      IsParameterSolutionOn F p I.toTimeInterval x :=
  (classicalParameterSolutionOn_iff F p I x).trans
    ((classical_iff_solutionOn (F.atParameter p) I x).trans
      (parameterSolutionOn_iff F p I.toTimeInterval x).symm)

end D13Unified
