import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.AutonomousParameters
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.LocalLipschitz

/-!
Local Lipschitz control in the state (paper.tex, d13:03:lipschitz).
Continuity and the open domain are carried by `ODE` and `ParameterODE`.
The predicates use the same state-difference estimate and retain the actual
domain. The existential neighborhood radii and constant occur after the
choice of center: no global Lipschitz constant is postulated.
-/

noncomputable section

open Set Metric

namespace D13Unified

universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]

open Specs.D13Unified.Ch03.LocalLipschitz

/-- State Lipschitz control on a specified time-state product with one
constant, shared by the ordinary and parameter-dependent local predicates. -/
def StateLipschitzOn (f : ℝ → E → E) (T : Set ℝ) (B : Set E) (L : ℝ) : Prop :=
  stateLipschitzOnValue f T B L

/-- Local state Lipschitz control uniformly in time on the actual open domain. -/
def ODE.LocallyLipschitzInState (F : ODE E) : Prop :=
  locallyLipschitzInStateValue F

/-- Local state Lipschitz control uniformly in both time and nearby parameters.
A parameter is held fixed in each state comparison. -/
def ParameterODE.LocallyLipschitzInState (F : ParameterODE E P) : Prop :=
  parameterLocallyLipschitzInStateValue F

/-- A uniformly controlled parameter family gives the common ordinary local
predicate at every fixed parameter, on exactly the original domain slice. -/
theorem ParameterODE.LocallyLipschitzInState.atParameter
    (F : ParameterODE E P) (h : F.LocallyLipschitzInState) (p : P) :
    (F.atParameter p).LocallyLipschitzInState := by
  intro s ξ hs
  obtain ⟨a, b, c, L, ha, hb, hc, hL, hdom, hbound⟩ := h s ξ p hs
  have hp : p ∈ ball p c := mem_ball_self hc
  refine ⟨a, b, L, ha, hb, hL, ?_, ?_⟩
  · intro tx htx
    exact hdom ⟨htx, hp⟩
  · exact hbound p hp

end D13Unified
