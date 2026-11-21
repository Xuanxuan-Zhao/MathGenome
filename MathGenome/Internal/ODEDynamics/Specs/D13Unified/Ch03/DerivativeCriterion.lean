import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch03.LocalLipschitz

/-!
Independent statements for paper.tex, d13:03:derivative-bound.
The quantitative assertion is stated for every convex state set, hence for
both open and closed state balls. Within derivatives suffice, a stronger
version of the source's continuously varying partial derivative hypothesis.
The other variables range over arbitrary specified sets and are held fixed
in each state comparison.

C¹ means jointly C¹ on the actual open domain, expressed using the canonical
ambient evaluation representative. Its values outside the domain impose no
condition. The conclusions are precisely the shared local predicates.
All statements allow arbitrary real normed spaces; this includes every
finite dimension, every fixed norm, and dimension zero.
-/

noncomputable section
open Set

namespace Specs.D13Unified.Ch03.DerivativeCriterion
open _root_.D13Unified
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch03.LocalLipschitz

universe u v

/-- Uniform partial derivative bound implies the quantitative state estimate.
No joint continuity is needed for this stronger form of the implication. -/
def derivativeBoundExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v}
    (f : ℝ → E → P → E) (D : ℝ → E → P → E →L[ℝ] E)
    (T : Set ℝ) (B : Set E) (Q : Set P) (L : ℝ),
    Convex ℝ B →
    (∀ t ∈ T, ∀ x ∈ B, ∀ p ∈ Q,
      HasFDerivWithinAt (fun y => f t y p) (D t x p) B x) →
    (∀ t ∈ T, ∀ x ∈ B, ∀ p ∈ Q, ‖D t x p‖ ≤ L) →
    ∀ p ∈ Q, stateLipschitzOnValue (fun t x => f t x p) T B L

/-- Joint C¹ regularity gives local state control uniformly in time. -/
def odeC1Expected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE E),
    ContDiffOn ℝ 1 (fun z : ℝ × E => F.eval z.1 z.2) F.domain →
    locallyLipschitzInStateValue F

/-- Joint C¹ regularity gives local state control uniformly also in parameters. -/
def parameterC1Expected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : ParameterODE E P),
    ContDiffOn ℝ 1
      (fun z : (ℝ × E) × P => parameterEvalValue F z.1.1 z.1.2 z.2) F.domain →
    parameterLocallyLipschitzInStateValue F

/-- The autonomous specialization uses the same time-state predicate. -/
def autonomousC1Expected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AutonomousODE E),
    ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    locallyLipschitzInStateValue (autonomousToODEValue F)

end Specs.D13Unified.Ch03.DerivativeCriterion
