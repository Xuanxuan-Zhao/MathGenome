import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.AutonomousParameters

/-!
Independent specification for paper.tex, Chapter 3, d13:03:lipschitz.

The ODE objects already contain openness of the actual domain and continuity
of the field. The additional property below is local in the state, uniformly
in time (and, for a parameter-dependent field, in nearby parameters).
All radii are strictly positive; the constant is finite and nonnegative.
The full product neighborhood must be contained in the original domain,
so evaluation outside that domain never affects these predicates.

Open balls form neighborhood bases for the norm topologies in the source.
Thus using balls here describes exactly the stated product neighborhoods.
The definitions work on any real normed state and parameter spaces, in
particular every finite-dimensional space with any fixed norm, including
dimension zero. No completeness or positive-dimension assumption is used.
-/

noncomputable section

open Set Metric

namespace Specs.D13Unified.Ch03.LocalLipschitz

open _root_.D13Unified
open Specs.D13Unified.Ch01.AutonomousParameters

universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The common state-difference estimate, with a single constant valid for
every time in `T` and every pair of states in `B`. -/
def stateLipschitzOnValue (f : ℝ → E → E) (T : Set ℝ) (B : Set E)
    (L : ℝ) : Prop :=
  ∀ t ∈ T, ∀ x ∈ B, ∀ y ∈ B, ‖f t x - f t y‖ ≤ L * ‖x - y‖

/-- Each admissible time-state point has an actual controlled product
neighborhood. Its radii and constant may depend on the center. -/
def locallyLipschitzInStateValue (F : ODE E) : Prop :=
  ∀ s ξ, (s, ξ) ∈ F.domain →
    ∃ a b L : ℝ, 0 < a ∧ 0 < b ∧ 0 ≤ L ∧
      ball s a ×ˢ ball ξ b ⊆ F.domain ∧
      stateLipschitzOnValue F.eval (ball s a) (ball ξ b) L

/-- The same estimate is uniform also over a whole parameter neighborhood.
It compares states at the same parameter, without requiring a Lipschitz
estimate for parameter differences. Triples retain the upstream association
`((t,x),p)` and the joint domain need not be a product globally. -/
def parameterLocallyLipschitzInStateValue (F : ParameterODE E P) : Prop :=
  ∀ s ξ p, ((s, ξ), p) ∈ F.domain →
    ∃ a b c L : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 ≤ L ∧
      (ball s a ×ˢ ball ξ b) ×ˢ ball p c ⊆ F.domain ∧
      ∀ q ∈ ball p c,
        stateLipschitzOnValue (fun t x => parameterEvalValue F t x q)
          (ball s a) (ball ξ b) L

/- Closed expected types expose every space and normed-space instance. -/

def stateLipschitzOnExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E],
    (ℝ → E → E) → Set ℝ → Set E → ℝ → Prop

def locallyLipschitzInStateExpectedType : Type (u + 1) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E], ODE E → Prop

def parameterLocallyLipschitzInStateExpectedType : Type (max (u + 1) (v + 1)) :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P],
    ParameterODE E P → Prop

/-- Fixing the parameter retains the ordinary predicate on the actual slice. -/
def atParameterExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F : ParameterODE E P),
    parameterLocallyLipschitzInStateValue F → ∀ p : P,
      locallyLipschitzInStateValue (atParameterValue F p)

end Specs.D13Unified.Ch03.LocalLipschitz
