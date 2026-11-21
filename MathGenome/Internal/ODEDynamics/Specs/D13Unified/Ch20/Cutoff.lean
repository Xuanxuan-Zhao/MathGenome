import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Independent types for paper.tex, Lemma d13:20:cutoff.
The order `k : ℕ∞` includes all finite orders and smoothness, but does not
include analyticity. The state space has an arbitrary finite-dimensional
real norm. The original field need only be regular on its actual open
neighborhood of zero. Ambient values outside this set are immaterial. -/
noncomputable section
open Set
open scoped NNReal

namespace Specs.D13Unified.Ch20.Cutoff
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Boundedness and uniform continuity of each derivative that exists under
the stated regularity. Order zero is included. -/
def ControlledDerivatives (k : ℕ∞) (r : E → E) : Prop :=
  ∀ j : ℕ, (j : ℕ∞) ≤ k →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ C) ∧
    UniformContinuous (iteratedFDeriv ℝ j r)

/-- A complete continuous flow, with its actual differential equation and
group law for all real times, including negative times. -/
def HasCompleteFlow (v : E → E) : Prop :=
  ∃ φ : ℝ → E → E,
    Continuous (Function.uncurry φ) ∧
    (∀ x, φ 0 x = x) ∧
    (∀ t s x, φ (t + s) x = φ t (φ s x)) ∧
    (∀ x t, HasDerivAt (fun s => φ s x) (v (φ t x)) t)

def cutoffExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (U : Set E) (f : E → E)
    (A : E →L[ℝ] E) (k : ℕ∞),
    IsOpen U → (0 : E) ∈ U → 1 ≤ k → ContDiffOn ℝ k f U →
    f 0 = 0 → HasFDerivAt f A 0 →
    ∀ δ : ℝ, 0 < δ → ∃ r : E → E,
      ContDiff ℝ k r ∧ HasCompactSupport r ∧
      r 0 = 0 ∧ HasFDerivAt r (0 : E →L[ℝ] E) 0 ∧
      (∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖) ∧
      (∃ V : Set E, IsOpen V ∧ (0 : E) ∈ V ∧ V ⊆ U ∧
        ∀ x ∈ V, A x + r x = f x) ∧
      ControlledDerivatives k r ∧ HasCompleteFlow (fun x => A x + r x)

def controlledDerivativesExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ∞) (r : E → E), ContDiff ℝ k r → HasCompactSupport r →
      ControlledDerivatives k r

def completeFlowExpected : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (v : E → E) (K : ℝ≥0),
    LipschitzWith K v → HasCompleteFlow v

end Specs.D13Unified.Ch20.Cutoff
