import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.AdaptedNorm
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch15.DiscreteDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Independent statement of paper.tex, Theorem `d13:15:linearized-stability`.
The open set `U` is the actual domain. A total function represents an arbitrary
extension of the map outside `U`; the conclusion keeps every iterate inside `U`,
so it applies to the original partially defined iteration. The norm in every
estimate and in the stability predicates is the given original norm.
The arbitrary basis computes the spectrum after complexification and imposes
no diagonalizability or positive-dimension restriction. -/
noncomputable section
open Module
open scoped Topology Matrix.Norms.Operator
namespace Specs.D13Unified.Ch15.LinearizedStability
open _root_.D13Unified.Ch08.MatrixPowerCriteria
open Specs.D13Unified.Ch15.DiscreteDefinitions

/-- Linearized attraction, quantitative domain control and both stability consequences. -/
def linearizedAttraction : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d : ℕ} (b : Basis (Fin d) ℝ E) (F : E → E) (U : Set E) (p : E),
    IsOpen U → p ∈ U → ContDiffOn ℝ 1 F U → F p = p →
    spectralRadius ℂ (complexify (LinearMap.toMatrix b b (fderiv ℝ F p).toLinearMap)) < 1 →
    (∃ C : ℝ, 0 < C ∧ ∃ q : ℝ, 0 < q ∧ q < 1 ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, ‖x - p‖ < δ → ∀ n : ℕ,
        F^[n] x ∈ U ∧ ‖F^[n] x - p‖ ≤ C * q ^ n * ‖x - p‖) ∧
    LocallyExponentiallyStable F p ∧ LyapunovStable F p ∧ AsymptoticallyStable F p

end Specs.D13Unified.Ch15.LinearizedStability
