import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.StableGraphs
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Flow

/-! Independent full statement of paper.tex, Theorem d13:20:stable-manifold.
Coordinates are centered at the arbitrary equilibrium p. Both half-line
characterizations quantify over actual original solutions and assume only
bounded confinement, never exponential decay. Canonical flow values are used
only together with membership in their actual maximal domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace Specs.D13Unified.Ch20.StableManifold
open _root_.D13Unified _root_.D13Unified.Ch20 _root_.D13Unified.Ch07
open _root_.D13Unified.Ch06.StateDerivative
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch20.HyperbolicSplitting
open Specs.D13Unified.Ch20.PerronFixedPoints
open Specs.D13Unified.Ch20.PerronRegularity
open Specs.D13Unified.Ch20.StableGraphs
universe u v
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Localization in one direction. σ=1 is forward time; σ=-1 is backward
 time. ψ is the corresponding elapsed-time extension flow. The last clause
 gives invariance along any original solution segment remaining in the ball,
 with all of its original existence-domain restrictions retained. -/
def LocalizedGraph (F : AutonomousODE E) (p : E) (σ : ℝ)
    (ψ : ℝ → E → E) {S T : Submodule ℝ E} (h : S → T)
    (ρ ε C β : ℝ) : Prop :=
  (∀ x : ℝ → E, ContinuousOn x (Ici 0) →
    (∀ t, 0 ≤ t → HasDerivWithinAt x (σ • (autonomousEvalValue F) (x t)) (Ici 0) t) →
    (∀ t, 0 ≤ t → ‖x t - p‖ < ρ) →
    x 0 - p ∈ Set.range (graphMap h)) ∧
  (∀ ξ : S, ‖(ξ : E)‖ < ε → ∀ t, 0 ≤ t →
    ‖ψ t (graphMap h ξ)‖ < ρ ∧
    (σ * t, p + graphMap h ξ) ∈ flowDomain F ∧
    flow F (σ * t) (p + graphMap h ξ) = p + ψ t (graphMap h ξ) ∧
    ‖flow F (σ * t) (p + graphMap h ξ) - p‖ ≤
      C * ‖(ξ : E)‖ * Real.exp (-β * t)) ∧
  (∀ x : ℝ → E, ∀ t, 0 ≤ t → ContinuousOn x (Icc 0 t) →
    (∀ s ∈ Icc 0 t, HasDerivWithinAt x (σ • (autonomousEvalValue F) (x s)) (Icc 0 t) s) →
    (∀ s ∈ Icc 0 t, ‖x s - p‖ < ρ) →
    x 0 - p ∈ Set.range (graphMap h) →
    x t - p ∈ Set.range (graphMap h))

/-- No spectral gap or contraction constant is an extra hypothesis: they and
 the extension, graphs, and local radii are constructed from hyperbolicity. -/
def stableManifoldExpected : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (F : AutonomousODE E) (p : E)
    (A : Matrix n n ℝ) (k : ℕ∞),
    p ∈ F.domain → 1 ≤ k → ContDiffOn ℝ k (autonomousEvalValue F) F.domain →
    (autonomousEvalValue F) p = 0 → HasFDerivAt (autonomousEvalValue F) (matrixOperatorEquiv b A) p → hyperbolicValue A →
    ∃ K α β δ ρ ε C : ℝ,
      1 ≤ K ∧ 0 < α ∧ dichotomyBounds b A K α ∧
      0 < β ∧ β < α ∧ 0 < δ ∧ contractionRate K α β δ < 1 ∧
      0 < ρ ∧ 0 < ε ∧ 0 < C ∧ C = K / (1 - contractionRate K α β δ) ∧
    ∃ (r : E → E) (φ : ℝ → E → E)
      (hs : stableParameters b A → unstableParameters b A)
      (hu : unstableParameters b A → stableParameters b A),
      ContDiff ℝ k r ∧ HasCompactSupport r ∧ r 0 = 0 ∧
      HasFDerivAt r (0 : E →L[ℝ] E) 0 ∧
      (∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖) ∧
      (∀ x, ‖x‖ < ρ → p + x ∈ F.domain ∧
        matrixOperatorEquiv b A x + r x = (autonomousEvalValue F) (p + x)) ∧
      CompleteFlow (fun x => matrixOperatorEquiv b A x + r x) φ ∧
      GraphGeometry k (stableParameters b A) (unstableParameters b A) hs ∧
      GraphGeometry k (unstableParameters b A) (stableParameters b A) hu ∧
      (∀ ξ t, 0 ≤ t → φ t (graphMap hs ξ) ∈ Set.range (graphMap hs)) ∧
      (∀ η t, t ≤ 0 → φ t (graphMap hu η) ∈ Set.range (graphMap hu)) ∧
      (∀ ξ t, 0 ≤ t → ‖φ t (graphMap hs ξ)‖ ≤ C * ‖(ξ : E)‖ * Real.exp (-β * t)) ∧
      (∀ η t, t ≤ 0 → ‖φ t (graphMap hu η)‖ ≤ C * ‖(η : E)‖ * Real.exp (β * t)) ∧
      LocalizedGraph F p 1 φ hs ρ ε C β ∧
      LocalizedGraph F p (-1) (fun t x => φ (-t) x) hu ρ ε C β
end Specs.D13Unified.Ch20.StableManifold
