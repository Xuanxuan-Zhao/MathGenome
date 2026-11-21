import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.PerronFixedPoints
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Independent specification of paper.tex, Lemma d13:20:perron, including
regularity in the infinite-time weighted norm. No proof implementation is
imported, and none of the conclusions is an assumed certificate. -/
noncomputable section
open Set MeasureTheory

namespace Specs.D13Unified.Ch20.PerronRegularity
open _root_.D13Unified.Ch20 _root_.D13Unified.Ch07
open Specs.D13Unified.Ch20.HyperbolicSplitting
open Specs.D13Unified.Ch20.PerronFixedPoints
universe u v

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual stable spectral subspace in the chosen normed state space. -/
def stableParameters (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) : Submodule ℝ E :=
  (stableSpaceValue A).comap b.equivFun.toLinearMap

/-- Boundedness and uniform continuity of precisely the positive-order
 derivatives allowed by the regularity order. Unlike compact support, this
 does not unnecessarily require boundedness of the remainder itself. -/
def regularDerivatives (k : ℕ∞) (r : E → E) : Prop :=
  ∀ j : ℕ, 1 ≤ j → (j : ℕ∞) ≤ k →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ j r x‖ ≤ C) ∧
    UniformContinuous (iteratedFDeriv ℝ j r)

/-- Pointwise identity for the nonlinear integral operator, with convergence
of both integrals required explicitly. -/
def NonlinearOperator (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (r : E → E) (β : ℝ) (N : WeightedPath β E → WeightedPath β E) : Prop :=
  ∀ w : WeightedPath β E, ∀ t : ℝ, 0 ≤ t →
    IntervalIntegrable (kernel b A r β w true t) volume 0 t ∧
    IntegrableOn (kernel b A r β w false t) (Ici t) ∧
    (N w).atReal t =
      (∫ s in (0 : ℝ)..t, kernel b A r β w true t s) -
      ∫ s in Ici t, kernel b A r β w false t s

/-- The full fixed-point properties retained for the selected family. -/
def SolutionFamily (b : Module.Basis n ℝ E) (A : Matrix n n ℝ)
    (r : E → E) (K α β δ : ℝ)
    (W : stableParameters b A → WeightedPath β E) : Prop :=
  ∀ ξ : stableParameters b A,
    PerronEquation b A r β (ξ : E) (W ξ) ∧
    (∀ v : WeightedPath β E, PerronEquation b A r β (ξ : E) v → v = W ξ) ∧
    (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (W ξ).atReal
      (matrixOperatorEquiv b A ((W ξ).atReal t) + r ((W ξ).atReal t)) (Ici 0) t) ∧
    projection b A true ((W ξ).atReal 0) = (ξ : E) ∧
    ‖W ξ‖ ≤ K * ‖(ξ : E)‖ / (1 - contractionRate K α β δ)

/-- Full original regularity target.
Both finite orders and C∞ are included. The `ContDiff` assertions are on the
weighted normed space itself, not pointwise assertions at fixed finite time. -/
def regularityExpected : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ), hyperbolicValue A →
    ∀ K α β δ : ℝ, 1 ≤ K → 0 < α → dichotomyBounds b A K α →
      0 < β → β < α → 0 ≤ δ → contractionRate K α β δ < 1 →
      ∀ (r : E → E) (k : ℕ∞),
      r 0 = 0 → (∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖) →
      1 ≤ k → ContDiff ℝ k r → regularDerivatives k r →
      ∃ (N : WeightedPath β E → WeightedPath β E)
        (W : stableParameters b A → WeightedPath β E),
        NonlinearOperator b A r β N ∧
        ContDiff ℝ k N ∧
        (∀ w, ‖fderiv ℝ N w‖ ≤ contractionRate K α β δ) ∧
        (∀ w, ∃ J : WeightedPath β E ≃L[ℝ] WeightedPath β E,
          J.toContinuousLinearMap = ContinuousLinearMap.id ℝ _ - fderiv ℝ N w ∧
          ‖J.symm.toContinuousLinearMap‖ ≤ (1 - contractionRate K α β δ)⁻¹) ∧
        ContDiff ℝ k W ∧ SolutionFamily b A r K α β δ W

end Specs.D13Unified.Ch20.PerronRegularity
