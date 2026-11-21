import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.PerronRegularity
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.Cutoff
import Mathlib.Topology.Maps.Basic

/-! Independent interface for the global extension graphs in
paper.tex, Theorem d13:20:stable-manifold. The local characterization of
bounded original trajectories belongs to the separately allocated goal.
An embedded manifold is expressed by its global Cᵏ parametrization: it is
a closed topological embedding with injective differential at every point.
Its model space is the actual spectral subspace, including the zero space. -/
noncomputable section
open Set Topology
open scoped ContDiff

namespace Specs.D13Unified.Ch20.StableGraphs
open _root_.D13Unified.Ch20 _root_.D13Unified.Ch07
open Specs.D13Unified.Ch20.HyperbolicSplitting
open Specs.D13Unified.Ch20.PerronFixedPoints
open Specs.D13Unified.Ch20.PerronRegularity
universe u v
variable {n : Type u} [Fintype n] [DecidableEq n]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def unstableParameters (b : Module.Basis n ℝ E) (A : Matrix n n ℝ) : Submodule ℝ E :=
  (unstableSpaceValue A).comap b.equivFun.toLinearMap

def graphMap {S T : Submodule ℝ E} (h : S → T) (ξ : S) : E :=
  (ξ : E) + (h ξ : E)

/-- Global embedding, regularity, and the exact tangent space at zero.
The derivative into the complementary space is zero, while the derivative
of the parametrization at zero is the original subspace inclusion. -/
def GraphGeometry (k : ℕ∞) (S T : Submodule ℝ E) (h : S → T) : Prop :=
  ContDiff ℝ k h ∧ h 0 = 0 ∧ HasFDerivAt h (0 : S →L[ℝ] T) 0 ∧
  ContDiff ℝ k (graphMap h) ∧ IsClosedEmbedding (graphMap h) ∧
  (∀ ξ, Function.Injective (fderiv ℝ (graphMap h) ξ)) ∧
  HasFDerivAt (graphMap h) S.subtypeL 0

/-- Stable graph construction, with the complete Perron family retained.
This separately useful static construction is part of the original goal;
invariance and the unstable graph are additional obligations below. -/
def stableGeometryExpected : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (A : Matrix n n ℝ), hyperbolicValue A →
    ∀ K α β δ : ℝ, 1 ≤ K → 0 < α → dichotomyBounds b A K α →
      0 < β → β < α → 0 ≤ δ → contractionRate K α β δ < 1 →
      ∀ (r : E → E) (k : ℕ∞),
      r 0 = 0 → HasFDerivAt r (0 : E →L[ℝ] E) 0 →
      (∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖) →
      1 ≤ k → ContDiff ℝ k r → regularDerivatives k r →
      ∃ (h : stableParameters b A → unstableParameters b A)
        (W : stableParameters b A → WeightedPath β E),
        GraphGeometry k (stableParameters b A) (unstableParameters b A) h ∧
        ContDiff ℝ k W ∧ SolutionFamily b A r K α β δ W ∧
        (∀ ξ, (W ξ).atReal 0 = graphMap h ξ) ∧
        (∀ ξ t, 0 ≤ t → ‖(W ξ).atReal t‖ ≤
          (K / (1 - contractionRate K α β δ)) * ‖(ξ : E)‖ * Real.exp (-β * t))

/-- A particular complete flow, retaining both signs of time and its actual ODE. -/
def CompleteFlow (v : E → E) (φ : ℝ → E → E) : Prop :=
  Continuous (Function.uncurry φ) ∧ (∀ x, φ 0 x = x) ∧
  (∀ t s x, φ (t + s) x = φ t (φ s x)) ∧
  (∀ x t, HasDerivAt (fun s => φ s x) (v (φ t x)) t)

/-- The full assigned extension-graph conclusion. Coordinates have been
centered at the arbitrary equilibrium p; the equality on V below explicitly
relates the extension to the original field on its actual open domain.
The quantitative assertions use the selected K, α, β, δ without weakening C. -/
def stableGraphsExpected : Prop :=
  ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Module.Basis n ℝ E) (U : Set E) (f : E → E) (p : E)
    (A : Matrix n n ℝ) (k : ℕ∞),
    IsOpen U → p ∈ U → 1 ≤ k → ContDiffOn ℝ k f U →
    f p = 0 → HasFDerivAt f (matrixOperatorEquiv b A) p → hyperbolicValue A →
    ∀ K α β δ : ℝ, 1 ≤ K → 0 < α → dichotomyBounds b A K α →
      0 < β → β < α → 0 < δ → contractionRate K α β δ < 1 →
      ∃ (r : E → E) (φ : ℝ → E → E)
        (hs : stableParameters b A → unstableParameters b A)
        (hu : unstableParameters b A → stableParameters b A),
        ContDiff ℝ k r ∧ HasCompactSupport r ∧ r 0 = 0 ∧
        HasFDerivAt r (0 : E →L[ℝ] E) 0 ∧
        (∀ x y, ‖r x - r y‖ ≤ δ * ‖x - y‖) ∧
        (∃ V : Set E, IsOpen V ∧ (0 : E) ∈ V ∧ (∀ x ∈ V, p + x ∈ U) ∧
          ∀ x ∈ V, matrixOperatorEquiv b A x + r x = f (p + x)) ∧
        CompleteFlow (fun x => matrixOperatorEquiv b A x + r x) φ ∧
        GraphGeometry k (stableParameters b A) (unstableParameters b A) hs ∧
        GraphGeometry k (unstableParameters b A) (stableParameters b A) hu ∧
        (∀ ξ t, 0 ≤ t → φ t (graphMap hs ξ) ∈ Set.range (graphMap hs)) ∧
        (∀ η t, t ≤ 0 → φ t (graphMap hu η) ∈ Set.range (graphMap hu)) ∧
        (∀ ξ t, 0 ≤ t → ‖φ t (graphMap hs ξ)‖ ≤
          (K / (1 - contractionRate K α β δ)) * ‖(ξ : E)‖ * Real.exp (-β * t)) ∧
        (∀ η t, t ≤ 0 → ‖φ t (graphMap hu η)‖ ≤
          (K / (1 - contractionRate K α β δ)) * ‖(η : E)‖ * Real.exp (β * t))

end Specs.D13Unified.Ch20.StableGraphs
