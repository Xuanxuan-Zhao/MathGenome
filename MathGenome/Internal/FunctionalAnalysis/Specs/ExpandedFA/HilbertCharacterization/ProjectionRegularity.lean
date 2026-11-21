import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.HilbertCharacterization.ProjectionUniqueness
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Independent full statements for paper.tex:9111–9194.
The normal functional is normalized by its value at the contact point for
uniqueness, and by Euclidean operator norm for the continuous outward normal.
The graph coordinates use the tangent plane ker f and the transverse radial
direction p. No smoothness or strict convexity is among the hypotheses. -/
namespace Specs.ExpandedFA.HilbertCharacterization.ProjectionRegularity

universe u
open Set ConvexBodySetup

/-- Unique supporting affine plane, encoded by its unique defining functional
with value one at the contact point. Positivity at contact makes this equivalent
to uniqueness of the outward supporting ray. -/
def supportingPlaneType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E), ProjectionBody K →
    ∀ p ∈ frontier K, ∃! f : E →L[ℝ] ℝ, f ∈ NormalCone K p ∧ f p = 1

/-- Continuous outward unit conormal and its explicit Euclidean unit normal
vector, related by the Riesz pairing. -/
def continuousNormalType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E), ProjectionBody K →
    ∃ n : frontier K → (E →L[ℝ] ℝ), Continuous n ∧
      (∀ p : frontier K, n p ∈ NormalCone K (p : E) ∧ ‖n p‖ = 1 ∧
        ∀ g ∈ NormalCone K (p : E), ‖g‖ = 1 → g = n p) ∧
      ∃ v : frontier K → E, Continuous v ∧
        ∀ p : frontier K, ‖v p‖ = 1 ∧ ∀ x : E, n p x = inner ℝ (v p) x

/-- Actual C¹ local graph coordinates, rather than only a label of smoothness.
The graph is tangent to ker f at p. The neighborhoods are open in their
respective ambient spaces and contain the base points. -/
def localGraphType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Set E), ProjectionBody K →
    ∀ p ∈ frontier K, ∃ f : E →L[ℝ] ℝ,
      f ∈ NormalCone K p ∧ f p = 1 ∧
      Module.finrank ℝ f.ker = 2 ∧
      ∃ (U : Set f.ker) (V : Set E) (h : f.ker → ℝ),
        IsOpen U ∧ (0 : f.ker) ∈ U ∧ IsOpen V ∧ p ∈ V ∧
        ContDiffOn ℝ 1 h U ∧ h 0 = 0 ∧ HasFDerivAt h (0 : f.ker →L[ℝ] ℝ) 0 ∧
        ∀ x ∈ V, x ∈ frontier K ↔
          ∃ y ∈ U, x = p + (y : E) + h y • p

/-- Complete regularity lemma, including the previously established projection
uniqueness and kernel continuity conclusions. -/
def regularityType : Prop :=
  supportingPlaneType.{u} ∧ continuousNormalType.{u} ∧ localGraphType.{u} ∧
    ProjectionUniqueness.uniquenessType.{u} ∧ ProjectionUniqueness.continuityType.{u}

end Specs.ExpandedFA.HilbertCharacterization.ProjectionRegularity
