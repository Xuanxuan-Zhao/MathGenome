import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm
import Mathlib.Basic.ENNReal.Basic

/-!
Independent statements for Theorem `fa2:p1:c07:uniform-boundedness`
(paper.tex, lines 1409–1417). The maps are the native continuous linear maps
of the shared operator interface. Only the domain is assumed complete.
`RCLike` includes both real and complex scalars; neither the domain nor the
index type is assumed nontrivial, countable, or nonempty.

Suprema take values in `ℝ≥0∞`, so finiteness is a substantive assertion and
the supremum of an empty family is canonically zero.
-/

namespace ExpandedFA.P1.C07UniformBoundedness.Spec

open scoped ENNReal

universe u v w z

/-- Pointwise finite real bounds imply a uniform nonnegative real norm bound. -/
def UniformBoundedness : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (I : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E]
    (T : I → E →L[𝕜] F),
    (∀ x : E, ∃ C : ℝ, ∀ i, ‖T i x‖ ≤ C) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖T i‖ ≤ C

/-- The extended nonnegative supremum is finite exactly when a finite
nonnegative real bound exists. This bridge needs no completeness. -/
def FiniteSupremumCriterion : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (I : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : I → E →L[𝕜] F),
    ((⨆ i, (‖T i‖₊ : ℝ≥0∞)) < ⊤) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖T i‖ ≤ C

/-- Uniform boundedness in the manuscript's nonnegative-supremum formulation. -/
def UniformBoundednessSupremum : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (I : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E]
    (T : I → E →L[𝕜] F),
    (∀ x : E, (⨆ i, (‖T i x‖₊ : ℝ≥0∞)) < ⊤) →
      (⨆ i, (‖T i‖₊ : ℝ≥0∞)) < ⊤

/-- Both operator and pointwise suprema of an empty family are zero. -/
def EmptyFamilySuprema : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (I : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [IsEmpty I]
    (T : I → E →L[𝕜] F),
    (⨆ i, (‖T i‖₊ : ℝ≥0∞)) = 0 ∧
      ∀ x : E, (⨆ i, (‖T i x‖₊ : ℝ≥0∞)) = 0

/-- On the zero domain the operator-norm supremum is zero, for every family. -/
def ZeroDomainSupremum : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (I : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [Subsingleton E]
    (T : I → E →L[𝕜] F),
    (⨆ i, (‖T i‖₊ : ℝ≥0∞)) = 0

end ExpandedFA.P1.C07UniformBoundedness.Spec
