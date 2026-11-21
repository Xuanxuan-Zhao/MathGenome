import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Independent statements for `fa2:p1:c01:finite-dimension`, paper.tex lines 188–194.
`RCLike` covers the manuscript's real and complex scalar fields. The comparison
quantifies over arbitrary norm functions on one algebraic vector space, so it
does not assume continuity or compatibility of their norm topologies.
No positive-dimension, ambient-completeness, or set-nonemptiness assumption occurs.
-/

namespace ExpandedFA.P1.C01FiniteDimension.Spec

/-- Any two norms on a finite-dimensional vector space admit positive global
two-sided comparison constants. This includes the zero-dimensional space. -/
def NormEquivalence : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] (p q : E → ℝ),
    C01Norm.NormAxioms 𝕜 p → C01Norm.NormAxioms 𝕜 q →
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ x, c * p x ≤ q x ∧ q x ≤ C * p x

/-- Completeness for the uniformity induced by the displayed norm. -/
def Completeness : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E], CompleteSpace E

/-- The norm-topological Heine–Borel property, allowing the empty set. -/
def ClosedBoundedCompact : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (s : Set E),
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s

/-- Local compactness in the same norm topology. -/
def LocalCompactness : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E], LocallyCompactSpace E

/-- Only the subspace is finite-dimensional; the ambient normed space is
arbitrary, and in particular need not be complete. -/
def SubspaceClosed : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M], IsClosed (M : Set E)

end ExpandedFA.P1.C01FiniteDimension.Spec
