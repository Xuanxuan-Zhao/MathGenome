import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Basis
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! The criterion of paper.tex, lines 3906–3917. `range N` represents
exactly the first N terms of the source's sequence indexed from one.
The coefficients may be arbitrary sequences: only their first N entries
are used, so this is precisely quantification over finite scalar families.
The conclusion is the upstream raw unique-expansion property; continuity
of coordinates is neither an input nor part of its definition. -/
noncomputable section
universe u v
namespace ExpandedFA.P1.C15BasisCriterion.Spec
open Filter Topology

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def UniformPrefixBound (e : ℕ → E) : Prop :=
  ∃ C : ℝ, ∀ (a : ℕ → 𝕜) (m N : ℕ), m ≤ N →
    ‖ExpandedFA.P1.C15Basis.Spec.orderedPartialSum e a m‖ ≤
      C * ‖ExpandedFA.P1.C15Basis.Spec.orderedPartialSum e a N‖

def BasisCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (e : ℕ → E), (∀ i, e i ≠ 0) →
    Dense (Submodule.span 𝕜 (Set.range e) : Set E) →
    (ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e ↔ UniformPrefixBound (𝕜 := 𝕜) e)

/-- The finite bound already forces linear independence; no coordinate
continuity or algebraic independence is assumed. -/
def PrefixBoundIndependence : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (e : ℕ → E), (∀ i, e i ≠ 0) →
    UniformPrefixBound (𝕜 := 𝕜) e → LinearIndependent 𝕜 e

end ExpandedFA.P1.C15BasisCriterion.Spec
