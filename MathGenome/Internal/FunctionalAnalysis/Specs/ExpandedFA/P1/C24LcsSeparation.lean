import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
Independent statements for `paper.tex:4965–4970`,
`fa2:p1:c24:lcs-separation`.

The ambient space has its given Hausdorff locally convex topology. No norm,
completeness, metrizability, or boundedness of the convex set is assumed.
On complex spaces the functionals are real-linear and real-valued, as required
by the chapter's underlying-real-space convention. Convexity is always real.
The explicit boundedness of the functional image makes its real supremum
meaningful; the positive margin is also recorded for the same functional.
-/
namespace Specs.ExpandedFA.P1.C24LcsSeparation

universe u

/-- The continuous real dual distinguishes every pair of distinct points. -/
def realPointsType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (x y : E), x ≠ y →
    ∃ ℓ : E →L[ℝ] ℝ, ℓ x ≠ ℓ y

/-- Strict separation, with a finite supremum and a uniform positive margin. -/
def realClosedConvexType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (C : Set E) (x₀ : E),
    C.Nonempty → IsClosed C → Convex ℝ C → x₀ ∉ C →
    ∃ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 ∧ BddAbove (ℓ '' C) ∧
      sSup (ℓ '' C) < ℓ x₀ ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ c ∈ C, ℓ c + ε ≤ ℓ x₀

/-- Point separation on the underlying real space of a complex LCS. -/
def complexPointsType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (x y : E), x ≠ y →
    ∃ ℓ : E →L[ℝ] ℝ, ℓ x ≠ ℓ y

/-- The same strict separation, retaining the topology of the complex space. -/
def complexClosedConvexType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (C : Set E) (x₀ : E),
    C.Nonempty → IsClosed C → Convex ℝ C → x₀ ∉ C →
    ∃ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 ∧ BddAbove (ℓ '' C) ∧
      sSup (ℓ '' C) < ℓ x₀ ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ c ∈ C, ℓ c + ε ≤ ℓ x₀

end Specs.ExpandedFA.P1.C24LcsSeparation
