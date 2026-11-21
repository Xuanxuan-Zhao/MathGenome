import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-! Independent statements for `fa2:p1:c06:open-separation`, paper.tex:1083–1094.

These statements hold in any topological vector space, which is stronger than
requiring a convex balanced neighborhood base. No separation axiom or completeness
is imposed. Complex convexity is real convexity, and the real scalar action is
the canonical restriction of the complex action. The complex conclusion explicitly
identifies the nonzero real separator with the real part of a complex functional.
-/
namespace Specs.ExpandedFA.P1.C06OpenSeparation
universe u

def realType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (A B : Set E), A.Nonempty → B.Nonempty → Convex ℝ A → Convex ℝ B →
    Disjoint A B → IsOpen A →
    ∃ (h : E →L[ℝ] ℝ) (α : ℝ), h ≠ 0 ∧
      (∀ a ∈ A, h a < α) ∧ (∀ b ∈ B, α ≤ h b)

def complexType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (A B : Set E), A.Nonempty → B.Nonempty → Convex ℝ A → Convex ℝ B →
    Disjoint A B → IsOpen A →
    ∃ (h : E →L[ℝ] ℝ) (f : E →L[ℂ] ℂ) (α : ℝ),
      h ≠ 0 ∧ f ≠ 0 ∧ (∀ x, h x = (f x).re) ∧
      (∀ a ∈ A, h a < α) ∧ (∀ b ∈ B, α ≤ h b)

def realNormedType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : Set E), A.Nonempty → B.Nonempty → Convex ℝ A → Convex ℝ B →
    Disjoint A B → IsOpen A →
    ∃ (h : E →L[ℝ] ℝ) (α : ℝ), h ≠ 0 ∧
      (∀ a ∈ A, h a < α) ∧ (∀ b ∈ B, α ≤ h b)

def complexNormedType : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : Set E), A.Nonempty → B.Nonempty → Convex ℝ A → Convex ℝ B →
    Disjoint A B → IsOpen A →
    ∃ (h : E →L[ℝ] ℝ) (f : E →L[ℂ] ℂ) (α : ℝ),
      h ≠ 0 ∧ f ≠ 0 ∧ (∀ x, h x = (f x).re) ∧
      (∀ a ∈ A, h a < α) ∧ (∀ b ∈ B, α ≤ h b)

end Specs.ExpandedFA.P1.C06OpenSeparation
