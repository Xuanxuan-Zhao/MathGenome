import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Order.Compact

/-!
Independent statements of compact--closed separation, paper.tex:2070–2078.
The native TVS and real local convexity structures are those of the shared
TVS interface. Open separation does not need local convexity or separation.
For the chapter's compact--closed assertion Hausdorffness is explicit.

The scalar supremum on the compact set is attained; boundedness above and
below is explicit so that the real supremum and infimum are finite extrema
in the manuscript's sense. No attainment of the closed-set infimum is asserted.
Complex separators belong to the continuous complex-linear dual.
-/
namespace Specs.ExpandedFA.P1.LcsStrongSeparation
universe u

/-- Separation if either of the two nonempty convex sets is open. -/
def realOpenType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (A B : Set E), A.Nonempty → B.Nonempty → Convex ℝ A → Convex ℝ B →
    Disjoint A B → (IsOpen A ∨ IsOpen B) →
    ∃ (h : E →L[ℝ] ℝ) (α : ℝ), h ≠ 0 ∧
      (∀ a ∈ A, h a ≤ α) ∧ (∀ b ∈ B, α ≤ h b) ∧
      ∀ a ∈ A, ∀ b ∈ B, h a < h b

/-- The complex open-set conclusion, with a nonzero real part. -/
def complexOpenType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (A B : Set E), A.Nonempty → B.Nonempty → Convex ℝ A → Convex ℝ B →
    Disjoint A B → (IsOpen A ∨ IsOpen B) →
    ∃ (h : E →L[ℝ] ℝ) (f : E →L[ℂ] ℂ) (α : ℝ),
      h ≠ 0 ∧ f ≠ 0 ∧ (∀ x, h x = (f x).re) ∧
      (∀ a ∈ A, h a ≤ α) ∧ (∀ b ∈ B, α ≤ h b) ∧
      ∀ a ∈ A, ∀ b ∈ B, h a < h b

/-- The maximum on K is strictly less than the finite infimum on C. -/
def realCompactClosedType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    (K C : Set E), K.Nonempty → C.Nonempty → IsCompact K → IsClosed C →
    Convex ℝ K → Convex ℝ C → Disjoint K C →
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ BddAbove (f '' K) ∧ BddBelow (f '' C) ∧
      (∃ k ∈ K, f k = sSup (f '' K)) ∧ sSup (f '' K) < sInf (f '' C)

/-- Complex compact--closed separation uses real parts, with the same extrema. -/
def complexCompactClosedType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [LocallyConvexSpace ℝ E]
    (K C : Set E), K.Nonempty → C.Nonempty → IsCompact K → IsClosed C →
    Convex ℝ K → Convex ℝ C → Disjoint K C →
    ∃ f : E →L[ℂ] ℂ, f ≠ 0 ∧
      BddAbove ((fun x => (f x).re) '' K) ∧
      BddBelow ((fun x => (f x).re) '' C) ∧
      (∃ k ∈ K, (f k).re = sSup ((fun x => (f x).re) '' K)) ∧
      sSup ((fun x => (f x).re) '' K) < sInf ((fun x => (f x).re) '' C)

end Specs.ExpandedFA.P1.LcsStrongSeparation
