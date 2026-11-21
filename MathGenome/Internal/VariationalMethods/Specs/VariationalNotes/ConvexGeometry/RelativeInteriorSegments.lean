import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations

/-!
Independent statements for `paper.tex`, Theorem `thm:relative-segment`,
Lemma `lem:ri-extendible`, and the two closure identities of `thm:ri-calculus`.
The ambient space is any finite-dimensional Hausdorff real topological vector
space. No positive dimension, full affine span, or closedness is required.
-/

open Set
noncomputable section
universe u
namespace VariationalNotes.ConvexGeometry.Specs

def relativeInterior_nonempty : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (C : Set E),
    Convex ℝ C → C.Nonempty → (relativeInterior C).Nonempty

def relativeInterior_halfOpenSegment : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (C : Set E), Convex ℝ C →
    ∀ (a b : E), a ∈ relativeInterior C → b ∈ closure C →
    ∀ t : ℝ, 0 ≤ t → t < 1 → (1 - t) • a + t • b ∈ relativeInterior C

def mem_relativeInterior_iff_extendible : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (C : Set E), Convex ℝ C →
    ∀ x ∈ C, x ∈ relativeInterior C ↔
      ∀ y ∈ C, ∃ s : ℝ, 0 < s ∧ x + s • (x - y) ∈ C

def closure_relativeInterior : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (C : Set E), Convex ℝ C → C.Nonempty →
      closure (relativeInterior C) = closure C

def relativeInterior_closure : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (C : Set E), Convex ℝ C → C.Nonempty →
      relativeInterior (closure C) = relativeInterior C

end VariationalNotes.ConvexGeometry.Specs
