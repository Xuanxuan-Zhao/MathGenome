import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.RelativeInteriorSegments

/-!
The finite-intersection assertions of `paper.tex`, Theorem `thm:ri-calculus`
(lines 206–211, proof at 233–242). The index type may be empty, and the
intersection then means the universal set. No full-dimensionality is assumed.
-/

open Set
universe u v
namespace VariationalNotes.ConvexGeometry.Specs

def relativeInterior_iInter : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] {ι : Type v} [Finite ι] (C : ι → Set E),
    (∀ i, Convex ℝ (C i)) → (⋂ i, relativeInterior (C i)).Nonempty →
    relativeInterior (⋂ i, C i) = ⋂ i, relativeInterior (C i)

def closure_iInter : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] {ι : Type v} [Finite ι] (C : ι → Set E),
    (∀ i, Convex ℝ (C i)) → (⋂ i, relativeInterior (C i)).Nonempty →
    closure (⋂ i, C i) = ⋂ i, closure (C i)

end VariationalNotes.ConvexGeometry.Specs
