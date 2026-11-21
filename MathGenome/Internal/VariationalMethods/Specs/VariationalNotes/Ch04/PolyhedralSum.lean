import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Subgradients
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.PolyhedraElimination
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent statements of paper.tex, Theorem `thm:polyhedral-sum`
and its normal-intersection consequence (2001–2044). No closedness of f
or C is assumed, and the qualification uses dom g, not ri dom g. -/
noncomputable section
open Set
open scoped Pointwise
universe u
namespace VariationalNotes.Ch04.Specs
open ConvexAnalysis.Specs ConvexGeometry.Specs

def polyhedral_sum : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (f g : E → WithTop ℝ),
    Proper f → IsConvex f → Proper g → IsConvex g →
    IsPolyhedron (epigraph g) →
    (relativeInterior (effectiveDomain f) ∩ effectiveDomain g).Nonempty →
    ∀ x ∈ effectiveDomain f ∩ effectiveDomain g,
      subdifferential (fun z => f z + g z) x = subdifferential f x + subdifferential g x

def polyhedral_normal_intersection : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (C D : Set E),
    Convex ℝ C → IsPolyhedron D → (relativeInterior C ∩ D).Nonempty →
    ∀ x ∈ C ∩ D, normalCone (C ∩ D) x = normalCone C x + normalCone D x

end VariationalNotes.Ch04.Specs
