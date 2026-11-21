import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Conjugates
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Theorem `thm:finite-fenchel`, paper.tex §v04-02. Spaces carry their given Hausdorff real vector topology. A is an arbitrary linear map;
its continuous representative exists automatically. No closedness, ambient
interior, or primal minimizer is assumed. -/
noncomputable section
universe u v
namespace VariationalNotes.Ch04.Specs
open VariationalNotes.ConvexAnalysis.Specs
open VariationalNotes.ConvexGeometry.Specs

def finite_fenchel : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X] [FiniteDimensional ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y] [FiniteDimensional ℝ Y]
    (A : X →ₗ[ℝ] Y) (f : X → WithTop ℝ) (g : Y → WithTop ℝ),
    Proper f → IsConvex f → Proper g → IsConvex g →
    (A '' relativeInterior (effectiveDomain f) ∩
      relativeInterior (effectiveDomain g)).Nonempty →
    ∀ p : ℝ, (⨅ x, toEReal (f x + g (A x))) = (p : EReal) →
    ∃ y : Y →L[ℝ] ℝ,
      (p : EReal) = -conjugate f (-(y.comp A.toContinuousLinearMap)) - conjugate g y ∧
      (⨆ z : Y →L[ℝ] ℝ,
        -conjugate f (-(z.comp A.toContinuousLinearMap)) - conjugate g z) = (p : EReal)

end VariationalNotes.Ch04.Specs
