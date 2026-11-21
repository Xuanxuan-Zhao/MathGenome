import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24Faces
import Mathlib.Analysis.Complex.Basic

/-!
Independent statements for Theorem `fa2:p1:c24:krein-milman`
(also `fa2:p1:krein-milman`), paper.tex:5010–5019.

The extreme-point set is the shared manuscript definition, using proper real
convex combinations. `convexHull ℝ` is the hull of finite real convex
combinations, and `closure` uses the given topology. The real and complex
statements impose neither normability, completeness nor metrizability.
-/

universe u

namespace ExpandedFA.P1.C24KreinMilmanSpec

open ExpandedFA.P1.C24FacesSpec

/-- Krein–Milman in a real Hausdorff locally convex topological vector space. -/
def realKreinMilmanType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K : Set E),
    K.Nonempty → IsCompact K → Convex ℝ K →
    K = closure (convexHull ℝ (extremePoints K))

/-- A complex ambient space is viewed over ℝ without changing its topology. -/
def complexKreinMilmanType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K : Set E),
    K.Nonempty → IsCompact K → Convex ℝ K →
    K = closure (convexHull ℝ (extremePoints K))

end ExpandedFA.P1.C24KreinMilmanSpec
