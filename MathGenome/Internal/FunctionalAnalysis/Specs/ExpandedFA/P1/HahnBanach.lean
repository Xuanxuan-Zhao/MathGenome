import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
Independent statements for `paper.tex:2048–2055`, `fa2:p1:hahn-banach`.

`RCLike` covers both real and complex scalars. The modulus is the scalar norm,
and all functionals are linear over the original scalar field. In the first
statement the vector space is purely algebraic; no topology is imposed.
The topological statements use the chapter's Hausdorff LCS convention, with
real local convexity and the subspace topology on an arbitrary submodule.
No completeness, closedness of the subspace, or nonzero-space hypothesis is
required. The zero seminorm and the zero subspace are included.
-/

namespace ExpandedFA.P1.HahnBanachSpec

def SeminormExtension : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (p : Seminorm 𝕜 E) (M : Submodule 𝕜 E) (f : M →ₗ[𝕜] 𝕜),
    (∀ m : M, ‖f m‖ ≤ p (m : E)) →
      ∃ F : E →ₗ[𝕜] 𝕜,
        (∀ m : M, F (m : E) = f m) ∧ ∀ x : E, ‖F x‖ ≤ p x

def ContinuousExtension : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [T2Space E],
    LCS 𝕜 E → ∀ (M : Submodule 𝕜 E) (f : M →L[𝕜] 𝕜),
      ∃ F : E →L[𝕜] 𝕜, ∀ m : M, F (m : E) = f m

def DualSeparatesPoints : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [T2Space E],
    LCS 𝕜 E → ∀ x y : E, x ≠ y → ∃ f : E →L[𝕜] 𝕜, f x ≠ f y

end ExpandedFA.P1.HahnBanachSpec
