import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.HahnBanach
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.SeminormModel
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.LocallyConvex.Separation

/-! Seminorm Hahn–Banach and its LCS consequences, `fa2:p1:hahn-banach`.

The algebraic library theorem includes the passage from real to complex
scalars and preserves domination by the given seminorm. For continuity we
first identify the native LCS topology with its continuous seminorm topology;
this supplies precisely the polynormability hypothesis of the library's
continuous extension theorem. Point separation uses geometric Hahn–Banach
over the original scalar field, whose real parts strictly separate the points.
-/

namespace ExpandedFA.P1

theorem seminorm_hahn_banach : HahnBanachSpec.SeminormExtension := by
  intro 𝕜 E _ _ _ p M f hf
  exact Module.Dual.exists_extension_of_le_seminorm M f hf

theorem continuous_hahn_banach : HahnBanachSpec.ContinuousExtension := by
  intro 𝕜 E _ _ _ _ _ _ _ hE M f
  let : PolynormableSpace 𝕜 E := (with_continuous_seminorms hE).toPolynormableSpace
  exact StrongDual.exists_extension M f

theorem continuous_dual_separates_points : HahnBanachSpec.DualSeparatesPoints := by
  intro 𝕜 E _ _ _ _ _ _ _ hE x y hxy
  let : IsTopologicalAddGroup E := hE.1.1
  let : ContinuousSMul 𝕜 E := hE.1.2
  let : LocallyConvexSpace ℝ E := hE.2
  obtain ⟨f, hf⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hxy
  exact ⟨f, fun h => (ne_of_lt hf) (congrArg RCLike.re h)⟩

end ExpandedFA.P1
