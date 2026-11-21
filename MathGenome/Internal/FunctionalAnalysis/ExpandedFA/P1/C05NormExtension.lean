import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05NormExtension
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
Norm-preserving Hahn–Banach over both scalar fields,
`fa2:p1:c05:norm-extension`, paper.tex:902–908.

Mathlib's `exists_extension_norm_eq` applies to an arbitrary subspace of a
seminormed space over an `IsRCLikeNormedField`, hence to the manuscript's
real and complex normed spaces. Its `StrongDual` is definitionally the native
continuous scalar-linear dual used in the shared dual interface. In particular,
the complex extension is complex-linear. The theorem imposes no completeness,
closedness, or nontriviality condition, so it also covers zero functionals
and the zero space.
-/

namespace ExpandedFA.P1.C05NormExtension

universe u v

/-- Extend any continuous scalar-linear functional on any subspace without
changing its operator norm. -/
theorem norm_preserving_extension : Spec.NormPreservingExtension.{u, v} := by
  intro 𝕜 E _ _ _ M f
  exact exists_extension_norm_eq M f

end ExpandedFA.P1.C05NormExtension
