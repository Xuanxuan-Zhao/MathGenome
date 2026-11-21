import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.FiniteDimensionalContinuity
import Mathlib.Analysis.Convex.Continuous

/-! Finite-dimensional convex continuity, paper.tex:8198–8208.

`ConvexOn.continuousOn` uses the finite-vertex argument: a small simplex
containing an interior neighborhood of a domain point lies in the domain;
convexity bounds the function on its convex hull by its finitely many vertex
values. Reflection gives a lower bound and the convex secant estimate gives
local Lipschitz continuity. A simplex serves the same purpose as the source's
coordinate cube. In particular, no lower semicontinuity is used.
-/

namespace ExpandedFA.BanachConvex

/-- A finite convex function on an open convex subset of real n-space is
continuous. The empty domain and dimension zero are included. -/
theorem finite_convex_continuity :
    FiniteDimensionalContinuitySpec.FiniteConvexContinuity := by
  intro n U φ hU hφ
  exact hφ.continuousOn hU

end ExpandedFA.BanachConvex
