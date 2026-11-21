import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
The real adjoint-intertwining clause of `fa2:p2:fuglede-putnam`, under
the manuscript's real-or-complex scalar convention. The spaces may differ
and may be zero or nonseparable. Normality uses the actual real adjoints.
-/

namespace ExpandedFA.SpectralMeasure.RealFugledeIntertwining.Spec
universe u v

/-- Rectangular real Fuglede–Putnam, without assumptions on the intertwiner. -/
def AdjointIntertwining : Prop :=
  ∀ (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (N : H →L[ℝ] H) (M : K →L[ℝ] K) (T : K →L[ℝ] H),
    N.adjoint.comp N = N.comp N.adjoint →
    M.adjoint.comp M = M.comp M.adjoint →
    N.comp T = T.comp M →
    N.adjoint.comp T = T.comp M.adjoint

end ExpandedFA.SpectralMeasure.RealFugledeIntertwining.Spec
