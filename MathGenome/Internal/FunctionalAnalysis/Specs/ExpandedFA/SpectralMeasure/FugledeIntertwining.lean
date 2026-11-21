import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
The adjoint implication in `paper.tex`, `fa2:p2:fuglede-putnam`, lines
12501–12518. The chapter allows arbitrary complex Hilbert spaces, including
zero and nonseparable spaces. Normality is the explicit identity N* N = N N*.
The native adjoint is the conjugate-first Hilbert adjoint of the shared
Hilbert interfaces. The Borel-calculus and similarity consequences belong
to the other allocated stages of this source theorem.
-/

namespace ExpandedFA.SpectralMeasure.FugledeIntertwining.Spec
universe u v

/-- Rectangular Fuglede–Putnam: no injectivity or invertibility of T is assumed. -/
def AdjointIntertwining : Prop :=
  ∀ (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (N : H →L[ℂ] H) (M : K →L[ℂ] K) (T : K →L[ℂ] H),
    N.adjoint.comp N = N.comp N.adjoint →
    M.adjoint.comp M = M.comp M.adjoint →
    N.comp T = T.comp M →
    N.adjoint.comp T = T.comp M.adjoint

end ExpandedFA.SpectralMeasure.FugledeIntertwining.Spec
