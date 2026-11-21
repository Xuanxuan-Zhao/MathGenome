import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.FugledeIntertwining
import Mathlib.Analysis.CStarAlgebra.Fuglede
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
Apply the C*-algebra Fuglede theorem on the Hilbert sum H ⊕₂ K.
The diagonal operator diag(N,M) is normal, and the operator with upper-right
block T commutes with it precisely when NT = TM. Extracting the upper-right
block after taking the adjoint of the diagonal gives N*T = TM*.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.SpectralMeasure.FugledeIntertwining
universe u v
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private def diagonal (N : H →L[ℂ] H) (M : K →L[ℂ] K) :
    WithLp 2 (H × K) →L[ℂ] WithLp 2 (H × K) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
    ((N.prodMap M).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toContinuousLinearMap)

omit [CompleteSpace H] [CompleteSpace K] in
private lemma diagonal_apply (N : H →L[ℂ] H) (M : K →L[ℂ] K)
    (x : WithLp 2 (H × K)) :
    diagonal N M x = WithLp.toLp 2 (N x.fst, M x.snd) := rfl

private lemma diagonal_adjoint (N : H →L[ℂ] H) (M : K →L[ℂ] K) :
    (diagonal N M).adjoint = diagonal N.adjoint M.adjoint := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [diagonal_apply, WithLp.prod_inner_apply]
  exact congrArg₂ (· + ·) (ContinuousLinearMap.adjoint_inner_left N _ _)
    (ContinuousLinearMap.adjoint_inner_left M _ _)

theorem adjoint_intertwining : Spec.AdjointIntertwining.{u, v} := by
  intro H K _ _ _ _ _ _ N M T hN hM hT
  let D := diagonal N M
  let X : WithLp 2 (H × K) →L[ℂ] WithLp 2 (H × K) :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ H K).symm.toContinuousLinearMap.comp
      (((T.comp (ContinuousLinearMap.snd ℂ H K)).prod 0).comp
        (WithLp.prodContinuousLinearEquiv 2 ℂ H K).toContinuousLinearMap)
  have hD : IsStarNormal D := by
    constructor
    change D.adjoint * D = D * D.adjoint
    rw [show D.adjoint = diagonal N.adjoint M.adjoint from diagonal_adjoint N M]
    ext x
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact congrArg (fun A : H →L[ℂ] H => A x.fst) hN
    · exact congrArg (fun A : K →L[ℂ] K => A x.snd) hM
  have hDX : Commute D X := by
    change D.comp X = X.comp D
    ext x
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact congrArg (fun A : K →L[ℂ] H => A x.snd) hT
    · simp [D, X, diagonal_apply]
  have hstar := hD.commute_star_left hDX
  ext k
  have hh := congrArg (fun A : WithLp 2 (H × K) →L[ℂ] WithLp 2 (H × K) =>
    (A (WithLp.toLp 2 (0, k))).fst) hstar.eq
  simpa [ContinuousLinearMap.star_eq_adjoint, D, diagonal_adjoint, diagonal_apply, X] using hh

end ExpandedFA.SpectralMeasure.FugledeIntertwining
