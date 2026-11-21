import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.TwoSpaceForms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Adjoint

/-!
Bounded forms on two different Hilbert spaces (`paper.tex` 7852–7880).

Apply inverse Riesz on H₂ to the continuous scalar-linear functional a x.
Both a and inverse Riesz are conjugate linear, so their composition is a
bounded scalar-linear map H₁ → H₂. Inverse Riesz preserves every slice norm,
which gives equality of the native operator and form norms. The accepted
adjoint identity gives the second representation. Testing against every y
proves uniqueness without any nonzero-space hypothesis.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.TwoSpaceForms
universe u v w

theorem form_representation : Spec.FormRepresentation.{u, v, w} := by
  intro 𝕜 H₁ H₂ _ _ _ _ _ _ _ a
  let S : H₁ →L[𝕜] H₂ :=
    (InnerProductSpace.toDual 𝕜 H₂).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp a
  have hS (x : H₁) (y : H₂) : a x y = ⟪S x, y⟫_𝕜 :=
    InnerProductSpace.toDual_symm_apply.symm
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · intro x y
    exact (hS x y).trans (Adjoint.adjoint_inner 𝕜 H₁ H₂ S x y)
  · apply ContinuousLinearMap.opNorm_ext
    intro x
    exact (InnerProductSpace.toDual 𝕜 H₂).symm.norm_map (a x)
  · intro T hT
    ext x
    apply ext_inner_right 𝕜
    intro y
    exact (hT x y).symm.trans (hS x y)

end ExpandedFA.Hilbert.TwoSpaceForms
