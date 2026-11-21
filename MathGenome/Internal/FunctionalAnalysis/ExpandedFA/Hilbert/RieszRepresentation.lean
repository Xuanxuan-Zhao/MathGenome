import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.RieszRepresentation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Conventions
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Riesz representation (`paper.tex` 7444–7450).
Mathlib's conjugate-linear isometric equivalence `toDual` takes values in
the continuous scalar-linear dual, with evaluation ⟪h,x⟫. Its inverse gives
the representing vector, including for the zero functional and zero space.

For a form a, inverse Riesz applied to each second-slot functional a x gives
a bounded scalar-linear S with a(x,y) = ⟪Sx,y⟫. Slice norms are preserved, so
the operator norm of S is exactly the native norm of a. The adjoint A = S*
then gives the required second-slot identity and preserves that norm.
These are library constructions, not imports of the downstream adjoint goal.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.RieszRepresentation
universe u v

theorem functional_representation : Spec.FunctionalRepresentation.{u, v} := by
  intro 𝕜 H _ _ _ _ f
  refine ⟨(InnerProductSpace.toDual 𝕜 H).symm f, ?_, ?_, ?_⟩
  · intro x
    exact InnerProductSpace.toDual_symm_apply.symm
  · exact ((InnerProductSpace.toDual 𝕜 H).symm.norm_map f).symm
  · intro k hk
    apply (InnerProductSpace.toDual 𝕜 H).injective
    apply ContinuousLinearMap.ext
    intro x
    change ⟪k, x⟫_𝕜 = ⟪(InnerProductSpace.toDual 𝕜 H).symm f, x⟫_𝕜
    rw [← hk x, InnerProductSpace.toDual_symm_apply]

theorem form_representation : Spec.FormRepresentation.{u, v} := by
  intro 𝕜 H _ _ _ _ a
  let S : H →L[𝕜] H := InnerProductSpace.continuousLinearMapOfBilin a
  have hS (x y : H) : ⟪S x, y⟫_𝕜 = a x y :=
    InnerProductSpace.continuousLinearMapOfBilin_apply a x y
  have hnorm : ‖S‖ = ‖a‖ := by
    apply ContinuousLinearMap.opNorm_ext
    intro x
    exact (InnerProductSpace.toDual 𝕜 H).symm.norm_map (a x)
  let A : H →L[𝕜] H := ContinuousLinearMap.adjoint S
  have hA (x y : H) : a x y = ⟪x, A y⟫_𝕜 := by
    rw [ContinuousLinearMap.adjoint_inner_right, hS]
  refine ⟨A, hA, ?_, ?_⟩
  · exact (ContinuousLinearMap.adjoint.norm_map S).trans hnorm
  · intro B hB
    ext y
    apply ext_inner_left 𝕜
    intro x
    exact (hB x y).symm.trans (hA x y)

end ExpandedFA.Hilbert.RieszRepresentation
