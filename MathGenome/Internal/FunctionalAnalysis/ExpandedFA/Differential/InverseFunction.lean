import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Differential.InverseFunction
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

open Filter Set
open scoped Topology ContDiff

namespace ExpandedFA.Differential.InverseFunction

/-- A continuous derivative is invertible on a neighborhood of a point where it
is invertible. Restrict the inverse-function homeomorphism to that neighborhood
and the original open domain. This gives the derivative and every regularity
upgrade at every point of its target, rather than only at the base point. -/
theorem inverse_function : Spec.LocalInverseTheorem := by
  intro 𝕜 E F _ _ _ _ _ _ _ Ω hΩ f hf x₀ hx₀ A hA
  have hfx : ContDiffAt 𝕜 1 f x₀ := hf.contDiffAt (hΩ.mem_nhds hx₀)
  have hinv : {x | (fderiv 𝕜 f x).IsInvertible} ∈ 𝓝 x₀ := by
    have hAn : (fderiv 𝕜 f x₀).IsInvertible := by
      rw [hA.fderiv]
      exact ⟨A, rfl⟩
    exact (hfx.continuousAt_fderiv one_ne_zero).preimage_mem_nhds
      hAn.eventually_nhds
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp
    (inter_mem (hΩ.mem_nhds hx₀) hinv)
  let e₀ := hfx.toOpenPartialHomeomorph f hA one_ne_zero
  let e := e₀.restrOpen W hWopen
  have he : (e : E → F) = f := rfl
  have hx : x₀ ∈ e.source :=
    ⟨hfx.mem_toOpenPartialHomeomorph_source hA one_ne_zero, hxW⟩
  have hsub : e.source ⊆ Ω := fun x hx => (hWsub hx.2).1
  have hderiv (x : E) (hx : x ∈ e.source) :
      (fderiv 𝕜 f x).IsInvertible := (hWsub hx.2).2
  have hdiff (x : E) (hx : x ∈ e.source) : ContDiffAt 𝕜 1 f x :=
    hf.contDiffAt (hΩ.mem_nhds (hsub hx))
  have hregular (k : WithTop ℕ∞) (hk : ContDiffOn 𝕜 k f Ω) :
      ContDiffOn 𝕜 k e.symm e.target := by
    apply e.open_target.contDiffOn_iff.mpr
    intro y hy
    have hx' := e.map_target hy
    obtain ⟨B, hB⟩ := hderiv (e.symm y) hx'
    apply e.contDiffAt_symm hy
    · rw [he, hB]
      exact ((hdiff _ hx').differentiableAt one_ne_zero).hasFDerivAt
    · rw [he]
      exact hk.contDiffAt (hΩ.mem_nhds (hsub hx'))
  refine ⟨e, he, hx, hsub, ?_, hregular 1 hf, ?_, ?_, ?_, ?_, ?_, hregular⟩
  · exact e.map_source hx
  · intro x hx
    exact e.left_inv hx
  · intro y hy
    exact e.right_inv hy
  · intro y hy
    have hx' := e.map_target hy
    obtain ⟨B, hB⟩ := hderiv (e.symm y) hx'
    have hBderiv : HasFDerivAt e (B : E →L[𝕜] F) (e.symm y) := by
      rw [he, hB]
      exact ((hdiff _ hx').differentiableAt one_ne_zero).hasFDerivAt
    have hi := e.hasFDerivAt_symm hy hBderiv
    have hi' : HasFDerivAt e.symm (fderiv 𝕜 f (e.symm y)).inverse y := by
      simpa only [← hB, ContinuousLinearMap.inverse_equiv] using hi
    exact ⟨hderiv _ hx', hi', hi'.fderiv⟩
  · intro y hy x hx'
    constructor
    · intro hxy
      calc x = e.symm (f x) := (e.left_inv hx').symm
           _ = e.symm y := congrArg e.symm hxy
    · intro hxy
      rw [hxy]
      exact e.right_inv hy
  · intro g hg
    exact eventuallyEq_of_left_inv_of_right_inv hg (e.eventually_right_inverse' hx)
      (e.tendsto_symm hx)

end ExpandedFA.Differential.InverseFunction
