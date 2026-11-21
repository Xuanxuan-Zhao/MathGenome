import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Differential.InverseFunction
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
The implicit clause of `fa2:p1:banach-implicit`, paper.tex:6755–6798.
The inverse clause is the accepted upstream `LocalInverseTheorem`.
An ambient H represents its restriction to the open set Ω. The compositions
of its Fréchet derivative with `inl` and `inr` are precisely its partial
Fréchet derivatives, by the chain rule. Thus the displayed isomorphism is
only the derivative in Y, and imposes no restriction on the derivative in E.
All three spaces are arbitrary Banach spaces over either ℝ or ℂ.
-/

open Filter Set
open scoped Topology ContDiff

namespace ExpandedFA.Differential.ImplicitFunction.Spec

/-- One open product neighborhood has the exact zero-set graph, pointwise
uniqueness, C¹ regularity and the partial-derivative formula everywhere.
Every Cᵏ upgrade uses the same map and neighborhoods (including smoothness).
Germ uniqueness also covers other local continuous solutions through the base
point without imposing an a priori common range neighborhood. -/
def LocalImplicitTheorem : Prop :=
  ∀ (𝕜 E Y Z : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]
    (Ω : Set (E × Y)), IsOpen Ω → ∀ (H : E × Y → Z),
    ContDiffOn 𝕜 1 H Ω → ∀ (x₀ : E) (y₀ : Y), (x₀, y₀) ∈ Ω →
    H (x₀, y₀) = 0 → ∀ B : Y ≃L[𝕜] Z,
    (fderiv 𝕜 H (x₀, y₀)).comp (ContinuousLinearMap.inr 𝕜 E Y) =
      (B : Y →L[𝕜] Z) →
    ∃ (U : Set E) (V : Set Y) (φ : E → Y),
      IsOpen U ∧ IsOpen V ∧ x₀ ∈ U ∧ y₀ ∈ V ∧ U ×ˢ V ⊆ Ω ∧
      φ x₀ = y₀ ∧ MapsTo φ U V ∧ ContDiffOn 𝕜 1 φ U ∧
      (∀ x ∈ U, ∀ y ∈ V, H (x, y) = 0 ↔ y = φ x) ∧
      (∀ x ∈ U,
        ((fderiv 𝕜 H (x, φ x)).comp (ContinuousLinearMap.inr 𝕜 E Y)).IsInvertible ∧
        HasFDerivAt φ
          ((-((fderiv 𝕜 H (x, φ x)).comp (ContinuousLinearMap.inr 𝕜 E Y)).inverse).comp
            ((fderiv 𝕜 H (x, φ x)).comp (ContinuousLinearMap.inl 𝕜 E Y))) x ∧
        fderiv 𝕜 φ x =
          (-((fderiv 𝕜 H (x, φ x)).comp (ContinuousLinearMap.inr 𝕜 E Y)).inverse).comp
            ((fderiv 𝕜 H (x, φ x)).comp (ContinuousLinearMap.inl 𝕜 E Y))) ∧
      (∀ ψ : E → Y, (∀ x ∈ U, ψ x ∈ V ∧ H (x, ψ x) = 0) → EqOn ψ φ U) ∧
      (∀ ψ : E → Y, ContinuousAt ψ x₀ → ψ x₀ = y₀ →
        (∀ᶠ x in 𝓝 x₀, H (x, ψ x) = 0) → ψ =ᶠ[𝓝 x₀] φ) ∧
      (∀ k : WithTop ℕ∞, ContDiffOn 𝕜 k H Ω → ContDiffOn 𝕜 k φ U)

end ExpandedFA.Differential.ImplicitFunction.Spec
