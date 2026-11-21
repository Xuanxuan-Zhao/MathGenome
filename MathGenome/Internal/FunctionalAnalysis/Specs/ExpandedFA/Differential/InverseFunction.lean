import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Differential.Definitions
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
Independent statement for the inverse clause of `fa2:p1:banach-implicit`,
paper.tex:6755–6794. The implicit clause is allocated separately.

An ambient function represents a function on the open set Ω; its values outside
Ω are unrestricted. All derivatives are native scalar-linear Fréchet derivatives.
At points of Ω these agree with `fderivWithin 𝕜 f Ω` by openness. The inverse
operator in the conclusion is accompanied by actual invertibility, so the total
extension of `ContinuousLinearMap.inverse` at noninvertible maps plays no role.
The open partial homeomorphism supplies open source and target neighborhoods,
continuous inverse maps, and both inverse identities. The additional explicit
identities and uniqueness clauses allow direct use without unpacking it.
-/

open Filter
open scoped Topology ContDiff

namespace ExpandedFA.Differential.InverseFunction.Spec

/-- The full local inverse theorem, including the derivative formula throughout
the target neighborhood, local uniqueness, and every Cᵏ upgrade on the same
neighborhoods. Orders include all natural orders and smoothness. No dimension,
nonzero-space, or global regularity assumption is imposed. -/
def LocalInverseTheorem : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (Ω : Set E), IsOpen Ω → ∀ (f : E → F), ContDiffOn 𝕜 1 f Ω →
    ∀ (x₀ : E), x₀ ∈ Ω → ∀ (A : E ≃L[𝕜] F),
    HasFDerivAt f (A : E →L[𝕜] F) x₀ →
    ∃ e : OpenPartialHomeomorph E F,
      (e : E → F) = f ∧
      x₀ ∈ e.source ∧ e.source ⊆ Ω ∧ f x₀ ∈ e.target ∧
      ContDiffOn 𝕜 1 e.symm e.target ∧
      (∀ x ∈ e.source, e.symm (f x) = x) ∧
      (∀ y ∈ e.target, f (e.symm y) = y) ∧
      (∀ y ∈ e.target,
        (fderiv 𝕜 f (e.symm y)).IsInvertible ∧
        HasFDerivAt e.symm (fderiv 𝕜 f (e.symm y)).inverse y ∧
        fderiv 𝕜 e.symm y = (fderiv 𝕜 f (e.symm y)).inverse) ∧
      (∀ y ∈ e.target, ∀ x ∈ e.source, f x = y ↔ x = e.symm y) ∧
      (∀ g : F → E, (∀ᶠ x in 𝓝 x₀, g (f x) = x) →
        g =ᶠ[𝓝 (f x₀)] e.symm) ∧
      (∀ k : WithTop ℕ∞, ContDiffOn 𝕜 k f Ω → ContDiffOn 𝕜 k e.symm e.target)

end ExpandedFA.Differential.InverseFunction.Spec
