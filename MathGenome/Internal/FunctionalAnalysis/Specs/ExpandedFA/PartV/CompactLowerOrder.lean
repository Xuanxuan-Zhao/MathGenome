import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.SobolevFormBridge
import Mathlib.Algebra.Module.LinearMap.Index
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! The bounded form map takes values in the pointwise scalar antidual.
For such a map T, the adjoint form has value conj (T v u) at (v,u).
Its nullspace is therefore exactly {v | ∀ u, T u v = 0}; this formulation
needs no artificial inner product on the Banach antidual. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace ExpandedFA.PartV.CompactLowerOrder
open ExpandedFA.Sobolev ExpandedFA.Distributions SobolevFormBridge

/-- Closed range, finite nullity and deficiency, index zero, and the exact
compatibility condition against the nullspace of the adjoint form. -/
def FredholmConclusion {𝕜 E : Type} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : E →L[𝕜] (E →L⋆[𝕜] 𝕜)) : Prop :=
  IsClosed (T.range : Set (E →L⋆[𝕜] 𝕜)) ∧
  FiniteDimensional 𝕜 T.ker ∧
  FiniteDimensional 𝕜 ((E →L⋆[𝕜] 𝕜) ⧸ T.range) ∧
  T.toLinearMap.index = 0 ∧
  ∀ F : E →L⋆[𝕜] 𝕜, (∃ u, T u = F) ↔
    ∀ v, (∀ u, T u v = 0) → F v = 0

namespace Spec
/-- The actual L² inclusion and integral form on the gradient realization,
including every L∞ coefficient, both scalar fields, and the empty domain.
The bounded-open-set hypothesis is stronger than the required C¹-domain result. -/
def CompactLowerOrder : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)), EnergyScope Ω →
  ∃ (e : W 𝕜 Ω ≃L[𝕜] Energy 𝕜 Ω)
    (J : Energy 𝕜 Ω →L[𝕜] DomainLp 𝕜 Ω 2),
    (∀ u, (e u).val = gradientMap u) ∧
    (∀ u, J (e u) = u.val.val (zeroIndex d 1)) ∧
    IsCompactOperator J ∧
    ∀ q : DomainLp 𝕜 Ω ∞,
      ∃ B : Energy 𝕜 Ω →L[𝕜] (Energy 𝕜 Ω →L⋆[𝕜] 𝕜),
        (∀ u v : W 𝕜 Ω, B (e u) (e v) =
          ∫ x, q x * conj (v.val.val (zeroIndex d 1) x) *
            u.val.val (zeroIndex d 1) x ∂(volume.restrict (Ω : Set (Domain d)))) ∧
        IsCompactOperator B ∧
        ∀ (a : Hilbert.Conventions.Spec.BoundedSesquilinearFormValue
            𝕜 (Energy 𝕜 Ω) (Energy 𝕜 Ω)) (c : ℝ),
          Hilbert.Conventions.Spec.FormCoerciveValue 𝕜 (Energy 𝕜 Ω) a c →
          FredholmConclusion (a.flip + B)
end Spec
end ExpandedFA.PartV.CompactLowerOrder
