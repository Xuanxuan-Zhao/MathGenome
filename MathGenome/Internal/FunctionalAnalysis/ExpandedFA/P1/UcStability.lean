import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UcStability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.UcQuotients
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.UcSums
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.LurRadonRiesz

/-! Uniform convexity stability, `fa2:p1:uc-stability`, paper.tex:4656–4711.
The subspace clause restricts the closed-unit-ball implication. The remaining
clauses assemble the accepted quotient, sum, and Radon–Riesz results. -/
namespace ExpandedFA.P1.UcStability

universe u v w
open scoped ENNReal

/-- Every scalar-linear subspace inherits uniform convexity, whether closed or not. -/
theorem uniformlyConvex_subspace : Spec.Subspace.{u,v} := by
  intro 𝕜 E _ _ _ M hE ε hε hε₂
  obtain ⟨δ, hδ, hgap⟩ := hE ε hε hε₂
  refine ⟨δ, hδ, fun x y hx hy hsep => ?_⟩
  exact hgap (x : E) (y : E) hx hy hsep

/-- The distance quotient by a closed subspace inherits uniform convexity. -/
theorem uniformlyConvex_quotient : Spec.Quotient.{u,v} :=
  UcQuotients.uniformlyConvex_quotient

/-- Local uniform convexity gives the sequential Radon–Riesz property. -/
theorem locallyUniformlyConvex_radonRiesz :
    Spec.LocallyUniformlyConvexRadonRiesz.{u,v} :=
  LurRadonRiesz.locallyUniformlyConvex_radonRiesz

/-- Every finite ℓᵖ sum of uniformly convex spaces is uniformly convex. -/
theorem finite_sum_uniformlyConvex :
    ∀ (𝕜 : Type w) {I : Type u} [Finite I] (E : I → Type v)
      [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
      (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
      (∀ i, C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 (E i)) →
      C14UniformConvexity.Spec.UniformlyConvexValue 𝕜
        (ExpandedFA.Supplements.BanachSumDefinitions.Spec.Space E p) :=
  UcSums.finite_sum_uniformlyConvex

/-- A common positive modulus suffices for an arbitrary ℓᵖ sum. -/
theorem arbitrary_sum_uniformlyConvex :
    ∀ (𝕜 : Type w) {I : Type u} (E : I → Type v)
      [RCLike 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
      (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
      (∀ ε : ℝ, 0 < ε → ε ≤ 2 → ∃ δ : ℝ, 0 < δ ∧
        ∀ i, δ ≤ RotundDefinitions.Spec.ModulusValue 𝕜 (E i) ε) →
      C14UniformConvexity.Spec.UniformlyConvexValue 𝕜
        (ExpandedFA.Supplements.BanachSumDefinitions.Spec.Space E p) :=
  UcSums.arbitrary_sum_uniformlyConvex

end ExpandedFA.P1.UcStability
