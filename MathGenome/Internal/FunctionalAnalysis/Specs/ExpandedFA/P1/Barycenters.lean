import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.CompactHullMeasureBarycenters

/-! Independent statements of all three clauses of `fa2:p1:barycenters`,
paper.tex:2155–2164. Convex hulls are real, and the tests use the original
scalar-linear continuous dual. No local convexity or metrizability is imposed.
The Borel sigma algebra belongs to the original compact Hausdorff topology.
-/

namespace ExpandedFA.P1.Barycenters.Spec

open Set MeasureTheory

universe u v w

/-- Existence in the compact closed convex hull and uniqueness there, with
integrability of every scalar test made explicit. -/
def BarycenterExistsUnique : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (Q : Type w) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
    [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [TopologicalSpace Q] [T2Space Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q],
    (∀ x y : E, x ≠ y → ∃ ℓ : E →L[𝕜] 𝕜, ℓ x ≠ ℓ y) →
    ∀ (μ : Measure Q) [IsProbabilityMeasure μ], μ.Regular →
    ∀ (f : Q → E), Continuous f → IsCompact (closure (convexHull ℝ (range f))) →
    ∃! b : E, b ∈ closure (convexHull ℝ (range f)) ∧
      ∀ ℓ : E →L[𝕜] 𝕜, Integrable (fun q => ℓ (f q)) μ ∧
        ℓ b = ∫ q, ℓ (f q) ∂μ

/-- The representing-probability clause uses the accepted shared statement,
including the empty compact set and regularity on its original topology. -/
def RepresentingProbability : Prop :=
  CompactHullMeasureBarycenters.Spec.RepresentingProbability.{u,v}

/-- The norm bound for any barycenter in a Banach space. Its scalar moment
identities suffice; the compact-hull hypothesis is needed only for existence. -/
def BarycenterNormEstimate : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (Q : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [TopologicalSpace Q] [T2Space Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q],
    ∀ (μ : Measure Q) [IsProbabilityMeasure μ], μ.Regular →
    ∀ (f : Q → E), Continuous f → ∀ b : E,
      (∀ ℓ : E →L[𝕜] 𝕜, ℓ b = ∫ q, ℓ (f q) ∂μ) →
      Integrable (fun q => ‖f q‖) μ ∧ ‖b‖ ≤ ∫ q, ‖f q‖ ∂μ

end ExpandedFA.P1.Barycenters.Spec
