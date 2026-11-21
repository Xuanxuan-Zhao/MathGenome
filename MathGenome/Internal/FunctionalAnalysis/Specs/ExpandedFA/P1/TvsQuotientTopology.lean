import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions

/-!
Independent statements for the topological clauses of `fa2:p1:tvs-quotient`,
paper.tex:1896–1914. The quotient is the algebraic module quotient with its
native quotient topology, not a norm quotient or an independently chosen topology.
The scalar field is real or complex. Local convexity always means real convexity;
the real module structure agrees with restriction of scalars by `IsScalarTower`.

Completeness and the Frechet consequences belong to the separately allocated
`root_tvs_quotient` goal. No nontriviality or properness of the submodule is assumed.
-/

open Set Filter
open scoped Topology

namespace ExpandedFA.P1.TvsQuotientTopologySpec

/-- Addition and scalar multiplication remain jointly continuous. -/
def QuotientTVS : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) → TVS 𝕜 (E ⧸ M)

/-- A closed subspace has Hausdorff quotient. -/
def QuotientHausdorff : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) → T2Space (E ⧸ M)

/-- The projection, already bundled as a scalar-linear map, is continuous and open. -/
def ProjectionContinuousOpen : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) →
      Continuous M.mkQ ∧ IsOpenMap M.mkQ

/-- The universal property concerns every map into any topological space,
without linearity or separation requirements on that map or its target. -/
def UniversalContinuity : Prop :=
  ∀ (𝕜 E Y : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [TopologicalSpace Y], ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) →
    ∀ f : (E ⧸ M) → Y, Continuous f ↔ Continuous (f ∘ M.mkQ)

/-- Real local convexity passes to both real and complex quotients. -/
def QuotientLocallyConvex : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) →
      LocallyConvexSpace ℝ E → LocallyConvexSpace ℝ (E ⧸ M)

/-- A countable local base means the zero-neighborhood filter is countably
generated. Only local countability at zero is required. -/
def QuotientCountableLocalBasis : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) →
      (𝓝 (0 : E)).IsCountablyGenerated →
      (𝓝 (0 : E ⧸ M)).IsCountablyGenerated

end ExpandedFA.P1.TvsQuotientTopologySpec
