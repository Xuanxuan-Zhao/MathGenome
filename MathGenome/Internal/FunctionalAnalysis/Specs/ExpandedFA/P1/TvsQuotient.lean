import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsQuotientTopology

/-! Independent statements for the completeness and Fréchet clauses of
`fa2:p1:tvs-quotient`, paper.tex:1896–1930. All subspaces have the induced
topology, all quotients the module quotient topology, and completeness always
means completeness for the translation uniformity of that topology. -/

open Set Filter TopologicalSpace
open scoped Topology

namespace ExpandedFA.P1.TvsQuotientSpec

/-- The topological assertions, including arbitrary maps out of the quotient,
are supplied by the accepted quotient-topology interface. -/
def TopologicalQuotient.{u, v, w} : Prop :=
  TvsQuotientTopologySpec.QuotientTVS.{u, v} ∧
  TvsQuotientTopologySpec.QuotientHausdorff.{u, v} ∧
  TvsQuotientTopologySpec.ProjectionContinuousOpen.{u, v} ∧
  TvsQuotientTopologySpec.UniversalContinuity.{u, v, w} ∧
  TvsQuotientTopologySpec.QuotientLocallyConvex.{u, v} ∧
  TvsQuotientTopologySpec.QuotientCountableLocalBasis.{u, v}

def QuotientMetrizable : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [T2Space E], ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) →
      MetrizableSpace E → MetrizableSpace (E ⧸ M)

/-- The source assumes metrizability of the ambient TVS, not a norm or local
convexity. There is no properness or nonzero hypothesis on the subspace. -/
def QuotientComplete : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [T2Space E], ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) →
      MetrizableSpace E → TranslationComplete E → TranslationComplete (E ⧸ M)

/-- Completeness of a subspace forces closedness in a Hausdorff TVS, with no
ambient completeness or metrizability assumption. -/
def CompleteSubspaceClosed : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [T2Space E], ∀ M : Submodule 𝕜 E,
      TranslationComplete M → IsClosed (M : Set E)

def ClosedSubspaceComplete : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [T2Space E], ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) →
      TranslationComplete E → TranslationComplete M

def ClosedSubspaceFSpace : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E], FSpace 𝕜 E →
      ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) → FSpace 𝕜 M

def ClosedQuotientFSpace : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E], FSpace 𝕜 E →
      ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) → FSpace 𝕜 (E ⧸ M)

/-- Convexity is real convexity even for complex subspaces. -/
def ClosedSubspaceFrechet : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E], FrechetSpace 𝕜 E →
      ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) → FrechetSpace 𝕜 M

def ClosedQuotientFrechet : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E], FrechetSpace 𝕜 E →
      ∀ M : Submodule 𝕜 E, IsClosed (M : Set E) → FrechetSpace 𝕜 (E ⧸ M)

end ExpandedFA.P1.TvsQuotientSpec
