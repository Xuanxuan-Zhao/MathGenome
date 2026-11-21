import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.UniversalContinuousEmbedding
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Complex.Basic

/-! Independent full statements for paper.tex:6637–6650. No nonemptiness
hypothesis is imposed on either compact Hausdorff space. -/
namespace ExpandedFA.Supplements.BanachStone.Spec

universe u v

/-- Classification of every onto scalar-linear isometric embedding. -/
def ClassificationFor (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (K : Type u) (L : Type v) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace L] [CompactSpace L] [T2Space L]
    (U : C(K, 𝕜) →ₗᵢ[𝕜] C(L, 𝕜)), Function.Surjective U →
    ∃ (φ : L ≃ₜ K) (h : C(L, 𝕜)),
      (∀ t, ‖h t‖ = 1) ∧ ∀ f t, U f t = h t * f (φ t)

def RealClassification : Prop := ClassificationFor.{u,v} ℝ

def ComplexClassification : Prop := ClassificationFor.{u,v} ℂ

/-- Every continuous unimodular weighted composition is an onto linear
isometry, with exactly the stipulated action on functions. -/
def Converse : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜]
    (K : Type u) (L : Type v) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace L] [CompactSpace L] [T2Space L]
    (φ : L ≃ₜ K) (h : C(L, 𝕜)), (∀ t, ‖h t‖ = 1) →
    ∃ U : C(K, 𝕜) ≃ₗᵢ[𝕜] C(L, 𝕜), ∀ f t, U f t = h t * f (φ t)

/-- The continuous real weight in the classification takes only the two signs. -/
def RealSigns : Prop :=
  ∀ (L : Type v) [TopologicalSpace L] (h : C(L, ℝ)),
    (∀ t, ‖h t‖ = 1) → ∀ t, h t = 1 ∨ h t = -1

/-- The separately established universal embedding, retained in this theorem. -/
def UniversalEmbedding : Prop :=
  UniversalContinuousEmbedding.Spec.UniversalEmbedding.{0,u}

end ExpandedFA.Supplements.BanachStone.Spec
