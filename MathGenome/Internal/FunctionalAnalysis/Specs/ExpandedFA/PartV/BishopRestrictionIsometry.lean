import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! The norm and density stage of Bishop restriction interpolation,
paper.tex, `fa2:p5:bishop-interpolation`. Compact sets and the ambient
compact Hausdorff space may be empty. Scalar pairing is linear, not conjugate-linear. -/
noncomputable section
namespace ExpandedFA.PartV.BishopRestrictionIsometrySpec
open Set MeasureTheory
open FunctionSpaces.ScalarRieszMarkovSpec
universe u

variable {𝕜 : Type} [RCLike 𝕜] {K : Type u} [TopologicalSpace K]
  [CompactSpace K] [T2Space K]

/-- Restriction of continuous functions to the actual compact subset. -/
def ambientRestriction (F : TopologicalSpace.Compacts K) : C(K, 𝕜) →L[𝕜] C(F, 𝕜) :=
  ContinuousMap.compCLM 𝕜 𝕜 ⟨Subtype.val, continuous_subtype_val⟩

/-- Restriction with domain the subspace, equipped with its inherited norm. -/
def restriction (Y : Submodule 𝕜 C(K, 𝕜)) (F : TopologicalSpace.Compacts K) :
    Y →L[𝕜] C(F, 𝕜) := (ambientRestriction F).comp Y.subtypeL

/-- The transpose acts on continuous scalar-linear functionals by composition. -/
def restrictionTranspose (Y : Submodule 𝕜 C(K, 𝕜)) (F : TopologicalSpace.Compacts K) :
    (C(F, 𝕜) →L[𝕜] 𝕜) →L[𝕜] (Y →L[𝕜] 𝕜) :=
  { toFun := fun l => l.comp (restriction Y F)
    map_add' := fun _ _ => by ext y; rfl
    map_smul' := fun _ _ => by ext y; rfl
    cont := Continuous.clm_comp_const continuous_id (restriction Y F) }

/-- The measure condition is zero *total variation* on F for every finite
scalar Radon measure annihilating Y. It is not just zero scalar mass. -/
def AnnihilatorsVanish [MeasurableSpace K] [BorelSpace K]
    (Y : Submodule 𝕜 C(K, 𝕜)) (F : TopologicalSpace.Compacts K) : Prop :=
  ∀ μ : VectorMeasure K 𝕜, FiniteScalarRadon μ →
    (∀ y : Y, scalarIntegral μ (y : C(K, 𝕜)) = 0) → μ.variation (F : Set K) = 0

/-- Full transpose-isometry assertion for one of the manuscript's scalar fields. -/
def TransposeIsometry (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (Y : Submodule 𝕜 C(K, 𝕜)),
    IsClosed (Y : Set C(K, 𝕜)) → ∀ F : TopologicalSpace.Compacts K,
    AnnihilatorsVanish Y F → Isometry (restrictionTranspose Y F)

/-- Closure of the image of every open radius-r ball contains the entire
closed radius-r ball, hence also the open radius-r ball in the source statement. -/
def BallImageDensity (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (Y : Submodule 𝕜 C(K, 𝕜)),
    IsClosed (Y : Set C(K, 𝕜)) → ∀ F : TopologicalSpace.Compacts K,
    AnnihilatorsVanish Y F → ∀ r : ℝ, 0 < r →
      Metric.closedBall (0 : C(F, 𝕜)) r ⊆
        closure (restriction Y F '' Metric.ball (0 : Y) r)

def RealTransposeIsometry : Prop := TransposeIsometry.{u} ℝ
def ComplexTransposeIsometry : Prop := TransposeIsometry.{u} ℂ
def RealBallImageDensity : Prop := BallImageDensity.{u} ℝ
def ComplexBallImageDensity : Prop := BallImageDensity.{u} ℂ

end ExpandedFA.PartV.BishopRestrictionIsometrySpec
