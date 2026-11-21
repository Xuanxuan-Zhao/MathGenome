import MathGenome.Internal.FourierSobolev.Specs.P102.U4.TestSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Compactness.SigmaCompact

/-! Independent statements for the strict LF proposition, paper.tex:1291–1298.
All spaces and seminorms are the canonical ones of `TestSpace`.
The exhaustion is in the ambient Euclidean space, including empty opens and d = 0.
-/
noncomputable section
open Set TopologicalSpace Topology
open scoped ContDiff Distributions
namespace P102.U4

/-- Ambient compact exhaustion by interiors. -/
structure TestExhaustion {d : ℕ} (Ω : Opens (Space d)) where
  compact : ℕ → Compacts (Space d)
  subset_open : ∀ n, (compact n : Set (Space d)) ⊆ Ω
  subset_interior_succ : ∀ n, (compact n : Set (Space d)) ⊆ interior (compact (n + 1))
  interiors_cover : ⋃ n, interior (compact n : Set (Space d)) = Ω

/-- Locally convex inductive limit along the specified exhaustion, on the same underlying
vector space. The infimum is in Lean's order on topologies (finer topologies are smaller). -/
@[instance_reducible]
def exhaustionTopology {d : ℕ} (𝕜 : Type) [RCLike 𝕜] {Ω : Opens (Space d)}
    (e : TestExhaustion Ω) : TopologicalSpace (TestSpace 𝕜 Ω) :=
  sInf {t | @IsTopologicalAddGroup (TestSpace 𝕜 Ω) t _ ∧
    @ContinuousSMul ℝ (TestSpace 𝕜 Ω) _ _ t ∧
    @LocallyConvexSpace ℝ (TestSpace 𝕜 Ω) _ _ _ _ t ∧
    ∀ n, @Continuous _ _ _ t (stageInclusion 𝕜 (e.subset_open n))}

namespace Expected

def FixedSupportFrechet : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space d)),
    T2Space (FixedSupport d 𝕜 K) ∧ MetrizableSpace (FixedSupport d 𝕜 K) ∧
    LocallyConvexSpace ℝ (FixedSupport d 𝕜 K) ∧ CompleteSpace (FixedSupport d 𝕜 K) ∧
    WithSeminorms (coordinateSupSeminorm 𝕜 K)

def FixedStageClosedEmbedding : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (K L : Compacts (Space d)), K ≤ L →
    IsClosedEmbedding (ContDiffMapSupportedIn.monoCLM 𝕜 :
      FixedSupport d 𝕜 K → FixedSupport d 𝕜 L)

def ExistsTestExhaustion : Prop :=
  ∀ (d : ℕ) (Ω : Opens (Space d)), Nonempty (TestExhaustion Ω)

def ExhaustionCofinality : Prop :=
  ∀ (d : ℕ) (Ω : Opens (Space d)) (e : TestExhaustion Ω)
    (K : Compacts (Space d)), (K : Set (Space d)) ⊆ Ω → ∃ n, K ≤ e.compact n

/-- The exhaustion stages cover the whole canonical test space algebraically. -/
def ExhaustionStageCoverage : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (e : TestExhaustion Ω)
    (f : TestSpace 𝕜 Ω), ∃ (n : ℕ) (g : FixedSupport d 𝕜 (e.compact n)),
      stageInclusion 𝕜 (e.subset_open n) g = f

def ExhaustionTopology : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (e : TestExhaustion Ω),
    TestFunction.topologicalSpace Ω 𝕜 ⊤ = exhaustionTopology 𝕜 e

/-- Stronger than the claimed embedding for each exhaustion stage. -/
def StageClosedEmbedding : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (K : Compacts (Space d)) (hK : (K : Set (Space d)) ⊆ Ω),
    IsClosedEmbedding (stageInclusion 𝕜 hK)

def ExhaustionSeminormContinuity : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (e : TestExhaustion Ω)
    (p : Seminorm 𝕜 (TestSpace 𝕜 Ω)),
    Continuous p ↔ ∀ n, Continuous (p ∘ stageInclusion 𝕜 (e.subset_open n))

def EmptyTestSpace : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜], Subsingleton (TestSpace 𝕜 (⊥ : Opens (Space d)))

end Expected
end P102.U4
