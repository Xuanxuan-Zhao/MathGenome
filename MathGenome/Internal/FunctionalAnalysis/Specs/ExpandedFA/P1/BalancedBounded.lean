import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Independent statements for paper.tex:1759–1767 (`fa2:p1:balanced-bounded`).
The real module is the restriction of scalars, as enforced by `IsScalarTower`.
Absolute convexity means balance over the original field and real convexity,
including in the complex case. Boundedness is the shared manuscript definition.
The finite union and sum assertions include empty index sets and empty summands.
-/

open Set Filter
open scoped Topology Pointwise BigOperators

namespace ExpandedFA.P1.BalancedBoundedSpec

def BalancedNeighborhoodBasis : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : E),
      IsOpen V ∧ Balanced 𝕜 V ∧ V ⊆ U

def AbsolutelyConvexNeighborhoodBasis : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    LocallyConvexSpace ℝ E →
    ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : E),
      IsOpen V ∧ Balanced 𝕜 V ∧ Convex ℝ V ∧ V ⊆ U

def NeighborhoodAbsorbing : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ U ∈ 𝓝 (0 : E), Absorbing U

def CompactBounded : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ A : Set E, IsCompact A → Bounded A

def ConvergentSequenceBounded : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ (x : ℕ → E) (a : E), Tendsto x atTop (𝓝 a) → Bounded (range x)

def BoundedClosure : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ A : Set E, Bounded A → Bounded (closure A)

def BoundedFiniteUnion : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ (ι : Type*) (I : Set ι), I.Finite → ∀ A : ι → Set E,
      (∀ i ∈ I, Bounded (A i)) → Bounded (⋃ i ∈ I, A i)

def BoundedFiniteSum : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ (ι : Type*) (I : Finset ι) (A : ι → Set E),
      (∀ i ∈ I, Bounded (A i)) → Bounded (∑ i ∈ I, A i)

def BoundedScalarMultiple : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E],
    ∀ (c : 𝕜) (A : Set E), Bounded A → Bounded (c • A)

def LinearContinuityAtZero : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
    [Module 𝕜 E] [Module 𝕜 F] [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [T2Space E] [T2Space F],
    ∀ T : E →ₗ[𝕜] F, Continuous T ↔ ContinuousAt T 0

def ContinuousLinearImageBounded : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜] [AddCommGroup E] [AddCommGroup F]
    [Module 𝕜 E] [Module 𝕜 F] [Module ℝ E] [Module ℝ F]
    [IsScalarTower ℝ 𝕜 E] [IsScalarTower ℝ 𝕜 F]
    [TopologicalSpace E] [TopologicalSpace F]
    [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [T2Space E] [T2Space F],
    ∀ (T : E →ₗ[𝕜] F), Continuous T →
    ∀ A : Set E, Bounded A → Bounded (T '' A)

end ExpandedFA.P1.BalancedBoundedSpec
