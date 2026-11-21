import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import Mathlib.Topology.Metrizable.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
The incomplete-predual example in fa2:p1:c13:whole-dual, paper.tex 2677–2681.
We put the inherited ℓ² norm on the shared finite-support sequences by taking
the range of their canonical inclusion into ℓ². Natural coordinate n denotes
the manuscript's coordinate n+1. Duals are continuous scalar-linear maps for
this norm; their weak-star topology is the accepted evaluation topology.
-/
noncomputable section
open scoped Topology

universe u
namespace ExpandedFA.P1.IncompleteWholeDualMetric

/-- Finitely supported sequences, with precisely the subspace norm from ℓ². -/
abbrev C00L2 (𝕜 : Type u) [RCLike 𝕜] :=
  ↥(C01SequenceSpaces.Spec.C00ToLpValue 𝕜 2).range

/-- The shared c₀₀ representation, mapped to its ℓ² realization. -/
def c00L2Inclusion (𝕜 : Type u) [RCLike 𝕜] :
    C01SequenceSpaces.SequenceC00 𝕜 →ₗ[𝕜] C00L2 𝕜 :=
  (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 2).rangeRestrict

def c00L2Unit (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : C00L2 𝕜 :=
  c00L2Inclusion 𝕜 (Finsupp.single n 1)

abbrev C00L2Dual (𝕜 : Type u) [RCLike 𝕜] := C00L2 𝕜 →L[𝕜] 𝕜

def c00DualCoordinates (𝕜 : Type u) [RCLike 𝕜] :
    C00L2Dual 𝕜 →ₗ[𝕜] (ℕ → 𝕜) where
  toFun f n := f (c00L2Unit 𝕜 n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev c00DualWeakStar (𝕜 : Type u) [RCLike 𝕜] : TopologicalSpace (C00L2Dual 𝕜) :=
  C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (C00L2 𝕜)

namespace Spec

/-- The finite-support realization preserves every coordinate and the inherited norm. -/
def Realization : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜],
  Function.Bijective (c00L2Inclusion 𝕜) ∧
  (∀ (a : C01SequenceSpaces.SequenceC00 𝕜) n, (c00L2Inclusion 𝕜 a).val n = a n) ∧
  (∀ x : C00L2 𝕜, ‖x‖ = ‖x.val‖) ∧
  (∀ n j, (c00L2Unit 𝕜 n).val j = if j = n then 1 else 0)

/-- Each evaluation is exactly a finite linear combination of the coordinate tests. -/
def EvaluationFormula : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜]
  (a : C01SequenceSpaces.SequenceC00 𝕜) (f : C00L2Dual 𝕜),
  f (c00L2Inclusion 𝕜 a) =
    ∑ n ∈ a.support, a n * c00DualCoordinates 𝕜 f n

/-- All coordinate tests, on the entire dual, generate its weak-star topology. -/
def CoordinateInitial : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜],
  c00DualWeakStar 𝕜 =
    ⨅ n : ℕ, TopologicalSpace.induced
      (fun f : C00L2Dual 𝕜 => c00DualCoordinates 𝕜 f n) inferInstance

/-- A topological embedding into the countable product, with no dual norm bound. -/
def CoordinateEmbedding : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜],
  @Topology.IsEmbedding (C00L2Dual 𝕜) (ℕ → 𝕜) (c00DualWeakStar 𝕜)
    inferInstance (c00DualCoordinates 𝕜)

/-- Metrizability refers to the full dual's weak-star topology. -/
def WholeDualMetrizable : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜],
  @TopologicalSpace.MetrizableSpace (C00L2Dual 𝕜) (c00DualWeakStar 𝕜)

/-- This is an infinite-dimensional incomplete normed predual. -/
def IncompleteInfiniteDimensional : Prop := ∀ (𝕜 : Type u) [RCLike 𝕜],
  ¬ FiniteDimensional 𝕜 (C00L2 𝕜) ∧ ¬ CompleteSpace (C00L2 𝕜)

end Spec
end ExpandedFA.P1.IncompleteWholeDualMetric
