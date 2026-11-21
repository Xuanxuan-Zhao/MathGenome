import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.EberleinSmulian
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecificLimits.Normed

/-! The example `fa2:p1:incomplete-compact-hull`, paper.tex 3296–3307.
Natural coordinate n denotes the manuscript coordinate n+1. The finite-support
space is the range of the canonical coordinate-preserving inclusion into ℓ¹;
its norm and topology are inherited from ℓ¹. Convex hulls are over ℝ, also when
the scalar field is ℂ. Closure below is taken in this incomplete normed space.
-/
noncomputable section
open Filter Set
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.IncompleteCompactHull

abbrev finiteSupportSubmodule (𝕜 : Type u) [RCLike 𝕜] :
    Submodule 𝕜 (C01SequenceSpaces.SequenceLp 𝕜 1) :=
  (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 1).range

abbrev C00 (𝕜 : Type u) [RCLike 𝕜] := ↥(finiteSupportSubmodule 𝕜)

def ofFinsupp (𝕜 : Type u) [RCLike 𝕜] :
    C01SequenceSpaces.SequenceC00 𝕜 →ₗ[𝕜] C00 𝕜 :=
  (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 1).rangeRestrict

/-- The points e_(n+1)/(n+1). -/
def point (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) : C00 𝕜 :=
  ofFinsupp 𝕜 (Finsupp.single n ((n + 1 : 𝕜)⁻¹))

def compactSet (𝕜 : Type u) [RCLike 𝕜] : Set (C00 𝕜) :=
  insert 0 (range (point 𝕜))

def closedHull (𝕜 : Type u) [RCLike 𝕜] : Set (C00 𝕜) :=
  closure (convexHull ℝ (compactSet 𝕜))

def weight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)

def partialCombination (𝕜 : Type u) [RCLike 𝕜] (m : ℕ) : C00 𝕜 :=
  ∑ n ∈ Finset.range m, weight n • point 𝕜 n

abbrev weakTopology (𝕜 : Type u) [RCLike 𝕜] : TopologicalSpace (C00 𝕜) :=
  EberleinSmulian.Spec.weakTopology 𝕜 (C00 𝕜)

namespace Spec
/-- The chosen model is exactly finite-support scalar sequences with the ℓ¹ norm. -/
def ModelIdentification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (Function.Bijective (ofFinsupp 𝕜)) ∧
    (∀ (x : C01SequenceSpaces.SequenceC00 𝕜) n, (ofFinsupp 𝕜 x).val n = x n) ∧
    (∀ x : C00 𝕜, ‖x‖ = ∑' n, ‖x.val n‖)

def CompactSet : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], IsCompact (compactSet 𝕜)

def HullNotWeaklyCompact : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ @IsCompact (C00 𝕜) (weakTopology 𝕜) (closedHull 𝕜)

def HullNotNormCompact : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], ¬ IsCompact (closedHull 𝕜)
end Spec
end ExpandedFA.P1.IncompleteCompactHull
