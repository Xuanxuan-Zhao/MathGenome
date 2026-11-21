import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12Convergence
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05LinfinityCounterexample
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
Independent statements for `fa2:p1:c12:examples`, paper.tex 2344–2360.
Scalars range over ℝ and ℂ. Natural index n denotes manuscript index n+1.
All duals are continuous scalar-linear duals with their original norm topology.
The topology on ℓ∞ uses the bilinear ℓ¹ pairing, and is explicitly identified
with the weak-star topology transported through an isometric duality.
Finite dimension includes dimension zero. Equality with the norm topology is
stated on E, and all three topologies are compared on E′, where they coexist.
-/

noncomputable section
open Filter
open scoped Topology ENNReal
universe u v
namespace ExpandedFA.P1.C12Examples.Spec
open C01SequenceSpaces

def TailSequenceType := ∀ (𝕜 : Type u) [RCLike 𝕜], ℕ → SequenceLInfinity 𝕜

def TailSequenceValue : TailSequenceType := fun 𝕜 _ n =>
  ⟨fun k => if n ≤ k then 1 else 0, memℓp_infty ⟨1, by
    rintro _ ⟨k, rfl⟩
    dsimp only
    split_ifs <;> simp⟩⟩

def TailTopologyType := ∀ (𝕜 : Type u) [RCLike 𝕜],
  TopologicalSpace (SequenceLInfinity 𝕜)

/-- σ(ℓ∞,ℓ¹), using the linear dual, with no complex conjugation. -/
def TailTopologyValue : TailTopologyType := fun 𝕜 _ =>
  ⨅ a : SequenceLp 𝕜 1,
    TopologicalSpace.induced (fun x : SequenceLInfinity 𝕜 => ∑' k, x k * a k)
      inferInstance

def UnitVectors : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    Tendsto (fun n : ℕ => lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜)) atTop
      (@nhds (SequenceLp 𝕜 2)
        (C12DualPairSpec.DualPairTopologyValue 𝕜 (SequenceLp 𝕜 2)
          (SequenceLp 𝕜 2 →L[𝕜] 𝕜) (topDualPairing 𝕜 (SequenceLp 𝕜 2))) 0) ∧
    (∀ n : ℕ, ‖lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜)‖ = 1) ∧
    ¬ Tendsto (fun n : ℕ => lp.single (E := fun _ : ℕ => 𝕜) 2 n (1 : 𝕜))
      atTop (𝓝 (0 : SequenceLp 𝕜 2))

def TailWeakStar : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    Tendsto (TailSequenceValue 𝕜) atTop
      (@nhds (SequenceLInfinity 𝕜) (TailTopologyValue 𝕜) 0)

def SpecifiedPredual : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ U : SequenceLInfinity 𝕜 ≃ₗᵢ[𝕜] (SequenceLp 𝕜 1 →L[𝕜] 𝕜),
      (∀ x a, U x a = ∑' k, x k * a k) ∧
      TailTopologyValue 𝕜 = TopologicalSpace.induced U
        (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (SequenceLp 𝕜 1)) ∧
      Tendsto (fun n => U (TailSequenceValue 𝕜 n)) atTop
        (@nhds (SequenceLp 𝕜 1 →L[𝕜] 𝕜)
          (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (SequenceLp 𝕜 1)) 0)

/-- The whole subspace of convergent bounded sequences carries the norm-one
limit functional; a norm-one extension agrees with it and detects every tail. -/
def LimitExtension : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ (lim : C05LinfinityCounterexample.convergentSequences 𝕜 →L[𝕜] 𝕜)
      (L : SequenceLInfinity 𝕜 →L[𝕜] 𝕜),
      ‖lim‖ = 1 ∧ ‖L‖ = 1 ∧
      (∀ (x : C05LinfinityCounterexample.convergentSequences 𝕜) (a : 𝕜),
        Tendsto (fun k => x.val k) atTop (𝓝 a) → lim x = a) ∧
      (∀ x : C05LinfinityCounterexample.convergentSequences 𝕜, L x.val = lim x) ∧
      (∀ n : ℕ, L (TailSequenceValue 𝕜 n) = 1)

def TailNotWeak : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ Tendsto (TailSequenceValue 𝕜) atTop
      (@nhds (SequenceLInfinity 𝕜)
        (C12DualPairSpec.DualPairTopologyValue 𝕜 (SequenceLInfinity 𝕜)
          (SequenceLInfinity 𝕜 →L[𝕜] 𝕜) (topDualPairing 𝕜 (SequenceLInfinity 𝕜))) 0)

def WeakNormEquality : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E],
    C12DualPairSpec.DualPairTopologyValue 𝕜 E (E →L[𝕜] 𝕜) (topDualPairing 𝕜 E) =
      (inferInstance : TopologicalSpace E)

def CanonicalEvaluationSurjective : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E],
    Function.Surjective (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)

def DualTopologiesEquality : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E],
    C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E =
      C12WeakStar.Spec.DualWeakTopologyValue 𝕜 E ∧
    C12WeakStar.Spec.DualWeakTopologyValue 𝕜 E =
      (inferInstance : TopologicalSpace (E →L[𝕜] 𝕜))

end ExpandedFA.P1.C12Examples.Spec
