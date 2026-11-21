import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OperatorTopology.ContinuousDuals

/-! Independent specifications for `fa2:p1:operator-topologies`, paper.tex:6176–6209.
The topology definitions and structural assertions are the accepted canonical ones.
All compositions below have domain E, intermediate space F, and target G.
There is no completeness assumption for fixed factors or uniformly bounded nets.
Only the sequence corollary assumes that F is Banach. Zero spaces are included.
-/

namespace ExpandedFA.OperatorTopology.CompositionSpec
open scoped Topology
noncomputable section
universe u v w z a

/-- The structural part, using the shared full statements, including real convexity. -/
def Structure : Prop :=
  DualSpec.StrongHausdorff.{u,v,w} ∧ DualSpec.WeakHausdorff.{u,v,w} ∧
  DualSpec.StrongVectorTopology.{u,v,w} ∧ DualSpec.WeakVectorTopology.{u,v,w} ∧
  DualSpec.StrongLocallyConvex.{u,v,w} ∧ DualSpec.WeakLocallyConvex.{u,v,w} ∧
  DualSpec.TopologyComparison.{u,v,w} ∧ DualSpec.StrongDualFiniteSum.{u,v,w} ∧
  DualSpec.WeakDualFiniteSum.{u,v,w} ∧ DualSpec.DualsEqual.{u,v,w} ∧
  DualSpec.ClosedConvexSets.{u,v,w}

def StrongLeft : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (G : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G],
    ∀ A : F →L[𝕜] G,
    @Continuous (E →L[𝕜] F) (E →L[𝕜] G)
      (Spec.StrongTopologyValue 𝕜 E F) (Spec.StrongTopologyValue 𝕜 E G)
      (fun T => A.comp T)

def StrongRight : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (G : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G],
    ∀ B : E →L[𝕜] F,
    @Continuous (F →L[𝕜] G) (E →L[𝕜] G)
      (Spec.StrongTopologyValue 𝕜 F G) (Spec.StrongTopologyValue 𝕜 E G)
      (fun T => T.comp B)

def WeakLeft : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (G : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G],
    ∀ A : F →L[𝕜] G,
    @Continuous (E →L[𝕜] F) (E →L[𝕜] G)
      (Spec.WeakTopologyValue 𝕜 E F) (Spec.WeakTopologyValue 𝕜 E G)
      (fun T => A.comp T)

def WeakRight : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (G : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G],
    ∀ B : E →L[𝕜] F,
    @Continuous (F →L[𝕜] G) (E →L[𝕜] G)
      (Spec.WeakTopologyValue 𝕜 F G) (Spec.WeakTopologyValue 𝕜 E G)
      (fun T => T.comp B)

/-- Arbitrary-filter version of the net assertion. The bound is over the full
index family, not just one tail, and is imposed only on the outer factors. -/
def BoundedStrongComposition : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (G : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G],
    ∀ (ι : Type a) (l : Filter ι) (S : ι → E →L[𝕜] F) (T : ι → F →L[𝕜] G)
      (S₀ : E →L[𝕜] F) (T₀ : F →L[𝕜] G),
    Filter.Tendsto S l (@nhds _ (Spec.StrongTopologyValue 𝕜 E F) S₀) →
    Filter.Tendsto T l (@nhds _ (Spec.StrongTopologyValue 𝕜 F G) T₀) →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ i, ‖T i‖ ≤ C) →
    Filter.Tendsto (fun i => (T i).comp (S i)) l
      (@nhds _ (Spec.StrongTopologyValue 𝕜 E G) (T₀.comp S₀))

/-- Strong convergence of a sequence on a Banach domain gives a full uniform bound. -/
def StrongSequenceBound : Prop :=
  ∀ (𝕜 : Type u) (F : Type w) (G : Type z) [RCLike 𝕜]
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 F] [NormedSpace 𝕜 G] [CompleteSpace F],
    ∀ (T : ℕ → F →L[𝕜] G) (T₀ : F →L[𝕜] G),
    Filter.Tendsto T Filter.atTop (@nhds _ (Spec.StrongTopologyValue 𝕜 F G) T₀) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖T n‖ ≤ C

/-- Completeness is needed only for the intermediate space. -/
def StrongSequenceComposition : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (G : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G],
    ∀ [CompleteSpace F],
    ∀ (S : ℕ → E →L[𝕜] F) (T : ℕ → F →L[𝕜] G)
      (S₀ : E →L[𝕜] F) (T₀ : F →L[𝕜] G),
    Filter.Tendsto S Filter.atTop (@nhds _ (Spec.StrongTopologyValue 𝕜 E F) S₀) →
    Filter.Tendsto T Filter.atTop (@nhds _ (Spec.StrongTopologyValue 𝕜 F G) T₀) →
    Filter.Tendsto (fun n => (T n).comp (S n)) Filter.atTop
      (@nhds _ (Spec.StrongTopologyValue 𝕜 E G) (T₀.comp S₀))

end
end ExpandedFA.OperatorTopology.CompositionSpec
