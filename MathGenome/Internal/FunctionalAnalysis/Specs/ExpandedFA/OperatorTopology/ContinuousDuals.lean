import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OperatorTopology.Definitions

/-! Independent statements for the dual and convex-set assertions of
`paper.tex:6176–6203`, `fa2:p1:operator-topologies`.
The operators and target dual retain their original norm topology. The tested
functional is scalar-linear over the original field, with real convexity in
both scalar cases. Empty finite sums and zero spaces are included. Lean's
order on topologies is reversed relative to inclusion of open sets. -/
namespace ExpandedFA.OperatorTopology.DualSpec
noncomputable section
universe u v w

def StrongHausdorff : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    @T2Space (E →L[𝕜] F) (Spec.StrongTopologyValue 𝕜 E F)

def WeakHausdorff : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    @T2Space (E →L[𝕜] F) (Spec.WeakTopologyValue 𝕜 E F)

def StrongVectorTopology : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    letI : TopologicalSpace (E →L[𝕜] F) := Spec.StrongTopologyValue 𝕜 E F
    IsTopologicalAddGroup (E →L[𝕜] F) ∧ ContinuousSMul 𝕜 (E →L[𝕜] F)

def WeakVectorTopology : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    letI : TopologicalSpace (E →L[𝕜] F) := Spec.WeakTopologyValue 𝕜 E F
    IsTopologicalAddGroup (E →L[𝕜] F) ∧ ContinuousSMul 𝕜 (E →L[𝕜] F)

def StrongLocallyConvex : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    letI : TopologicalSpace (E →L[𝕜] F) := Spec.StrongTopologyValue 𝕜 E F
    letI : Module ℝ (E →L[𝕜] F) := Module.restrictScalars ℝ 𝕜 (E →L[𝕜] F)
    LocallyConvexSpace ℝ (E →L[𝕜] F)

def WeakLocallyConvex : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    letI : TopologicalSpace (E →L[𝕜] F) := Spec.WeakTopologyValue 𝕜 E F
    letI : Module ℝ (E →L[𝕜] F) := Module.restrictScalars ℝ 𝕜 (E →L[𝕜] F)
    LocallyConvexSpace ℝ (E →L[𝕜] F)

def TopologyComparison : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    (inferInstance : TopologicalSpace (E →L[𝕜] F)) ≤ Spec.StrongTopologyValue 𝕜 E F ∧
    Spec.StrongTopologyValue 𝕜 E F ≤ Spec.WeakTopologyValue 𝕜 E F

def StrongDualFiniteSum : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    ∀ φ : (E →L[𝕜] F) →ₗ[𝕜] 𝕜,
    @Continuous _ _ (Spec.StrongTopologyValue 𝕜 E F) inferInstance φ ↔
    ∃ (s : Finset E) (g : E → F →L[𝕜] 𝕜),
      ∀ T : E →L[𝕜] F, φ T = ∑ x ∈ s, g x (T x)

def WeakDualFiniteSum : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    ∀ φ : (E →L[𝕜] F) →ₗ[𝕜] 𝕜,
    @Continuous _ _ (Spec.WeakTopologyValue 𝕜 E F) inferInstance φ ↔
    ∃ (s : Finset E) (g : E → F →L[𝕜] 𝕜),
      ∀ T : E →L[𝕜] F, φ T = ∑ x ∈ s, g x (T x)

def DualsEqual : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    ∀ φ : (E →L[𝕜] F) →ₗ[𝕜] 𝕜,
    @Continuous _ _ (Spec.StrongTopologyValue 𝕜 E F) inferInstance φ ↔
    @Continuous _ _ (Spec.WeakTopologyValue 𝕜 E F) inferInstance φ

def ClosedConvexSets : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    letI : Module ℝ (E →L[𝕜] F) := Module.restrictScalars ℝ 𝕜 (E →L[𝕜] F)
    ∀ C : Set (E →L[𝕜] F), Convex ℝ C →
    (@IsClosed _ (Spec.StrongTopologyValue 𝕜 E F) C ↔
     @IsClosed _ (Spec.WeakTopologyValue 𝕜 E F) C)

end
end ExpandedFA.OperatorTopology.DualSpec
