import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricFoundation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricGeodesicCompleteness
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CoveringLifting
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.CoveringStructure

/-! The converse of Theorem 9.1 and the geometric universal-cover bridge.
The topologies and intrinsic tangent fibers are the original ones. Smooth
coverings include surjectivity. The componentwise formulation below retains
arbitrary disconnected smooth covering spaces and includes dimension zero. -/
set_option autoImplicit false

namespace P202.CoveringMetricData
open SmoothManifolds.AtlasData P202.MetricData P202.CompletenessData
universe u

/-- A surjective topological covering which is a local diffeomorphism. -/
def SmoothCovering {n : ℕ} {E B : Type u}
    [TopologicalSpace E] [TopologicalSpace B]
    (T : SmoothManifold n .euclidean E) (S : SmoothManifold n .euclidean B)
    (p : E → B) : Prop :=
  P202Specs.Topology.Covering p ∧ SmoothManifolds.TensorData.IsLocalDiffeomorphism T S p

/-- Completeness for the canonical upstream length distance on every
connected component, with exactly the original subspace topology. No finite
distance between different components is introduced. -/
def ComponentwiseComplete {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S) : Prop :=
  ∀ x : M, ∃ d : MetricSpace (connectedComponent x),
    d.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (connectedComponent x)) ∧
    (∀ p q, @dist _ d.toDist p q = P202.DistanceData.componentDistance g x p q) ∧
    @CompleteSpace (connectedComponent x) d.toUniformSpace

end P202.CoveringMetricData

namespace P202Specs.Geometry.CoveringMetricCompleteness
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.CoveringData P202.MetricData P202.CoveringMetricData
universe u

def smoothCoveringType := {n : ℕ} → {E B : Type u} →
  [TopologicalSpace E] → [TopologicalSpace B] →
  SmoothManifold n .euclidean E → SmoothManifold n .euclidean B → (E → B) → Prop

def smoothCoveringValue : smoothCoveringType := @SmoothCovering

def componentwiseCompleteType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → RiemannianMetric S → Prop

def componentwiseCompleteValue : componentwiseCompleteType := @ComponentwiseComplete

/-- For a connected manifold the componentwise convention agrees exactly
with the existing upstream notion of completeness of the length metric. -/
def connected_complete_iffType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S),
    ComponentwiseComplete g ↔ P202.CompletenessData.LengthMetricComplete g

/-- Equivalent description in terms of smooth projection and all smooth local
inverse branches. P104's IsSmoothCovering alone does not require surjectivity. -/
def smoothCovering_iff_branchesType : Prop :=
  ∀ {n : ℕ} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (T : SmoothManifold n .euclidean E) (S : SmoothManifold n .euclidean B) (p : E → B),
    SmoothCovering T S p ↔ Function.Surjective p ∧ IsSmoothCovering T S p

/-- The metric is smooth and positive definite, with the actual differential
of the projection as its pullback formula. No connectedness or completeness
of either manifold is used in this construction. -/
def pullback_metricType : Prop :=
  ∀ {n : ℕ} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (T : SmoothManifold n .euclidean E) (S : SmoothManifold n .euclidean B)
    (p : E → B) (hp : SmoothCovering T S p) (g : RiemannianMetric S),
    ∃ h : RiemannianMetric T, IsLocalIsometry h g p ∧
      ∀ x v w, pairing h x v w = pairing g (p x)
        (SmoothManifolds.differential T S p hp.2.1 x v)
        (SmoothManifolds.differential T S p hp.2.1 x w)

/-- Uniqueness is equality of maximal smooth atlases on the same topology. -/
def smooth_structure_agreementType : Prop :=
  ∀ {n : ℕ} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (T T' : SmoothManifold n .euclidean E) (S : SmoothManifold n .euclidean B)
    (p : E → B), SmoothCovering T S p → SmoothCovering T' S p →
      T.smoothStructure = T'.smoothStructure

/-- Hausdorffness needs no connectedness assumption on the total space. -/
def covering_hausdorffType : Prop :=
  ∀ {n : ℕ} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (S : SmoothManifold n .euclidean B) (p : E → B),
    P202Specs.Topology.Covering p → T2Space E

/-- Connected topological covers, including universal covers, retain their
original topology, acquire the canonical lifted atlas and its pullback metric,
and agree with every existing smooth covering structure. -/
def canonical_geometryType : Prop :=
  ∀ {n : ℕ} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    [PreconnectedSpace E] (S : SmoothManifold n .euclidean B)
    (g : RiemannianMetric S) (p : E → B), P202Specs.Topology.Covering p →
    T2Space E ∧ SecondCountableTopology E ∧
      ∃ T : SmoothManifold n .euclidean E,
        T.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
          (liftedAtlas S.smoothStructure.val p) ∧
        SmoothCovering T S p ∧
        (∃ h : RiemannianMetric T, IsLocalIsometry h g p) ∧
        ∀ T' : SmoothManifold n .euclidean E, SmoothCovering T' S p →
          T'.smoothStructure = T.smoothStructure

/-- A base curve extended to all real times has a unique continuous lift for
all real times through any specified point. No completeness is used here. -/
def real_path_liftingType : Prop :=
  ∀ (E B : Type u) [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), P202Specs.Topology.Covering p →
    ∀ (γ : C(ℝ, B)) (e : E), p e = γ 0 →
      ∃! L : C(ℝ, E), L 0 = e ∧ ∀ t, p (L t) = γ t

/-- Full converse, componentwise on both manifolds. Neither connectedness of E
nor completeness of E is a hypothesis. -/
def covering_completeType : Prop :=
  ∀ {n : ℕ} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    (T : SmoothManifold n .euclidean E) (S : SmoothManifold n .euclidean B)
    (p : E → B) (hp : SmoothCovering T S p) (g : RiemannianMetric S),
    ComponentwiseComplete g →
      ∃ h : RiemannianMetric T, IsLocalIsometry h g p ∧
        (∀ x v w, pairing h x v w = pairing g (p x)
          (SmoothManifolds.differential T S p hp.2.1 x v)
          (SmoothManifolds.differential T S p hp.2.1 x w)) ∧
        ComponentwiseComplete h

/-- Explicit specialization to the usual connected complete base hypothesis.
The total covering space is still allowed to be disconnected. -/
def covering_complete_connectedBaseType : Prop :=
  ∀ {n : ℕ} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace B]
    (T : SmoothManifold n .euclidean E) (S : SmoothManifold n .euclidean B)
    (p : E → B) (hp : SmoothCovering T S p) (g : RiemannianMetric S),
    P202.CompletenessData.LengthMetricComplete g →
      ∃ h : RiemannianMetric T, IsLocalIsometry h g p ∧
        (∀ x v w, pairing h x v w = pairing g (p x)
          (SmoothManifolds.differential T S p hp.2.1 x v)
          (SmoothManifolds.differential T S p hp.2.1 x w)) ∧
        ComponentwiseComplete h

/-- The complete metric on a connected topological cover is constructed, rather
than assumed; its topology is the original covering-space topology. -/
def canonical_complete_geometryType : Prop :=
  ∀ {n : ℕ} {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
    [PreconnectedSpace E] (S : SmoothManifold n .euclidean B)
    (g : RiemannianMetric S) (p : E → B), P202Specs.Topology.Covering p →
    ComponentwiseComplete g →
      ∃ T : SmoothManifold n .euclidean E,
        T.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
          (liftedAtlas S.smoothStructure.val p) ∧
        SmoothCovering T S p ∧
        ∃ h : RiemannianMetric T, IsLocalIsometry h g p ∧ ComponentwiseComplete h

end P202Specs.Geometry.CoveringMetricCompleteness
