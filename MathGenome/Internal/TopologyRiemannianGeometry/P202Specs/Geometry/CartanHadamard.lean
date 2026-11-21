import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialPullbackComplete
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CompleteLocalIsometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.HopfRinow

/-! Cartan–Hadamard, paper.tex:4642–4697. All dimensions are allowed.
The exponential and geodesics are those of the actual maximal geodesic family.
An affine model supplies the ordinary topology and smooth structure on the
original intrinsic tangent fiber; such models exist by the upstream theorem.
The existence of the Levi–Civita connection and maximal family is also upstream.

Geodesic uniqueness is stated after affine normalization to [0,1], for every
geodesic defined on an open interval containing that segment. It asserts
uniqueness even among nonminimizing geodesics. The existence clause retains
the exact minimizing length, comparison with all piecewise C1 competitors,
and the constant segment for coincident endpoints.

For the universal-cover consequence, a chart in the maximal smooth atlas with
source and target both univ expresses a diffeomorphism with all of R^n, with
its usual smooth structure. An actual diffeomorphism to the standard Euclidean
identity atlas is also included explicitly.
The covering space retains its original topology, and the conclusion constructs
its canonical lifted atlas and complete pullback metric. -/
set_option autoImplicit false

namespace P202.CartanHadamardData
open SmoothManifolds.ModelData
/-- The identity chart on ordinary R^n. Testing smoothness in this atlas is
exactly the usual Euclidean smoothness test. -/
noncomputable def euclideanChart (n : ℕ) : ModelChart n .euclidean (Euclidean n) :=
  (Homeomorph.Set.univ (Euclidean n)).symm.toOpenPartialHomeomorph
end P202.CartanHadamardData

namespace P202Specs.Geometry.CartanHadamard
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.CurvatureData P202.NonpositiveJacobiData P202.CompletenessData
  P202.ExponentialData P202.ExponentialPullbackData P202.CompleteExponentialData
  P202.CoveringMetricData
open Set
universe u

def exponential_coveringType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    NonpositiveSectionalCurvature g R → LengthMetricComplete g →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ (p : M) (A : AffineFiberModel S p),
    letI := A.topology
    FullExponentialAt F p ∧ SmoothCovering A.manifold S (fiberExponential F p)

def exponential_diffeomorphismType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    NonpositiveSectionalCurvature g R → LengthMetricComplete g →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ (p : M) (A : AffineFiberModel S p),
    letI := A.topology
    ∃ D : Diffeomorph A.manifold.smoothStructure.val S.smoothStructure.val,
      ∀ v, D.toEquiv v = fiberExponential F p v

def unique_minimizersType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    [SimplyConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    NonpositiveSectionalCurvature g R → LengthMetricComplete g →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ p : M, MinimizingGeodesicsFrom g C F p ∧
      ∀ (q : M) (a b c d : ℝ), a < b → c < d →
      ∀ (I J : D13Unified.OpenTimeInterval) (γ η : ℝ → Phase S),
        Icc a b ⊆ I.carrier → Icc c d ⊆ J.carrier →
        IsGeodesicOn S C I.carrier γ → IsGeodesicOn S C J.carrier η →
        (γ a).1 = p → (η c).1 = p → (γ b).1 = q → (η d).1 = q →
        ∀ t ∈ Icc (0 : ℝ) 1,
          (γ ((b - a) * t + a)).1 = (η ((d - c) * t + c)).1

def universal_coverType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    NonpositiveSectionalCurvature g R → LengthMetricComplete g →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ (E : Type u) [TopologicalSpace E] [SimplyConnectedSpace E] (π : E → M),
    P202Specs.Topology.Covering π →
    ∃ T : SmoothManifold n .euclidean E,
      T.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (SmoothManifolds.CoveringData.liftedAtlas S.smoothStructure.val π) ∧
      ∃ hp : SmoothCovering T S π,
      (∃ h : RiemannianMetric T, IsLocalIsometry h g π ∧
        (∀ x v w, pairing h x v w = pairing g (π x)
          (SmoothManifolds.differential T S π hp.2.1 x v)
          (SmoothManifolds.differential T S π hp.2.1 x w)) ∧
        LengthMetricComplete h) ∧
      (∃ c : ModelChart n .euclidean E,
        c ∈ T.smoothStructure.val ∧ c.source = univ ∧ c.target = univ) ∧
      Nonempty (Diffeomorph T.smoothStructure.val
        {P202.CartanHadamardData.euclideanChart n})

end P202Specs.Geometry.CartanHadamard
