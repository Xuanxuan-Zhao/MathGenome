import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.NonpositiveJacobiGrowth

/-! The metric in G23 (paper.tex:4679–4692) lives on the entire original
intrinsic tangent fiber. `AffineFiberModel` records its usual linear smooth
structure explicitly, so tangent vectors to this vector space are identified
with vectors in the original fiber, rather than with unrelated coordinate data.
The existence obligation below prevents this presentation from adding a hypothesis.
All dimensions, including zero, are allowed. -/
set_option autoImplicit false

namespace P202.ExponentialPullbackData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.GeodesicData P202.ExponentialData P202.ExponentialJacobiData
open Set
universe u

/-- A global linear chart equips the actual tangent fiber with its ordinary
finite dimensional topology and maximal smooth structure. -/
structure AffineFiberModel {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (p : M) where
  coordinates : TangentSpace S p ≃ₗ[ℝ] Euclidean n
  topology : TopologicalSpace (TangentSpace S p)
  manifold : @SmoothManifold n .euclidean (TangentSpace S p) topology
  chart : @ModelChart n .euclidean (TangentSpace S p) topology
  chart_mem : chart ∈ manifold.smoothStructure.val
  chart_source : chart.source = univ
  chart_value : ∀ v, (chart v).val = coordinates v

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {p : M}

/-- The canonical vector-space identification T_v(T_p M) ≃ T_p M, expressed
through one linear global chart. It is an equivalence, in rank zero as well. -/
noncomputable def AffineFiberModel.identification (A : AffineFiberModel S p)
    (v : TangentSpace S p) :
    letI := A.topology
    TangentSpace A.manifold v ≃ₗ[ℝ] TangentSpace S p := by
  letI := A.topology
  exact ((tangentStructure A.manifold).fiberCoordinates.equiv A.chart A.chart_mem v
    (A.chart_source ▸ mem_univ v)).trans A.coordinates.symm

end P202.ExponentialPullbackData

namespace P202Specs.Geometry.ExponentialPullbackComplete
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.ExponentialData
  P202.ExponentialJacobiData P202.NonpositiveJacobiData P202.CompletenessData
  P202.ExponentialPullbackData
open Set
universe u

def affine_model_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (p : M), Nonempty (AffineFiberModel S p)

/-- A stronger local version of the norm estimate: completeness is unnecessary
when the input vector lies in the genuine exponential domain. It includes v=0. -/
def differential_expandsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    NonpositiveSectionalCurvature g R →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (v : TangentSpace S p), (⟨p, v⟩ : Phase S) ∈ exponentialDomain F →
    ∀ w : TangentSpace S p,
      tangentNorm g p w ≤ tangentNorm g (fiberExponential F p v)
        (fiberDifferential S F p v w)

/-- Full pullback construction, local isometry, norm domination and metric
completeness. The local compact-ball upper estimate is an explicit conclusion,
not an extra assumption. Its reference norm is exactly g_p. -/
def pullback_completeType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    NonpositiveSectionalCurvature g R → LengthMetricComplete g →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (A : AffineFiberModel S p),
    letI := A.topology
    ∃ h : RiemannianMetric A.manifold,
      (∀ (v : TangentSpace S p) (x y : TangentSpace A.manifold v),
        pairing h v x y = pairing g (fiberExponential F p v)
          (fiberDifferential S F p v (A.identification v x))
          (fiberDifferential S F p v (A.identification v y))) ∧
      IsLocalIsometry h g (fiberExponential F p) ∧
      (∀ (v : TangentSpace S p) (x : TangentSpace A.manifold v),
        tangentNorm g p (A.identification v x) ≤ tangentNorm h v x) ∧
      (∀ v : TangentSpace S p, ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        IsCompact {z : TangentSpace S p | tangentNorm g p (z - v) ≤ r} ∧
        ∀ z : TangentSpace S p, tangentNorm g p (z - v) ≤ r →
        ∀ x : TangentSpace A.manifold z,
          tangentNorm h z x ≤ K * tangentNorm g p (A.identification z x)) ∧
      LengthMetricComplete h

end P202Specs.Geometry.ExponentialPullbackComplete
