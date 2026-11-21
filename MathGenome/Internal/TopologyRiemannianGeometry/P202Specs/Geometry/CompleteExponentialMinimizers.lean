import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.NormalMinimality
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GeodesicCriticalityCorners

/-! The single-center implication in Theorem 6.10 (paper.tex:3464–3466,
3485–3524). All curves, tangent vectors, maximal domains and lengths are the
canonical upstream objects. Connectedness is imposed on the original manifold;
its dimension may be zero. No completeness or uniqueness is assumed. -/
set_option autoImplicit false

namespace P202.CompleteExponentialData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.CurveData P202.ConnectionData P202.LeviCivitaData
  P202.GeodesicData P202.ExponentialData P202.DistanceData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The original length infimum. On a connected manifold this is the finite
length metric. For points in a component it is definitionally componentDistance,
independently of the chosen proofs of component membership. -/
noncomputable def lengthDistance (g : RiemannianMetric S) (p q : M) : ℝ :=
  sInf (pathLengths g p q)

/-- Defined at time one on every vector of this one fiber. It imposes no
condition on the exponential maps at other centers. -/
def FullExponentialAt (F : CurveFamily (Phase S)) (p : M) : Prop :=
  ∀ v : TangentSpace S p, (⟨p, v⟩ : Phase S) ∈ exponentialDomain F

/-- The original geodesic and its actual compact-interval representative.
The zero vector and the constant minimizing geodesic are explicit when q = p.
No assertion of uniqueness is made. -/
def MinimizingGeodesicsFrom (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S)) (p : M) : Prop :=
  ∀ q : M, ∃ (v : TangentSpace S p) (γ : PiecewiseC1Curve S 0 1),
    γ 0 = p ∧ γ 1 = q ∧ fiberExponential F p v = q ∧
    EqOn γ (fun t => (F.curve ⟨p, v⟩ t).1) (Icc 0 1) ∧
    EqOn γ (fun t => fiberExponential F p (t • v)) (Icc 0 1) ∧
    IsGeodesicOn S C (Icc 0 1) (F.curve ⟨p, v⟩) ∧
    length g γ = tangentNorm g p v ∧ length g γ = lengthDistance g p q ∧
    (∀ {a b : ℝ} (η : PiecewiseC1Curve S a b),
      η a = p → η b = q → length g γ ≤ length g η) ∧
    (q = p → v = 0 ∧ ∀ t ∈ Icc 0 1, γ t = p)

/-- Both the exact closed-ball image identity and its compactness, at every
nonnegative radius, including radius zero. -/
def CompactExponentialBalls (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) : Prop :=
  ∀ R : ℝ, 0 ≤ R →
    {q : M | lengthDistance g p q ≤ R} =
      fiberExponential F p '' {v : TangentSpace S p | tangentNorm g p v ≤ R} ∧
    IsCompact {q : M | lengthDistance g p q ≤ R}

/-- Boundedness is stated in its equivalent form of containment in a ball
about the given center, using the original length metric. -/
def ClosedBoundedCompact (g : RiemannianMetric S) (p : M) : Prop :=
  ∀ K : Set M, IsClosed K →
    (∃ R : ℝ, ∀ q ∈ K, lengthDistance g p q ≤ R) → IsCompact K

end P202.CompleteExponentialData

namespace P202Specs.Geometry.CompleteExponentialMinimizers
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.CompleteExponentialData
universe u

/-- The full original target, without any of the conditional-draft premises.
Choosing any Levi-Civita connection or maximal family changes no hypothesis
on the Riemannian manifold; existence is supplied by the upstream results. -/
def complete_exponential_minimizersType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ p : M, FullExponentialAt F p →
      MinimizingGeodesicsFrom g C F p ∧ CompactExponentialBalls g F p ∧
        ClosedBoundedCompact g p

end P202Specs.Geometry.CompleteExponentialMinimizers
