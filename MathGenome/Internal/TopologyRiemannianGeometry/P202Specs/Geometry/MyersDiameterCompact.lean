import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MinimizingIndexForm
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RicciScalarBianchi
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.HopfRinow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Diameter and compactness in Bonnet--Myers, paper.tex:4703–4732.
The fundamental-group conclusion is allocated separately. All tangent fibers,
curves, curvature, completeness and distance are the original upstream ones.
The frame interface below describes the constructed test fields; it is not
assumed data in the final theorem types. -/
set_option autoImplicit false
namespace P202.MyersData
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.CurvatureData P202.RicciData P202.SecondVariationData
  P202.CriticalityData P202.CompleteExponentialData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The source normalization, on every actual tangent vector. -/
def RicciLowerBound (g : RiemannianMetric S) (R : CurvatureTensor S) (k : ℝ) : Prop :=
  ∀ (p : M) (v : TangentSpace S p),
    ((n : ℝ) - 1) * k * pairing g p v v ≤ ricci R p v v

/-- Diameter for the original length distance. On a connected manifold its
values are the finite metric distances, rather than extended distances. -/
noncomputable def lengthDiameter (g : RiemannianMetric S) : ℝ :=
  sSup (Set.range (fun pq : M × M => lengthDistance g pq.1 pq.2))

/-- The normal frame used by the source proof. Smoothness includes the closed
ends. The trace identity records that adjoining the unit tangent completes
an orthonormal basis; it must be proved in constructing this frame. -/
structure NormalParallelFrame (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (γ : ℝ → M) (L : ℝ) where
  field : Fin (n - 1) → (t : ℝ) → TangentSpace S (γ t)
  smooth : ∀ i, SmoothFieldAlongOn S γ (field i) (Icc 0 L)
  parallel : ∀ i t, t ∈ Icc 0 L →
    HasCovariantDerivativeWithinAt C γ (field i) (Icc 0 L) t 0
  orthonormal : ∀ t ∈ Icc 0 L, ∀ i j,
    pairing g (γ t) (field i t) (field j t) = if i = j then 1 else 0
  normal : ∀ t ∈ Icc 0 L, ∀ i,
    pairing g (γ t) (field i t) (segmentTangent S γ 0 L t) = 0
  trace : ∀ t ∈ Icc 0 L,
    (∑ i, curvatureForm g R (γ t) (field i t)
      (segmentTangent S γ 0 L t) (segmentTangent S γ 0 L t) (field i t)) =
    ricci R (γ t) (segmentTangent S γ 0 L t) (segmentTangent S γ 0 L t)

/-- This assertion has no completeness, curvature bound or minimality
premise. It describes the geometric construction used by the comparison proof. -/
def NormalFramesExist (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S) : Prop :=
  ∀ {L : ℝ}, 0 < L → ∀ γ : PiecewiseC1Curve S 0 L,
    IsAffineGeodesicSegment C γ 0 L →
    (∀ t ∈ Icc 0 L, tangentNorm g (γ t) (segmentTangent S γ 0 L t) = 1) →
    Nonempty (NormalParallelFrame g C R γ L)

end P202.MyersData

namespace P202Specs.Geometry.MyersDiameterCompact
open SmoothManifolds.AtlasData P202.MetricData P202.CurveData
  P202.ConnectionData P202.LeviCivitaData P202.CurvatureData
  P202.SecondVariationData P202.MinimizingIndexData P202.CompletenessData
  P202.CompleteExponentialData P202.MyersData
open Set
universe u

def lengthDiameterType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → RiemannianMetric S → ℝ
noncomputable def lengthDiameterValue : lengthDiameterType := @lengthDiameter

/-- The requested estimate applies to every positive-length unit-speed
minimizing affine geodesic segment. Completeness is unnecessary at this stage. -/
def segment_boundType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R → 2 ≤ n →
    ∀ k : ℝ, 0 < k → RicciLowerBound g R k →
    ∀ {L : ℝ}, 0 < L → ∀ γ : PiecewiseC1Curve S 0 L,
      IsAffineGeodesicSegment C γ 0 L → IsLengthMinimizing g γ →
      (∀ t ∈ Icc 0 L, tangentNorm g (γ t) (segmentTangent S γ 0 L t) = 1) →
      L ≤ Real.pi / Real.sqrt k ∧ length g γ ≤ Real.pi / Real.sqrt k

/-- Pairwise distance, diameter, and compactness, under exactly the original
completeness and curvature hypotheses. Existence of C and R is upstream, so
specifying any Levi-Civita representative does not restrict the manifolds. -/
def diameter_compactType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R → 2 ≤ n →
    ∀ k : ℝ, 0 < k → RicciLowerBound g R k → LengthMetricComplete g →
      (∀ p q : M, lengthDistance g p q ≤ Real.pi / Real.sqrt k) ∧
      lengthDiameter g ≤ Real.pi / Real.sqrt k ∧ IsCompact (univ : Set M)

/-- Intermediate comparison statement for an already constructed frame.
The unconditional Bonnet--Myers statement above has no such premise. -/
def segment_bound_of_framesType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R → 2 ≤ n →
    NormalFramesExist g C R →
    ∀ k : ℝ, 0 < k → RicciLowerBound g R k →
    ∀ {L : ℝ}, 0 < L → ∀ γ : PiecewiseC1Curve S 0 L,
      IsAffineGeodesicSegment C γ 0 L → IsLengthMinimizing g γ →
      (∀ t ∈ Icc 0 L, tangentNorm g (γ t) (segmentTangent S γ 0 L t) = 1) →
      L ≤ Real.pi / Real.sqrt k ∧ length g γ ≤ Real.pi / Real.sqrt k

/-- Intermediate assembly interface for the global conclusion. -/
def diameter_compact_of_framesType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R → 2 ≤ n →
    NormalFramesExist g C R →
    ∀ k : ℝ, 0 < k → RicciLowerBound g R k → LengthMetricComplete g →
      (∀ p q : M, lengthDistance g p q ≤ Real.pi / Real.sqrt k) ∧
      lengthDiameter g ≤ Real.pi / Real.sqrt k ∧ IsCompact (univ : Set M)

end P202Specs.Geometry.MyersDiameterCompact
