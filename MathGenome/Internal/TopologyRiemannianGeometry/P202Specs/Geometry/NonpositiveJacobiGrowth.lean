import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialJacobi
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricGeodesicCompleteness
import Mathlib.Analysis.Convex.Deriv

/-! G23, paper.tex:4652–4677. All geometric objects are the intrinsic
upstream ones. The local results are stronger than the complete-manifold
specialization: they hold on every actual open geodesic interval, at arbitrary
affine speed, without a normality assumption. No dimension restriction is used. -/
set_option autoImplicit false
namespace P202.NonpositiveJacobiData
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurvatureData
universe u

def NonpositiveSectionalCurvature {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (R : CurvatureTensor S) : Prop :=
  ∀ (p : M) (x y : TangentSpace S p) (h : LinearIndependent ℝ ![x, y]),
    sectionalCurvature g R p x y h ≤ 0
end P202.NonpositiveJacobiData

namespace P202Specs.Geometry.NonpositiveJacobiGrowth
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData P202.LeviCivitaData
  P202.GeodesicData P202.CurvatureData P202.JacobiData P202.ExponentialData
  P202.ExponentialJacobiData P202.NonpositiveJacobiData P202.CompletenessData
open Set
universe u

def growthType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    NonpositiveSectionalCurvature g R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
    IsGeodesicOn S C I.carrier q → 0 ∈ I.carrier →
    ∀ (J : (t : ℝ) → TangentSpace S (q t).1),
    IsJacobiField C R I.carrier q J → J 0 = 0 →
    ∀ w : TangentSpace S (q 0).1,
    HasCovariantDerivativeAt C (fun t => (q t).1) J 0 w →
      (∀ t ∈ I.carrier, 0 ≤ t → t * tangentNorm g (q 0).1 w ≤
        tangentNorm g (q t).1 (J t)) ∧
      ConvexOn ℝ (I.carrier ∩ Ici 0) (fun t => tangentNorm g (q t).1 (J t)) ∧
      HasDerivWithinAt (fun t => tangentNorm g (q t).1 (J t))
        (tangentNorm g (q 0).1 w) (Ici 0) 0 ∧
      (w ≠ 0 → ∀ t ∈ I.carrier, 0 < t → J t ≠ 0) ∧
      (w = 0 → ∀ t ∈ I.carrier, J t = 0)

def two_zerosType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    NonpositiveSectionalCurvature g R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
    IsGeodesicOn S C I.carrier q →
    ∀ (J : (t : ℝ) → TangentSpace S (q t).1),
    IsJacobiField C R I.carrier q J →
    ∀ a ∈ I.carrier, ∀ b ∈ I.carrier, a ≠ b → J a = 0 → J b = 0 →
      ∀ t ∈ I.carrier, J t = 0

def no_conjugateType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    NonpositiveSectionalCurvature g R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
    IsGeodesicOn S C I.carrier q → ∀ a b : I.carrier, a ≠ b →
      ¬ConjugateAlong S C R I q a b

def nonsingular_on_domainType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    NonpositiveSectionalCurvature g R →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (v : TangentSpace S p), (⟨p, v⟩ : Phase S) ∈ exponentialDomain F →
      Function.Bijective (fiberDifferential S F p v)

/-- Global conclusion under exactly the complete, connected, boundaryless
hypotheses; n=0 and n=1 are included. The first conjunct asserts existence at
every vector, avoiding use of a total exponential outside its genuine domain. -/
def nonsingularType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    NonpositiveSectionalCurvature g R → LengthMetricComplete g →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (v : TangentSpace S p),
      (⟨p, v⟩ : Phase S) ∈ exponentialDomain F ∧
      Function.Bijective (fiberDifferential S F p v)

def differential_zeroType : Prop :=
  P202Specs.Geometry.ExponentialNormalCoordinates.derivative_zeroType.{u}
end P202Specs.Geometry.NonpositiveJacobiGrowth
