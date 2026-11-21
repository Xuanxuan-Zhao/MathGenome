import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.JacobiMatrix
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SecondVariation

/-! Independent specification of the index lemma, paper.tex 4103–4143.
The geodesic is restricted from its actual open affine time domain to [0,b].
The fields, metric, curvature and index form use the shared intrinsic tangent
fibers. Equality of segment fields is equality at every point of [0,b]; values
of total representatives outside the segment do not enter the comparison.
No unit-speed, nonconstancy, normality or minimizing hypothesis is imposed. -/
set_option autoImplicit false
namespace P202.IndexLemmaData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.CurveConnectionData P202.GeodesicData
open Set
universe u

/-- A continuous piecewise C¹ field, including its matching values at every
node. C1FieldOn uses C¹ extensions at both closed edges of each piece, so
these conditions give continuity on the whole segment as well. -/
def PiecewiseC1FieldOn {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (γ : ℝ → M)
    (V : (t : ℝ) → TangentSpace S (γ t)) (a b : ℝ) : Prop :=
  ∃ (k : ℕ) (node : Fin (k+2) → ℝ), StrictMono node ∧
    node 0 = a ∧ node (Fin.last (k+1)) = b ∧
    ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ V
      (Icc (node i.castSucc) (node i.succ))

end P202.IndexLemmaData

namespace P202Specs.Geometry.IndexLemma
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData P202.LeviCivitaData
  P202.GeodesicData P202.CurvatureData P202.JacobiData P202.ExponentialJacobiData
  P202.SecondVariationData P202.IndexLemmaData
open Set
universe u

/-- Only nonconjugacy at the terminal point is needed for the boundary-value
problem. Uniqueness is on the actual geodesic domain, so ambient values outside
that domain are irrelevant. -/
def endpointType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → ∀ h0 : 0 ∈ I.carrier,
    ∀ b : ℝ, 0 < b → ∀ hb : b ∈ I.carrier,
      ¬ ConjugateAlong S C R I q ⟨0,h0⟩ ⟨b,hb⟩ →
    ∀ z : TangentSpace S (q b).1,
      ∃ J : (t : ℝ) → TangentSpace S (q t).1,
        IsJacobiField C R I.carrier q J ∧ J 0 = 0 ∧ J b = z ∧
        ∀ K : (t : ℝ) → TangentSpace S (q t).1,
          IsJacobiField C R I.carrier q K → K 0 = 0 → K b = z →
          ∀ t ∈ I.carrier, K t = J t

/-- The full comparison and its equality case, for every terminal vector and
every continuous piecewise C¹ competitor. No integrability or positivity
certificate is added to the geometric hypotheses. -/
def index_lemmaType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → ∀ h0 : 0 ∈ I.carrier,
    ∀ b : ℝ, 0 < b → Icc 0 b ⊆ I.carrier →
      (∀ t ∈ Ioc 0 b, ∀ ht : t ∈ I.carrier,
        ¬ ConjugateAlong S C R I q ⟨0,h0⟩ ⟨t,ht⟩) →
    ∀ z : TangentSpace S (q b).1,
      ∃ J : (t : ℝ) → TangentSpace S (q t).1,
        IsJacobiField C R I.carrier q J ∧ J 0 = 0 ∧ J b = z ∧
        (∀ K : (t : ℝ) → TangentSpace S (q t).1,
          IsJacobiField C R I.carrier q K → K 0 = 0 → K b = z →
          ∀ t ∈ I.carrier, K t = J t) ∧
        ∀ V : (t : ℝ) → TangentSpace S (q t).1,
          PiecewiseC1FieldOn (fun t => (q t).1) V 0 b → V 0 = 0 → V b = z →
          indexForm g C R (fun t => (q t).1) 0 b J J ≤
            indexForm g C R (fun t => (q t).1) 0 b V V ∧
          (indexForm g C R (fun t => (q t).1) 0 b V V =
            indexForm g C R (fun t => (q t).1) 0 b J J ↔
            ∀ t ∈ Icc 0 b, V t = J t)

/-- Strict positivity applies precisely to a nonzero zero-endpoint field.
Nonzero means nonzero somewhere on the closed segment. -/
def positive_definiteType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → ∀ h0 : 0 ∈ I.carrier,
    ∀ b : ℝ, 0 < b → Icc 0 b ⊆ I.carrier →
      (∀ t ∈ Ioc 0 b, ∀ ht : t ∈ I.carrier,
        ¬ ConjugateAlong S C R I q ⟨0,h0⟩ ⟨t,ht⟩) →
    ∀ V : (t : ℝ) → TangentSpace S (q t).1,
      PiecewiseC1FieldOn (fun t => (q t).1) V 0 b → V 0 = 0 → V b = 0 →
      (∃ t ∈ Icc 0 b, V t ≠ 0) →
        0 < indexForm g C R (fun t => (q t).1) 0 b V V

end P202Specs.Geometry.IndexLemma
