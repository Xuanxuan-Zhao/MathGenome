import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.BasicFundamentalGroups
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.HopfRinow
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurvatureAlgebra
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.StandardCoverings
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Contractible

/-! Canonical Euclidean and spherical models for the assigned stages of
`thm:p202-models`, paper.tex 3870–3904 and 3932, with independent statements
of their construction, topology, completeness, curvature and geodesic formulas.
The sphere is literally the radius-a metric sphere in Euclidean (n+1)-space;
at radius one it is the exact sphere of the accepted topology result. -/
set_option autoImplicit false
noncomputable section
namespace P202.SpaceFormData

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) (a : ℝ) := ↥(Metric.sphere (0 : E (n + 1)) a)

def line {n : ℕ} (p v : E n) (t : ℝ) : E n := p + t • v

def greatCircle {n : ℕ} (a : ℝ) (p u : E n) (t : ℝ) : E n :=
  Real.cos (t / a) • p + (a * Real.sin (t / a)) • u

def greatCircleVelocity {n : ℕ} (a : ℝ) (p u : E n) (t : ℝ) : E n :=
  (-(Real.sin (t / a)) / a) • p + Real.cos (t / a) • u

/-- The zero-speed branch is essential for the completeness application. -/
def sphereCurve {n : ℕ} (a : ℝ) (p v : E n) (t : ℝ) : E n :=
  if v = 0 then p else greatCircle a p (‖v‖⁻¹ • v) (‖v‖ * t)

def sphereCurveVelocity {n : ℕ} (a : ℝ) (p v : E n) (t : ℝ) : E n :=
  if v = 0 then 0 else ‖v‖ • greatCircleVelocity a p (‖v‖⁻¹ • v) (‖v‖ * t)

/- These data specify the actual intrinsic geometric realizations.
All certificates occur in conclusions of the existence targets, never as
additional hypotheses on the original n, a. -/
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData
  P202.CurveConnectionData P202.GeodesicData P202.CurvatureData

/-- A realization on the standard smooth Euclidean space, together with its
actual intrinsic tangent-coordinate map and the standard inner product. -/
structure EuclideanModel (n : ℕ) where
  manifold : SmoothManifold n .euclidean (E n)
  standard : manifold.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
    (SmoothManifolds.MapData.transportAtlas
      (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm
      (SmoothManifolds.StandardCoveringData.euclideanAtlas n))
  coordinates : (p : E n) → TangentSpace manifold p ≃ₗ[ℝ] E n
  velocity : ∀ (c : ℝ → E n) (t : ℝ) (v : TangentSpace manifold (c t)),
    HasVelocityWithinAt manifold c Set.univ t v ↔ HasDerivAt c (coordinates (c t) v) t
  metric : RiemannianMetric manifold
  metric_standard : ∀ p v w, pairing metric p v w = inner ℝ (coordinates p v) (coordinates p w)
  connection : Connection (tangentBundle manifold)
  leviCivita : IsLeviCivita metric connection

/-- A sphere with the smooth inclusion into standard Euclidean space and its
literal induced metric. Its tangent images are the actual orthogonal vectors. -/
structure SphericalModel (n : ℕ) (a : ℝ) (A : EuclideanModel (n + 1)) where
  manifold : SmoothManifold n .euclidean (Sphere n a)
  inclusion : SmoothImmersion manifold A.manifold Subtype.val
  tangent_range : ∀ p w, (∃ v, A.coordinates p.val (inclusion.differential p v) = w) ↔
    inner ℝ p.val w = 0
  metric : RiemannianMetric manifold
  induced : IsMetricPreserving metric A.metric Subtype.val inclusion.differential
  connection : Connection (tangentBundle manifold)
  leviCivita : IsLeviCivita metric connection

def SphericalModel.ambientVector {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) (p : Sphere n a) (v : TangentSpace B.manifold p) : E (n + 1) :=
  A.coordinates p.val (B.inclusion.differential p v)

def EuclideanModel.Conclusion {n : ℕ} (G : EuclideanModel n) : Prop :=
  ConnectedSpace (E n) ∧ SimplyConnectedSpace (E n) ∧
  P202.CompletenessData.LengthMetricComplete G.metric ∧
  (∃ T : CurvatureTensor G.manifold, RepresentsCurvature G.connection T ∧
    ∀ p X Y h, sectionalCurvature G.metric T p X Y h = 0) ∧
  ∀ p v, ∃ q : ℝ → Phase G.manifold,
    IsMaximalThrough G.manifold G.connection ⟨p, v⟩ D13Unified.OpenTimeInterval.whole q ∧
    ∀ t, (q t).1 = line p (G.coordinates p v) t ∧
      G.coordinates (q t).1 (q t).2 = G.coordinates p v ∧
      tangentNorm G.metric (q t).1 (q t).2 = ‖G.coordinates p v‖

def SphericalModel.Conclusion {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) : Prop :=
  ConnectedSpace (Sphere n a) ∧ SimplyConnectedSpace (Sphere n a) ∧
  P202.CompletenessData.LengthMetricComplete B.metric ∧
  (∃ T : CurvatureTensor B.manifold, RepresentsCurvature B.connection T ∧
    ∀ p X Y h, sectionalCurvature B.metric T p X Y h = (a ^ 2)⁻¹) ∧
  (∀ p v, ∃ q : ℝ → Phase B.manifold,
    IsMaximalThrough B.manifold B.connection ⟨p, v⟩ D13Unified.OpenTimeInterval.whole q ∧
    ∀ t, (q t).1.val = sphereCurve a p.val (B.ambientVector p v) t ∧
      B.ambientVector (q t).1 (q t).2 = sphereCurveVelocity a p.val (B.ambientVector p v) t ∧
      tangentNorm B.metric (q t).1 (q t).2 = tangentNorm B.metric p v) ∧
  (∀ p u, tangentNorm B.metric p u = 1 → ∃ q : ℝ → Phase B.manifold,
    IsMaximalThrough B.manifold B.connection ⟨p, u⟩ D13Unified.OpenTimeInterval.whole q ∧
    ∀ t, (q t).1.val = greatCircle a p.val (B.ambientVector p u) t ∧
      B.ambientVector (q t).1 (q t).2 = greatCircleVelocity a p.val (B.ambientVector p u) t ∧
      tangentNorm B.metric (q t).1 (q t).2 = 1)

end P202.SpaceFormData

namespace P202Specs.Geometry.EuclideanSphericalModels
open P202.SpaceFormData

/-- Actual homeomorphism to the unit sphere used by the earlier pi_1 proof. -/
def radiusBridgeType : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a →
    ∃ e : Sphere n a ≃ₜ P202Specs.Topology.BasicFundamentalGroups.Sphere n,
      (∀ p, (e p).val = a⁻¹ • p.val) ∧ (∀ q, (e.symm q).val = a • q.val)

def topologyType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a : ℝ, 0 < a →
    (ConnectedSpace (E n) ∧ SimplyConnectedSpace (E n)) ∧
    (ConnectedSpace (Sphere n a) ∧ SimplyConnectedSpace (Sphere n a))

def lineType : Prop :=
  ∀ (n : ℕ) (p v : E n), line p v 0 = p ∧
    (∀ t, HasDerivAt (line p v) v t) ∧
    (∀ t, HasDerivAt (fun _ : ℝ => v) 0 t)

/-- Both derivatives, membership, speed, and initial data. Normal ambient
acceleration is recorded explicitly, without calling it intrinsic geodesicity. -/
def greatCircleType : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a → ∀ (p u : E n),
    ‖p‖ = a → inner ℝ p u = 0 → ‖u‖ = 1 →
    greatCircle a p u 0 = p ∧ greatCircleVelocity a p u 0 = u ∧
    ∀ t : ℝ,
      ‖greatCircle a p u t‖ = a ∧ ‖greatCircleVelocity a p u t‖ = 1 ∧
      HasDerivAt (greatCircle a p u) (greatCircleVelocity a p u t) t ∧
      HasDerivAt (greatCircleVelocity a p u) (-(a⁻¹ ^ 2) • greatCircle a p u t) t

/-- All velocities, with zero included, are covered by the actual affine
rescalings of the displayed unit-speed great circles. -/
def arbitraryVelocityType : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a → ∀ (p v : E n),
    ‖p‖ = a → inner ℝ p v = 0 →
    sphereCurve a p v 0 = p ∧ sphereCurveVelocity a p v 0 = v ∧
    ∀ t : ℝ,
      ‖sphereCurve a p v t‖ = a ∧ ‖sphereCurveVelocity a p v t‖ = ‖v‖ ∧
      HasDerivAt (sphereCurve a p v) (sphereCurveVelocity a p v t) t ∧
      HasDerivAt (sphereCurveVelocity a p v)
        (-(‖v‖ ^ 2 / a ^ 2) • sphereCurve a p v t) t

/-- Actual smooth standard metrics and Levi--Civita connections, including
an induced radius-a sphere with its original intrinsic tangent fibers. -/
def constructionType : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a →
    Nonempty (EuclideanModel n) ∧
      ∃ A : EuclideanModel (n + 1), Nonempty (SphericalModel n a A)

/-- The complete Euclidean part, in every dimension. -/
def euclideanModelType : Prop :=
  ∀ n : ℕ, ∃ G : EuclideanModel n, G.Conclusion

/-- The all-speed spherical formulas lift to actual intrinsic velocities.
Intrinsic covariant acceleration remains a separate obligation in modelsType. -/
def sphericalPhaseType : Prop :=
  ∀ {n : ℕ} {a : ℝ}, 0 < a →
    ∀ {A : EuclideanModel (n + 1)} (B : SphericalModel n a A)
      (p : Sphere n a) (v : SmoothManifolds.TangentData.TangentSpace B.manifold p),
    ∃ q : ℝ → P202.GeodesicData.Phase B.manifold, q 0 = ⟨p, v⟩ ∧
      (∀ t, P202.CurveConnectionData.HasVelocityWithinAt B.manifold
        (fun s => (q s).1) Set.univ t (q t).2) ∧
      ∀ t,
      (q t).1.val = sphereCurve a p.val (B.ambientVector p v) t ∧
      B.ambientVector (q t).1 (q t).2 = sphereCurveVelocity a p.val (B.ambientVector p v) t ∧
      P202.MetricData.tangentNorm B.metric (q t).1 (q t).2 =
        P202.MetricData.tangentNorm B.metric p v ∧
      HasDerivAt (fun s => (q s).1.val) (B.ambientVector (q t).1 (q t).2) t ∧
      HasDerivAt (fun s => B.ambientVector (q s).1 (q s).2)
        (-(‖B.ambientVector p v‖ ^ 2 / a ^ 2) • (q t).1.val) t

/-- Completeness of the induced length metric and existence of actual global
maximal intrinsic geodesics, before identifying their explicit formulas. -/
def sphericalCompletenessType : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {a : ℝ}, 0 < a →
    ∀ {A : EuclideanModel (n + 1)} (B : SphericalModel n a A),
      P202.CompletenessData.LengthMetricComplete B.metric ∧
      P202.HopfRinowData.GeodesicallyComplete B.manifold B.connection ∧
      ∀ w : P202.GeodesicData.Phase B.manifold,
        ∃ q : ℝ → P202.GeodesicData.Phase B.manifold,
          P202.GeodesicData.IsMaximalThrough B.manifold B.connection w
            D13Unified.OpenTimeInterval.whole q

/-- The complete original Euclidean and spherical model obligation. This
expected proposition retains the full conclusion. Maximality is the actual upstream universal extension property, and
hence includes uniqueness and vanishing intrinsic covariant acceleration. -/
def modelsType : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ a : ℝ, 0 < a →
    ∃ (G : EuclideanModel n) (A : EuclideanModel (n + 1)) (B : SphericalModel n a A),
      G.Conclusion ∧ A.Conclusion ∧ B.Conclusion

end P202Specs.Geometry.EuclideanSphericalModels
