import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.FirstVariation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurvatureAlgebra

/-! Theorem `thm:p202-second-variation`, paper.tex 4065–4101.
Only canonical intrinsic tangent fibers, covariant derivatives, curvature and
energy are used. A common total map on all pieces enforces matching smooth
s-traces at every fixed node. No conclusion of second-variation calculus is
included in any regularity or geodesic hypothesis. -/
set_option autoImplicit false
namespace P202.SecondVariationData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.FirstVariationData P202.CurvatureData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The one-sided intrinsic tangent of the central curve, including its ends. -/
noncomputable def segmentTangent (S : SmoothManifold n .euclidean M)
    (γ : ℝ → M) (a b : ℝ) (t : ℝ) : TangentSpace S (γ t) :=
  segmentVelocity S (fun z => γ z.2) a b t

/-- Smoothness of the curve on the closed segment and vanishing affine
covariant acceleration. The constant s-extension is merely a way to reuse the
upstream coordinate-extension definition of smoothness up to closed edges. -/
def IsAffineGeodesicSegment (C : Connection (tangentBundle S))
    (γ : ℝ → M) (a b : ℝ) : Prop :=
  SmoothVariationOn S (fun z => γ z.2) 1 a b ∧
    ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C γ
      (segmentTangent S γ a b) (Icc a b) t 0

/-- The integrand of the bilinear index form. Its curvature sign agrees with
R(X,Y)Z = ∇X∇Y Z - ∇Y∇X Z - ∇[X,Y]Z in the source. -/
noncomputable def indexIntegrand (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (γ : ℝ → M) (a b : ℝ)
    (V W : (t : ℝ) → TangentSpace S (γ t)) (t : ℝ) : ℝ :=
  pairing g (γ t) (covariantDerivativeWithin C γ V (Icc a b) t)
    (covariantDerivativeWithin C γ W (Icc a b) t) -
  pairing g (γ t) (R.val (γ t) (V t) (segmentTangent S γ a b t)
    (segmentTangent S γ a b t)) (W t)

noncomputable def indexForm (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (γ : ℝ → M) (a b : ℝ)
    (V W : (t : ℝ) → TangentSpace S (γ t)) : ℝ :=
  ∫ t in a..b, indexIntegrand g C R γ a b V W t

/-- D_s ∂s F on the actual s-trace, evaluated at s=0. -/
noncomputable def variationAcceleration (C : Connection (tangentBundle S))
    (F : ℝ × ℝ → M) (t : ℝ) : TangentSpace S (F (0,t)) :=
  covariantDerivative C (fun s => F (s,t))
    (fun s => velocity S (fun r => F (r,t)) s) 0

noncomputable def accelerationBoundary (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : ℝ × ℝ → M) (a b : ℝ) : ℝ :=
  pairing g (F (0,b)) (variationAcceleration C F b) (segmentVelocity S F a b b) -
  pairing g (F (0,a)) (variationAcceleration C F a) (segmentVelocity S F a b a)

/-- Endpoint positions are fixed for all sufficiently small variations. -/
def FixedEndpoints (F : ℝ × ℝ → M) (ε a b : ℝ) : Prop :=
  ∀ s ∈ Ioo (-ε) ε, F (s,a) = F (0,a) ∧ F (s,b) = F (0,b)

/-- The derivatives at finitely many t-breaks may fail to exist as two-sided
derivatives; those values do not affect this integral. -/
def PiecewiseSmoothVariationOn (S : SmoothManifold n .euclidean M)
    (F : ℝ × ℝ → M) (ε : ℝ) {k : ℕ} (node : Fin (k+2) → ℝ) : Prop :=
  ContinuousOn F (Ioo (-ε) ε ×ˢ Icc (node 0) (node (Fin.last (k+1)))) ∧
    ∀ i : Fin (k+1), SmoothVariationOn S F ε (node i.castSucc) (node i.succ)

end P202.SecondVariationData

namespace P202Specs.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set
universe u

-- Definition interfaces have both independent types and expected values.
def indexFormType :=
  {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n .euclidean M} → RiemannianMetric S →
    Connection (tangentBundle S) → CurvatureTensor S → (γ : ℝ → M) →
    ℝ → ℝ → ((t : ℝ) → TangentSpace S (γ t)) →
    ((t : ℝ) → TangentSpace S (γ t)) → ℝ
noncomputable def indexFormValue : indexFormType := @indexForm

def variationAccelerationType :=
  {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n .euclidean M} → Connection (tangentBundle S) →
    (F : ℝ × ℝ → M) → (t : ℝ) → TangentSpace S (F (0,t))
noncomputable def variationAccelerationValue : variationAccelerationType := @variationAcceleration

def accelerationBoundaryType :=
  {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
    {S : SmoothManifold n .euclidean M} → RiemannianMetric S →
    Connection (tangentBundle S) → (ℝ × ℝ → M) → ℝ → ℝ → ℝ
noncomputable def accelerationBoundaryValue : accelerationBoundaryType := @accelerationBoundary

/-- Bilinearity on C¹ fields over a common finite partition. Choosing a
common refinement represents the usual space of continuous piecewise C¹
fields; no artificial integrability certificate is assumed here. -/
def indexForm_bilinearType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (γ : ℝ → M) (a b : ℝ), a < b →
    SmoothVariationOn S (fun z => γ z.2) 1 a b →
    ∀ {k : ℕ} (node : Fin (k+2) → ℝ), StrictMono node →
    node 0 = a → node (Fin.last (k+1)) = b →
    ∀ V U W : (t : ℝ) → TangentSpace S (γ t),
    (∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ V
      (Icc (node i.castSucc) (node i.succ))) →
    (∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ U
      (Icc (node i.castSucc) (node i.succ))) →
    (∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ W
      (Icc (node i.castSucc) (node i.succ))) →
    (indexForm g C R γ a b (fun t => V t + U t) W =
      indexForm g C R γ a b V W + indexForm g C R γ a b U W) ∧
    (indexForm g C R γ a b V (fun t => U t + W t) =
      indexForm g C R γ a b V U + indexForm g C R γ a b V W) ∧
    (∀ c : ℝ,
      indexForm g C R γ a b (fun t => c • V t) W = c * indexForm g C R γ a b V W ∧
      indexForm g C R γ a b V (fun t => c • W t) = c * indexForm g C R γ a b V W)

def indexForm_symmetricType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (γ : ℝ → M) (a b : ℝ) (V W : (t : ℝ) → TangentSpace S (γ t)),
    indexForm g C R γ a b V W = indexForm g C R γ a b W V

/-- Full moving-endpoint formula, stated as an actual second derivative of
the canonical energy, without assuming the existence of that derivative. -/
def second_variation_energyType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (F : ℝ × ℝ → M) (ε a b : ℝ), 0 < ε → a < b →
    SmoothVariationOn S F ε a b →
    IsAffineGeodesicSegment C (fun t => F (0,t)) a b →
    HasDerivAt (deriv (variedEnergy g F a b))
      (indexForm g C R (fun t => F (0,t)) a b (variationField S F) (variationField S F) +
        accelerationBoundary g C F a b) 0

/-- The boundary term vanishes because each endpoint trace is constant.
This assertion itself needs neither geodesicity nor metric compatibility. -/
def fixed_endpoint_boundaryType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : ℝ × ℝ → M)
    (ε a b : ℝ), 0 < ε → FixedEndpoints F ε a b →
    accelerationBoundary g C F a b = 0

/-- The same full formula for fixed finite breaks. Smooth matching s-traces
follow from the segment smoothness of the common map F at each node. The
central curve is a smooth affine geodesic across all the nodes. -/
def piecewise_second_variation_energyType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (F : ℝ × ℝ → M) (ε : ℝ), 0 < ε →
    ∀ {k : ℕ} (node : Fin (k+2) → ℝ), StrictMono node →
    PiecewiseSmoothVariationOn S F ε node →
    IsAffineGeodesicSegment C (fun t => F (0,t))
      (node 0) (node (Fin.last (k+1))) →
    HasDerivAt (deriv (variedEnergy g F (node 0) (node (Fin.last (k+1)))))
      (indexForm g C R (fun t => F (0,t)) (node 0) (node (Fin.last (k+1)))
        (variationField S F) (variationField S F) +
      accelerationBoundary g C F (node 0) (node (Fin.last (k+1)))) 0

end P202Specs.Geometry.SecondVariation
