import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.EuclideanSphericalModels
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.HyperboloidModel
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.BigOperators.Fin

/-! Independent specification for the half-space part and the complete
three-model theorem, paper.tex 3872–3955.  The parameter `m` counts horizontal
coordinates, so this half-space has dimension `m + 1`.  The half-space
construction is proved even in dimension one; its specialization `1 ≤ m`
is exactly the source's range `2 ≤ n`, without an extra restriction on radius.
Smoothness and the metric computation use ambient coordinates and the actual
Fréchet derivative of the prescribed map. The intrinsic bridge below connects
them to the canonical tangent fibers and smooth Riemannian metrics. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace P202.HalfSpaceData
open P202.HyperboloidData

abbrev Coordinates (m : ℕ) := Spatial m × ℝ

def domain (m : ℕ) : Set (Coordinates m) := {q | 0 < q.2}
abbrev HalfSpace (m : ℕ) := ↥(domain m)

/-- Null coordinates U = τ − x_n, V = τ + x_n. -/
def nullU {m : ℕ} (p : Ambient (m + 1)) : ℝ := p.2 - p.1 (Fin.last m)
def nullV {m : ℕ} (p : Ambient (m + 1)) : ℝ := p.2 + p.1 (Fin.last m)

def toHyperboloid {m : ℕ} (a : ℝ) (q : Coordinates m) : Ambient (m + 1) :=
  (Fin.snoc (fun i => a * q.1 i / q.2)
    ((a * (spatialDot q.1 q.1 + q.2 ^ 2) / q.2 - a / q.2) / 2),
    (a * (spatialDot q.1 q.1 + q.2 ^ 2) / q.2 + a / q.2) / 2)

def fromHyperboloid {m : ℕ} (a : ℝ) (p : Ambient (m + 1)) : Coordinates m :=
  ((fun i => p.1 i.castSucc / nullU p), a / nullU p)

/-- The specified half-space Riemannian metric in its standard open chart. -/
def halfMetric {m : ℕ} (a : ℝ) (q v w : Coordinates m) : ℝ :=
  (a ^ 2 / q.2 ^ 2) * (spatialDot v.1 w.1 + v.2 * w.2)

/-- Coordinate realization of a smooth bijective Riemannian isometry.  Both
smooth maps are the explicit formulas above.  The inverse formula is smooth
on the open ambient set U > 0 containing the entire upper sheet. -/
structure HalfSpaceIsometry (m : ℕ) (a : ℝ) where
  equiv : HalfSpace m ≃ Hyperboloid (m + 1) a
  forward : ∀ q, (equiv q).val = toHyperboloid a q.val
  inverse : ∀ p, (equiv.symm p).val = fromHyperboloid a p.val
  positive_null : ∀ p : Hyperboloid (m + 1) a, 0 < nullU p.val
  smooth_forward : ContDiffOn ℝ (⊤ : ℕ∞) (toHyperboloid a) (domain m)
  smooth_inverse : ContDiffOn ℝ (⊤ : ℕ∞) (fromHyperboloid a)
    {p : Ambient (m + 1) | 0 < nullU p}
  metric_pullback : ∀ (q : HalfSpace m) (v w : Coordinates m),
    lorentz (fderiv ℝ (toHyperboloid a) q.val v)
      (fderiv ℝ (toHyperboloid a) q.val w) = halfMetric a q.val v w

/-- Intrinsic half-space realization on the original derivation tangent
fibers.  The global chart fixes the standard smooth structure, and the
coordinate map is fixed by scalar differentiation, rather than chosen freely. -/
structure HalfSpaceModel (m : ℕ) (a : ℝ) where
  manifold : SmoothManifolds.AtlasData.SmoothManifold (m + 1) .euclidean (HalfSpace m)
  standard_chart : ∃ c ∈ manifold.smoothStructure.val,
    c.source = Set.univ ∧
    c.target = {x | 0 < x.val (Fin.last m)} ∧
    ∀ q, (c q).val = Fin.snoc q.val.1 q.val.2
  coordinates : (q : HalfSpace m) →
    SmoothManifolds.TangentData.TangentSpace manifold q ≃ₗ[ℝ] Coordinates m
  coordinates_standard : ∀ q v, coordinates q v =
    ((fun i => P202.ConnectionData.scalarDerivative manifold (fun p => p.val.1 i) q v),
      P202.ConnectionData.scalarDerivative manifold (fun p => p.val.2) q v)
  metric : P202.MetricData.RiemannianMetric manifold
  metric_standard : ∀ q v w,
    P202.MetricData.pairing metric q v w = halfMetric a q.val (coordinates q v) (coordinates q w)

end P202.HalfSpaceData
namespace P202Specs.Geometry.HyperbolicHalfSpace
open P202.HalfSpaceData

def isometryType : Prop :=
  ∀ (m : ℕ) (a : ℝ), 0 < a → Nonempty (HalfSpaceIsometry m a)

/-- Intrinsic bridge to every realization with the prescribed global
projection chart and induced Lorentz metric.  Such realizations are supplied
as a CONCLUSION by `intrinsic_modelType`; they are not assumed to exist.
The conclusion here includes an actual P104 smooth diffeomorphism, its
canonical differential, and equality of the two Riemannian metrics. -/
def intrinsicIsometryType : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (a : ℝ), 0 < a →
    ∀ S : SmoothManifolds.AtlasData.SmoothManifold (m + 1) .euclidean
      (P202.HyperboloidData.Hyperboloid (m + 1) a),
    ∀ g : P202.MetricData.RiemannianMetric S,
    (∃ c ∈ S.smoothStructure.val, c.source = Set.univ ∧ c.target = Set.univ ∧
      ∀ p, (c p).val = p.val.1) →
    P202.HyperboloidData.IsInduced g →
    ∃ H : HalfSpaceModel m a,
    ∃ d : SmoothManifolds.MapData.Diffeomorph H.manifold.smoothStructure.val S.smoothStructure.val,
      (∀ q, (d.toEquiv q).val = toHyperboloid a q.val) ∧
      (∀ p, (d.toEquiv.symm p).val = fromHyperboloid a p.val) ∧
      ∃ L : (q : HalfSpace m) →
        SmoothManifolds.TangentData.TangentSpace H.manifold q →ₗ[ℝ]
        SmoothManifolds.TangentData.TangentSpace S (d.toEquiv q),
        (∀ q, SmoothManifolds.DifferentialData.IsDifferential H.manifold S d.toEquiv q (L q)) ∧
        P202.MetricData.IsMetricPreserving H.metric g d.toEquiv L

/-- The COMPLETE original theorem.  The two intrinsic model propositions are
conclusions to prove, never extra assumptions on the radius or dimension.
Their actual definitions include completeness, sectional curvature and the
unique all-time geodesics, for all velocities including zero. -/
def modelsType : Prop :=
  P202Specs.Geometry.EuclideanSphericalModels.modelsType ∧
  P202Specs.Geometry.HyperboloidModel.intrinsic_modelType ∧
  P202Specs.Geometry.HyperboloidModel.topologyType ∧
  isometryType ∧ intrinsicIsometryType

end P202Specs.Geometry.HyperbolicHalfSpace
