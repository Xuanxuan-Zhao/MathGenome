import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.HopfRinow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.SmoothMaps

/-! Hyperboloid stage of thm:p202-models, paper.tex 3874–3891 and
3906–3934. Coordinates are finite real tuples with their usual topology;
no positive-definite ambient metric is imposed on the Lorentz form. -/
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
open scoped BigOperators

namespace P202.HyperboloidData

abbrev Spatial (n : ℕ) := Fin n → ℝ
abbrev Ambient (n : ℕ) := Spatial n × ℝ

def spatialDot {n : ℕ} (x y : Spatial n) : ℝ := ∑ i, x i * y i

def lorentz {n : ℕ} (p q : Ambient n) : ℝ := spatialDot p.1 q.1 - p.2 * q.2

def upperSheet (n : ℕ) (a : ℝ) : Set (Ambient n) :=
  {p | lorentz p p = -(a ^ 2) ∧ 0 < p.2}

abbrev Hyperboloid (n : ℕ) (a : ℝ) := ↥(upperSheet n a)

/-- The ambient description of the tangent plane. Its identification with
intrinsic derivation tangent fibers is a separate obligation. -/
def tangentPlane {n : ℕ} (p : Ambient n) : Set (Ambient n) :=
  {v | lorentz p v = 0}

noncomputable def graphPoint {n : ℕ} (a : ℝ) (x : Spatial n) : Ambient n :=
  (x, Real.sqrt (a ^ 2 + spatialDot x x))

noncomputable def unitCurve {n : ℕ} (a : ℝ) (p u : Ambient n) (t : ℝ) : Ambient n :=
  Real.cosh (t / a) • p + (a * Real.sinh (t / a)) • u

noncomputable def unitVelocity {n : ℕ} (a : ℝ) (p u : Ambient n) (t : ℝ) : Ambient n :=
  (Real.sinh (t / a) / a) • p + Real.cosh (t / a) • u

noncomputable def unitAcceleration {n : ℕ} (a : ℝ) (p u : Ambient n) (t : ℝ) : Ambient n :=
  (a ^ 2)⁻¹ • unitCurve a p u t

/-- The intrinsic differential of ambient inclusion, expressed through the
actual scalar differentials on derivation tangent fibers. Smoothness of these
coordinate representatives is established from the projection chart. -/
noncomputable def ambientDifferential {n : ℕ} {a : ℝ}
    (S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean (Hyperboloid n a))
    (p : Hyperboloid n a) (v : SmoothManifolds.TangentData.TangentSpace S p) : Ambient n :=
  ((fun i => P202.ConnectionData.scalarDerivative S (fun q => q.val.1 i) p v),
    P202.ConnectionData.scalarDerivative S (fun q => q.val.2) p v)

/-- The required metric is exactly the Lorentz restriction, not an arbitrary
positive metric on the same manifold. -/
def IsInduced {n : ℕ} {a : ℝ}
    {S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean (Hyperboloid n a)}
    (g : P202.MetricData.RiemannianMetric S) : Prop :=
  ∀ p v w, P202.MetricData.pairing g p v w =
    lorentz (ambientDifferential S p v) (ambientDifferential S p w)

/-- Actual connection curvature, with the manuscript's commutator sign. -/
noncomputable def curvatureField {n : ℕ} {a : ℝ}
    {S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean (Hyperboloid n a)}
    (C : P202.ConnectionData.Connection (P202.ConnectionData.tangentBundle S))
    (X Y Z : P202.ConnectionData.Field S) : P202.ConnectionData.Field S :=
  C.cov X (C.cov Y Z) + (-1 : ℝ) • C.cov Y (C.cov X Z) +
    (-1 : ℝ) • C.cov (P202.TorsionMetricData.bracket X Y) Z

end P202.HyperboloidData

namespace P202Specs.Geometry.HyperboloidModel
open P202.HyperboloidData

def lorentzType := {n : ℕ} → Ambient n → Ambient n → ℝ
def lorentzValue : lorentzType := @lorentz

-- The explicit dependent function type is used below for the set definition.
def upperSheetSetType := (n : ℕ) → ℝ → Set (Ambient n)
def upperSheetValue : upperSheetSetType := upperSheet

def graphPointType := {n : ℕ} → ℝ → Spatial n → Ambient n
noncomputable def graphPointValue : graphPointType := @graphPoint

def unitCurveType := {n : ℕ} → ℝ → Ambient n → Ambient n → ℝ → Ambient n
noncomputable def unitCurveValue : unitCurveType := @unitCurve

/-- Global projection, with its prescribed graph inverse, in the subspace topology. -/
def projection_homeomorphType : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a →
    ∃ e : Hyperboloid n a ≃ₜ Spatial n,
      (∀ p, e p = p.val.1) ∧ (∀ x, (e.symm x).val = graphPoint a x)

/-- This stronger dimension-free form includes the n≥2 source case. -/
def tangent_positiveType : Prop :=
  ∀ {n : ℕ} {a : ℝ}, 0 < a → ∀ p ∈ upperSheet n a,
    ∀ v ∈ tangentPlane p, v ≠ 0 → 0 < lorentz v v

/-- Quantitative coercivity from the source's Lorentz calculation. -/
def tangent_lower_boundType : Prop :=
  ∀ {n : ℕ} {a : ℝ}, 0 < a → ∀ p ∈ upperSheet n a,
    ∀ v ∈ tangentPlane p,
      (a ^ 2 / p.2 ^ 2) * spatialDot v.1 v.1 ≤ lorentz v v

/-- Ambient assertions are required before interpreting this curve intrinsically. -/
def unit_curve_ambientType : Prop :=
  ∀ {n : ℕ} {a : ℝ}, 0 < a → ∀ p ∈ upperSheet n a,
    ∀ u ∈ tangentPlane p, lorentz u u = 1 →
      unitCurve a p u 0 = p ∧ unitVelocity a p u 0 = u ∧
      ∀ t : ℝ,
        unitCurve a p u t ∈ upperSheet n a ∧
        HasDerivAt (unitCurve a p u) (unitVelocity a p u t) t ∧
        HasDerivAt (unitVelocity a p u) (unitAcceleration a p u t) t ∧
        lorentz (unitCurve a p u t) (unitVelocity a p u t) = 0 ∧
        lorentz (unitVelocity a p u t) (unitVelocity a p u t) = 1

/-- Ambient normal-acceleration curves for all tangent initial velocities. -/
def all_velocity_ambientType : Prop :=
  ∀ {n : ℕ} {a : ℝ}, 0 < a → ∀ p ∈ upperSheet n a,
    ∀ v ∈ tangentPlane p,
    ∃ γ δ : ℝ → Ambient n, γ 0 = p ∧ δ 0 = v ∧
      ∀ t : ℝ, γ t ∈ upperSheet n a ∧
        HasDerivAt γ (δ t) t ∧
        HasDerivAt δ ((lorentz v v / a ^ 2) • γ t) t ∧
        lorentz (δ t) (δ t) = lorentz v v

def topologyType : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a →
    ConnectedSpace (Hyperboloid n a) ∧ SimplyConnectedSpace (Hyperboloid n a)

/-- A global chart of exactly the original n-dimensional Euclidean model. -/
def smooth_manifoldType : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a →
    ∃ S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean (Hyperboloid n a),
      ∃ c ∈ S.smoothStructure.val,
        c.source = Set.univ ∧ c.target = Set.univ ∧
        (∀ p, (c p).val = p.val.1) ∧
        (∀ x, (c.symm x).val = graphPoint a x.val)

/-- Smoothness of the parametrization into the original ambient real space. -/
def graph_smoothType : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a →
    ContDiff ℝ (⊤ : ℕ∞) (graphPoint a : Spatial n → Ambient n)

/-- The target Euclidean structure contains its usual global identity chart. -/
def projection_diffeomorphType : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a →
    ∃ S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean (Hyperboloid n a),
    ∃ E : SmoothManifolds.AtlasData.SmoothManifold n .euclidean (Spatial n),
      (∃ c ∈ E.smoothStructure.val, c.source = Set.univ ∧ c.target = Set.univ ∧
        ∀ x, (c x).val = x) ∧
      ∃ d : SmoothManifolds.MapData.Diffeomorph S.smoothStructure.val E.smoothStructure.val,
        (∀ p, d.toEquiv p = p.val.1) ∧
        (∀ x, (d.toEquiv.symm x).val = graphPoint a x)

open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.HopfRinowData P202.CompletenessData

/-- The differential of inclusion has exactly the Lorentz-orthogonal plane
as its image in any smooth structure with the prescribed projection chart. -/
def tangent_identificationType : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a →
    ∀ (S : SmoothManifold n .euclidean (Hyperboloid n a))
      (c : SmoothManifolds.ModelData.ModelChart n .euclidean (Hyperboloid n a)),
      c ∈ S.smoothStructure.val → c.source = Set.univ →
      (∀ q, (c q).val = q.val.1) →
      ∀ p, Function.Injective (ambientDifferential S p) ∧
        Set.range (ambientDifferential S p) = tangentPlane p.val

/-- The smooth induced Riemannian metric, on the canonical intrinsic fibers,
including the full tangent-plane identification. -/
def induced_metricType : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a →
    ∃ S : SmoothManifold n .euclidean (Hyperboloid n a),
      (∃ c ∈ S.smoothStructure.val,
        c.source = Set.univ ∧ c.target = Set.univ ∧
        (∀ p, (c p).val = p.val.1) ∧
        (∀ x, (c.symm x).val = graphPoint a x.val)) ∧
      ∃ g : RiemannianMetric S, IsInduced g ∧
        ∀ p, Function.Injective (ambientDifferential S p) ∧
          Set.range (ambientDifferential S p) = tangentPlane p.val

/-- The induced metric admits its unique actual Levi-Civita connection. -/
def induced_leviCivitaType : Prop :=
  ∀ (n : ℕ) (a : ℝ), 0 < a →
    ∃ S : SmoothManifold n .euclidean (Hyperboloid n a),
      (∃ c ∈ S.smoothStructure.val,
        c.source = Set.univ ∧ c.target = Set.univ ∧
        (∀ p, (c p).val = p.val.1) ∧
        (∀ x, (c.symm x).val = graphPoint a x.val)) ∧
      ∃ g : RiemannianMetric S, IsInduced g ∧
        (∀ p, Function.Injective (ambientDifferential S p) ∧
          Set.range (ambientDifferential S p) = tangentPlane p.val) ∧
        ∃! C : Connection (tangentBundle S), IsLeviCivita g C

/-- The full intrinsic model on the original tangent fibers, with the induced
metric, its Levi-Civita curvature, global geodesics, and both completeness
assertions. This independent expected proposition assumes no construction
certificate. -/
def intrinsic_modelType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (a : ℝ), 0 < a →
    ∃ S : SmoothManifold n .euclidean (Hyperboloid n a),
      (∃ c ∈ S.smoothStructure.val,
        c.source = Set.univ ∧ c.target = Set.univ ∧
        (∀ p, (c p).val = p.val.1) ∧
        (∀ x, (c.symm x).val = graphPoint a x.val)) ∧
      ∃ g : RiemannianMetric S, IsInduced g ∧
        (∀ p, Function.Injective (ambientDifferential S p) ∧
          Set.range (ambientDifferential S p) = tangentPlane p.val) ∧
        ∃ C : Connection (tangentBundle S), IsLeviCivita g C ∧
          -- The complete curvature tensor formula fixes the sectional value.
          (∀ (X Y Z : Field S) (p : Hyperboloid n a),
            (curvatureField C X Y Z).val p =
              (-(a ^ 2)⁻¹) •
                (pairing g p (Y.val p) (Z.val p) • X.val p -
                 pairing g p (X.val p) (Z.val p) • Y.val p)) ∧
          (∀ (X Y : Field S) (p : Hyperboloid n a),
            pairing g p (X.val p) (X.val p) * pairing g p (Y.val p) (Y.val p) -
              pairing g p (X.val p) (Y.val p) ^ 2 ≠ 0 →
            pairing g p ((curvatureField C X Y Y).val p) (X.val p) /
              (pairing g p (X.val p) (X.val p) * pairing g p (Y.val p) (Y.val p) -
                pairing g p (X.val p) (Y.val p) ^ 2) = -(a ^ 2)⁻¹) ∧
          (∀ (p : Hyperboloid n a) (u : TangentSpace S p), pairing g p u u = 1 →
            ∃ q : ℝ → Phase S,
              q 0 = ⟨p, u⟩ ∧ IsGeodesicOn S C Set.univ q ∧
              (∀ r : ℝ → Phase S, r 0 = ⟨p, u⟩ →
                IsGeodesicOn S C Set.univ r → r = q) ∧
              ∀ t : ℝ,
                (q t).1.val = unitCurve a p.val (ambientDifferential S p u) t ∧
                ambientDifferential S (q t).1 (q t).2 =
                  unitVelocity a p.val (ambientDifferential S p u) t ∧
                pairing g (q t).1 (q t).2 (q t).2 = 1) ∧
          GeodesicallyComplete S C ∧ LengthMetricComplete g

end P202Specs.Geometry.HyperboloidModel
