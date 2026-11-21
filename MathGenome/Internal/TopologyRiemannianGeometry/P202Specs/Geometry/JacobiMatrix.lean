import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialJacobi
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace

/-! Independent specification of the Jacobi-operator stages of paper.tex
4114–4138 and 4421–4463. Coordinates are actual parallel linear maps into the
intrinsic tangent fibers. They need not be orthonormal: transpose and
self-adjointness are expressed using the original metric. In an orthonormal
parallel frame these are precisely AᵀB = BᵀA and Uᵀ = U. The analytic estimates
are operator-norm estimates. The same system type accommodates the full tangent
bundle and the normal subbundle; no invertibility or symmetry is included in
its data. All equations are confined to the actual open geodesic interval. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace P202.JacobiMatrixData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.GeodesicData P202.CurvatureData P202.JacobiData
universe u
abbrev Operator (r : ℕ) := Euclidean r →L[ℝ] Euclidean r

/-- A second-order fundamental solution in an actual parallel frame.
The geometric construction below produces this data without assuming a frame
or an ODE solution. Frame injectivity includes the rank-zero case. -/
structure JacobiSystem {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (r : ℕ) where
  frame : (t : ℝ) → Euclidean r →ₗ[ℝ] TangentSpace S (q t).1
  frame_injective : ∀ t ∈ I.carrier, Function.Injective (frame t)
  frame_parallel : ∀ x : Euclidean r, ∀ t ∈ I.carrier,
    HasCovariantDerivativeAt C (fun s => (q s).1) (fun s => frame s x) t 0
  curvature : ℝ → Operator r
  curvature_continuous : ContinuousOn curvature I.carrier
  curvature_eq : ∀ t ∈ I.carrier, ∀ x,
    frame t (curvature t x) = R.val (q t).1 (frame t x) (q t).2 (q t).2
  A : ℝ → Operator r
  B : ℝ → Operator r
  initial_A : A 0 = 0
  initial_B : B 0 = 1
  derivatives : ∀ t ∈ I.carrier,
    HasDerivAt A (B t) t ∧ HasDerivAt B (-(curvature t * A t)) t

noncomputable def riccati {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : Connection (tangentBundle S)}
    {R : CurvatureTensor S} {I : D13Unified.OpenTimeInterval}
    {q : ℝ → Phase S} {r : ℕ} (D : JacobiSystem S C R I q r) (t : ℝ) : Operator r :=
  D.B t * Ring.inverse (D.A t)

end P202.JacobiMatrixData

namespace P202Specs.Geometry.JacobiMatrix
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData P202.LeviCivitaData
  P202.GeodesicData P202.CurvatureData P202.JacobiData P202.ExponentialJacobiData
  P202.JacobiMatrixData
open Set Filter
open scoped Topology
universe u

/-- The full tangent Jacobi operator exists along every affine geodesic
whose open time domain contains zero. No nonconstancy is needed. -/
def constructionType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → 0 ∈ I.carrier →
      ∃ D : JacobiSystem S C R I q n,
        ∀ t ∈ I.carrier, Function.Bijective (D.frame t)

/-- Each column combination is the intrinsic Jacobi field with the prescribed
initial derivative. Every such field agrees on the entire actual interval. -/
def field_representationType : Prop :=
  ∀ {n r : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → 0 ∈ I.carrier →
    ∀ (D : JacobiSystem S C R I q r) (x : Euclidean r),
      let J := fun t => D.frame t (D.A t x)
      IsJacobiField C R I.carrier q J ∧ J 0 = 0 ∧
        HasCovariantDerivativeAt C (fun s => (q s).1) J 0 (D.frame 0 x) ∧
        ∀ K : (t : ℝ) → TangentSpace S (q t).1,
          IsJacobiField C R I.carrier q K → K 0 = 0 →
          HasCovariantDerivativeAt C (fun s => (q s).1) K 0 (D.frame 0 x) →
          ∀ t ∈ I.carrier, K t = J t

/-- The cubic and quadratic orders are retained, with a two-sided
neighborhood of zero in the open time domain. -/
def near_zeroType : Prop :=
  ∀ {n r : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
    0 ∈ I.carrier → ∀ D : JacobiSystem S C R I q r,
      Asymptotics.IsBigO (𝓝 0) (fun t => D.A t - t • (1 : Operator r))
        (fun t : ℝ => t ^ 3) ∧
      Asymptotics.IsBigO (𝓝 0) (fun t => D.B t - (1 : Operator r))
        (fun t : ℝ => t ^ 2)

/-- AᵀA′−(A′)ᵀA = 0, written intrinsically so no unproved orthonormal-frame
identification is hidden in the transpose notation. -/
def wronskianType : Prop :=
  ∀ {n r : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → 0 ∈ I.carrier →
    ∀ (D : JacobiSystem S C R I q r), ∀ t ∈ I.carrier, ∀ x y,
      pairing g (q t).1 (D.frame t (D.A t x)) (D.frame t (D.B t y)) =
      pairing g (q t).1 (D.frame t (D.B t x)) (D.frame t (D.A t y))

/-- Positivity of time is essential; invertibility is proved from absence of
conjugacy along this geodesic, not assumed as a system certificate. -/
def invertibleType : Prop :=
  ∀ {n r : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → ∀ h0 : 0 ∈ I.carrier,
    ∀ (D : JacobiSystem S C R I q r) (t : ℝ), 0 < t →
    ∀ ht : t ∈ I.carrier,
      ¬ ConjugateAlong S C R I q ⟨0, h0⟩ ⟨t, ht⟩ →
      Function.Bijective (D.A t)

/-- Riccati, metric self-adjointness, and the logarithmic determinant formula
on every open positive interval free of conjugacy. -/
def regular_intervalType : Prop :=
  ∀ {n r : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → ∀ h0 : 0 ∈ I.carrier,
    ∀ (D : JacobiSystem S C R I q r) (L : D13Unified.OpenTimeInterval),
      L.carrier ⊆ I.carrier → (∀ t ∈ L.carrier, 0 < t) →
      (∀ t ∈ L.carrier, ∀ ht : t ∈ I.carrier,
        ¬ ConjugateAlong S C R I q ⟨0, h0⟩ ⟨t, ht⟩) →
      ∀ t ∈ L.carrier,
        Function.Bijective (D.A t) ∧
        (∀ x y, pairing g (q t).1 (D.frame t (riccati D t x)) (D.frame t y) =
          pairing g (q t).1 (D.frame t x) (D.frame t (riccati D t y))) ∧
        HasDerivAt (riccati D) (-(riccati D t * riccati D t + D.curvature t)) t ∧
        (0 < LinearMap.det (D.A t).toLinearMap →
          HasDerivAt (fun s => Real.log (LinearMap.det (D.A s).toLinearMap))
            (LinearMap.trace ℝ (Euclidean r) (riccati D t).toLinearMap) t)

/-- The identical construction on the actual parallel normal subbundle of a
unit geodesic. Its rank is n−1; it is not a free-standing abstract matrix model.
All preceding system theorems apply to this same D. -/
def normal_constructionType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → 0 ∈ I.carrier →
      (∀ t ∈ I.carrier, pairing g (q t).1 (q t).2 (q t).2 = 1) →
      ∃ D : JacobiSystem S C R I q (n - 1), ∀ t ∈ I.carrier,
        ∀ v : TangentSpace S (q t).1,
          (∃ x, D.frame t x = v) ↔ pairing g (q t).1 v (q t).2 = 0

end P202Specs.Geometry.JacobiMatrix
