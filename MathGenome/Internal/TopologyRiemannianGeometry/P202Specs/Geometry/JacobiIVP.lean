import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GeodesicIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CurvatureAlgebra

/-! The linear IVP and decomposition in paper.tex 3975–4022.

`C` is any Levi–Civita connection and `R` represents its curvature with the
source sign convention. Upstream existence and uniqueness make these the
canonical geometric objects; neither a Jacobi solution nor a parallel frame
is assumed. Parameter intervals are the actual open connected geodesic domains,
possibly unbounded. Ambient fields are compared only on those domains.
-/
set_option autoImplicit false
namespace P202.JacobiData
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The second order equation uses two actual covariant derivative relations.
The auxiliary field is the derivative of J, not an existence certificate for
a solution. This avoids letting a default value of a total derivative satisfy
the equation at a point where the derivative does not exist. -/
def IsJacobiField (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : Set ℝ) (q : ℝ → Phase S)
    (J : (t : ℝ) → TangentSpace S (q t).1) : Prop :=
  ∃ V : (t : ℝ) → TangentSpace S (q t).1,
    ∀ t ∈ I,
      HasCovariantDerivativeAt C (fun s => (q s).1) J t (V t) ∧
      HasCovariantDerivativeAt C (fun s => (q s).1) V t
        (-(R.val (q t).1 (J t) (q t).2 (q t).2))

/-- Nonconstancy refers to the actual position curve on its domain. -/
def NonconstantOn (I : Set ℝ) (q : ℝ → Phase S) : Prop :=
  ∃ s ∈ I, ∃ t ∈ I, (q s).1 ≠ (q t).1

noncomputable def tangentialPart (g : RiemannianMetric S) (q : ℝ → Phase S)
    (J : (t : ℝ) → TangentSpace S (q t).1) (t : ℝ) : TangentSpace S (q t).1 :=
  (pairing g (q t).1 (J t) (q t).2 /
    pairing g (q t).1 (q t).2 (q t).2) • (q t).2

noncomputable def normalPart (g : RiemannianMetric S) (q : ℝ → Phase S)
    (J : (t : ℝ) → TangentSpace S (q t).1) (t : ℝ) : TangentSpace S (q t).1 :=
  J t - tangentialPart g q J t

end P202.JacobiData

namespace P202Specs.Geometry.JacobiIVP
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
open Set
universe u

def jacobiFieldType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → Connection (tangentBundle S) →
  CurvatureTensor S → Set ℝ → (q : ℝ → Phase S) →
  ((t : ℝ) → TangentSpace S (q t).1) → Prop

def jacobiFieldValue : jacobiFieldType := @IsJacobiField

def tangentialPartType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → RiemannianMetric S →
  (q : ℝ → Phase S) → ((t : ℝ) → TangentSpace S (q t).1) →
  (t : ℝ) → TangentSpace S (q t).1

noncomputable def tangentialPartValue : tangentialPartType := @tangentialPart
noncomputable def normalPartValue : tangentialPartType := @normalPart

/-- Full-interval existence and uniqueness with arbitrary two initial values.
Constant geodesics and dimension zero are included. -/
def exists_uniqueType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q →
    ∀ t₀ ∈ I.carrier, ∀ u w : TangentSpace S (q t₀).1,
      ∃ J : (t : ℝ) → TangentSpace S (q t).1,
        IsJacobiField C R I.carrier q J ∧ J t₀ = u ∧
        HasCovariantDerivativeAt C (fun s => (q s).1) J t₀ w ∧
        ∀ K : (t : ℝ) → TangentSpace S (q t).1,
          IsJacobiField C R I.carrier q K → K t₀ = u →
          HasCovariantDerivativeAt C (fun s => (q s).1) K t₀ w →
          ∀ t ∈ I.carrier, K t = J t

/-- Affine multiples of velocity are Jacobi fields, including on constant
geodesics; division by speed is unnecessary for this statement. -/
def affine_velocityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (I : Set ℝ) (q : ℝ → Phase S), IsGeodesicOn S C I q →
    ∀ a b : ℝ, IsJacobiField C R I q (fun t => (a + b * t) • (q t).2)

/-- The projection is exactly an affine multiple of velocity. Its complement
is orthogonal to velocity and solves the same intrinsic Jacobi equation. -/
def decompositionType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → NonconstantOn I.carrier q →
    ∀ J : (t : ℝ) → TangentSpace S (q t).1,
      IsJacobiField C R I.carrier q J →
      (∃ a b : ℝ, ∀ t ∈ I.carrier,
        tangentialPart g q J t = (a + b * t) • (q t).2) ∧
      IsJacobiField C R I.carrier q (tangentialPart g q J) ∧
      IsJacobiField C R I.carrier q (normalPart g q J) ∧
      ∀ t ∈ I.carrier, pairing g (q t).1 (normalPart g q J t) (q t).2 = 0

end P202Specs.Geometry.JacobiIVP
