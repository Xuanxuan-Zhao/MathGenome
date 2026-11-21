import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialJacobi
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GaussLemma
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SectionalRecovery
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Independent specification of paper.tex 4276–4311.
The angular tangent space at a unit vector v is its metric orthogonal
complement. All tensor equalities quantify both arguments. They do not
assume injectivity or nonsingularity of the exponential. -/
set_option autoImplicit false
namespace P202.ConstantCurvaturePolarData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.ConnectionData P202.MetricData
  P202.CurveConnectionData P202.GeodesicData P202.CurvatureData P202.ExponentialData
universe u

noncomputable def s (k t : ℝ) : ℝ :=
  if 0 < k then Real.sin (Real.sqrt k * t) / Real.sqrt k
  else if k = 0 then t else Real.sinh (Real.sqrt (-k) * t) / Real.sqrt (-k)

noncomputable def c (k t : ℝ) : ℝ :=
  if 0 < k then Real.cos (Real.sqrt k * t)
  else if k = 0 then 1 else Real.cosh (Real.sqrt (-k) * t)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

def ConstantSectional (g : RiemannianMetric S) (R : CurvatureTensor S) (k : ℝ) : Prop :=
  ∀ p (x y : TangentSpace S p) (h : LinearIndependent ℝ ![x, y]),
    sectionalCurvature g R p x y h = k

/-- Intrinsic parallel transport on an open geodesic interval. The selection
has no assumed correctness certificate; existence is proved by the candidate.
No assertion is made outside the given interval. -/
noncomputable def parallel (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (w : TangentSpace S (q 0).1) : (t : ℝ) → TangentSpace S (q t).1 := by
  classical
  exact if h : ∃ P : (t : ℝ) → TangentSpace S (q t).1,
      P 0 = w ∧ ∀ t ∈ I.carrier,
        HasCovariantDerivativeAt C (fun t => (q t).1) P t 0
    then Classical.choose h else fun _ => 0

/-- Differential of (t,v) ↦ exp_p(t v), on a radial and an angular vector.
The scalar multiplication differential is a v + t w. A chain-rule theorem
below verifies this interpretation in genuine atlas coordinates. -/
noncomputable def polarDifferential (F : CurveFamily (Phase S)) (p : M)
    (t : ℝ) (v : TangentSpace S p) (a : ℝ) (w : TangentSpace S p) :
    TangentSpace S (fiberExponential F p (t • v)) :=
  P202.ExponentialJacobiData.fiberDifferential S F p (t • v) (a • v + t • w)

end P202.ConstantCurvaturePolarData

namespace P202Specs.Geometry.ConstantCurvaturePolar
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.ConnectionData P202.MetricData
  P202.CurveConnectionData P202.LeviCivitaData P202.GeodesicData P202.CurvatureData
  P202.JacobiData P202.ExponentialData P202.ExponentialJacobiData
  P202.ConstantCurvaturePolarData
universe u

def scalar_modelType : Prop :=
  ∀ k : ℝ, s k 0 = 0 ∧ c k 0 = 1 ∧
    (∀ t, HasDerivAt (s k) (c k t) t) ∧
    (∀ t, HasDerivAt (c k) (-k * s k t) t) ∧
    (∀ t, deriv (deriv (s k)) t + k * s k t = 0) ∧ deriv (s k) 0 = 1

/-- The closed formula is a normal Jacobi field with precisely the stated
initial data, and is the unique such field on the entire original interval. -/
def normal_jacobiType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ k : ℝ, ConstantSectional g R k →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → 0 ∈ I.carrier →
      (∀ t ∈ I.carrier, pairing g (q t).1 (q t).2 (q t).2 = 1) →
    ∀ w : TangentSpace S (q 0).1, pairing g (q 0).1 w (q 0).2 = 0 →
      let J := fun t => s k t • parallel C I q w t
      IsJacobiField C R I.carrier q J ∧ J 0 = 0 ∧
      HasCovariantDerivativeAt C (fun t => (q t).1) J 0 w ∧
      (∀ t ∈ I.carrier, pairing g (q t).1 (J t) (q t).2 = 0) ∧
      ∀ K : (t : ℝ) → TangentSpace S (q t).1,
        IsJacobiField C R I.carrier q K → K 0 = 0 →
        HasCovariantDerivativeAt C (fun t => (q t).1) K 0 w →
        ∀ t ∈ I.carrier, K t = J t

/-- Chain rule for polar exponential, tested along every affine radial and
fiber variation, in every target chart. Restriction to w ⟂ v gives precisely
the derivative on ℝ × S_p M. -/
def polar_derivativeType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (t : ℝ) (v : TangentSpace S p),
      (⟨p, t • v⟩ : Phase S) ∈ exponentialDomain F →
    ∀ (d : ModelChart n .euclidean M) (hd : d ∈ S.smoothStructure.val)
      (hq : fiberExponential F p (t • v) ∈ d.source) (a : ℝ) (w : TangentSpace S p),
      HasDerivAt (fun r : ℝ =>
        (d (fiberExponential F p ((t + r * a) • (v + r • w)))).val)
        ((tangentStructure S).fiberCoordinates.equiv d hd _ hq
          (polarDifferential F p t v a w)) 0

/-- Equality of the whole bilinear pullback tensor, on the whole nonzero
polar exponential domain. No exclusion of zeros of s_k is imposed. -/
def polar_metricType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ k : ℝ, ConstantSectional g R k →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (t : ℝ) (v : TangentSpace S p), t ≠ 0 →
      pairing g p v v = 1 → (⟨p, t • v⟩ : Phase S) ∈ exponentialDomain F →
    ∀ (a b : ℝ) (w z : TangentSpace S p),
      pairing g p w v = 0 → pairing g p z v = 0 →
      pairing g (fiberExponential F p (t • v))
        (polarDifferential F p t v a w) (polarDifferential F p t v b z) =
        a * b + s k t ^ 2 * pairing g p w z

/-- On every normal ball the same pullback is the coordinate metric:
exp_p(tv) is the inverse of the genuine atlas chart at E(tv).
Smoothness and the inverse laws are carried by IsNormalChart, not asserted
at arbitrary singular points of the exponential. -/
def normal_ball_metricType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ k : ℝ, ConstantSectional g R k →
    ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n),
      IsOrthonormalCoordinates g p E →
    ∀ (r : ℝ) (d : ModelChart n .euclidean M), IsNormalChart g F p E r d →
    ∀ (t : ℝ) (v : TangentSpace S p), 0 < t → t < r → pairing g p v v = 1 →
      fiberExponential F p (t • v) = d.symm ⟨E (t • v), by simp [modelSet]⟩ ∧
      ∀ (a b : ℝ) (w z : TangentSpace S p),
        pairing g p w v = 0 → pairing g p z v = 0 →
        pairing g (fiberExponential F p (t • v))
          (polarDifferential F p t v a w) (polarDifferential F p t v b z) =
          a * b + s k t ^ 2 * pairing g p w z

/-- The unit sphere in a one-dimensional tangent fiber has zero tangent spaces. -/
def angular_zeroType : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] (S : SmoothManifold 1 .euclidean M)
    (g : RiemannianMetric S) (p : M) (v w : TangentSpace S p),
    pairing g p v v = 1 → pairing g p w v = 0 → w = 0

end P202Specs.Geometry.ConstantCurvaturePolar
