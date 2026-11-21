import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.JacobiVariation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialNormalCoordinates
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Independent statements for paper.tex 4028–4058 (G17).
The maximal family is the actual geodesic family, with no completeness
assumption. Fields are restricted to its open interval before forming vector
spaces: arbitrary values of total representatives outside the interval do not
contribute to multiplicity. All endpoint constructions retain the specified
geodesic, not just its endpoint in M. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
namespace P202.ExponentialJacobiData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.GeodesicData P202.CurvatureData P202.JacobiData P202.ExponentialData
open Set
open scoped SmoothManifolds.BoundaryConeData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n .euclidean M)

/-- Ordinary transport between the original tangent fibers. -/
def castTangent {p q : M} (h : p = q) : TangentSpace S p ≃ₗ[ℝ] TangentSpace S q := by
  subst q
  exact LinearEquiv.refl ℝ _

/-- Choose an actual atlas chart, including its source and membership proofs. -/
noncomputable def selectedChart (p : M) :
    {e : ModelChart n .euclidean M // e ∈ S.smoothStructure.val ∧ p ∈ e.source} :=
  ⟨Classical.choose (S.smoothStructure.property.1.1 p),
    Classical.choose_spec (S.smoothStructure.property.1.1 p)⟩

noncomputable def selectedCoordinates (p : M) : TangentSpace S p ≃ₗ[ℝ] Euclidean n :=
  (tangentStructure S).fiberCoordinates.equiv (selectedChart S p).val
    (selectedChart S p).property.1 p (selectedChart S p).property.2

/-- The ordinary differential of the fiber exponential, transported from
Euclidean coordinates to the original intrinsic tangent fibers. It is only
used on the open exponential domain, where the coordinate function is smooth.
Coordinate independence is included in the theorem interface below. -/
noncomputable def fiberDifferential (F : CurveFamily (Phase S)) (p : M)
    (v : TangentSpace S p) :
    TangentSpace S p →ₗ[ℝ] TangentSpace S (fiberExponential F p v) :=
  let E := selectedCoordinates S p
  let d := (selectedChart S (fiberExponential F p v)).val
  let D := selectedCoordinates S (fiberExponential F p v)
  D.symm.toLinearMap.comp ((fderiv ℝ
    (fun x : Euclidean n => (d (fiberExponential F p (E.symm x))).val)
    (E v)).toLinearMap.comp E.toLinearMap)

/-- The initial phase equality supplies the canonical identification at t=0. -/
def initialIdentification (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : TangentSpace S p) :
    TangentSpace S p ≃ₗ[ℝ] TangentSpace S (F.curve ⟨p, v⟩ 0).1 :=
  castTangent S (congrArg Sigma.fst (hF ⟨p, v⟩).2.1).symm

abbrev RestrictedField (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) :=
  (t : I.carrier) → TangentSpace S (q t.val).1

/-- Existence of an ambient representative solving the genuine intrinsic
Jacobi equation, with equality tested only on the actual time interval. -/
def IsJacobiSection (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (J : RestrictedField S I q) : Prop :=
  ∃ K : (t : ℝ) → TangentSpace S (q t).1,
    IsJacobiField C R I.carrier q K ∧ ∀ t : I.carrier, K t.val = J t

/-- A zero extension is only a representative. No equation is asserted off I. -/
noncomputable def extendField (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (J : RestrictedField S I q) (t : ℝ) : TangentSpace S (q t).1 := by
  classical
  exact if ht : t ∈ I.carrier then J ⟨t, ht⟩ else 0

def EndpointFields (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (a b : I.carrier) : Set (RestrictedField S I q) :=
  {J | IsJacobiSection S C R I q J ∧ J a = 0 ∧ J b = 0}

/-- The span is independent data; the closure theorem below proves that its
members are exactly the actual endpoint-vanishing Jacobi fields. -/
noncomputable def endpointSpace (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) (a b : I.carrier) :
    Submodule ℝ (RestrictedField S I q) :=
  Submodule.span ℝ (EndpointFields S C R I q a b)

def ConjugateAlong (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) (a b : I.carrier) : Prop :=
  ∃ J ∈ EndpointFields S C R I q a b, J ≠ 0

noncomputable def multiplicity (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) (a b : I.carrier) : ℕ :=
  Module.finrank ℝ (endpointSpace S C R I q a b)

end P202.ExponentialJacobiData

namespace P202Specs.Geometry.ExponentialJacobi
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.ExponentialData P202.ExponentialJacobiData
open Set
open scoped SmoothManifolds.BoundaryConeData
universe u

/-- The chosen-coordinate definition is the intrinsic derivative in every
source fiber chart and every target chart. -/
def differential_coordinatesType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (v : TangentSpace S p), (⟨p, v⟩ : Phase S) ∈ exponentialDomain F →
    ∀ (e d : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
      (hd : d ∈ S.smoothStructure.val) (hp : p ∈ e.source)
      (hq : fiberExponential F p v ∈ d.source),
      let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
      let D := (tangentStructure S).fiberCoordinates.equiv d hd (fiberExponential F p v) hq
      ∀ w : TangentSpace S p,
        D (fiberDifferential S F p v w) =
          fderiv ℝ (fun x : Euclidean n => (d (fiberExponential F p (E.symm x))).val)
            (E v) (E w)

/-- The factor t multiplies the argument w. The HEq only transports between
the equal endpoint fibers exp_p(tv) and gamma(t); their equality is the
upstream radial identity on the actual maximal interval. -/
def differential_formulaType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
      (p : M) (v w : TangentSpace S p),
    ∀ J : (t : ℝ) → TangentSpace S (F.curve ⟨p, v⟩ t).1,
      IsJacobiField C R (F.interval ⟨p, v⟩).carrier (F.curve ⟨p, v⟩) J →
      J 0 = 0 → HasCovariantDerivativeAt C (fun t => (F.curve ⟨p, v⟩ t).1)
        J 0 (initialIdentification S C F hF p v w) →
      ∀ t ∈ (F.interval ⟨p, v⟩).carrier,
        HEq (J t) (fiberDifferential S F p (t • v) (t • w))

/-- Existence and uniqueness of the field in the formula, on the entire
actual interval, with arbitrary initial velocity variation w. -/
def radial_fieldType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
      (p : M) (v w : TangentSpace S p),
      ∃ J : (t : ℝ) → TangentSpace S (F.curve ⟨p, v⟩ t).1,
        IsJacobiField C R (F.interval ⟨p, v⟩).carrier (F.curve ⟨p, v⟩) J ∧ J 0 = 0 ∧
        HasCovariantDerivativeAt C (fun t => (F.curve ⟨p, v⟩ t).1) J 0
          (initialIdentification S C F hF p v w) ∧
        (∀ t ∈ (F.interval ⟨p, v⟩).carrier,
          HEq (J t) (fiberDifferential S F p (t • v) (t • w))) ∧
        ∀ K : (t : ℝ) → TangentSpace S (F.curve ⟨p, v⟩ t).1,
          IsJacobiField C R (F.interval ⟨p, v⟩).carrier (F.curve ⟨p, v⟩) K → K 0 = 0 →
          HasCovariantDerivativeAt C (fun t => (F.curve ⟨p, v⟩ t).1) K 0
            (initialIdentification S C F hF p v w) →
          ∀ t ∈ (F.interval ⟨p, v⟩).carrier, K t = J t

/-- Positive-time kernel identification. The first space consists of actual
fields on this one geodesic's entire interval, vanishing at its two endpoints. -/
def kernel_equivalenceType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
      (p : M) (v : TangentSpace S p) (t : ℝ), 0 < t →
      ∀ ht : t ∈ (F.interval ⟨p, v⟩).carrier,
        let I := F.interval ⟨p, v⟩
        let q := F.curve ⟨p, v⟩
        let B := endpointSpace S C R I q ⟨0, (hF ⟨p, v⟩).1⟩ ⟨t, ht⟩
        Nonempty (B ≃ₗ[ℝ] LinearMap.ker (fiberDifferential S F p (t • v))) ∧
          Module.finrank ℝ B = Module.finrank ℝ (LinearMap.ker (fiberDifferential S F p (t • v)))

def conjugacy_singularityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
      (p : M) (v : TangentSpace S p) (t : ℝ), 0 < t →
      ∀ ht : t ∈ (F.interval ⟨p, v⟩).carrier,
        ConjugateAlong S C R (F.interval ⟨p, v⟩) (F.curve ⟨p, v⟩)
          ⟨0, (hF ⟨p, v⟩).1⟩ ⟨t, ht⟩ ↔
          ¬ Function.Bijective (fiberDifferential S F p (t • v))

/-- At zero, the differential is the identity in the same canonical source
and target fiber coordinates; no positive-time kernel assertion is used. -/
def differential_zeroType : Prop :=
  P202Specs.Geometry.ExponentialNormalCoordinates.derivative_zeroType.{u}

/-- These two statements also make precise that span has introduced no extra
fields and that the multiplicity is a finite vector-space dimension. -/
def endpoint_spaceType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
    IsGeodesicOn S C I.carrier q → ∀ (a b : I.carrier) (J : RestrictedField S I q),
      J ∈ endpointSpace S C R I q a b ↔ J ∈ EndpointFields S C R I q a b

def multiplicity_finiteType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → ∀ a b : I.carrier,
        FiniteDimensional ℝ (endpointSpace S C R I q a b) ∧
        (ConjugateAlong S C R I q a b ↔ 0 < multiplicity S C R I q a b)

/-- The final sentence of the source proof, for any two distinct times and
arbitrary affine speed. It also holds for the identically zero Jacobi field. -/
def two_zeros_normalType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (R : CurvatureTensor S), RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → NonconstantOn I.carrier q →
    ∀ J : (t : ℝ) → TangentSpace S (q t).1,
      IsJacobiField C R I.carrier q J →
    ∀ a ∈ I.carrier, ∀ b ∈ I.carrier, a ≠ b → J a = 0 → J b = 0 →
      ∀ t ∈ I.carrier, pairing g (q t).1 (J t) (q t).2 = 0

end P202Specs.Geometry.ExponentialJacobi
