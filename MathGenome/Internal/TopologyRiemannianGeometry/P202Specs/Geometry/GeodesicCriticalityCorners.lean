import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.FirstVariation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialNormalCoordinates
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Hom.Set
import Mathlib.Algebra.BigOperators.Fin

/-! Independent statements for Theorem 6.8, paper.tex:3318–3360.
The statements include genuine field realizations, full smooth-segment
criticality equivalences, actual finite arc-length parametrizations, and
no-corner and smooth-gluing conclusions for the original minimizing curves.
All fields below take values in the original intrinsic tangent fibers. -/
set_option autoImplicit false
set_option linter.unusedVariables false

namespace P202.CriticalityData
open Set

/-- The endpoints are fixed for every parameter in the variation strip. -/
def EndpointFixed {M : Type*} (F : ℝ × ℝ → M) (ε a b : ℝ) : Prop :=
  ∀ s ∈ Ioo (-ε) ε, F (s,a) = F (0,a) ∧ F (s,b) = F (0,b)

open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.GeodesicData
open Filter
open scoped Topology

/-- Smoothness of a field along a curve on a closed parameter set: its actual
intrinsic tangent lift is continuous and has smooth ambient coordinate germs
in the canonical tangent charts. No extension of the curve outside the set
is required. The tangent chart contains both base and vector coordinates. -/
def SmoothFieldAlongOn {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (γ : ℝ → M)
    (V : (t : ℝ) → TangentSpace S (γ t)) (J : Set ℝ) : Prop :=
  ContinuousOn (fun t => (⟨γ t, V t⟩ : Phase S)) J ∧
    ∀ t ∈ J, ∃ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val),
      γ t ∈ e.source ∧
      ∃ x : ℝ → Euclidean (n+n), ContDiffAt ℝ (⊤ : ℕ∞) x t ∧
        x t = (((tangentStructure S).chart e he)
          ⟨γ t, V t⟩).val ∧
        (fun r => (((tangentStructure S).chart e he)
          ⟨γ r, V r⟩).val) =ᶠ[𝓝[J] t] x


/-- Smoothness of a curve on a parameter set is expressed through genuine
ambient smooth coordinate germs, including one-sided endpoint germs. -/
def SmoothCurveOn {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (γ : ℝ → M) (J : Set ℝ) : Prop :=
  ContinuousOn γ J ∧ ∀ t ∈ J,
    ∃ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val),
      γ t ∈ e.source ∧ ∃ x : ℝ → Euclidean n,
        ContDiffAt ℝ (⊤ : ℕ∞) x t ∧ x t = (e (γ t)).val ∧
          (fun r => (e (γ r)).val) =ᶠ[𝓝[J] t] x

/-- The accumulated-speed parameter, defined by the actual interval integral. -/
noncomputable def arcParameter (v : ℝ → ℝ) (a t : ℝ) : ℝ := ∫ r in a..t, v r

/-- The source infimum ranges over all compact parameter intervals and all
original piecewise C¹ curves with these endpoints. -/
def endpointLengths {n : ℕ} {kind : SmoothManifolds.ModelKind} {M : Type*}
    [TopologicalSpace M] {S : SmoothManifold n kind M}
    (g : RiemannianMetric S) (p q : M) : Set ℝ :=
  {L | ∃ (a b : ℝ) (c : P202.CurveData.PiecewiseC1Curve S a b),
    c a = p ∧ c b = q ∧ P202.CurveData.length g c = L}

/-- Only the infimum definition is used here; no distance axioms are assumed. -/
noncomputable def endpointDistance {n : ℕ} {kind : SmoothManifolds.ModelKind} {M : Type*}
    [TopologicalSpace M] {S : SmoothManifold n kind M}
    (g : RiemannianMetric S) (p q : M) : ℝ := sInf (endpointLengths g p q)

end P202.CriticalityData

namespace P202.CriticalityData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData P202.MetricData
  P202.FirstVariationData
open Set
def EnergyCriticalOn {n : ℕ} {M : Type*} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (γ : ℝ → M) (a b : ℝ) : Prop :=
  ∀ (H : ℝ × ℝ → M) (ε : ℝ), 0 < ε → SmoothVariationOn S H ε a b →
    EndpointFixed H ε a b → (∀ t ∈ Icc a b, H (0,t) = γ t) →
      HasDerivAt (variedEnergy g H a b) 0 0

def LengthCriticalOn {n : ℕ} {M : Type*} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (γ : ℝ → M) (a b : ℝ) : Prop :=
  ∀ (H : ℝ × ℝ → M) (ε : ℝ), 0 < ε → SmoothVariationOn S H ε a b →
    EndpointFixed H ε a b → (∀ t ∈ Icc a b, H (0,t) = γ t) →
      HasDerivAt (variedLength g H a b) 0 0
end P202.CriticalityData

namespace P202Specs.Geometry.GeodesicCriticalityCorners
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CriticalityData
  P202.GeodesicData P202.ExponentialData
open Set Filter
open SmoothManifolds.TangentBundleData SmoothManifolds.VectorFieldData
open scoped Topology
universe u

/-- The continuous version of the fundamental lemma, including the endpoints
by continuity. Its tests vanish on neighborhoods of both endpoints. -/
def scalar_fundamental_lemmaType : Prop :=
  ∀ {a b : ℝ}, a < b → ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc a b) →
    (∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ t in a..b, φ t * f t) = 0) →
    ∀ t ∈ Icc a b, f t = 0

def fixed_endpoint_fieldsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (F : ℝ × ℝ → M) (ε a b : ℝ),
    0 < ε → EndpointFixed F ε a b →
    variationField S F a = 0 ∧ variationField S F b = 0

/-- The exact fixed-endpoint energy formula has no boundary contribution.
In particular no positivity or nonconstancy is required. -/
def fixed_endpoint_energyType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : ℝ × ℝ → M) (ε a b : ℝ), 0 < ε → a ≤ b →
    SmoothVariationOn S F ε a b → EndpointFixed F ε a b →
    HasDerivAt (variedEnergy g F a b)
      (-(∫ t in a..b, variationPairing g F
        (covariantDerivativeWithin C (fun r => F (0,r))
          (segmentVelocity S F a b) (Icc a b)) t)) 0

def fixed_endpoint_lengthType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : ℝ × ℝ → M) (ε a b : ℝ), 0 < ε → a ≤ b →
    SmoothVariationOn S F ε a b → EndpointFixed F ε a b →
    (∀ t ∈ Icc a b, 0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) →
    HasDerivAt (variedLength g F a b)
      (-(∫ t in a..b, variationPairing g F
        (covariantDerivativeWithin C (fun r => F (0,r))
          (unitVelocity g F a b) (Icc a b)) t)) 0

/-- The easy direction of energy criticality, expressed for every actual
variation. Vanishing acceleration is the actual covariant derivative relation. -/
def geodesic_energy_stationaryType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : ℝ × ℝ → M) (ε a b : ℝ), 0 < ε → a < b →
    SmoothVariationOn S F ε a b → EndpointFixed F ε a b →
    (∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C (fun r => F (0,r))
      (segmentVelocity S F a b) (Icc a b) t 0) →
    HasDerivAt (variedEnergy g F a b) 0 0

/-- The easy direction of length criticality at positive speed. The converse
and the arc-length/geodesic equivalence are not assumptions of this statement. -/
def parallel_unit_length_stationaryType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (F : ℝ × ℝ → M) (ε a b : ℝ), 0 < ε → a < b →
    SmoothVariationOn S F ε a b → EndpointFixed F ε a b →
    (∀ t ∈ Icc a b, 0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) →
    (∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C (fun r => F (0,r))
      (unitVelocity g F a b) (Icc a b) t 0) →
    HasDerivAt (variedLength g F a b) 0 0

/-- The compactness step for exponential variations. Continuity of the scaled
lift is a hypothesis of this helper only; it still has to be established for
every smooth field in the full realization theorem. No completeness is used. -/
def uniform_exponential_domainType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (γ : ℝ → M) (V : (t : ℝ) → TangentSpace S (γ t)) (a b : ℝ),
    ContinuousOn (fun z : ℝ × ℝ => (⟨γ z.2, z.1 • V z.2⟩ : Phase S))
      (univ ×ˢ Icc a b) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      (⟨γ t, s • V t⟩ : Phase S) ∈ exponentialDomain F

/-- A radial exponential variation has precisely its prescribed tangent
velocity, with heterogeneous equality accounting only for exp_p(0)=p. -/
def exponential_ray_velocityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)), IsMaximalFamily S C F →
    ∀ (p : M) (v : TangentSpace S p),
      HEq (velocity S (fun s : ℝ => fiberExponential F p (s • v)) 0) v

/-- Every smooth intrinsic field on a compact segment is realized by a genuine
smooth variation on a uniform strip. If its endpoint values vanish the
variation fixes the endpoints; in particular this covers fields vanishing
near the endpoints. The base and variation field agree on all of ℝ. -/
def realize_smooth_fieldType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (C : Connection (tangentBundle S))
    (γ : ℝ → M) (V : (t : ℝ) → TangentSpace S (γ t)) (a b : ℝ),
    SmoothFieldAlongOn S γ V (Icc a b) →
    ∃ ε : ℝ, 0 < ε ∧ ∃ H : ℝ × ℝ → M,
      SmoothVariationOn S H ε a b ∧
      (∀ t : ℝ, H (0,t) = γ t ∧ HEq (variationField S H t) (V t)) ∧
      (V a = 0 → V b = 0 → EndpointFixed H ε a b)

def realize_finite_piecewise_fieldType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : Connection (tangentBundle S))
    (γ : ℝ → M) (V : (t : ℝ) → TangentSpace S (γ t))
    (left right : ι → ℝ)
    (hV : ∀ i, SmoothFieldAlongOn S γ V (Icc (left i) (right i))),
  ∃ ε : ℝ, 0 < ε ∧ ∃ H : ℝ × ℝ → M,
      (∀ i, SmoothVariationOn S H ε (left i) (right i)) ∧
      (∀ t : ℝ, H (0,t) = γ t ∧ HEq (variationField S H t) (V t)) ∧
      (∀ a b : ℝ, V a = 0 → V b = 0 → EndpointFixed H ε a b)

def smooth_field_fundamental_lemmaType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (g : RiemannianMetric S) {γ : ℝ → M}
    {A : (t : ℝ) → TangentSpace S (γ t)} {a b : ℝ} (hab : a < b)
    (hA : SmoothFieldAlongOn S γ A (Icc a b))
    (htest : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ t in a..b, pairing g (γ t) (φ t • A t) (A t)) = 0),
  ∀ t ∈ Icc a b, A t = 0

def arcParameter_inverseType : Prop :=
  ∀ {v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < v t),
  ∃ τ : ℝ → ℝ,
      Continuous τ ∧
      MapsTo τ (Icc 0 (arcParameter v a b)) (Icc a b) ∧
      (∀ t ∈ Icc a b, τ (arcParameter v a t) = t) ∧
      (∀ s ∈ Icc 0 (arcParameter v a b), arcParameter v a (τ s) = s) ∧
      (∀ s ∈ Icc 0 (arcParameter v a b),
        HasDerivWithinAt τ (v (τ s))⁻¹ (Icc 0 (arcParameter v a b)) s)

def regular_arc_length_parameterizationType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S)
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    (hpos : ∀ t ∈ Icc a b, 0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t)),
  let v := fun t => tangentNorm g (F (0,t)) (segmentVelocity S F a b t)
    let σ := arcParameter v a
    ∃ τ : ℝ → ℝ, Continuous τ ∧ MapsTo τ (Icc 0 (σ b)) (Icc a b) ∧
      (∀ t ∈ Icc a b, τ (σ t) = t) ∧
      (∀ s ∈ Icc 0 (σ b), σ (τ s) = s) ∧
      (∀ s ∈ Icc 0 (σ b), HasDerivWithinAt τ (v (τ s))⁻¹ (Icc 0 (σ b)) s) ∧
      (∀ s ∈ Icc 0 (σ b), HasVelocityWithinAt S (fun r => F (0,τ r))
        (Icc 0 (σ b)) s (unitVelocity g F a b (τ s))) ∧
      (∀ s ∈ Icc 0 (σ b), tangentNorm g (F (0,τ s)) (unitVelocity g F a b (τ s)) = 1) ∧
      (∀ C : Connection (tangentBundle S),
        (∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C (fun r => F (0,r))
          (unitVelocity g F a b) (Icc a b) t 0) ↔
        (∀ s ∈ Icc 0 (σ b), HasCovariantDerivativeWithinAt C (fun r => F (0,τ r))
          (fun r => unitVelocity g F a b (τ r)) (Icc 0 (σ b)) s 0))

def regular_arc_length_geodesicType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M],
  ∀ {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    (hpos : ∀ t ∈ Icc a b, 0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t))
    (hpar : ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C (fun r => F (0,r))
      (unitVelocity g F a b) (Icc a b) t 0),
  let σ := arcParameter (fun t => tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) a
    ∃ τ : ℝ → ℝ, Continuous τ ∧ MapsTo τ (Icc 0 (σ b)) (Icc a b) ∧
      (∀ t ∈ Icc a b, τ (σ t) = t) ∧
      (∀ s ∈ Icc 0 (σ b), σ (τ s) = s) ∧
      (∀ s ∈ Icc 0 (σ b), tangentNorm g (F (0,τ s)) (unitVelocity g F a b (τ s)) = 1) ∧
      IsGeodesicOn S C (Ioo 0 (σ b))
        (fun s => (⟨F (0,τ s), unitVelocity g F a b (τ s)⟩ : Phase S))

def minimizing_of_length_eq_distanceType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S)
    {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (hmin : length g c = endpointDistance g (c a) (c b))
    {l r : ℝ} (d : PiecewiseC1Curve S l r)
    (hp : d l = c a) (hq : d r = c b),
  length g c ≤ length g d

def piecewise_variation_localMin_of_distanceType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M},
  ∀ (g : RiemannianMetric S) {F : ℝ × ℝ → M} {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : Monotone node)
    (hF : ∀ i : Fin (k+1), SmoothVariationOn S F ε (node i.castSucc) (node i.succ))
    (hfix : ∀ s ∈ Ioo (-ε) ε,
      F (s,node 0) = F (0,node 0) ∧
      F (s,node (Fin.last (k+1))) = F (0,node (Fin.last (k+1))))
    (hmin : variedLength g F (node 0) (node (Fin.last (k+1))) 0 =
      endpointDistance g (F (0,node 0)) (F (0,node (Fin.last (k+1))))),
  IsLocalMin (variedLength g F (node 0) (node (Fin.last (k+1)))) 0

def geodesic_gluingType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C)
    (I J : D13Unified.OpenTimeInterval) (q r : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (hr : IsGeodesicOn S C J.carrier r)
    (c : ℝ) (hc : c ∈ I.carrier ∩ J.carrier) (hjoin : q c = r c),
  ∃ (K : D13Unified.OpenTimeInterval) (z : ℝ → Phase S),
      I.carrier ∪ J.carrier ⊆ K.carrier ∧
      IsGeodesicOn S C K.carrier z ∧
      EqOn z q I.carrier ∧ EqOn z r J.carrier ∧
      ∀ t ∈ K.carrier, ∀ e ∈ (phaseManifold S).smoothStructure.val,
        z t ∈ e.source →
        ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (e (z s)).val) t

def smooth_field_covariantDerivativeType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (C : Connection (tangentBundle S)) {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {a b : ℝ} (hab : a < b)
    (hV : SmoothFieldAlongOn S γ V (Icc a b)),
  SmoothFieldAlongOn S γ (covariantDerivativeWithin C γ V (Icc a b)) (Icc a b)

def energy_criticality_iffType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hγ : SmoothCurveOn S γ (Icc a b)),
  EnergyCriticalOn g γ a b ↔
      ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C γ
        (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b) (Icc a b) t 0

def length_criticality_iff_arclength_geodesicType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hγ : SmoothCurveOn S γ (Icc a b))
    (hpos : ∀ t ∈ Icc a b, 0 < tangentNorm g (γ t)
      (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b t)),
  let σ := arcParameter (fun t => tangentNorm g (γ t)
      (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) a b t)) a
    ∃ τ : ℝ → ℝ, Continuous τ ∧ MapsTo τ (Icc 0 (σ b)) (Icc a b) ∧
      (∀ t ∈ Icc a b, τ (σ t) = t) ∧
      (∀ s ∈ Icc 0 (σ b), σ (τ s) = s) ∧
      (∀ s ∈ Icc 0 (σ b), tangentNorm g (γ (τ s))
        (unitVelocity g (fun z : ℝ × ℝ => γ z.2) a b (τ s)) = 1) ∧
      (LengthCriticalOn g γ a b ↔ IsGeodesicOn S C (Ioo 0 (σ b))
        (fun s => (⟨γ (τ s),unitVelocity g (fun z : ℝ × ℝ => γ z.2) a b (τ s)⟩ : Phase S)))

def regular_arc_length_geodesic_iffType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    (hpos : ∀ t ∈ Icc a b, 0 < tangentNorm g (F (0,t)) (segmentVelocity S F a b t)),
  let σ := arcParameter (fun t => tangentNorm g (F (0,t)) (segmentVelocity S F a b t)) a
    ∃ τ : ℝ → ℝ, Continuous τ ∧ MapsTo τ (Icc 0 (σ b)) (Icc a b) ∧
      (∀ t ∈ Icc a b, τ (σ t) = t) ∧
      (∀ s ∈ Icc 0 (σ b), σ (τ s) = s) ∧
      (∀ s ∈ Icc 0 (σ b), tangentNorm g (F (0,τ s)) (unitVelocity g F a b (τ s)) = 1) ∧
      ((∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C (fun r => F (0,r))
        (unitVelocity g F a b) (Icc a b) t 0) ↔
      IsGeodesicOn S C (Ioo 0 (σ b))
        (fun s => (⟨F (0,τ s), unitVelocity g F a b (τ s)⟩ : Phase S)))

def minimizing_broken_geodesic_no_cornerType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (γ : ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (I : Fin (k+1) → D13Unified.OpenTimeInterval)
    (q : Fin (k+1) → ℝ → Phase S)
    (hq : ∀ i, IsGeodesicOn S C (I i).carrier (q i))
    (hdom : ∀ i, Icc (node i.castSucc) (node i.succ) ⊆ (I i).carrier)
    (hpiece : ∀ i, EqOn γ (fun t => (q i t).1) (Icc (node i.castSucc) (node i.succ)))
    (hne : ∀ i, ∃ s ∈ Icc (node i.castSucc) (node i.succ),
      ∃ t ∈ Icc (node i.castSucc) (node i.succ), (q i s).1 ≠ (q i t).1)
    (hmin : (∫ t in node 0..node (Fin.last (k+1)), speed g γ t) =
      endpointDistance g (γ (node 0)) (γ (node (Fin.last (k+1))))),
  ∀ j : Fin k,
      unitVelocity g (fun z : ℝ × ℝ => γ z.2)
        (node j.castSucc.castSucc) (node j.castSucc.succ) (node j.succ.castSucc) =
      unitVelocity g (fun z : ℝ × ℝ => γ z.2)
        (node j.succ.castSucc) (node j.succ.succ) (node j.succ.castSucc)

def minimizing_broken_geodesic_global_gluingType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (γ : ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (I : Fin (k+1) → D13Unified.OpenTimeInterval)
    (q : Fin (k+1) → ℝ → Phase S)
    (hq : ∀ i, IsGeodesicOn S C (I i).carrier (q i))
    (hdom : ∀ i, Icc (node i.castSucc) (node i.succ) ⊆ (I i).carrier)
    (hpiece : ∀ i, EqOn γ (fun t => (q i t).1) (Icc (node i.castSucc) (node i.succ)))
    (hne : ∀ i, ∃ s ∈ Icc (node i.castSucc) (node i.succ),
      ∃ t ∈ Icc (node i.castSucc) (node i.succ), (q i s).1 ≠ (q i t).1)
    (hmin : (∫ t in node 0..node (Fin.last (k+1)), speed g γ t) =
      endpointDistance g (γ (node 0)) (γ (node (Fin.last (k+1))))),
  let c := fun i : Fin (k+1) => tangentNorm g (q i (node i.castSucc)).1 (q i (node i.castSucc)).2
    let s := Fin.partialSum (fun i : Fin (k+1) => c i * (node i.succ - node i.castSucc))
    ∃ (K : D13Unified.OpenTimeInterval) (z : ℝ → Phase S),
      StrictMono s ∧ IsGeodesicOn S C K.carrier z ∧
      (∀ i, affineDomain (I i).carrier (c i)⁻¹ (node i.castSucc - (c i)⁻¹ * s i.castSucc) ⊆ K.carrier ∧
        EqOn z (affineCurve S (q i) (c i)⁻¹ (node i.castSucc - (c i)⁻¹ * s i.castSucc))
          (affineDomain (I i).carrier (c i)⁻¹ (node i.castSucc - (c i)⁻¹ * s i.castSucc))) ∧
      (∀ t ∈ K.carrier, tangentNorm g (z t).1 (z t).2 = 1) ∧
      ∀ t ∈ K.carrier, ∀ e ∈ (phaseManifold S).smoothStructure.val,
        z t ∈ e.source → ContDiffAt ℝ (⊤ : ℕ∞) (fun r => (e (z r)).val) t

def unit_speed_geodesic_gluingType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C)
    (I J : D13Unified.OpenTimeInterval) (q r : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (hr : IsGeodesicOn S C J.carrier r)
    (c : ℝ) (hc : c ∈ I.carrier ∩ J.carrier)
    (hp : (q c).1 = (r c).1)
    (hqpos : 0 < tangentNorm g (q c).1 (q c).2)
    (hrpos : 0 < tangentNorm g (r c).1 (r c).2)
    (hunit : HEq ((tangentNorm g (q c).1 (q c).2)⁻¹ • (q c).2)
      ((tangentNorm g (r c).1 (r c).2)⁻¹ • (r c).2)),
  ∃ (K : D13Unified.OpenTimeInterval) (z : ℝ → Phase S),
      affineDomain I.carrier (tangentNorm g (q c).1 (q c).2)⁻¹ c ∪
        affineDomain J.carrier (tangentNorm g (r c).1 (r c).2)⁻¹ c ⊆ K.carrier ∧
      IsGeodesicOn S C K.carrier z ∧
      EqOn z (affineCurve S q (tangentNorm g (q c).1 (q c).2)⁻¹ c)
        (affineDomain I.carrier (tangentNorm g (q c).1 (q c).2)⁻¹ c) ∧
      EqOn z (affineCurve S r (tangentNorm g (r c).1 (r c).2)⁻¹ c)
        (affineDomain J.carrier (tangentNorm g (r c).1 (r c).2)⁻¹ c) ∧
      (∀ t ∈ K.carrier, tangentNorm g (z t).1 (z t).2 = 1) ∧
      ∀ t ∈ K.carrier, ∀ e ∈ (phaseManifold S).smoothStructure.val,
        z t ∈ e.source → ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (e (z s)).val) t

def finite_geodesic_gluingType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {k : ℕ} (I : Fin (k+1) → D13Unified.OpenTimeInterval)
    (q : Fin (k+1) → ℝ → Phase S)
    (hq : ∀ i, IsGeodesicOn S C (I i).carrier (q i))
    (h0 : (0:ℝ) ∈ (I 0).carrier)
    (join : Fin k → ℝ)
    (hjoin : ∀ j : Fin k, join j ∈ (I j.castSucc).carrier ∩ (I j.succ).carrier ∧
      q j.castSucc (join j) = q j.succ (join j)),
  ∃ (K : D13Unified.OpenTimeInterval) (z : ℝ → Phase S),
      IsGeodesicOn S C K.carrier z ∧
      (∀ i, (I i).carrier ⊆ K.carrier ∧ EqOn z (q i) (I i).carrier) ∧
      ∀ t ∈ K.carrier, ∀ e ∈ (phaseManifold S).smoothStructure.val,
        z t ∈ e.source → ContDiffAt ℝ (⊤ : ℕ∞) (fun s => (e (z s)).val) t

def minimizing_regular_curve_no_cornerType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (γ : ℝ → M) {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : ∀ i : Fin (k+1), SmoothCurveOn S γ (Icc (node i.castSucc) (node i.succ)))
    (hpos : ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      0 < tangentNorm g (γ t)
        (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) (node i.castSucc) (node i.succ) t))
    (hmin : (∫ t in node 0..node (Fin.last (k+1)), speed g γ t) =
      endpointDistance g (γ (node 0)) (γ (node (Fin.last (k+1))))),
  ∀ j : Fin k,
      unitVelocity g (fun z : ℝ × ℝ => γ z.2)
        (node j.castSucc.castSucc) (node j.castSucc.succ) (node j.succ.castSucc) =
      unitVelocity g (fun z : ℝ × ℝ => γ z.2)
        (node j.succ.castSucc) (node j.succ.succ) (node j.succ.castSucc)

def arcParameter_piecewiseRegularIncreasingType : Prop :=
  ∀ {v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hv : ContinuousOn v (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 < v t)
    (hvgerm : ∀ t ∈ Icc a b, ∃ x : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) x t ∧
      x t = v t ∧ v =ᶠ[𝓝[Icc a b] t] x),
  ∃ φ : PiecewiseRegularIncreasing a b 0 (arcParameter v a b),
      ∀ t ∈ Icc a b, φ (arcParameter v a t) = t

def regular_piecewise_arc_length_parameterizationType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (g : RiemannianMetric S) (γ : ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : ∀ i : Fin (k+1), SmoothCurveOn S γ (Icc (node i.castSucc) (node i.succ)))
    (hpos : ∀ (i : Fin (k+1)) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
      0 < tangentNorm g (γ t)
        (segmentVelocity S (fun z : ℝ × ℝ => γ z.2) (node i.castSucc) (node i.succ) t)),
  let σ := arcParameter (speed g γ) (node 0)
    ∃ φ : PiecewiseRegularIncreasing (node 0) (node (Fin.last (k+1))) 0
        (σ (node (Fin.last (k+1)))),
      (∀ t ∈ Icc (node 0) (node (Fin.last (k+1))), φ (σ t) = t) ∧
      (∀ s ∈ Icc 0 (σ (node (Fin.last (k+1)))), σ (φ s) = s) ∧
      ∀ (i : Fin (k+1)) (s : ℝ), s ∈ Icc (σ (node i.castSucc)) (σ (node i.succ)) →
        HasVelocityWithinAt S (γ ∘ φ) (Icc (σ (node i.castSucc)) (σ (node i.succ))) s
          (unitVelocity g (fun z : ℝ × ℝ => γ z.2)
            (node i.castSucc) (node i.succ) (φ s)) ∧
        tangentNorm g (γ (φ s))
          (unitVelocity g (fun z : ℝ × ℝ => γ z.2)
            (node i.castSucc) (node i.succ) (φ s)) = 1

def geodesic_cumulative_arclength_nodesType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M},
  ∀ (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (γ : ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (I : Fin (k+1) → D13Unified.OpenTimeInterval) (q : Fin (k+1) → ℝ → Phase S)
    (hq : ∀ i, IsGeodesicOn S C (I i).carrier (q i))
    (hdom : ∀ i, Icc (node i.castSucc) (node i.succ) ⊆ (I i).carrier)
    (hpiece : ∀ i, EqOn γ (fun t => (q i t).1) (Icc (node i.castSucc) (node i.succ))),
  let c := fun i : Fin (k+1) => tangentNorm g (q i (node i.castSucc)).1 (q i (node i.castSucc)).2
    let s := Fin.partialSum (fun i : Fin (k+1) => c i * (node i.succ - node i.castSucc))
    s 0 = 0 ∧
    (∀ i : Fin (k+1), s i.succ = s i.castSucc +
      ∫ t in node i.castSucc..node i.succ, speed g γ t) ∧
    s = Fin.partialSum (fun i : Fin (k+1) =>
      ∫ t in node i.castSucc..node i.succ, speed g γ t)

/-- Complete first variation, including moving endpoints and all finite
corner terms, fixed-endpoint criticality, arc length and minimizer conclusions. -/
def complete_first_variationType : Prop :=
  P202Specs.Geometry.FirstVariation.first_variation_energyType.{u} ∧
  P202Specs.Geometry.FirstVariation.first_variation_lengthType.{u} ∧
  P202Specs.Geometry.FirstVariation.piecewise_energyType.{u} ∧
  P202Specs.Geometry.FirstVariation.piecewise_lengthType.{u} ∧
  P202Specs.Geometry.FirstVariation.length_sq_le_energyType.{u} ∧
  P202Specs.Geometry.FirstVariation.constant_speed_equalityType.{u} ∧
  P202Specs.Geometry.FirstVariation.equality_iff_constant_speedType.{u} ∧
  P202Specs.Geometry.FirstVariation.degenerateType.{u} ∧
  P202Specs.Geometry.GeodesicCriticalityCorners.realize_smooth_fieldType.{u} ∧
  P202Specs.Geometry.GeodesicCriticalityCorners.energy_criticality_iffType.{u} ∧
  P202Specs.Geometry.GeodesicCriticalityCorners.length_criticality_iff_arclength_geodesicType.{u} ∧
  P202Specs.Geometry.GeodesicCriticalityCorners.minimizing_broken_geodesic_no_cornerType.{u} ∧
  P202Specs.Geometry.GeodesicCriticalityCorners.minimizing_broken_geodesic_global_gluingType.{u} ∧
  P202Specs.Geometry.GeodesicCriticalityCorners.geodesic_cumulative_arclength_nodesType.{u} ∧
  P202Specs.Geometry.GeodesicCriticalityCorners.regular_piecewise_arc_length_parameterizationType.{u} ∧
  P202Specs.Geometry.GeodesicCriticalityCorners.minimizing_regular_curve_no_cornerType.{u}

end P202Specs.Geometry.GeodesicCriticalityCorners
