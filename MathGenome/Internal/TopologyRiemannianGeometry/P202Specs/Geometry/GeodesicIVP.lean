import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LeviCivita
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.MaximalFlow
import MathGenome.Internal.ODEDynamics.D13Unified.Ch01.SolutionConcepts

/-! Independent draft for Theorem 6.5, paper.tex 3172–3204.
The base has no boundary. Phase space is the original P104 tangent bundle,
with exactly the intrinsic fibers already fixed by MetricFoundation.
All assertions on total representatives are restricted to the recorded domains.
The spray, its coordinate law and its intrinsic interpretation are conclusions,
not additional data assumed of the connection. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace P202.GeodesicData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.VectorFieldData SmoothManifolds.IntegralCurveData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData P202.LeviCivitaData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n .euclidean M)

abbrev Phase := SmoothManifolds.TangentBundleData.TotalSpace S

noncomputable instance phaseTopology : TopologicalSpace (Phase S) :=
  (tangentStructure S).topology

noncomputable abbrev phaseManifold : SmoothManifold (n + n) .euclidean (Phase S) :=
  (tangentStructure S).manifold

/-- Vanishing covariant acceleration, with the displayed tangent component
required to be the actual velocity. No smoothness/ODE certificate is assumed.
Only interior parameter germs are used; all later intervals are open. -/
def IsGeodesicOn (C : Connection (tangentBundle S)) (I : Set ℝ)
    (q : ℝ → Phase S) : Prop :=
  ∀ t ∈ I,
    HasVelocityWithinAt S (fun s => (q s).1) univ t (q t).2 ∧
    HasCovariantDerivativeAt C (fun s => (q s).1) (fun s => (q s).2) t 0

/-- Maximality is the universal extension property for both position and
velocity. Values of the representatives outside the intervals are irrelevant. -/
def IsMaximalThrough (C : Connection (tangentBundle S)) (w : Phase S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) : Prop :=
  0 ∈ I.carrier ∧ q 0 = w ∧ IsGeodesicOn S C I.carrier q ∧
    ∀ (J : D13Unified.OpenTimeInterval) (r : ℝ → Phase S),
      0 ∈ J.carrier → r 0 = w → IsGeodesicOn S C J.carrier r →
        J.carrier ⊆ I.carrier ∧ EqOn q r J.carrier

/-- Time and velocity scale together. This definition includes a = 0. -/
def affineCurve (q : ℝ → Phase S) (a b : ℝ) (t : ℝ) : Phase S :=
  ⟨(q (a * t + b)).1, a • (q (a * t + b)).2⟩

def constantCurve (p : M) (_t : ℝ) : Phase S := ⟨p, 0⟩

def IsMaximalFamily (C : Connection (tangentBundle S))
    (F : SmoothManifolds.MaximalFlowData.CurveFamily (Phase S)) : Prop :=
  ∀ w, IsMaximalThrough S C w (F.interval w) (F.curve w)

/-- The exact transformed time set, without replacing a possibly finite
lifespan by the whole real line. For zero scaling this is all or nothing. -/
def affineDomain (I : Set ℝ) (a b : ℝ) : Set ℝ := {t | a * t + b ∈ I}

/-- The local Christoffel acceleration in the original tangent coordinates. -/
noncomputable def coordinateAcceleration (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (v : Euclidean n) : Euclidean n :=
  fun k => -∑ i : Fin n, ∑ j : Fin n, christoffel C c p k i j * v i * v j

/-- Velocity components in an actual tangent trivialization. Values outside
its base domain are zero representatives and never enter chart assertions. -/
noncomputable def chartVelocity
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (q : ℝ → Phase S) : ℝ → Euclidean n :=
  coefficientsAlong (SmoothManifolds.ConstantRankBundles.trivializationFrame
    (tangentBundle S) c) (fun t => (q t).1) (fun t => (q t).2)

/-- The spray's coefficients in every tangent chart are precisely (v,-Γ(v,v)).
The target tangent chart uses the P104 product linear equivalence; no arbitrary
identification between two tangent models is substituted. -/
def HasSprayCoordinates (C : Connection (tangentBundle S))
    (G : SmoothField (tangentStructure (phaseManifold S))) : Prop :=
  ∀ (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (v : TangentSpace S p.val),
    let hp : p.val ∈ c.val.source :=
      (tangentRealization S).baseSet c ▸ p.property
    let z : Phase S := ⟨p.val, v⟩
    let e := (tangentStructure S).chart c.val c.property
    let he := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) c.val c.property
    let hz : z ∈ e.source := by
      simpa only [e, SmoothManifolds.TangentBundleData.TangentBundleStructure.chart_source,
        SmoothManifolds.TangentBundleData.projection, mem_preimage] using hp
    let w := (tangentStructure S).fiberCoordinates.equiv c.val c.property p.val hp v
    (tangentStructure (phaseManifold S)).fiberCoordinates.equiv e he z hz (G.val z) =
      (tangentStructure S).productCoordinates.linearEquiv
        (w, coordinateAcceleration S C c p w)

/-- Joint smoothness of position, in all product source coordinates and all
base target coordinates, at an interior point of the actual flow domain. -/
def PositionSmoothAt
    (F : SmoothManifolds.MaximalFlowData.CurveFamily (Phase S))
    (z : ℝ × Phase S) : Prop :=
  ContinuousAt (fun w : ℝ × Phase S => (F.curve w.2 w.1).1) z ∧
  ∀ e ∈ (phaseManifold S).smoothStructure.val,
    ∀ d ∈ S.smoothStructure.val,
      z.2 ∈ e.source → (F.curve z.2 z.1).1 ∈ d.source →
      ∃ U : Set (ℝ × Euclidean (n + n)), IsOpen U ∧ (z.1, (e z.2).val) ∈ U ∧
        ∃ H : ℝ × Euclidean (n + n) → Euclidean n,
          ContDiffOn ℝ (⊤ : ℕ∞) H U ∧
          (fun w : ℝ × Phase S => H (w.1, (e w.2).val)) =ᶠ[𝓝 z]
            (fun w => (d (F.curve w.2 w.1).1).val)

end P202.GeodesicData

namespace P202Specs.Geometry.GeodesicIVP
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.VectorFieldData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.GeodesicData
open Set
universe u

/-- Construction includes the full coordinate equation on every chart and the
bridge from the first-order flow to the original covariant curve equation.
The universal chart clause asserts compatibility on chart overlaps. -/
def spray_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S)),
    ∃ G : SmoothField (tangentStructure (phaseManifold S)),
      HasSprayCoordinates S C G ∧
      ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
        SmoothManifolds.IntegralCurveData.IsIntegralCurveOn G I.carrier q ↔
          IsGeodesicOn S C I.carrier q

/-- Both first-order coordinate equations, in every coordinate chart that
contains the point. This applies to arbitrary intrinsic geodesics. -/
def coordinate_equationType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (I : Set ℝ) (q : ℝ → Phase S), IsGeodesicOn S C I q →
    ∀ (t : ℝ), t ∈ I →
      ∀ (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
        (hp : (q t).1 ∈ (tangentBundle S).baseSet c),
        HasDerivAt (fun s => (c.val (q s).1).val) (chartVelocity S c q t) t ∧
        HasDerivAt (chartVelocity S c q)
          (coordinateAcceleration S C c ⟨(q t).1, hp⟩ (chartVelocity S c q t)) t

def maximal_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ w : Phase S, ∃ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsMaximalThrough S C w I q

def maximal_uniqueType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (w : Phase S) (I J : D13Unified.OpenTimeInterval) (q r : ℝ → Phase S),
    IsMaximalThrough S C w I q → IsMaximalThrough S C w J r →
      I.carrier = J.carrier ∧ EqOn q r I.carrier

def overlap_uniqueType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (I J : D13Unified.OpenTimeInterval) (q r : ℝ → Phase S),
    IsGeodesicOn S C I.carrier q → IsGeodesicOn S C J.carrier r →
    ∀ s ∈ I.carrier ∩ J.carrier, q s = r s → EqOn q r (I.carrier ∩ J.carrier)

/-- Smoothness of the tangent lift is simultaneous smoothness of position
and velocity. The position clause is also stated explicitly. -/
def domain_open_smoothType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (F : SmoothManifolds.MaximalFlowData.CurveFamily (Phase S)),
    IsMaximalFamily S C F →
      IsOpen (SmoothManifolds.MaximalFlowData.flowDomain F) ∧
      ∀ z ∈ SmoothManifolds.MaximalFlowData.flowDomain F,
        SmoothManifolds.MaximalFlowData.FlowSmoothAt (phaseManifold S) F z ∧
          PositionSmoothAt S F z

def affine_geodesicType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (I : Set ℝ) (q : ℝ → Phase S) (a b : ℝ),
    IsGeodesicOn S C I q →
      IsGeodesicOn S C (affineDomain I a b) (affineCurve S q a b)

/-- Nonzero affine changes preserve the full maximal domain. The transformed
initial phase is (γ(b),a γ'(b)); arbitrary translations are included. -/
def maximal_affineType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (w : Phase S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
    IsMaximalThrough S C w I q → ∀ (a b : ℝ), a ≠ 0 → b ∈ I.carrier →
      ∃ J : D13Unified.OpenTimeInterval,
        J.carrier = affineDomain I.carrier a b ∧
        IsMaximalThrough S C (affineCurve S q a b 0) J (affineCurve S q a b)

def constant_speedType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → ∀ s ∈ I.carrier, ∀ t ∈ I.carrier,
        tangentNorm g (q s).1 (q s).2 = tangentNorm g (q t).1 (q t).2

def constant_geodesicType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S)) (p : M),
    IsGeodesicOn S C univ (constantCurve S p)

def zero_maximalType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S)) (p : M),
    IsMaximalThrough S C ⟨p, 0⟩ D13Unified.OpenTimeInterval.whole (constantCurve S p)

end P202Specs.Geometry.GeodesicIVP
