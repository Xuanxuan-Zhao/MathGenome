import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GeodesicIVP

/-! Independent statements for Proposition 6.6 (paper.tex:3206–3234).
The exponential domain is the time-one slice of the actual maximal geodesic
family. Families carry no correctness certificates in their definition;
existence is a separate obligation. All statements are invariant under choice
of a maximal family. The derivative is stated in the same canonical chart
coordinates on the source tangent fiber and on the target manifold.
A normal chart records an actual smooth atlas chart with inverse equal to the
exponential of an orthonormal basis on a metric ball. Thus its source is an
open normal neighborhood and its inverse is a diffeomorphism on that ball.
There is no positive dimension or completeness assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace P202.ExponentialData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.GeodesicData P202.LeviCivitaData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

def exponentialDomain (F : CurveFamily (Phase S)) : Set (Phase S) :=
  {w | 1 ∈ (F.interval w).carrier}

def exponential (F : CurveFamily (Phase S)) (w : Phase S) : M :=
  (F.curve w 1).1

def fiberExponential (F : CurveFamily (Phase S)) (p : M)
    (v : TangentSpace S p) : M := exponential F ⟨p, v⟩

def IsOrthonormalCoordinates (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) : Prop :=
  ∀ i j : Fin n, pairing g p (E.symm (Pi.single i 1)) (E.symm (Pi.single j 1)) =
    if i = j then 1 else 0

/-- `c.symm` is precisely the exponential in basis coordinates on the metric
ball. Membership in the maximal smooth atlas supplies smoothness in both
directions; the chart supplies openness, injectivity and both inverse laws. -/
def IsNormalChart (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (r : ℝ) (c : ModelChart n .euclidean M) : Prop :=
  0 < r ∧ c ∈ S.smoothStructure.val ∧ p ∈ c.source ∧ (c p).val = 0 ∧
    c.target = {x | tangentNorm g p (E.symm x.val) < r} ∧
    ∀ x : ModelSpace n .euclidean, tangentNorm g p (E.symm x.val) < r →
      (⟨p, E.symm x.val⟩ : Phase S) ∈ exponentialDomain F ∧
        fiberExponential F p (E.symm x.val) = c.symm x

end P202.ExponentialData

namespace P202Specs.Geometry.ExponentialNormalCoordinates
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.GeodesicData P202.LeviCivitaData
  P202.ExponentialData
open Set
universe u

def exponentialDomainType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → CurveFamily (Phase S) → Set (Phase S)
def exponentialDomainValue : exponentialDomainType := @P202.ExponentialData.exponentialDomain

def exponentialType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → CurveFamily (Phase S) → Phase S → M
def exponentialValue : exponentialType := @P202.ExponentialData.exponential

def fiberExponentialType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → CurveFamily (Phase S) →
  (p : M) → TangentSpace S p → M
def fiberExponentialValue : fiberExponentialType := @P202.ExponentialData.fiberExponential

def IsOrthonormalCoordinatesType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → RiemannianMetric S →
  (p : M) → (TangentSpace S p ≃ₗ[ℝ] Euclidean n) → Prop
def IsOrthonormalCoordinatesValue : IsOrthonormalCoordinatesType :=
  @P202.ExponentialData.IsOrthonormalCoordinates

def IsNormalChartType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → RiemannianMetric S →
  CurveFamily (Phase S) → (p : M) → (TangentSpace S p ≃ₗ[ℝ] Euclidean n) →
  ℝ → ModelChart n .euclidean M → Prop
def IsNormalChartValue : IsNormalChartType := @P202.ExponentialData.IsNormalChart

/-- Construction prevents the family hypothesis in subsequent results from
being an extra existence assumption on the manifold or connection. -/
def family_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S)),
    ∃ F : CurveFamily (Phase S), P202.GeodesicData.IsMaximalFamily S C F

def domain_openType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)), P202.GeodesicData.IsMaximalFamily S C F →
      IsOpen (exponentialDomain F)

def zero_sectionType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)), P202.GeodesicData.IsMaximalFamily S C F →
      ∀ p : M, (⟨p, 0⟩ : Phase S) ∈ exponentialDomain F ∧ fiberExponential F p 0 = p

def fiber_star_shapedType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)), P202.GeodesicData.IsMaximalFamily S C F →
      ∀ (p : M) (v : TangentSpace S p), (⟨p, v⟩ : Phase S) ∈ exponentialDomain F →
        ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (⟨p, s • v⟩ : Phase S) ∈ exponentialDomain F

def smoothType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)), P202.GeodesicData.IsMaximalFamily S C F →
      ManifoldSmoothOn (phaseManifold S).smoothStructure.val S.smoothStructure.val
        (exponential F) (exponentialDomain F)

/-- The equality includes existence at scaled velocities and all real scales
whose corresponding time belongs to the actual maximal interval. -/
def radial_identityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)), P202.GeodesicData.IsMaximalFamily S C F →
      ∀ (p : M) (v : TangentSpace S p) (s : ℝ), s ∈ (F.interval ⟨p, v⟩).carrier →
        (⟨p, s • v⟩ : Phase S) ∈ exponentialDomain F ∧
          fiberExponential F p (s • v) = (F.curve ⟨p, v⟩ s).1

/-- Canonical tangent identification: use the same intrinsic chart-coordinate
linear equivalence for the source fiber and the target tangent space. -/
def derivative_zeroType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)), P202.GeodesicData.IsMaximalFamily S C F →
      ∀ (p : M) (e : ModelChart n .euclidean M)
        (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source),
        let E := (tangentStructure S).fiberCoordinates.equiv e he p hp
        HasFDerivAt (fun x : Euclidean n => (e (fiberExponential F p (E.symm x))).val)
          (ContinuousLinearMap.id ℝ (Euclidean n)) 0

def orthonormal_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S) (p : M),
    ∃ E : TangentSpace S p ≃ₗ[ℝ] Euclidean n, IsOrthonormalCoordinates g p E

def normal_chart_existsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ F : CurveFamily (Phase S), P202.GeodesicData.IsMaximalFamily S C F →
      ∀ (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n),
        IsOrthonormalCoordinates g p E →
        ∃ (r : ℝ) (c : ModelChart n .euclidean M), IsNormalChart g F p E r c

/-- All three identities in every exponential chart from an orthonormal basis.
The Christoffel symbols and scalar derivatives are the upstream intrinsic
connection coefficients and derivatives, evaluated at the actual center. -/
def normal_chart_identitiesType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ F : CurveFamily (Phase S), P202.GeodesicData.IsMaximalFamily S C F →
      ∀ (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n),
        IsOrthonormalCoordinates g p E →
        ∀ (r : ℝ) (c : ModelChart n .euclidean M) (hc : IsNormalChart g F p E r c),
        let d : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc.2.1⟩
        let q : (tangentBundle S).baseSet d := ⟨p, by
          simpa only [(tangentRealization S).baseSet d] using hc.2.2.1⟩
        (∀ i j : Fin n, metricMatrix g d p i j = if i = j then 1 else 0) ∧
        (∀ k i j : Fin n, christoffel C d q k i j = 0) ∧
        (∀ i j k : Fin n, scalarDerivative S (fun z => metricMatrix g d z j k) p
          (coordinateVector d i p) = 0)

end P202Specs.Geometry.ExponentialNormalCoordinates
