import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CutCriterion
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GaussLemma
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ScalarCalculus

/-! The complete theorem `thm:p202-cut-polar`, paper.tex:4202–4270.
The topology on the unit tangent sphere is the topology induced by any linear
coordinates on the actual tangent fiber. The local inverse assertion is an
unpackaged smooth diffeomorphism assertion: the global polar map is bijective,
and its inverse, in exponential charts, is the smooth radius/normalization map.
No cut endpoint or the basepoint is included in the regular domain. -/
set_option autoImplicit false
noncomputable section

namespace P202.CutPolarData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.GeodesicData P202.ExponentialData
  P202.CutTimeData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The original sphere topology, expressed in arbitrary linear coordinates. -/
def directionTopology (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) : TopologicalSpace (UnitDirection g p) :=
  TopologicalSpace.induced (fun v => E v.val) inferInstance

def regularDomain (g : RiemannianMetric S) (F : CurveFamily (Phase S)) (p : M) : Set M :=
  ({p} ∪ cutLocus g F p)ᶜ

def polarMap (g : RiemannianMetric S) (F : CurveFamily (Phase S)) (p : M)
    (tv : ℝ × UnitDirection g p) : M := fiberExponential F p (tv.1 • tv.2.val)

end P202.CutPolarData

namespace P202Specs.Geometry.CutPolarDomain
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  SmoothManifolds.PartitionData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.ExponentialData P202.CompletenessData P202.CompleteExponentialData
  P202.CutTimeData P202.CutCriterionData P202.CutPolarData
  P202.CurvatureData P202.ExponentialJacobiData
open Set
universe u

/-- Continuity in the extended order topology, with infinity retained. -/
def cut_time_continuousType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 0 < n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n),
      letI := directionTopology g p E
      Continuous (cutTime g F p)

/-- The full, globally defined polar map has exactly the asserted image and
is one-to-one on the entire open polar domain. -/
def polar_bijectionType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 0 < n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ p : M, BijOn (polarMap g F p) (polarDomain g F p) (regularDomain g F p)

/-- Smooth polar inverse in each exponential chart. Normalization is written
in the same linear coordinates as that chart, giving the smooth sphere-valued
inverse by its ambient coordinates. The forward map is the actual smooth
exponential composed with (t,v) ↦ t v. -/
def polar_diffeomorphismType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 0 < n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ p : M,
      BijOn (polarMap g F p) (polarDomain g F p) (regularDomain g F p) ∧
      IsOpen (regularDomain g F p) ∧
      (∀ E : TangentSpace S p ≃ₗ[ℝ] Euclidean n,
        letI := directionTopology g p E
        IsOpen (polarDomain g F p)) ∧
      ∀ q ∈ regularDomain g F p, ∃ (w : TangentSpace S p)
        (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
        (c : ModelChart n .euclidean M) (U : Set M),
        MinimizingInitialVector g F p q w ∧ IsExponentialInverseAt F p w E c ∧
        IsOpen U ∧ q ∈ U ∧ U ⊆ regularDomain g F p ∩ c.source ∧
        (∀ y ∈ U, ∀ tv ∈ polarDomain g F p, polarMap g F p tv = y ↔
          tv.1 = tangentNorm g p (E.symm (c y).val) ∧
          tv.1 • tv.2.val = E.symm (c y).val) ∧
        (∀ y ∈ U, ContDiffAt ℝ (⊤ : ℕ∞)
          (fun x : Euclidean n => tangentNorm g p (E.symm x)) (c y).val ∧
          ContDiffAt ℝ (⊤ : ℕ∞)
            (fun x : Euclidean n => (tangentNorm g p (E.symm x))⁻¹ • x) (c y).val) ∧
        (∀ (d : ModelChart n .euclidean M), d ∈ S.smoothStructure.val →
          ∀ x : Euclidean n, fiberExponential F p (E.symm x) ∈ d.source →
            ContDiffAt ℝ (⊤ : ℕ∞)
              (fun z : Euclidean n => (d (fiberExponential F p (E.symm z))).val) x)

/-- Smoothness and the intrinsic metric gradient identity for distance, only
away from both the basepoint and every cut endpoint. The vector is the actual
terminal unit radial velocity: on [0,1] the minimizing initial vector has speed
its norm, so division by that norm gives the unit velocity. -/
def distance_regularType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 0 < n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ (p q : M), q ∈ regularDomain g F p →
      ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val (lengthDistance g p) q ∧
      ∃ (w : TangentSpace S p) (h : fiberExponential F p w = q),
        MinimizingInitialVector g F p q w ∧
        (∀ z, MinimizingInitialVector g F p q z → z = w) ∧
        let V := (tangentNorm g p w)⁻¹ •
          castTangent S h (fiberDifferential S F p w w)
        tangentNorm g q V = 1 ∧
        (∀ X : TangentSpace S q,
          pairing g q V X = scalarDerivative S (lengthDistance g p) q X) ∧
        ∃ (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
          (hp : p ∈ e.source) (d : ModelChart n .euclidean M)
          (hd : d ∈ S.smoothStructure.val) (hq : fiberExponential F p w ∈ d.source),
          fiberDifferential S F p w w =
            P202.GaussData.fiberDifferential F p w e he hp d hd hq w ∧
          P202.GaussData.fiberDifferential F p w e he hp d hd hq w =
            (F.curve ⟨p,w⟩ 1).2

/-- All assertions of the original theorem, including its first two clauses. -/
def cut_polarType : Prop :=
  P202Specs.Geometry.CutCriterion.finite_cut_criterionType.{u} ∧
  P202Specs.Geometry.CutCriterion.interior_unique_nonconjugateType.{u} ∧
  cut_time_continuousType.{u} ∧ polar_diffeomorphismType.{u} ∧ distance_regularType.{u}

end P202Specs.Geometry.CutPolarDomain
