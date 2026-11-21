import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CutTime
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ExponentialJacobi

/-! The first two assertions and stability argument of thm:p202-cut-polar,
paper.tex:4202–4253. Tangent vectors parametrize affine segments on [0,1].
The equality defining a minimizing initial vector is the original length
metric equality, rather than a certificate postulated for an arbitrary map. -/
set_option autoImplicit false

namespace P202.CutCriterionData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.GeodesicData P202.ExponentialData
  P202.CompleteExponentialData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Under the complete geodesic-family hypotheses these are exactly the
initial vectors of minimizing constant-speed segments on [0,1]. -/
def MinimizingInitialVector (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p q : M) (w : TangentSpace S p) : Prop :=
  fiberExponential F p w = q ∧ tangentNorm g p w = lengthDistance g p q

/-- A smooth local inverse in the original maximal atlas. The chart's inverse
is the exponential in linear coordinates on an open neighborhood of w. -/
def IsExponentialInverseAt (F : CurveFamily (Phase S)) (p : M)
    (w : TangentSpace S p) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (c : ModelChart n .euclidean M) : Prop :=
  c ∈ S.smoothStructure.val ∧ fiberExponential F p w ∈ c.source ∧
    (c (fiberExponential F p w)).val = E w ∧
    ∀ x ∈ c.target, fiberExponential F p (E.symm x.val) = c.symm x

end P202.CutCriterionData

namespace P202Specs.Geometry.CutCriterion
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.ExponentialData P202.CompletenessData P202.CompleteExponentialData
  P202.CutTimeData P202.CutCriterionData P202.CurvatureData P202.ExponentialJacobiData
open Set
universe u

def minimizingInitialVectorType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → RiemannianMetric S →
  CurveFamily (Phase S) → (p q : M) → TangentSpace S p → Prop
def minimizingInitialVectorValue : minimizingInitialVectorType := @MinimizingInitialVector

def isExponentialInverseAtType := {n : ℕ} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold n .euclidean M} → CurveFamily (Phase S) → (p : M) →
  TangentSpace S p → (TangentSpace S p ≃ₗ[ℝ] Euclidean n) →
  ModelChart n .euclidean M → Prop
def isExponentialInverseAtValue : isExponentialInverseAtType := @IsExponentialInverseAt

/-- All nearby endpoints have their unique minimizing initial vector supplied
by this one smooth local inverse of exp_p. -/
def minimizing_stabilityType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 0 < n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ (p q : M) (w : TangentSpace S p), q ≠ p →
      MinimizingInitialVector g F p q w →
      (∀ z, MinimizingInitialVector g F p q z → z = w) →
      Function.Bijective (fiberDifferential S F p w) →
      ∃ (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
        (c : ModelChart n .euclidean M) (U : Set M),
        IsExponentialInverseAt F p w E c ∧ IsOpen U ∧ q ∈ U ∧ U ⊆ c.source ∧
        ∀ y ∈ U, ∀ z : TangentSpace S p,
          MinimizingInitialVector g F p y z ↔ z = E.symm (c y).val

/-- The radial segment is minimizing and is the only minimizing segment with
the common [0,1] parametrization; conjugacy is along the given radial ray. -/
def interior_unique_nonconjugateType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 0 < n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
      (p : M) (v : UnitDirection g p) (t : ℝ),
      0 < t → ENNReal.ofReal t < cutTime g F p v →
      MinimizingInitialVector g F p (fiberExponential F p (t • v.val)) (t • v.val) ∧
      (∀ z, MinimizingInitialVector g F p (fiberExponential F p (t • v.val)) z →
        z = t • v.val) ∧
      ∃ ht : t ∈ (F.interval ⟨p,v.val⟩).carrier,
        ¬ ConjugateAlong S C R (F.interval ⟨p,v.val⟩) (F.curve ⟨p,v.val⟩)
          ⟨0,(hF ⟨p,v.val⟩).1⟩ ⟨t,ht⟩

/-- Only finite cut times have a cut-point dichotomy. The two minimizing
vectors are different, hence determine distinct affine segments on [0,1]. -/
def finite_cut_criterionType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 0 < n →
    LengthMetricComplete g → ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
      (p : M) (v : UnitDirection g p) (hfin : cutTime g F p v ≠ ⊤),
      let t := (cutTime g F p v).toReal
      MinimizingInitialVector g F p (cutPoint g F p v hfin) (t • v.val) ∧
      ((∃ ht : t ∈ (F.interval ⟨p,v.val⟩).carrier,
        ConjugateAlong S C R (F.interval ⟨p,v.val⟩) (F.curve ⟨p,v.val⟩)
          ⟨0,(hF ⟨p,v.val⟩).1⟩ ⟨t,ht⟩) ∨
        ∃ z : TangentSpace S p, z ≠ t • v.val ∧
          MinimizingInitialVector g F p (cutPoint g F p v hfin) z)

end P202Specs.Geometry.CutCriterion
