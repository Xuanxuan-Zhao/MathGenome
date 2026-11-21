import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricFoundation
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Connected.TotallyDisconnected

/-! The infimum is taken over the original compact-interval curves, with no
restriction on their compact parameter interval. The real distance is defined
only for pairs in one connected component. In particular this definition does
not put a finite distance between different components. -/
set_option autoImplicit false

namespace P202.DistanceData
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData P202.MetricData P202.CurveData Set
universe u

variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]

def HasPiecewiseC1Path (S : SmoothManifold n kind M) (p q : M) : Prop :=
  ∃ a b : ℝ, ∃ c : PiecewiseC1Curve S a b, c a = p ∧ c b = q

def pathLengths {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    (p q : M) : Set ℝ :=
  {L | ∃ a b : ℝ, ∃ c : PiecewiseC1Curve S a b,
    c a = p ∧ c b = q ∧ L = length g c}

noncomputable def componentDistance {S : SmoothManifold n kind M}
    (g : RiemannianMetric S) (o : M)
    (p q : connectedComponent o) : ℝ := sInf (pathLengths g p.val q.val)

/-- Local geometric estimates used in the proof, not additional hypotheses
in the full theorem below. -/
def LocalShortCurves {S : SmoothManifold n kind M} (g : RiemannianMetric S) : Prop :=
  ∀ p : M, ∀ ε : ℝ, 0 < ε → ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
    ∀ q ∈ U, ∃ a b : ℝ, ∃ c : PiecewiseC1Curve S a b,
      c a = p ∧ c b = q ∧ length g c < ε

def LocalCurveTrapping {S : SmoothManifold n kind M} (g : RiemannianMetric S) : Prop :=
  ∀ p : M, ∀ U : Set M, IsOpen U → p ∈ U → ∃ ε : ℝ, 0 < ε ∧
    ∀ {a b : ℝ} (c : PiecewiseC1Curve S a b),
      c a = p → length g c < ε → c b ∈ U

end P202.DistanceData

namespace P202Specs.Geometry.LengthDistance
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData P202.MetricData P202.CurveData P202.DistanceData Set
universe u

def hasPiecewiseC1PathType := {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → SmoothManifold n kind M → M → M → Prop
def hasPiecewiseC1PathValue : hasPiecewiseC1PathType := @HasPiecewiseC1Path

def pathLengthsType := {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n kind M} →
  RiemannianMetric S → M → M → Set ℝ
noncomputable def pathLengthsValue : pathLengthsType := @pathLengths

def componentDistanceType := {n : ℕ} → {kind : ModelKind} → {M : Type u} →
  [TopologicalSpace M] → {S : SmoothManifold n kind M} →
  RiemannianMetric S → (o : M) → connectedComponent o → connectedComponent o → ℝ
noncomputable def componentDistanceValue : componentDistanceType := @componentDistance

def length_nonnegType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S)
    {a b : ℝ} (c : PiecewiseC1Curve S a b), 0 ≤ length g c

def path_existsType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n kind M) (p q : M),
    HasPiecewiseC1Path S p q ↔ q ∈ connectedComponent p

/-- Nonempty and bounded below: the displayed infimum is an actual finite
real infimum, rather than the default infimum of an empty real set. -/
def component_finiteType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S) (o : M)
    (p q : connectedComponent o),
    (pathLengths g p.val q.val).Nonempty ∧ BddBelow (pathLengths g p.val q.val)

def component_metricType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S) (o : M),
    ∃ d : MetricSpace (connectedComponent o),
      d.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (connectedComponent o)) ∧
      ∀ p q, @dist _ d.toDist p q = componentDistance g o p q

def zero_dimensionType : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 kind M) (o : M), connectedComponent o = {o}

def componentDistance_nonnegType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S) (o : M)
    (p q : connectedComponent o), 0 ≤ componentDistance g o p q

def componentDistance_selfType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S) (o : M)
    (p : connectedComponent o), componentDistance g o p p = 0

def componentDistance_commType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S) (o : M)
    (p q : connectedComponent o), componentDistance g o p q = componentDistance g o q p

def componentDistance_triangleType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S) (o : M)
    (p q r : connectedComponent o),
    componentDistance g o p r ≤ componentDistance g o p q + componentDistance g o q r

def component_metric_of_localType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S),
    LocalShortCurves g → LocalCurveTrapping g →
    ∀ o : M, ∃ d : MetricSpace (connectedComponent o),
      d.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (connectedComponent o)) ∧
      ∀ p q, @dist _ d.toDist p q = componentDistance g o p q

def local_short_curvesType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S), LocalShortCurves g

def local_curve_trappingType : Prop :=
  ∀ {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n kind M} (g : RiemannianMetric S), LocalCurveTrapping g

def zero_dimension_metricType : Prop :=
  ∀ {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 kind M} (g : RiemannianMetric S) (o : M),
    ∃ d : MetricSpace (connectedComponent o),
      d.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (connectedComponent o)) ∧
      ∀ p q, @dist _ d.toDist p q = componentDistance g o p q

/-- The entire stated theorem, including its boundary extension. The first
three conjuncts reuse the independent full propositions for the already
allocated metric existence, immersion pullback and length preservation. The
remaining conjuncts impose no extra geometric hypotheses, even in rank zero. -/
def metric_distanceType : Prop :=
  P202Specs.Geometry.MetricFoundation.exists_metricType.{u} ∧
  P202Specs.Geometry.MetricFoundation.pullback_metric_originalType.{u} ∧
  P202Specs.Geometry.MetricFoundation.localIsometry_length_existsType.{u} ∧
  path_existsType.{u} ∧ component_finiteType.{u} ∧ component_metricType.{u} ∧
  zero_dimensionType.{u}

def metric_distance_of_localType : Prop :=
  local_short_curvesType.{u} → local_curve_trappingType.{u} → metric_distanceType.{u}

end P202Specs.Geometry.LengthDistance
