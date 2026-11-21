import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.NormalMinimality
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch05.Frames

/-! Independent statements for the whole Theorem 6.9, especially the uniform
inverse and convex-neighborhood conclusions in paper.tex:3413–3451.
The product atlas below is the actual product of the given smooth atlas.
All distances asserted on a neighborhood concern one connected component;
the total infimum representative is used only to avoid proof-dependent maps.
No connection, inverse map, or convexity certificate is assumed to exist. -/
set_option autoImplicit false
noncomputable section

namespace P202.ConvexNormalData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData SmoothManifolds.ProductData
  SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.CurveData P202.GeodesicData
  P202.LeviCivitaData P202.ExponentialData P202.DistanceData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  (S : SmoothManifold n .euclidean M)

/-- Generating product atlas, with the fixed upstream linear product coordinates. -/
def endpointAtlas : Set (ModelChart (n + n) .euclidean (M × M)) :=
  productAtlas (tangentStructure S).productCoordinates
    S.smoothStructure.val S.smoothStructure.val

def endpointMap (F : CurveFamily (Phase S)) (w : Phase S) : M × M :=
  (w.1, exponential F w)

/-- Total representative of the squared length distance. On any connected
component this is definitionally the square of `componentDistance`. -/
def squaredDistance (g : RiemannianMetric S) (x : M × M) : ℝ :=
  (sInf (pathLengths g x.1 x.2)) ^ 2

/-- The compact curve has an actual affine geodesic tangent lift and realizes
the global infimum over all piecewise C¹ competitors in M. -/
def IsMinimizingGeodesic (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (q z : M)
    (γ : PiecewiseC1Curve S 0 1) : Prop :=
  γ 0 = q ∧ γ 1 = z ∧
    (∃ V : ℝ → Phase S, IsGeodesicOn S C (Icc 0 1) V ∧
      EqOn γ (fun t => (V t).1) (Icc 0 1)) ∧
    length g γ = sInf (pathLengths g q z)

/-- Ambient joint smoothness in time and both endpoints, including at time
0 and 1 and at equal endpoints. This is the same local extension convention
as the upstream joint position-flow smoothness predicate. -/
def SegmentSmoothAt (σ : M → M → ℝ → M) (x : ℝ × (M × M)) : Prop :=
  ContinuousAt (fun w : ℝ × (M × M) => σ w.2.1 w.2.2 w.1) x ∧
  ∀ e ∈ S.smoothStructure.val, ∀ d ∈ S.smoothStructure.val,
    ∀ c ∈ S.smoothStructure.val,
    x.2.1 ∈ e.source → x.2.2 ∈ d.source → σ x.2.1 x.2.2 x.1 ∈ c.source →
    ∃ W : Set (ℝ × (Euclidean n × Euclidean n)),
      IsOpen W ∧ (x.1, (e x.2.1).val, (d x.2.2).val) ∈ W ∧
      ∃ H : ℝ × (Euclidean n × Euclidean n) → Euclidean n,
        ContDiffOn ℝ (⊤ : ℕ∞) H W ∧
        (fun w : ℝ × (M × M) => H (w.1, (e w.2.1).val, (d w.2.2).val)) =ᶠ[𝓝 x]
          (fun w => (c (σ w.2.1 w.2.2 w.1)).val)

/-- A single smooth local inverse near the zero section, containing closed
fiber balls with one uniform positive radius and all pairs in V × V.
The inverse vectors for those pairs have length less than half that radius. -/
def UniformExponentialInverse (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) : Prop :=
  ∃ (r : ℝ) (V : Set M) (h : OpenPartialHomeomorph (Phase S) (M × M)),
    0 < r ∧ IsOpen V ∧ p ∈ V ∧ (⟨p, 0⟩ : Phase S) ∈ h.source ∧
    h.source ⊆ exponentialDomain F ∧ EqOn h (endpointMap S F) h.source ∧
    ManifoldSmoothOn (phaseManifold S).smoothStructure.val (endpointAtlas S)
      h h.source ∧
    ManifoldSmoothOn (endpointAtlas S) (phaseManifold S).smoothStructure.val
      h.symm h.target ∧
    (∀ q ∈ V, ∀ v : TangentSpace S q, tangentNorm g q v ≤ r →
      (⟨q, v⟩ : Phase S) ∈ h.source) ∧
    V ×ˢ V ⊆ h.target ∧
    ∀ q ∈ V, ∀ z ∈ V,
      (h.symm (q, z)).1 = q ∧
      tangentNorm g (h.symm (q, z)).1 (h.symm (q, z)).2 < r / 2

/-- A convex neighborhood carries a smoothly varying, globally minimizing
affine segment. Uniqueness is tested against every minimizing affine
geodesic in M, without requiring the competitor to stay in U.
Equal endpoints explicitly have a constant segment. -/
def IsConvexNormalNeighborhood (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (p : M) (U : Set M) : Prop :=
  IsOpen U ∧ p ∈ U ∧ U ⊆ connectedComponent p ∧
  ∃ σ : M → M → ℝ → M,
    (∀ q ∈ U, ∀ z ∈ U,
      (∃ γ : PiecewiseC1Curve S 0 1,
        EqOn γ (σ q z) (Icc 0 1) ∧ IsMinimizingGeodesic S g C q z γ) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, σ q z t ∈ U) ∧
      (∀ γ : PiecewiseC1Curve S 0 1, IsMinimizingGeodesic S g C q z γ →
        EqOn γ (σ q z) (Icc 0 1)) ∧
      (q = z → ∀ t ∈ Icc (0 : ℝ) 1, σ q z t = q) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, SegmentSmoothAt S σ (t, q, z))) ∧
    ∀ x ∈ U ×ˢ U,
      VectorSmoothAt (endpointAtlas S) (squaredDistance S g) x

end P202.ConvexNormalData

namespace P202Specs.Geometry.ConvexNormalNeighborhoods
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.GeodesicData P202.LeviCivitaData
  P202.ConvexNormalData
open Set
universe u

def uniform_inverseType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S)),
    IsMaximalFamily S C F → ∀ p : M, UniformExponentialInverse S g F p

def convex_neighborhoodsType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ (p : M) (O : Set M), IsOpen O → p ∈ O →
      ∃ U : Set M, U ⊆ O ∧ IsConvexNormalNeighborhood S g C p U

/-- The complete theorem retains the original radial formula and the full
centered comparison/equality statement, with no added assumptions. -/
def gauss_normalType : Prop :=
  P202Specs.Geometry.GaussLemma.gauss_lemmaType.{u} ∧
  P202Specs.Geometry.NormalMinimality.normal_minimalityType.{u} ∧
  uniform_inverseType.{u} ∧ convex_neighborhoodsType.{u}

end P202Specs.Geometry.ConvexNormalNeighborhoods
