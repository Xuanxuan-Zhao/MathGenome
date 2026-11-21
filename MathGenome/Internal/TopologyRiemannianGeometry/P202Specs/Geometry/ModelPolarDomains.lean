import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.HyperbolicHalfSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Model geometry for paper.tex 4559–4587, also used at 4477–4480.

`GlobalNormalGeometry` describes the exponential as the inverse of an actual
GLOBAL smooth atlas chart, not merely a bijection of underlying sets.
`SphericalNormalGeometry` uses the whole open tangent ball of radius πa;
its image includes the pole and excludes precisely its antipode. Removing the
zero vector and the pole gives the polar diffeomorphism: the remaining change
of variables is v ↔ (‖v‖, v/‖v‖) on a positive definite vector space.

Distances below are infima of the ORIGINAL piecewise-C1 Riemannian lengths.
In these connected complete models the path-length sets are nonempty and
bounded below by the accepted distance theorem. Ambient chordal distances,
or coordinate norms on the hyperboloid, are not used as intrinsic distances.

Existence of the actual complete simply connected realizations is a separate
conclusion (`modelsExistType`). The universal statements then apply to those
realizations; their hypotheses are the already proved model interfaces and
contain none of the polar-domain or distance assertions being established.
-/
set_option autoImplicit false
noncomputable section
namespace P202.ModelPolarData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.GeodesicData
  P202.ExponentialData P202.DistanceData P202.SpaceFormData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Intrinsic distance on a connected model, using the source's curve class. -/
abbrev modelDistance (g : RiemannianMetric S) (p q : M) : ℝ :=
  P202.CompleteExponentialData.lengthDistance g p q

/-- An actual smooth isometry, including its actual intrinsic differential. -/
def IsSmoothIsometry (g : RiemannianMetric S)
    (d : Diffeomorph S.smoothStructure.val S.smoothStructure.val) : Prop :=
  ∃ L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S (d.toEquiv p),
    (∀ p, SmoothManifolds.DifferentialData.IsDifferential S S d.toEquiv p (L p)) ∧
    IsMetricPreserving g g d.toEquiv L

def IsHomogeneous (g : RiemannianMetric S) : Prop :=
  ∀ p q : M, ∃ d : Diffeomorph S.smoothStructure.val S.smoothStructure.val,
    d.toEquiv p = q ∧ IsSmoothIsometry g d

/-- Positive radial coordinate and a unit vector, in the fixed orthonormal
fiber coordinates. The unit locus has its ordinary embedded sphere structure. -/
def polarParameters (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (J : Set ℝ) : Set (ℝ × Euclidean n) :=
  {z | z.1 ∈ J ∧ tangentNorm g p (E.symm z.2) = 1}

/-- Explicit polar diffeomorphism in the chart c. Smoothness is expressed by
ambient smooth coordinate extensions on the embedded unit sphere and by a
smooth inverse on the punctured vector space. Thus this conclusion does not
leave the change from Cartesian to polar coordinates as an informal bridge. -/
def HasPolarDiffeomorphism (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (c : ModelChart n .euclidean M) (J : Set ℝ) : Prop :=
  ∃ e : ↥(polarParameters g p E J) ≃ {q : M | q ∈ c.source ∧ q ≠ p},
    (∀ z, (e z).val = fiberExponential F p (E.symm (z.val.1 • z.val.2))) ∧
    (∀ q, (e.symm q).val =
      (tangentNorm g p (E.symm (c q.val).val),
        (tangentNorm g p (E.symm (c q.val).val))⁻¹ • (c q.val).val)) ∧
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × Euclidean n =>
        (c (fiberExponential F p (E.symm (z.1 • z.2)))).val)
      (polarParameters g p E J) ∧
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Euclidean n =>
        (tangentNorm g p (E.symm y), (tangentNorm g p (E.symm y))⁻¹ • y))
      {y | y ≠ 0}

/-- Every positive radius is a metric normal-ball radius, uniformly in center.
The global inverse chart proves the global diffeomorphism assertion. -/
def GlobalNormalGeometry (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) : Prop :=
  ∀ (F : CurveFamily (Phase S)), IsMaximalFamily S C F → ∀ p : M,
    ∃ (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
      (c : ModelChart n .euclidean M),
      IsOrthonormalCoordinates g p E ∧ c ∈ S.smoothStructure.val ∧
      c.source = Set.univ ∧ c.target = Set.univ ∧ (c p).val = 0 ∧
      (∀ v : TangentSpace S p,
        (⟨p, v⟩ : Phase S) ∈ exponentialDomain F ∧
        fiberExponential F p v = c.symm ⟨E v, by simp [modelSet]⟩ ∧
        modelDistance g p (fiberExponential F p v) = tangentNorm g p v) ∧
      HasPolarDiffeomorphism g F p E c (Set.Ioi 0) ∧
      ∀ r : ℝ, 0 < r → ∃ d : ModelChart n .euclidean M,
        IsNormalChart g F p E r d ∧
        d.source = {q | modelDistance g p q < r}

def EuclideanTranslations {n : ℕ} (G : EuclideanModel n) : Prop :=
  ∀ p q : E n,
    ∃ d : Diffeomorph G.manifold.smoothStructure.val G.manifold.smoothStructure.val,
      (∀ x, d.toEquiv x = x + (q - p)) ∧ d.toEquiv p = q ∧
      IsSmoothIsometry G.metric d

/-- Orthonormal ambient maps restricted to the literal radius-a sphere. -/
def SphericalHomogeneity {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) : Prop :=
  ∀ p q : Sphere n a, ∃ U : E (n + 1) ≃ₗᵢ[ℝ] E (n + 1),
    U p.val = q.val ∧
    ∃ d : Diffeomorph B.manifold.smoothStructure.val B.manifold.smoothStructure.val,
      (∀ x, (d.toEquiv x).val = U x.val) ∧ d.toEquiv p = q ∧
      IsSmoothIsometry B.metric d

/-- The full spherical normal ball plus its metric meaning, including the
cut-time boundary. The distance formula also covers the pole and antipode. -/
def SphericalNormalGeometry {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A) : Prop :=
  ∀ (F : CurveFamily (Phase B.manifold)),
    IsMaximalFamily B.manifold B.connection F → ∀ p : Sphere n a,
    ∃ (E : TangentSpace B.manifold p ≃ₗ[ℝ] Euclidean n)
      (c : ModelChart n .euclidean (Sphere n a)),
      IsOrthonormalCoordinates B.metric p E ∧
      IsNormalChart B.metric F p E (Real.pi * a) c ∧
      c.source = {q | q.val ≠ -p.val} ∧
      (∀ v : TangentSpace B.manifold p,
        (⟨p, v⟩ : Phase B.manifold) ∈ exponentialDomain F ∧
        (fiberExponential F p v).val = sphereCurve a p.val (B.ambientVector p v) 1) ∧
      (∀ v : TangentSpace B.manifold p, tangentNorm B.metric p v ≤ Real.pi * a →
        modelDistance B.metric p (fiberExponential F p v) = tangentNorm B.metric p v) ∧
      (∀ v : TangentSpace B.manifold p, tangentNorm B.metric p v = 1 →
        (fiberExponential F p ((Real.pi * a) • v)).val = -p.val) ∧
      (∀ q : Sphere n a,
        modelDistance B.metric p q = a * Real.arccos (inner ℝ p.val q.val / a ^ 2)) ∧
      (∀ q : Sphere n a, q.val = -p.val → modelDistance B.metric p q = Real.pi * a) ∧
      HasPolarDiffeomorphism B.metric F p E c (Set.Ioo 0 (Real.pi * a)) ∧
      ∀ r : ℝ, 0 < r → r < Real.pi * a →
        ∃ d : ModelChart n .euclidean (Sphere n a),
          IsNormalChart B.metric F p E r d ∧
          d.source = {q | modelDistance B.metric p q < r}

/-- The specific half-space actions used in the source's homogeneity proof.
Here the half-space has dimension m+1. -/
def HalfSpaceHomogeneity {m : ℕ} {a : ℝ}
    (H : P202.HalfSpaceData.HalfSpaceModel m a) : Prop :=
  ∀ p q : P202.HalfSpaceData.HalfSpace m,
    ∃ (b : P202.HyperboloidData.Spatial m) (k : ℝ), 0 < k ∧
      ∃ d : Diffeomorph H.manifold.smoothStructure.val H.manifold.smoothStructure.val,
        (∀ x, (d.toEquiv x).val = (b + k • x.val.1, k * x.val.2)) ∧
        d.toEquiv p = q ∧ IsSmoothIsometry H.metric d

/-- The prescribed global projection chart, which fixes the smooth structure
on the actual upper sheet. It does not assume anything about exponentials. -/
def HasProjectionChart {n : ℕ} {a : ℝ}
    (S : SmoothManifold n .euclidean (P202.HyperboloidData.Hyperboloid n a)) : Prop :=
  ∃ c ∈ S.smoothStructure.val, c.source = Set.univ ∧ c.target = Set.univ ∧
    ∀ p, (c p).val = p.val.1

end P202.ModelPolarData

namespace P202Specs.Geometry.ModelPolarDomains
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.SpaceFormData P202.ModelPolarData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.ExponentialData

/-- Accepted construction theorem reused as a conclusion, never postulated. -/
def modelsExistType : Prop := P202Specs.Geometry.HyperbolicHalfSpace.modelsType

def euclideanFormulaType : Prop :=
  ∀ (n : ℕ) (G : EuclideanModel n), G.Conclusion →
    ∀ F : CurveFamily (Phase G.manifold), IsMaximalFamily G.manifold G.connection F →
    ∀ (p : E n) (v : TangentSpace G.manifold p),
      (⟨p, v⟩ : Phase G.manifold) ∈ exponentialDomain F ∧
      fiberExponential F p v = line p (G.coordinates p v) 1

/-- Intrinsic Euclidean distance, not just ambient displacement. -/
def euclideanDistanceType : Prop :=
  ∀ (n : ℕ) (G : EuclideanModel n), G.Conclusion →
    ∀ F : CurveFamily (Phase G.manifold), IsMaximalFamily G.manifold G.connection F →
    ∀ (p : E n) (v : TangentSpace G.manifold p),
      modelDistance G.metric p (fiberExponential F p v) = tangentNorm G.metric p v

def sphericalFormulaType : Prop :=
  ∀ {n : ℕ} {a : ℝ} {A : EuclideanModel (n + 1)} (B : SphericalModel n a A),
    B.Conclusion → ∀ F : CurveFamily (Phase B.manifold),
    IsMaximalFamily B.manifold B.connection F →
    ∀ (p : Sphere n a) (v : TangentSpace B.manifold p),
      (⟨p, v⟩ : Phase B.manifold) ∈ exponentialDomain F ∧
      (fiberExponential F p v).val = sphereCurve a p.val (B.ambientVector p v) 1

def sphericalCutTimeType : Prop :=
  ∀ {n : ℕ} {a : ℝ}, 0 < a → ∀ {A : EuclideanModel (n + 1)}
    (B : SphericalModel n a A), B.Conclusion →
    ∀ F : CurveFamily (Phase B.manifold), IsMaximalFamily B.manifold B.connection F →
    ∀ (p : Sphere n a) (v : TangentSpace B.manifold p), tangentNorm B.metric p v = 1 →
      (⟨p, (Real.pi * a) • v⟩ : Phase B.manifold) ∈ exponentialDomain F ∧
      (fiberExponential F p ((Real.pi * a) • v)).val = -p.val

/-- Complete flat model domain, distance and explicit transitive action. -/
def euclideanType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ G : EuclideanModel n, G.Conclusion →
    GlobalNormalGeometry G.metric G.connection ∧ EuclideanTranslations G

/-- Complete spherical domain, distance (including the antipode) and action. -/
def sphericalType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a : ℝ, 0 < a →
    ∀ (A : EuclideanModel (n + 1)) (B : SphericalModel n a A), B.Conclusion →
      SphericalNormalGeometry B ∧ SphericalHomogeneity B

/-- No Killing–Hopf or general classification theorem occurs as a hypothesis.
The center is arbitrary, so all positive normal radii are uniform in center. -/
def hyperbolicType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ a : ℝ, 0 < a →
    ∀ (S : SmoothManifold n .euclidean (P202.HyperboloidData.Hyperboloid n a))
      (g : RiemannianMetric S) (C : Connection (tangentBundle S)),
    HasProjectionChart S → P202.HyperboloidData.IsInduced g → IsLeviCivita g C →
    GlobalNormalGeometry g C ∧ IsHomogeneous g ∧
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
      ∀ (p : P202.HyperboloidData.Hyperboloid n a) (v : TangentSpace S p),
      tangentNorm g p v = 1 → ∀ t : ℝ,
        (⟨p, t • v⟩ : Phase S) ∈ exponentialDomain F ∧
        (fiberExponential F p (t • v)).val =
          P202.HyperboloidData.unitCurve a p.val (P202.HyperboloidData.ambientDifferential S p v) t

/-- The half-space formulas supply the hyperbolic transitive isometries, and
are connected to the hyperboloid by modelsExistType's intrinsic isometry. -/
def halfSpaceHomogeneityType : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ a : ℝ, 0 < a →
    ∀ H : P202.HalfSpaceData.HalfSpaceModel m a, HalfSpaceHomogeneity H

/-- All model geometry required by the assigned source stage. -/
def modelPolarDomainsType : Prop :=
  modelsExistType ∧ euclideanFormulaType ∧ euclideanDistanceType ∧ sphericalFormulaType ∧
    sphericalCutTimeType ∧ euclideanType ∧ sphericalType ∧ hyperbolicType ∧
    halfSpaceHomogeneityType

end P202Specs.Geometry.ModelPolarDomains
