import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LocalSpaceFormDevelopment
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ModelPolarDomains

/-! Independent statement for paper.tex 4589–4625.

The source is the actual Euclidean, radius-1/√k spherical, or
radius-1/√(-k) hyperboloid model. The model realization hypotheses are the
previously constructed smooth structures and metrics; no normal-ball,
continuation, covering, monodromy or global-development certificate is an input.
The three clauses cover k = 0, k > 0 and k < 0 respectively.
-/
set_option autoImplicit false
noncomputable section

namespace P202Specs.Geometry.GlobalSpaceFormDevelopment
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.CurvatureData
  P202.ConstantCurvaturePolarData P202.CompletenessData P202.LocalDevelopmentData
  P202.SpaceFormData P202.ModelPolarData

/-- The original target and prescribed first-order data, for one fixed
literal source model and its prescribed curvature. -/
def developmentFromType {n : ℕ} {X : Type} [TopologicalSpace X]
    (S : SmoothManifold n .euclidean X) (g : RiemannianMetric S) (k : ℝ) : Prop :=
  ∀ {M : Type} [TopologicalSpace M] [ConnectedSpace M]
    (T : SmoothManifold n .euclidean M) (h : RiemannianMetric T)
    (D : Connection (tangentBundle T)), IsLeviCivita h D →
    ∀ Q : CurvatureTensor T, RepresentsCurvature D Q →
    ConstantSectional h Q k → LengthMetricComplete h →
    ∀ (x : X) (y : M) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y),
    (∀ v w, pairing h y (A v) (A w) = pairing g x v w) →
    ∃ f : X → M, IsLocalIsometryOn g h f Set.univ ∧ HasCenterData f x y A

/-- The flat model, on the original Euclidean space and standard metric. -/
def euclideanDevelopmentType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ G : EuclideanModel n, G.Conclusion →
    developmentFromType G.manifold G.metric 0

/-- For every positive curvature, the literal sphere has radius 1/√k. -/
def sphericalDevelopmentType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (k : ℝ), 0 < k →
    ∀ (A : EuclideanModel (n + 1))
      (B : SphericalModel n (1 / Real.sqrt k) A), B.Conclusion →
      developmentFromType B.manifold B.metric k

/-- For every negative curvature, use the original upper-sheet hyperboloid
with radius 1/√(-k), its projection smooth structure, and Lorentz-induced metric. -/
def hyperbolicDevelopmentType : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (k : ℝ), k < 0 →
    ∀ (S : SmoothManifold n .euclidean
        (P202.HyperboloidData.Hyperboloid n (1 / Real.sqrt (-k))))
      (g : RiemannianMetric S),
      HasProjectionChart S → P202.HyperboloidData.IsInduced g →
      developmentFromType S g k

/-- Globalization for all three actual simply connected curvature models. -/
def developmentType : Prop :=
  euclideanDevelopmentType ∧ sphericalDevelopmentType ∧ hyperbolicDevelopmentType

end P202Specs.Geometry.GlobalSpaceFormDevelopment
