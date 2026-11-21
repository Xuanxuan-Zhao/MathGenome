import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConstantCurvaturePolar
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MetricGeodesicCompleteness

/-! Independent statements for paper.tex 4589–4607.

The source is allowed to be any manifold of the same constant curvature with
a supplied normal chart. This is stronger than restricting it to the standard
model: model normal charts are supplied by ModelPolarDomains. No normal chart
or injectivity of the exponential on the target is assumed. All manifolds
are boundaryless, with the original intrinsic tangent spaces and metrics.

Maps are total representatives, with smoothness, metric preservation, and
inverse germs required only on the stated open domain. Equality of germs is
ordinary eventual equality on a neighborhood of the center. The metric and
local inverse clauses include the center, not just the punctured polar chart.
-/
set_option autoImplicit false
noncomputable section

namespace P202.LocalDevelopmentData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.ConnectionData
  P202.GeodesicData P202.ExponentialData P202.ExponentialJacobiData
open Set Filter
open scoped _root_.Topology
universe u
variable {n : ℕ} {X M : Type u} [TopologicalSpace X] [TopologicalSpace M]
  {S : SmoothManifold n .euclidean X} {T : SmoothManifold n .euclidean M}

/-- A finite positive radius strictly below the first positive zero of s_k.
For k ≤ 0 there is no finite upper bound. -/
def BelowModelRadius (k r : ℝ) : Prop :=
  0 < r ∧ (0 < k → r < Real.pi / Real.sqrt k)

/-- The literal exponential formula (*), represented on the whole source.
Its meaningful domain is the normal chart's source. -/
def development (G : CurveFamily (Phase T)) (x : X) (y : M)
    (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y)
    (E : TangentSpace S x ≃ₗ[ℝ] Euclidean n)
    (d : ModelChart n .euclidean X) (z : X) : M :=
  fiberExponential G y (A (E.symm (d z).val))

/-- A smooth local isometry on an open domain, without global injectivity.
The inverses and the differential are the actual intrinsic ones. -/
def IsLocalIsometryOn (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f : X → M) (U : Set X) : Prop :=
  IsOpen U ∧ ∀ p ∈ U,
    ManifoldSmoothAt S.smoothStructure.val T.smoothStructure.val f p ∧
    (∃ j : M → X,
      ManifoldSmoothAt T.smoothStructure.val S.smoothStructure.val j (f p) ∧
      j (f p) = p ∧ (j ∘ f) =ᶠ[𝓝 p] id ∧ (f ∘ j) =ᶠ[𝓝 (f p)] id) ∧
    ∃ L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p),
      IsDifferential S T f p L ∧
      ∀ v w, pairing h (f p) (L v) (L w) = pairing g p v w

/-- A prescribed value and differential at the center. The cast merely
identifies the fibers over the propositionally equal points f(x) and y. -/
def HasCenterData (f : X → M) (x : X) (y : M)
    (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y) : Prop :=
  ∃ e : f x = y, IsDifferential S T f x
    ((castTangent T e).symm.toLinearMap.comp A.toLinearMap)

end P202.LocalDevelopmentData

namespace P202Specs.Geometry.LocalSpaceFormDevelopment
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.GeodesicData
  P202.ExponentialData P202.ExponentialJacobiData P202.CurvatureData
  P202.ConstantCurvaturePolarData P202.CompletenessData P202.LocalDevelopmentData
open Set Filter
open scoped _root_.Topology
universe u

/-- Formula (*) is a local isometry on EVERY supplied normal ball below rho_k,
with the specified center data. Completeness is imposed only on the target;
this strengthening covers, in particular, every complete standard model.
No target injectivity hypothesis is present. -/
def developmentType : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {X M : Type u}
    [TopologicalSpace X] [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (D : Connection (tangentBundle T)),
    IsLeviCivita g C → IsLeviCivita h D →
    ∀ (R : CurvatureTensor S) (Q : CurvatureTensor T),
    RepresentsCurvature C R → RepresentsCurvature D Q →
    ∀ k : ℝ, ConstantSectional g R k → ConstantSectional h Q k →
    LengthMetricComplete h →
    ∀ (F : CurveFamily (Phase S)) (G : CurveFamily (Phase T)),
    IsMaximalFamily S C F → IsMaximalFamily T D G →
    ∀ (x : X) (y : M) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y),
    (∀ v w, pairing h y (A v) (A w) = pairing g x v w) →
    ∀ (E : TangentSpace S x ≃ₗ[ℝ] Euclidean n), IsOrthonormalCoordinates g x E →
    ∀ (r : ℝ) (d : ModelChart n .euclidean X),
    BelowModelRadius k r → IsNormalChart g F x E r d →
    IsLocalIsometryOn g h (development G x y A E d) d.source ∧
    HasCenterData (development G x y A E d) x y A

/-- Any two germs of local isometries with the same center data agree.
This statement needs neither completeness nor constant curvature. -/
def germUniquenessType : Prop :=
  ∀ {n : ℕ} {X M : Type u} [TopologicalSpace X] [TopologicalSpace M]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f₁ f₂ : X → M) (U₁ U₂ : Set X),
    IsLocalIsometryOn g h f₁ U₁ → IsLocalIsometryOn g h f₂ U₂ →
    ∀ (x : X), x ∈ U₁ → x ∈ U₂ →
    ∀ (y : M) (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T y),
    HasCenterData f₁ x y A → HasCenterData f₂ x y A → f₁ =ᶠ[𝓝 x] f₂

/-- Every local isometry germ extends by formula (*) over every such ball.
The value and metric differential determining the extension are extracted
from the germ, not supplied as assumed exponential-intertwining data. -/
def germExtensionType : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ {X M : Type u}
    [TopologicalSpace X] [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean X) (T : SmoothManifold n .euclidean M)
    (g : RiemannianMetric S) (h : RiemannianMetric T)
    (C : Connection (tangentBundle S)) (D : Connection (tangentBundle T)),
    IsLeviCivita g C → IsLeviCivita h D →
    ∀ (R : CurvatureTensor S) (Q : CurvatureTensor T),
    RepresentsCurvature C R → RepresentsCurvature D Q →
    ∀ k : ℝ, ConstantSectional g R k → ConstantSectional h Q k →
    LengthMetricComplete h →
    ∀ (F : CurveFamily (Phase S)) (G : CurveFamily (Phase T)),
    IsMaximalFamily S C F → IsMaximalFamily T D G →
    ∀ (x : X) (f : X → M) (U : Set X),
    IsLocalIsometryOn g h f U → x ∈ U →
    ∀ (E : TangentSpace S x ≃ₗ[ℝ] Euclidean n), IsOrthonormalCoordinates g x E →
    ∀ (r : ℝ) (d : ModelChart n .euclidean X),
    BelowModelRadius k r → IsNormalChart g F x E r d →
    ∃ (A : TangentSpace S x ≃ₗ[ℝ] TangentSpace T (f x)),
      (∀ v w, pairing h (f x) (A v) (A w) = pairing g x v w) ∧
      HasCenterData f x (f x) A ∧
      IsLocalIsometryOn g h (development G x (f x) A E d) d.source ∧
      f =ᶠ[𝓝 x] development G x (f x) A E d

end P202Specs.Geometry.LocalSpaceFormDevelopment
