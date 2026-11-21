import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.OrientedTopDegree
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.InteriorInverse
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.Sard

/-! M12.01, paper.tex:2611–2666. The integer is characterized by integration
of ALL smooth top forms and by EVERY regular fiber. Both uniform model kinds
are permitted; compactness and empty intrinsic boundary express “closed”.
No regular value, inverse neighborhood, finite fiber, or substitution
certificate is assumed. The zero-dimensional case retains both ray signs. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SmoothManifolds.DegreeData
open ModelData AtlasData MapData TangentData DifferentialData CovectorData
  BundleOperationsData ExteriorData FormPullbackData OrientationData
  OrientationProductData LocalIntegrationData GlobalIntegrationData
universe u

/-- The sign of the ACTUAL tangent map between the specified determinant rays.
The value zero is used only for a singular map; at a regular point in equal
dimensions the map will be proved bijective. The two nonsingular values are
integers, so the regular-fiber sum is an integer without rounding a real scalar. -/
def differentialSign {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold n b N} {f : M → N}
    (o : Orientation S) (q : Orientation T) (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) : ℤ :=
  if h : Function.Bijective L then
    if Module.Ray.map (determinantMap n (LinearEquiv.ofBijective L h)) (o.val p) =
      q.val (f p) then 1 else -1
  else 0

/-- The field formula and integral identity use the original compact continuous
form interface. Every smooth top form is tested, with no support restriction
beyond the automatic compactness of the source and target manifolds. -/
def IntegralFormula {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ) (r : ℝ) : Prop :=
  ∀ (C : CotangentBundle T) (B : FormBundle C n) (ω : Form B)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
    (∀ p, IsDifferential S T f p (L p)) →
    ∃ (η : CompactTopForm T) (ξ : CompactTopForm S),
      η.field = ω.field ∧ ξ.field = pullbackField S T f L ω.field ∧
      I ξ = r * J η

/-- The count includes the empty fiber and uses the full original differential.
The finite-set witness is independent of the chosen differential realization. -/
def FiberFormula {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold n b N}
    (f : M → N) (o : Orientation S) (q : Orientation T) (d : ℤ) : Prop :=
  ∀ y, MapClassData.IsRegularValue S T f y →
    ∃ h : (f ⁻¹' {y}).Finite,
      ∀ (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
        (∀ p, IsDifferential S T f p (L p)) →
        d = ∑ p ∈ h.toFinset, differentialSign o q p (L p)

/-- Both original characterizations of degree, with a single integer. -/
def HasDegree {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (o : Orientation S) (q : Orientation T)
    (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ) (d : ℤ) : Prop :=
  IntegralFormula S T f I J (d : ℝ) ∧ FiberFormula f o q d

end SmoothManifolds.DegreeData

namespace Specs.SmoothManifolds.Degree.RegularFibers
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.MapClassData _root_.SmoothManifolds.TangentData
  _root_.SmoothManifolds.DifferentialData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.ExteriorData
  _root_.SmoothManifolds.FormPullbackData _root_.SmoothManifolds.OrientationData
  _root_.SmoothManifolds.LocalIntegrationData _root_.SmoothManifolds.GlobalIntegrationData
  _root_.SmoothManifolds.BoundaryData _root_.SmoothManifolds.DegreeData
universe u

/-- This stronger finite-fiber assertion does not require connectedness,
orientability, nonemptiness, or positive dimension. -/
def regular_fiber_finiteType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [CompactSpace M]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ →
    ∀ y, IsRegularValue S T f y → (f ⁻¹' {y}).Finite

/-- In positive dimension use Sard; dimension zero is included rather than
being hidden behind a positivity or “chosen regular value” hypothesis. -/
def regular_value_existsType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [Nonempty N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → ∃ y, IsRegularValue S T f y

/-- The real scalar prior to proving integrality. -/
def real_scalarType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    [ConnectedSpace M] [ConnectedSpace N] [CompactSpace M] [CompactSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ →
    ∀ (o : Orientation S) (q : Orientation T)
      (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ),
      IsIntegral o I → IsIntegral q J → ∃ r : ℝ, IntegralFormula S T f I J r

/-- The full original theorem: one uniquely determined integer works for ALL
smooth top forms and ALL regular values, including those outside the image. -/
def degree_existsType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    [ConnectedSpace M] [ConnectedSpace N] [CompactSpace M] [CompactSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ →
    ∀ (o : Orientation S) (q : Orientation T)
      (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ),
      IsIntegral o I → IsIntegral q J → ∃! d : ℤ, HasDegree S T f o q I J d

/-- Explicit independence, allowing different cardinalities and different
representations of the unique tangent differential. -/
def regular_value_independentType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    [ConnectedSpace M] [ConnectedSpace N] [CompactSpace M] [CompactSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ →
    ∀ (o : Orientation S) (q : Orientation T) (y z : N),
      IsRegularValue S T f y → IsRegularValue S T f z →
      ∀ (hy : (f ⁻¹' {y}).Finite) (hz : (f ⁻¹' {z}).Finite)
        (L K : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)),
        (∀ p, IsDifferential S T f p (L p)) →
        (∀ p, IsDifferential S T f p (K p)) →
        ∑ p ∈ hy.toFinset, differentialSign o q p (L p) =
          ∑ p ∈ hz.toFinset, differentialSign o q p (K p)

/-- Nonzero degree implies surjectivity, with no existence-of-regular-values
hypothesis: a missing point itself is a regular value with empty fiber. -/
def nonzero_degree_surjectiveType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    [ConnectedSpace M] [ConnectedSpace N] [CompactSpace M] [CompactSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ →
    ∀ (o : Orientation S) (q : Orientation T)
      (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ) (d : ℤ),
      IsIntegral o I → IsIntegral q J → HasDegree S T f o q I J d →
      d ≠ 0 → Function.Surjective f

/-- Each connected zero-manifold is a point. The degree is the product of the
two orientation signs, and the integral formula has that signed scalar. -/
def zero_dimensionType : Prop :=
  ∀ {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    [ConnectedSpace M] [ConnectedSpace N] [CompactSpace M] [CompactSpace N]
    (S : SmoothManifold 0 a M) (T : SmoothManifold 0 b N) (f : M → N),
    IsSmoothMap S T f →
    ∀ (o : Orientation S) (q : Orientation T)
      (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ),
      IsIntegral o I → IsIntegral q J →
      Subsingleton M ∧ Subsingleton N ∧ ∀ p : M,
        ∃ d : ℤ, HasDegree S T f o q I J d ∧
          (d : ℝ) = zeroSign o p * zeroSign q (f p)

end Specs.SmoothManifolds.Degree.RegularFibers
