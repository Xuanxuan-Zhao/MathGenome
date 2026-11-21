import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LeviCivita
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RiemannianVolume
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.MetricSplittings
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Conventions of paper.tex:4747–4758 and 5093–5117. All vectors are in
actual tangent fibers; the area density is the upstream metric density.
An orientation is the upstream continuous field of determinant rays. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical RealInnerProductSpace
namespace P202.SurfaceBoundaryData
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
open Module
open P202.MetricData P202.ConnectionData
universe u
variable {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 a M}

/-- The metric inner product on the original tangent vector space. Only local
norm instances are used: this does not change its smooth bundle realization. -/
def metricCore (g : RiemannianMetric S) (p : M) :
    InnerProductSpace.Core ℝ (TangentSpace S p) where
  inner := fun x y => pairing g p x y
  conj_inner_symm x y := g.symmetric p y x
  re_inner_nonneg x := by
    change 0 ≤ pairing g p x x
    by_cases h : x = 0
    · simp [h]
    · exact (g.positive p x h).le
  add_left x y z := LinearMap.BilinForm.add_left _ _ _
  smul_left x y r := by
    change pairing g p (r • x) y = r * pairing g p x y
    exact LinearMap.BilinForm.smul_left _ _ _
  definite x hx := by
    by_contra hn
    exact (ne_of_gt (g.positive p x hn)) hx

/-- An arbitrary metric orthonormal basis, used solely to express rotation. -/
def referenceBasis (g : RiemannianMetric S) (p : M) : Basis (Fin 2) ℝ (TangentSpace S p) := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  exact ((stdOrthonormalBasis ℝ (TangentSpace S p)).reindex
    (finCongr (SmoothManifolds.tangent_dimension S p).2)).toBasis

/-- Transfer the original determinant-ray orientation to the metric plane.
The sign test uses the actual wedge of the reference tangent basis. -/
def planeOrientation (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S) (p : M) :
    _root_.Orientation ℝ (TangentSpace S p) (Fin 2) :=
  let r : _root_.Orientation ℝ (TangentSpace S p) (Fin 2) :=
    (referenceBasis g p).orientation (R := ℝ) (M := TangentSpace S p)
  if SmoothManifolds.OrientationData.IsPositive (o.val p)
      (exteriorPower.ιMulti ℝ 2 (referenceBasis g p)) then r else -r

/-- Rotation by +π/2 with respect to the metric and the given orientation. -/
def rotation (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S) (p : M) :
    TangentSpace S p ≃ₗ[ℝ] TangentSpace S p := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  exact (planeOrientation g o p).rightAngleRotation.toLinearEquiv

/-- The signed area form on the same oriented metric tangent plane. -/
def orientedArea (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S) (p : M) :
    LinearMap.BilinForm ℝ (TangentSpace S p) := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  exact (planeOrientation g o p).areaForm

/-- Positive means that the interior side lies to the left of the tangent.
N points into the region, in the tangent plane of the surface. -/
def PositiveBoundaryOrientation (o : SmoothManifolds.OrientationData.Orientation S)
    (p : M) (T N : TangentSpace S p) : Prop :=
  SmoothManifolds.OrientationData.IsPositive (o.val p)
    (exteriorPower.ιMulti ℝ 2 ![T, N])

/-- The geometric inward side is specified by a defining conormal ℓ, positive
on vectors pointing into the region (a local defining function is ≥ 0 inside).
This definition does not refer to the surface orientation or to rotation. -/
def IsInwardUnitNormal (g : RiemannianMetric S) (p : M)
    (ℓ : Module.Dual ℝ (TangentSpace S p)) (N : TangentSpace S p) : Prop :=
  pairing g p N N = 1 ∧ (∀ V, ℓ V = 0 → pairing g p N V = 0) ∧ 0 < ℓ N

/-- A smooth local description of the actual region. The positive side of
its actual differential is the geometric inward side. This also allows a
half-space surface whose entire manifold is the region. -/
structure BoundarySideAt (D : Set M) (p : M) where
  neighborhood : Set M
  isOpen : IsOpen neighborhood
  contains : p ∈ neighborhood
  definingFunction : M → ℝ
  smooth : ∀ q ∈ neighborhood,
    SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      S.smoothStructure.val definingFunction q
  vanishes : definingFunction p = 0
  region : ∀ q ∈ neighborhood, q ∈ D ↔ 0 ≤ definingFunction q
  regular : scalarDerivative S definingFunction p ≠ 0

/-- Normalize the metric dual of an inward conormal. No normal or rotation
certificate is supplied as part of the construction. -/
def normalVector (g : RiemannianMetric S) (p : M)
    (ℓ : Module.Dual ℝ (TangentSpace S p)) : TangentSpace S p :=
  let v := (SmoothManifolds.MetricSplittings.metricEquiv (tangentBundle S) g p).symm ℓ
  (tangentNorm g p v)⁻¹ • v

def boundaryNormal (g : RiemannianMetric S) {D : Set M} {p : M}
    (b : BoundarySideAt (S := S) D p) : TangentSpace S p :=
  normalVector g p (scalarDerivative S b.definingFunction p)

/-- The unique Levi–Civita connection will be supplied by the proved existence
theorem when instantiating curvature. It is not an assumed certificate. -/
def signedCurvature (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S) (p : M)
    (T A : TangentSpace S p) : ℝ := pairing g p A (rotation g o p T)

/-- A is the curvature vector D_T T. The normal is inward within the surface;
no global orientation is needed for this definition. -/
def inwardCurvature (g : RiemannianMetric S) (p : M)
    (A N : TangentSpace S p) : ℝ := pairing g p A N

/-- Unit tangent obtained from the actual velocity of a regular parametrized
curve. Nonvanishing and differentiability belong to regularity, not to extra
curvature certificates. -/
def unitTangent (g : RiemannianMetric S) (c : ℝ → M)
    (V : (t : ℝ) → TangentSpace S (c t)) (t : ℝ) : TangentSpace S (c t) :=
  (tangentNorm g (c t) (V t))⁻¹ • V t

/-- D_T T = |γ'|⁻¹ D_t T, computed by the upstream intrinsic curve connection. -/
def curvatureVector (C : Connection (tangentBundle S)) (g : RiemannianMetric S)
    (c : ℝ → M) (T : (t : ℝ) → TangentSpace S (c t))
    (speed : ℝ → ℝ) (t : ℝ) : TangentSpace S (c t) :=
  (speed t)⁻¹ • P202.CurveConnectionData.covariantDerivative C c T t

def signedCurveCurvature (C : Connection (tangentBundle S)) (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ℝ → M) (T : (t : ℝ) → TangentSpace S (c t))
    (speed : ℝ → ℝ) (t : ℝ) : ℝ :=
  signedCurvature g o (c t) (T t) (curvatureVector C g c T speed t)

def inwardCurveCurvature (C : Connection (tangentBundle S)) (g : RiemannianMetric S)
    (c : ℝ → M) (T N : (t : ℝ) → TangentSpace S (c t))
    (speed : ℝ → ℝ) (t : ℝ) : ℝ :=
  inwardCurvature g (c t) (curvatureVector C g c T speed t) (N t)

/-- A compact regular arc, C¹ up to its endpoints and with C¹ unit tangent.
These are precisely the regularity requirements for D_T T; smooth boundary
arcs satisfy them. Curvature is evaluated on the open interval, and endpoints
and corners carry no separate arc-length mass. -/
structure RegularArc (g : RiemannianMetric S) where
  left : ℝ
  right : ℝ
  ordered : left < right
  curve : ℝ → M
  velocity : (t : ℝ) → TangentSpace S (curve t)
  hasVelocity : ∀ t ∈ Set.Ioo left right,
    P202.CurveData.HasVelocityAt S curve t (velocity t)
  regular : ∀ t ∈ Set.Icc left right, velocity t ≠ 0
  coordinateC1 : P202.CurveData.CoordinateC1On S curve (Set.Icc left right)
  continuous : ContinuousOn curve (Set.Icc left right)
  unitC1 : P202.CurveConnectionData.C1FieldOn (B := tangentBundle S) curve
    (unitTangent g curve velocity) (Set.Icc left right)

def RegularArc.speed {g : RiemannianMetric S} (c : RegularArc g) (t : ℝ) : ℝ :=
  tangentNorm g (c.curve t) (c.velocity t)

def RegularArc.tangent {g : RiemannianMetric S} (c : RegularArc g) (t : ℝ) :=
  unitTangent g c.curve c.velocity t

/-- The source's signed geodesic curvature on a regular oriented arc, for the
Levi–Civita connection C. A non-unit parametrization contributes the factor
|γ'|⁻¹ required by differentiation with respect to arc length. -/
def geodesicCurvature (C : Connection (tangentBundle S)) (g : RiemannianMetric S)
    (_hC : P202.LeviCivitaData.IsLeviCivita g C)
    (o : SmoothManifolds.OrientationData.Orientation S) (c : RegularArc g) (t : ℝ) : ℝ :=
  signedCurveCurvature C g o c.curve c.tangent c.speed t

/-- The same definition on an arbitrary surface, paired with its inward
normal. It requires no orientation on S. -/
def boundaryGeodesicCurvature (C : Connection (tangentBundle S)) (g : RiemannianMetric S)
    (_hC : P202.LeviCivitaData.IsLeviCivita g C)
    (c : RegularArc g) (N : (t : ℝ) → TangentSpace S (c.curve t)) (t : ℝ) : ℝ :=
  inwardCurveCurvature C g c.curve c.tangent N c.speed t

/-- Boundary curvature with the actual geometric inward normal. The local
region is described by b; its positive defining differential, rather than an
arbitrary choice of sign or a surface orientation, determines the normal. -/
def inwardBoundaryCurvature (C : Connection (tangentBundle S)) (g : RiemannianMetric S)
    (hC : P202.LeviCivitaData.IsLeviCivita g C) (c : RegularArc g)
    {D : Set M} (t : ℝ) (b : BoundarySideAt (S := S) D (c.curve t)) : ℝ :=
  inwardCurvature g (c.curve t) (curvatureVector C g c.curve c.tangent c.speed t)
    (boundaryNormal g b)

/-- Arc length integral for any scalar along a parametrized smooth arc:
∫ f ds = ∫ f(t)|γ'(t)| dt. A finite boundary is the sum of its arc integrals;
corner points carry no extra curvature integral. -/
def arcIntegral (g : RiemannianMetric S) (c : ℝ → M)
    (V : (t : ℝ) → TangentSpace S (c t)) (f : ℝ → ℝ) (l r : ℝ) : ℝ :=
  ∫ t in l..r, f t * tangentNorm g (c t) (V t)

def boundaryIntegral (g : RiemannianMetric S) {k : ℕ}
    (c : Fin k → ℝ → M) (V : (i : Fin k) → (t : ℝ) → TangentSpace S (c i t))
    (f : Fin k → ℝ → ℝ) (l r : Fin k → ℝ) : ℝ :=
  ∑ i, arcIntegral g (c i) (V i) (f i) (l i) (r i)

/-- The bounds are ordered by RegularArc; the integral is with respect to
unsigned arc length, for every smooth piece of the boundary. -/
def integralOnArc (g : RiemannianMetric S) (c : RegularArc g) (f : ℝ → ℝ) : ℝ :=
  arcIntegral g c.curve c.velocity f c.left c.right

def integralOnBoundary (g : RiemannianMetric S) {k : ℕ}
    (c : Fin k → RegularArc g) (f : Fin k → ℝ → ℝ) : ℝ :=
  ∑ i, integralOnArc g (c i) (f i)

/-- The unsigned metric density, also on a nonorientable surface. -/
abbrev areaDensity (g : RiemannianMetric S) := P202.VolumeData.density g

/-- Noncuspidal corners include convex, straight, and reflex vertices. -/
structure Corner where
  interiorAngle : ℝ
  positive : 0 < interiorAngle
  less_two_pi : interiorAngle < 2 * Real.pi

def exteriorAngle (c : Corner) : ℝ := Real.pi - c.interiorAngle
end P202.SurfaceBoundaryData

namespace P202Specs.Geometry.SurfaceBoundaryGeometry
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
open Module
open P202.MetricData P202.SurfaceBoundaryData
universe u

def rotationType := {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold 2 a M} → RiemannianMetric S → SmoothManifolds.OrientationData.Orientation S →
  (p : M) → TangentSpace S p ≃ₗ[ℝ] TangentSpace S p

def rotationValue : rotationType := @P202.SurfaceBoundaryData.rotation

def positiveBoundaryType := {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold 2 a M} → SmoothManifolds.OrientationData.Orientation S →
  (p : M) → TangentSpace S p → TangentSpace S p → Prop

def positiveBoundaryValue : positiveBoundaryType := @P202.SurfaceBoundaryData.PositiveBoundaryOrientation

def inwardNormalType := {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold 2 a M} → RiemannianMetric S → (p : M) →
  Module.Dual ℝ (TangentSpace S p) → TangentSpace S p → Prop

def inwardNormalValue : inwardNormalType := @P202.SurfaceBoundaryData.IsInwardUnitNormal

def regularArcType := {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold 2 a M} → RiemannianMetric S → Type u

def regularArcValue : regularArcType := @P202.SurfaceBoundaryData.RegularArc

def signedCurvatureType := {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold 2 a M} →
  (C : P202.ConnectionData.Connection (P202.ConnectionData.tangentBundle S)) →
  (g : RiemannianMetric S) → P202.LeviCivitaData.IsLeviCivita g C →
  SmoothManifolds.OrientationData.Orientation S → RegularArc g → ℝ → ℝ

def signedCurvatureValue : signedCurvatureType := @P202.SurfaceBoundaryData.geodesicCurvature

def inwardCurvatureType := {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold 2 a M} →
  (C : P202.ConnectionData.Connection (P202.ConnectionData.tangentBundle S)) →
  (g : RiemannianMetric S) → P202.LeviCivitaData.IsLeviCivita g C → (c : RegularArc g) →
  ((t : ℝ) → TangentSpace S (c.curve t)) → ℝ → ℝ

def inwardCurvatureValue : inwardCurvatureType := @P202.SurfaceBoundaryData.boundaryGeodesicCurvature

def geometricBoundaryCurvatureType := {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold 2 a M} →
  (C : P202.ConnectionData.Connection (P202.ConnectionData.tangentBundle S)) →
  (g : RiemannianMetric S) → P202.LeviCivitaData.IsLeviCivita g C → (c : RegularArc g) →
  {D : Set M} → (t : ℝ) → BoundarySideAt (S := S) D (c.curve t) → ℝ

def geometricBoundaryCurvatureValue : geometricBoundaryCurvatureType :=
  @P202.SurfaceBoundaryData.inwardBoundaryCurvature

def arcIntegralType := {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold 2 a M} → (g : RiemannianMetric S) → RegularArc g → (ℝ → ℝ) → ℝ

def arcIntegralValue : arcIntegralType := @P202.SurfaceBoundaryData.integralOnArc

def boundaryIntegralType := {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold 2 a M} → (g : RiemannianMetric S) → {k : ℕ} →
  (Fin k → RegularArc g) → (Fin k → ℝ → ℝ) → ℝ

def boundaryIntegralValue : boundaryIntegralType := @P202.SurfaceBoundaryData.integralOnBoundary

def areaDensityType := {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold 2 a M} → RiemannianMetric S → SmoothManifolds.MetricVolumeData.DensityField S

def areaDensityValue : areaDensityType := @P202.SurfaceBoundaryData.areaDensity

def cornerType := Type

def cornerValue : cornerType := @P202.SurfaceBoundaryData.Corner

def exteriorAngleType := Corner → ℝ

def exteriorAngleValue : exteriorAngleType := @P202.SurfaceBoundaryData.exteriorAngle


def normalVectorType := {a : ModelKind} → {M : Type u} → [TopologicalSpace M] →
  {S : SmoothManifold 2 a M} → RiemannianMetric S → (p : M) →
  Module.Dual ℝ (TangentSpace S p) → TangentSpace S p

def normalVectorValue : normalVectorType := @P202.SurfaceBoundaryData.normalVector

def normalVector_inwardType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S) (p : M)
    (ℓ : Module.Dual ℝ (TangentSpace S p)), ℓ ≠ 0 →
    IsInwardUnitNormal g p ℓ (normalVector g p ℓ)

def boundary_rotationType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S) {D : Set M} {p : M}
    (b : BoundarySideAt (S := S) D p) (T : TangentSpace S p),
    P202.ConnectionData.scalarDerivative S b.definingFunction p T = 0 →
    pairing g p T T = 1 → PositiveBoundaryOrientation o p T (boundaryNormal g b) →
    rotation g o p T = boundaryNormal g b ∧
      IsInwardUnitNormal g p (P202.ConnectionData.scalarDerivative S b.definingFunction p)
        (rotation g o p T)

def rotation_propertiesType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S) (p : M)
    (X Y : TangentSpace S p),
    rotation g o p (rotation g o p X) = -X ∧
      pairing g p (rotation g o p X) (rotation g o p Y) = pairing g p X Y ∧
      pairing g p (rotation g o p X) X = 0

def rotation_positiveType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S) (p : M)
    (T : TangentSpace S p), T ≠ 0 → PositiveBoundaryOrientation o p T (rotation g o p T)

def inward_rotationType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S) (p : M)
    (ℓ : Module.Dual ℝ (TangentSpace S p)) (T N : TangentSpace S p),
    IsInwardUnitNormal g p ℓ N → ℓ T = 0 → pairing g p T T = 1 →
    PositiveBoundaryOrientation o p T N → rotation g o p T = N

def unitTangent_unitType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S) (c : RegularArc g)
    (t : ℝ), t ∈ Set.Ioo c.left c.right →
    pairing g (c.curve t) (c.tangent t) (c.tangent t) = 1 ∧ 0 < c.speed t

def regularArc_derivativeType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    (C : P202.ConnectionData.Connection (P202.ConnectionData.tangentBundle S))
    (c : RegularArc g) (t : ℝ), t ∈ Set.Ioo c.left c.right →
    ∃ D, P202.CurveConnectionData.HasCovariantDerivativeAt C c.curve c.tangent t D

def curvature_reversalType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (C : P202.ConnectionData.Connection
      (P202.ConnectionData.tangentBundle S)) (g : RiemannianMetric S)
    (c : ℝ → M) (T N : (t : ℝ) → TangentSpace S (c t)) (speed : ℝ → ℝ)
    (s : ℝ) (D : TangentSpace S (c (-s))),
    P202.CurveConnectionData.HasCovariantDerivativeAt C c T (-s) D →
    inwardCurveCurvature C g (c ∘ Neg.neg) (fun t => -T (-t))
      (fun t => N (-t)) (fun t => speed (-t)) s =
      inwardCurveCurvature C g c T N speed (-s)

/-- Full specialization to the actual reversed velocity of a regular arc.
No covariant-derivative existence assumption is added to regularity. -/
def regularArc_curvature_reversalType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M}
    (C : P202.ConnectionData.Connection (P202.ConnectionData.tangentBundle S))
    (g : RiemannianMetric S) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (c : RegularArc g) (N : (t : ℝ) → TangentSpace S (c.curve t)) (s : ℝ),
    -s ∈ Set.Ioo c.left c.right →
    P202.CurveData.HasVelocityAt S (c.curve ∘ Neg.neg) s (-c.velocity (-s)) ∧
    inwardCurveCurvature C g (c.curve ∘ Neg.neg)
      (unitTangent g (c.curve ∘ Neg.neg) (fun t => -c.velocity (-t)))
      (fun t => N (-t))
      (fun t => tangentNorm g (c.curve (-t)) (-c.velocity (-t))) s =
        boundaryGeodesicCurvature C g hC c N (-s)

/-- The canonical boundary curvature uses a provably inward unit normal. -/
def geometricBoundary_normalType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    {D : Set M} {p : M} (b : BoundarySideAt (S := S) D p),
    IsInwardUnitNormal g p (P202.ConnectionData.scalarDerivative S b.definingFunction p)
      (boundaryNormal g b)

/-- Independence of either tangent direction, for the actual inward normal of
an actual region. The reversed velocity and unit tangent are computed directly. -/
def geometricBoundary_reversalType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M}
    (C : P202.ConnectionData.Connection (P202.ConnectionData.tangentBundle S))
    (g : RiemannianMetric S) (hC : P202.LeviCivitaData.IsLeviCivita g C)
    (c : RegularArc g) {D : Set M} (s : ℝ)
    (b : BoundarySideAt (S := S) D (c.curve (-s))),
    -s ∈ Set.Ioo c.left c.right →
    pairing g (c.curve (-s))
      (curvatureVector C g (c.curve ∘ Neg.neg)
        (unitTangent g (c.curve ∘ Neg.neg) (fun t => -c.velocity (-t)))
        (fun t => tangentNorm g (c.curve (-t)) (-c.velocity (-t))) s)
      (boundaryNormal g b) = inwardBoundaryCurvature C g hC c (-s) b

def signed_inwardType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S)
    (o : SmoothManifolds.OrientationData.Orientation S) (p : M)
    (ℓ : Module.Dual ℝ (TangentSpace S p)) (T N A : TangentSpace S p),
    IsInwardUnitNormal g p ℓ N → ℓ T = 0 → pairing g p T T = 1 →
    PositiveBoundaryOrientation o p T N → signedCurvature g o p T A = inwardCurvature g p A N

def area_compatibleType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 a M} (g : RiemannianMetric S),
    SmoothManifolds.MetricVolumeData.IsMetricDensity (P202.VolumeData.libraryMetric g)
      (areaDensity g) ∧ SmoothManifolds.MetricVolumeData.IsSmoothDensity (areaDensity g) ∧
    ∀ o : SmoothManifolds.OrientationData.Orientation S,
      SmoothManifolds.DensityIntegrationData.absoluteTopForm (P202.VolumeData.volumeForm g o).field =
        areaDensity g

def cornersType : Prop :=
  (∀ c : Corner, -Real.pi < exteriorAngle c ∧ exteriorAngle c < Real.pi) ∧
  (∀ c : Corner, Real.pi < c.interiorAngle → exteriorAngle c < 0) ∧
  (∀ c : Corner, c.interiorAngle = Real.pi → exteriorAngle c = 0)
end P202Specs.Geometry.SurfaceBoundaryGeometry
