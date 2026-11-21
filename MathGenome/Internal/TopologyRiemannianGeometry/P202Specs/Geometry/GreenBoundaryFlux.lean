import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ScalarCalculus
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.Global
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Boundary
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.Cartan

/-! Independent boundary and integral representation obligations for Theorem 6.7.
Canonical Green data are shared with the eventual divergence theorem.
Source: paper.tex 3246–3294.
Integrals are the fixed intrinsic compact-density integral. An identity includes
compact continuous representatives of its integrands, rather than silently
assigning a value to an integral of an unverified integrand. No orientation is
required for the density statements. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology CompactlySupported

namespace P202.GreenData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.BoundaryData
  SmoothManifolds.BoundaryRegularLevelData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData
universe u

/-- Strict geometric outwardness. Dimension zero has no outward vector;
its intrinsic boundary is empty. In positive dimension this is the existing
coordinate-independent strict outward cone, not an arbitrary normal ray. -/
def Outward {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) :
    (p : intrinsicBoundary S) → TangentSpace S p.val → Prop :=
  match n, S with
  | 0, _ => fun _ _ => False
  | _ + 1, T => SmoothManifolds.BoundaryOrientationData.IsOutward T

/-- The natural boundary, its induced metric, and the actual outward unit
normal, defined only at boundary points. Empty boundaries require no chosen
ambient vector. Smoothness of the normal is a local smooth extension condition. -/
structure BoundaryGeometry {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) where
  manifold : SmoothManifold (n - 1) .euclidean (intrinsicBoundary S)
  natural : IsNaturalBoundaryStructure S manifold
  metric : RiemannianMetric manifold
  induced : ∀ p v w, pairing metric p v w = pairing g p.val
    (SmoothManifolds.differential manifold S Subtype.val natural.1 p v)
    (SmoothManifolds.differential manifold S Subtype.val natural.1 p w)
  normal : (p : intrinsicBoundary S) → TangentSpace S p.val
  unit : ∀ p, pairing g p.val (normal p) (normal p) = 1
  orthogonal : ∀ p v, pairing g p.val (normal p)
    (SmoothManifolds.differential manifold S Subtype.val natural.1 p v) = 0
  outward : ∀ p, Outward S p (normal p)
  normal_smooth : ∀ p : intrinsicBoundary S, ∃ (U : Set M) (_hU : IsOpen U), p.val ∈ U ∧
    ∃ X : Field S, ∀ q : intrinsicBoundary S, q.val ∈ U → X.val q.val = normal q

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

def flux (g : RiemannianMetric S) (b : BoundaryGeometry g) (X : Field S)
    (p : intrinsicBoundary S) : ℝ := pairing g p.val (X.val p.val) (b.normal p)

def firstIntegrand (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (u v : GlobalSmooth S) (p : M) : ℝ :=
  pairing g p ((gradient g u).val p) ((gradient g v).val p) +
    v.val p * laplacian g C u p

def secondIntegrand (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (u v : GlobalSmooth S) (p : M) : ℝ :=
  v.val p * laplacian g C u p - u.val p * laplacian g C v p

/-- The integral notation, with both integrands represented in the original
compact-density integration domain. -/
def IntegralIdentity {m : ℕ} {k : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m k N} (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f : M → ℝ) (q : N → ℝ) : Prop :=
  ∃ (F : C_c(M, ℝ)) (Q : C_c(N, ℝ)),
    (∀ p, F p = f p) ∧ (∀ p, Q p = q p) ∧
      P202.VolumeData.integral g F = P202.VolumeData.integral h Q

def IntegralZero (g : RiemannianMetric S) (f : M → ℝ) : Prop :=
  ∃ F : C_c(M, ℝ), (∀ p, F p = f p) ∧ P202.VolumeData.integral g F = 0

/-- Compact support concerns the field integrated. Neither factor of a product
field is individually required to have compact support. -/
def DivergenceIdentity (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (b : BoundaryGeometry g) : Prop :=
  ∀ X : Field S, IsCompact (sectionSupport X.val) →
    IntegralIdentity g b.metric (divergence C X) (flux g b X)

end P202.GreenData

namespace P202Specs.Geometry.GreenBoundaryFlux
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BoundaryData SmoothManifolds.BoundaryRegularLevelData
  SmoothManifolds.OrientationData SmoothManifolds.BoundaryOrientationData
  SmoothManifolds.LocalIntegrationData SmoothManifolds.GlobalIntegrationData
  P202.MetricData P202.ConnectionData P202.ScalarData P202.GreenData
universe u

def boundary_geometry_existsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S), Nonempty (BoundaryGeometry g)

/-- The orientation is outward-first. The contraction is the actual first-slot
Cartan contraction and the pullback uses the actual inclusion differential. -/
def boundary_fluxType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) a M} (g : RiemannianMetric S)
    (b : BoundaryGeometry g) (o : Orientation S),
    ∃ q : Orientation b.manifold, IsInducedOrientation o q ∧
      ∀ X : Field S,
      SmoothManifolds.FormPullbackData.pullbackField b.manifold S Subtype.val
        (SmoothManifolds.differential b.manifold S Subtype.val b.natural.1)
        (SmoothManifolds.CartanData.contraction (P202.VolumeData.cotangentBundle S)
          X.val (n+1) (P202.VolumeData.volumeForm g o).field) =
        (fun p => flux g b X p • (P202.VolumeData.volumeForm b.metric q).field p)

/-- Signed scalar functions, including at true boundary points and in dimension
zero. Compatible oriented integrals are identified with the fixed density
integral, not merely with the absolute value of a top form. -/
def metric_integral_bridgeType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (o : Orientation S)
    (f : C_c(M, ℝ)), ∃ η : CompactTopForm S,
      η.field = (fun p => f p • (P202.VolumeData.volumeForm g o).field p) ∧
      ∀ I : CompactTopForm S → ℝ, IsIntegral o I → I η = P202.VolumeData.integral g f

def boundary_geometry_of_emptyType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S),
    intrinsicBoundary S = ∅ → Nonempty (BoundaryGeometry g)

def boundary_geometry_zero_dimensionType : Prop :=
  ∀ {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (g : RiemannianMetric S), Nonempty (BoundaryGeometry g)

def unit_normal_of_covectorType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (g : RiemannianMetric S) (p : M)
    (φ : Module.Dual ℝ (TangentSpace S p)), φ ≠ 0 →
    ∃ ν : TangentSpace S p, pairing g p ν ν = 1 ∧ φ ν < 0 ∧
      ∀ z, φ z = 0 → pairing g p ν z = 0

/-- A genuine pointwise geometric normal, without asserting smoothness. -/
def boundary_normal_pointwiseType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) a M} (g : RiemannianMetric S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundaryStructure S B) (p : intrinsicBoundary S),
    ∃ ν : TangentSpace S p.val, pairing g p.val ν ν = 1 ∧
      (∀ v, pairing g p.val ν
        (SmoothManifolds.differential B S Subtype.val hB.1 p v) = 0) ∧
      Outward S p ν

def boundary_normal_uniqueType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold (n+1) a M} (g : RiemannianMetric S)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundaryStructure S B) (p : intrinsicBoundary S)
    (ν μ : TangentSpace S p.val),
    pairing g p.val ν ν = 1 → pairing g p.val μ μ = 1 →
    (∀ v, pairing g p.val ν
      (SmoothManifolds.differential B S Subtype.val hB.1 p v) = 0) →
    (∀ v, pairing g p.val μ
      (SmoothManifolds.differential B S Subtype.val hB.1 p v) = 0) →
    Outward S p ν → Outward S p μ → ν = μ

end P202Specs.Geometry.GreenBoundaryFlux
