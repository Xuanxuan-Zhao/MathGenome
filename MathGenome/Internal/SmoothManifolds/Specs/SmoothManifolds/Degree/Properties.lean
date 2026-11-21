import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Degree.RegularFibers
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.HomotopyInvariance
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.Stokes
import Mathlib.Topology.Connected.LocallyConnected

/-! M12.02, paper.tex:2668–2694. Degrees below are the same integers
characterized by M12.01, with the original integral and regular-fiber formulas.
`ConnectedSpace` includes nonemptiness. All statements include dimension zero.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SmoothManifolds.DegreeComponentData
open ModelData AtlasData MapData TangentData DifferentialData OrientationData OrientationProductData
universe u

/-- The actual nonempty connected component indexed by the quotient. -/
abbrev componentSet {M : Type u} [TopologicalSpace M] (c : ConnectedComponents M) : Set M :=
  QuotientData.componentSet c

/-- The inherited smooth structure and orientation on an actual component.
Every compatibility field is a construction obligation in `component_geometry`;
no component geometry or integration identity is assumed by the boundary theorem. -/
structure Geometry {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (q : Orientation S)
    (c : ConnectedComponents M) where
  isOpen : IsOpen (componentSet c)
  manifold : SmoothManifold n .euclidean (componentSet c)
  atlas_eq : manifold.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
    (openSubsetAtlas S.smoothStructure.val (componentSet c) isOpen)
  inclusion_smooth : IsSmoothMap manifold S Subtype.val
  tangentEquiv : ∀ p : componentSet c,
    TangentSpace manifold p ≃ₗ[ℝ] TangentSpace S p.val
  tangent_differential : ∀ p,
    IsDifferential manifold S Subtype.val p (tangentEquiv p).toLinearMap
  orientation : Orientation manifold
  orientation_preserving : ∀ p,
    Module.Ray.map (determinantMap n (tangentEquiv p)) (orientation.val p) = q.val p.val

end SmoothManifolds.DegreeComponentData

namespace Specs.SmoothManifolds.Degree.Properties
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.CovectorData _root_.SmoothManifolds.BundleOperationsData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.FormPullbackData
  _root_.SmoothManifolds.OrientationData _root_.SmoothManifolds.LocalIntegrationData
  _root_.SmoothManifolds.GlobalIntegrationData _root_.SmoothManifolds.BoundaryData
  _root_.SmoothManifolds.BoundaryOrientationData
  _root_.SmoothManifolds.DegreeData _root_.SmoothManifolds.InteriorHomotopyData
universe u
open _root_.SmoothManifolds.DegreeComponentData

/-- The homotopy is continuous, and only its two endpoints must be smooth. -/
def homotopy_invarianceType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    [ConnectedSpace M] [ConnectedSpace N] [CompactSpace M] [CompactSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f g : M → N),
    IsSmoothMap S T f → IsSmoothMap S T g →
    intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ →
    (∃ H : HomotopyTime × M → N, Continuous H ∧
      (∀ p, H (timeZero, p) = f p) ∧ (∀ p, H (timeOne, p) = g p)) →
    ∀ (o : Orientation S) (q : Orientation T)
      (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ),
      IsIntegral o I → IsIntegral q J → ∀ d e : ℤ,
      HasDegree S T f o q I J d → HasDegree S T g o q I J e → d = e

def identityType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [ConnectedSpace M] [CompactSpace M]
    (S : SmoothManifold n a M), intrinsicBoundary S = ∅ →
    ∀ (o : Orientation S) (I : CompactTopForm S → ℝ),
      IsIntegral o I → HasDegree S S id o o I I 1

/-- The order is deg(g ∘ f) = deg(g) deg(f), with the same middle orientation. -/
def compositionType : Prop :=
  ∀ {n : ℕ} {a b c : ModelKind} {M N P : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    [ConnectedSpace M] [ConnectedSpace N] [ConnectedSpace P]
    [CompactSpace M] [CompactSpace N] [CompactSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N)
    (U : SmoothManifold n c P) (f : M → N) (g : N → P),
    IsSmoothMap S T f → IsSmoothMap T U g →
    intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ → intrinsicBoundary U = ∅ →
    ∀ (o : Orientation S) (q : Orientation T) (r : Orientation U)
      (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ)
      (K : CompactTopForm U → ℝ),
      IsIntegral o I → IsIntegral q J → IsIntegral r K → ∀ d e : ℤ,
      HasDegree S T f o q I J d → HasDegree T U g q r J K e →
      HasDegree S U (g ∘ f) o r I K (e * d)

/-- The nonempty connected components, with none in the empty-boundary case. -/
def finite_boundary_componentsType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {W : Type u}
    [TopologicalSpace W] [CompactSpace W]
    (S : SmoothManifold (n+1) a W)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)),
    Finite (ConnectedComponents (intrinsicBoundary S))

/-- Stokes annihilates the full boundary pullback, without a connectedness
assumption on W or its boundary. The displayed field is the actual restriction
of G*ω, so the statement also applies when the boundary is empty. -/
def boundary_pullback_integral_zeroType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {W N : Type u}
    [TopologicalSpace W] [TopologicalSpace N] [CompactSpace W]
    (S : SmoothManifold (n+1) a W) (T : SmoothManifold n b N)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S)),
    IsNaturalBoundary S B → ∀ (o : Orientation S) (q : Orientation B),
    IsInducedOrientation o q → ∀ G : W → N, IsSmoothMap S T G →
    ∀ (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (G p))
      (R : ∀ p : intrinsicBoundary S, TangentSpace B p →ₗ[ℝ] TangentSpace S p.val),
      (∀ p, IsDifferential S T G p (L p)) →
      (∀ p, IsDifferential B S Subtype.val p (R p)) →
      ∀ (A : CotangentBundle T) (E : FormBundle A n) (ω : Form E)
        (J : CompactTopForm B → ℝ), IsIntegral q J →
        ∃ β : CompactTopForm B,
          β.field = pullbackField B S Subtype.val R (pullbackField S T G L ω.field) ∧
          J β = 0

/-- In particular the geometry of the components is supplied, rather than
required as a certificate from the user of the degree-sum theorem. -/
def component_geometryType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (B : SmoothManifold n .euclidean M) (q : Orientation B)
    (c : ConnectedComponents M), Nonempty (Geometry B q c)

/-- All degree hypotheses for the actual nonempty components. -/
def component_degree_hypothesesType : Prop :=
  ∀ {n m : ℕ} {b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [CompactSpace M]
    (B : SmoothManifold n .euclidean M) (T : SmoothManifold m b N)
    (q : Orientation B) (D : ∀ c : ConnectedComponents M, Geometry B q c)
    (f : M → N), IsSmoothMap B T f → ∀ c : ConnectedComponents M,
      ConnectedSpace (componentSet c) ∧ CompactSpace (componentSet c) ∧
      intrinsicBoundary (D c).manifold = ∅ ∧
      IsSmoothMap (D c).manifold T (fun p => f p.val)

/-- The full boundary-extension conclusion. The component structures and their
orientations are constructed with the inherited maximal atlas and actual
orientation-preserving inclusion differentials. Each degree is the integer
from M12.01, with both its integral and signed-regular-fiber characterizations.
The separately proved finiteness makes the displayed `finsum` the ordinary
finite sum, also for the empty boundary and for dimension zero. -/
def boundary_degree_sumType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {W N : Type u}
    [TopologicalSpace W] [TopologicalSpace N] [CompactSpace W]
    [ConnectedSpace N] [CompactSpace N]
    (S : SmoothManifold (n+1) a W) (T : SmoothManifold n b N),
    intrinsicBoundary T = ∅ →
    ∀ (B : SmoothManifold n .euclidean (intrinsicBoundary S)),
    IsNaturalBoundary S B → ∀ (o : Orientation S) (q : Orientation B),
    IsInducedOrientation o q → ∀ (r : Orientation T)
      (J : CompactTopForm T → ℝ), IsIntegral r J →
    ∀ G : W → N, IsSmoothMap S T G →
    ∃ (D : ∀ c : ConnectedComponents (intrinsicBoundary S), Geometry B q c)
      (I : ∀ c, CompactTopForm (D c).manifold → ℝ)
      (d : ConnectedComponents (intrinsicBoundary S) → ℤ),
      (∀ c, ConnectedSpace (componentSet c) ∧ CompactSpace (componentSet c) ∧
        intrinsicBoundary (D c).manifold = ∅ ∧
        IsSmoothMap (D c).manifold T (fun p => G p.val.val) ∧
        IsIntegral (D c).orientation (I c) ∧
        HasDegree (D c).manifold T (fun p => G p.val.val)
          (D c).orientation r (I c) J (d c)) ∧
      (∑ᶠ c, d c) = 0

/-- The boundary extension theorem directly from the original data, constructing
the natural boundary, its outward-first orientation, and all component degrees. -/
def boundary_extensionType : Prop :=
  ∀ {n : ℕ} {a b : ModelKind} {W N : Type u}
    [TopologicalSpace W] [TopologicalSpace N] [CompactSpace W]
    [ConnectedSpace N] [CompactSpace N]
    (S : SmoothManifold (n+1) a W) (T : SmoothManifold n b N),
    intrinsicBoundary T = ∅ → ∀ (o : Orientation S) (r : Orientation T)
      (G : W → N), IsSmoothMap S T G →
    Finite (ConnectedComponents (intrinsicBoundary S)) ∧
    ∃ B : SmoothManifold n .euclidean (intrinsicBoundary S),
      IsNaturalBoundary S B ∧ ∃ q : Orientation B,
      IsInducedOrientation o q ∧ ∃ J : CompactTopForm T → ℝ,
      IsIntegral r J ∧
      ∃ (D : ∀ c : ConnectedComponents (intrinsicBoundary S), Geometry B q c)
        (I : ∀ c, CompactTopForm (D c).manifold → ℝ)
        (d : ConnectedComponents (intrinsicBoundary S) → ℤ),
        (∀ c, ConnectedSpace (componentSet c) ∧ CompactSpace (componentSet c) ∧
          intrinsicBoundary (D c).manifold = ∅ ∧
          IsSmoothMap (D c).manifold T (fun p => G p.val.val) ∧
          IsIntegral (D c).orientation (I c) ∧
          HasDegree (D c).manifold T (fun p => G p.val.val)
            (D c).orientation r (I c) J (d c)) ∧
        (∑ᶠ c, d c) = 0

end Specs.SmoothManifolds.Degree.Properties
