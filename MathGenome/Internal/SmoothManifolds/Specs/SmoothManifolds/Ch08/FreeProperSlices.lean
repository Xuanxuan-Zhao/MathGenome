import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Products
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Tangent.Differential
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.IsLocalHomeomorph

/-! Independent data for the free proper action slice construction.

Properness below is exactly compactness of inverse images, as in the source.
No slice, quotient, immersion, or differential injectivity is part of the input.
-/
namespace SmoothManifolds.FreeProperSliceData
open ModelData AtlasData MapData ProductData BoundaryData MapClassData
open Set
universe u v

/-- The map used in the manuscript's definition of properness, in its stated order. -/
def actionTransport {G : Type u} {M : Type v} [SMul G M] (z : G × M) : M × M :=
  (z.2, z.1 • z.2)

/-- The union of all translates of a subset. -/
def saturation {G : Type u} {M : Type v} [SMul G M] (s : Set M) : Set M :=
  {y | ∃ (g : G) (x : M), x ∈ s ∧ g • x = y}

/-- Triviality of every point stabilizer. -/
def FreeAction (G : Type u) (M : Type v) [Group G] [MulAction G M] : Prop :=
  ∀ (g : G) (x : M), g • x = x → g = 1

/-- A product smooth structure represented using Euclidean atlases on the two
boundaryless factors. The identity maps record their compatibility with the
original structures, which may use either uniform model. This is ordinary
product data, not an assumed slice or trivialization. -/
structure BoundarylessProduct {d n : ℕ} {a b : ModelKind}
    {G : Type u} {M : Type v} [TopologicalSpace G] [TopologicalSpace M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M) where
  left : SmoothManifold d .euclidean G
  right : SmoothManifold n .euclidean M
  left_to : IsSmoothMap A left id
  left_from : IsSmoothMap left A id
  right_to : IsSmoothMap B right id
  right_from : IsSmoothMap right B id
  coordinates : ProductCoordinates d .euclidean n .euclidean .euclidean
  manifold : SmoothManifold (d + n) .euclidean (G × M)
  atlas_eq : manifold.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
    (productAtlas coordinates left.smoothStructure.val right.smoothStructure.val)

/-- A finite dimensional Lie group and its smooth action, stated entirely in
terms of the shared chart-based smoothness. The selected product atlases are
ordinary product structures; their existence is an upstream theorem. -/
structure SmoothLieAction {d n : ℕ} {a b : ModelKind}
    {G M : Type u} [TopologicalSpace G] [TopologicalSpace M]
    [Group G] [MulAction G M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M) where
  group_boundary : intrinsicBoundary A = ∅
  space_boundary : intrinsicBoundary B = ∅
  groupProduct : BoundarylessProduct A A
  actionProduct : BoundarylessProduct A B
  smooth_mul : IsSmoothMap groupProduct.manifold A (fun z => z.1 * z.2)
  smooth_inv : IsSmoothMap A A (fun g => g⁻¹)
  smooth_action : IsSmoothMap actionProduct.manifold B (fun z => z.1 • z.2)

/-- Local transverse product data used in the construction. Its existence is
an obligation, not part of `SmoothLieAction` or of the parent hypotheses. -/
structure LocalProductSlice {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M) (p : M) where
  carrier : Set M
  contains : p ∈ carrier
  slice : SmoothManifold (n - d) .euclidean carrier
  embedding : IsSmoothEmbedding slice B Subtype.val
  product : BoundarylessProduct A slice
  identityNeighborhood : Set G
  neighborhood_open : IsOpen identityNeighborhood
  one_mem : (1 : G) ∈ identityNeighborhood
  chart : OpenPartialHomeomorph (G × carrier) M
  chart_source : chart.source = identityNeighborhood ×ˢ univ
  chart_action : EqOn chart (fun z : G × carrier => z.1 • z.2.val) chart.source
  smooth_inverse : ManifoldContDiffOn (⊤ : ℕ∞) B.smoothStructure.val
    product.manifold.smoothStructure.val chart.symm chart.target

/-- Full requested geometric conclusion at p, including the actual action map
and the subspace topologies on the slice and its saturation. -/
structure GlobalSlice {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    (A : SmoothManifold d a G) (B : SmoothManifold n b M) (p : M) where
  carrier : Set M
  contains : p ∈ carrier
  slice : SmoothManifold (n - d) .euclidean carrier
  boundary_empty : intrinsicBoundary slice = ∅
  embedding : IsSmoothEmbedding slice B Subtype.val
  saturated_open : IsOpen (saturation (G := G) carrier)
  product : BoundarylessProduct A slice
  neighborhood : SmoothManifold n b (saturation (G := G) carrier)
  neighborhood_atlas : neighborhood.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
    (openSubsetAtlas B.smoothStructure.val (saturation (G := G) carrier) saturated_open)
  trivialization : Diffeomorph product.manifold.smoothStructure.val
    neighborhood.smoothStructure.val
  action_eq : ∀ z : G × carrier,
    (trivialization.toEquiv z).val = z.1 • z.2.val
  orbit_unique : ∀ y ∈ saturation (G := G) carrier,
    ∃! s : carrier, ∃ g : G, g • s.val = y

end SmoothManifolds.FreeProperSliceData

namespace Specs.SmoothManifolds.Ch08.FreeProperSlices
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.FreeProperSliceData _root_.SmoothManifolds.MapClassData
open Set
universe u v

/-- The complete parent obligation. Differential injectivity quantifies over
all maps satisfying the intrinsic germ-derivation differential interface. -/
def free_proper_slicesType : Prop :=
  ∀ {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    [Nonempty M] (A : SmoothManifold d a G) (B : SmoothManifold n b M),
    SmoothLieAction A B → FreeAction G M → IsProper (actionTransport (G := G) (M := M)) →
    (∀ p : M, ∃ L : TangentSpace A (1 : G) →ₗ[ℝ]
      TangentSpace B ((1 : G) • p),
      IsDifferential A B (fun g : G => g • p) 1 L ∧ Function.Injective L ∧
      ∀ K : TangentSpace A (1 : G) →ₗ[ℝ] TangentSpace B ((1 : G) • p),
        IsDifferential A B (fun g : G => g • p) 1 K → K = L) ∧
    d ≤ n ∧ ∀ p : M, Nonempty (GlobalSlice A B p)

/-- The infinitesimal part of the parent result, with no properness hypothesis:
freeness alone gives the unique injective orbit differential and d ≤ n. -/
def orbit_differential_injectiveType : Prop :=
  ∀ {d n : ℕ} {a b : ModelKind} {G M : Type u}
    [TopologicalSpace G] [TopologicalSpace M] [Group G] [MulAction G M]
    [Nonempty M] (A : SmoothManifold d a G) (B : SmoothManifold n b M),
    SmoothLieAction A B → FreeAction G M →
    (∀ p : M, ∃ L : TangentSpace A (1 : G) →ₗ[ℝ]
      TangentSpace B ((1 : G) • p),
      IsDifferential A B (fun g : G => g • p) 1 L ∧ Function.Injective L ∧
      ∀ K : TangentSpace A (1 : G) →ₗ[ℝ] TangentSpace B ((1 : G) • p),
        IsDifferential A B (fun g : G => g • p) 1 K → K = L) ∧ d ≤ n

/-- The properness shrinking step, independent of differentiability. -/
def small_transportersType : Prop :=
  ∀ {G : Type u} {M : Type v} [TopologicalSpace G] [TopologicalSpace M]
    [Group G] [MulAction G M] [T2Space M] [LocallyCompactSpace M],
    Continuous (fun z : G × M => z.1 • z.2) → FreeAction G M →
    IsProper (actionTransport (G := G) (M := M)) →
    ∀ (p : M) (W : Set G), IsOpen W → (1 : G) ∈ W →
      ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
        ∀ (g : G) (x y : M), x ∈ U → y ∈ U → g • x = y → g ∈ W

/-- The set-theoretic shrinking and uniqueness step after a local product
chart has been obtained. It gives the global product bijection as well. -/
def shrink_sliceType : Prop :=
  ∀ {G : Type u} {M : Type v} [TopologicalSpace G] [TopologicalSpace M]
    [Group G] [MulAction G M] [T2Space M] [LocallyCompactSpace M],
    Continuous (fun z : G × M => z.1 • z.2) → FreeAction G M →
    IsProper (actionTransport (G := G) (M := M)) →
    ∀ (p : M) (W : Set G) (s₁ : Set M), IsOpen W → (1 : G) ∈ W → p ∈ s₁ →
    Set.InjOn (fun z : G × M => z.1 • z.2) (W ×ˢ s₁) →
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      let s := s₁ ∩ U
      p ∈ s ∧
      (∀ (g : G) (x y : M), x ∈ s → y ∈ s → g • x = y → g = 1 ∧ x = y) ∧
      Function.Bijective (fun z : G × s =>
        (⟨z.1 • z.2.val, ⟨z.1, z.2.val, z.2.property, rfl⟩⟩ : saturation (G := G) s)) ∧
      ∀ y ∈ saturation (G := G) s, ∃! x : s, ∃ g : G, g • x.val = y

/-- The full topological globalization of a local product chart. The remaining
geometric work is construction of that chart and smoothness of the inverse. -/
def topological_trivializationType : Prop :=
  ∀ {G : Type u} {M : Type v} [TopologicalSpace G] [TopologicalSpace M]
    [Group G] [MulAction G M] [SeparatelyContinuousMul G] [ContinuousConstSMul G M]
    [T2Space M] [LocallyCompactSpace M],
    Continuous (fun z : G × M => z.1 • z.2) → FreeAction G M →
    IsProper (actionTransport (G := G) (M := M)) →
    ∀ (p : M) (W : Set G) (s₁ : Set M), IsOpen W → (1 : G) ∈ W → p ∈ s₁ →
    ∀ h : OpenPartialHomeomorph (G × s₁) M,
      h.source = W ×ˢ univ →
      EqOn h (fun z : G × s₁ => z.1 • z.2.val) h.source →
      ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
        let s := s₁ ∩ U
        p ∈ s ∧ IsOpen (saturation (G := G) s) ∧
        (∃ H : (G × s) ≃ₜ saturation (G := G) s,
          ∀ z, (H z).val = z.1 • z.2.val) ∧
        ∀ y ∈ saturation (G := G) s, ∃! x : s, ∃ g : G, g • x.val = y

end Specs.SmoothManifolds.Ch08.FreeProperSlices
