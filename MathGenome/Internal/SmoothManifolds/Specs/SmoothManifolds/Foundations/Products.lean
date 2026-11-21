import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Boundary
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-! Product coordinates and restricted atlases, using the shared ambient-extension
convention. A coordinate witness is an actual linear change of coordinates
carrying precisely the product model onto the asserted ordinary model. -/
namespace SmoothManifolds.ProductData
open ModelData AtlasData Set
universe u v

/-- A zero-dimensional half-space has no constrained coordinate. -/
def productKind (n : ℕ) (a : ModelKind) (m : ℕ) (b : ModelKind) : ModelKind :=
  if (a = .halfSpace ∧ 0 < n) ∨ (b = .halfSpace ∧ 0 < m) then .halfSpace else .euclidean

/-- Coordinate changes for ordinary products. The set equality excludes treating
an orthant as a half-space by a mere type-level dimension count. -/
structure ProductCoordinates (n : ℕ) (a : ModelKind) (m : ℕ) (b k : ModelKind) where
  linearEquiv : (Euclidean n × Euclidean m) ≃L[ℝ] Euclidean (n + m)
  mem_model : ∀ z, linearEquiv z ∈ modelSet (n + m) k ↔
    z.1 ∈ modelSet n a ∧ z.2 ∈ modelSet m b

/-- The homeomorphism on model subspaces induced by ambient linear coordinates. -/
def ProductCoordinates.homeomorph {n m : ℕ} {a b k : ModelKind}
    (C : ProductCoordinates n a m b k) :
    (ModelSpace n a × ModelSpace m b) ≃ₜ ModelSpace (n + m) k :=
  (Homeomorph.Set.prod (modelSet n a) (modelSet m b)).symm.trans
    (C.linearEquiv.toHomeomorph.subtype (fun z => (C.mem_model z).symm))

/-- The product chart has the product source and the specified linear coordinates. -/
def productChart {n m : ℕ} {a b k : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinates n a m b k) (c : ModelChart n a M) (d : ModelChart m b N) :
    ModelChart (n + m) k (M × N) :=
  (c.prod d).trans C.homeomorph.toOpenPartialHomeomorph

/-- Product charts from two given atlases. -/
def productAtlas {n m : ℕ} {a b k : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinates n a m b k)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N)) :
    Set (ModelChart (n + m) k (M × N)) :=
  {e | ∃ c ∈ A, ∃ d ∈ B, e = productChart C c d}

end SmoothManifolds.ProductData

namespace Specs.SmoothManifolds.Foundations.Products
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.ProductData _root_.SmoothManifolds.BoundaryData Set
universe u v

/-- Restrict all original smooth charts and take their unique maximal extension.
The topological atlas is the restricted atlas, including on the empty subspace. -/
def exists_openSubset_smoothManifoldType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (s : Set M) (hs : IsOpen s),
    ∃ R : SmoothManifold n a s,
      R.topologicalManifold.atlas = openSubsetAtlas S.smoothStructure.val s hs ∧
      R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (openSubsetAtlas S.smoothStructure.val s hs) ∧
      IsSmoothMap R S Subtype.val

/-- Ordinary products of two Euclidean models, including dimensions zero. -/
def exists_euclidean_productCoordinatesType : Prop :=
  ∀ n m : ℕ, Nonempty (ProductCoordinates n .euclidean m .euclidean .euclidean)

/-- A positive-dimensional half-space in the second factor retains its last
coordinate as the last coordinate of the sum-dimensional model. -/
def exists_rightHalfSpace_productCoordinatesType : Prop :=
  ∀ n m : ℕ, ∃ C : ProductCoordinates n .euclidean (m + 1) .halfSpace .halfSpace,
    ∀ z, C.linearEquiv z (Fin.last (n + m)) = z.2 (Fin.last m)

/-- A positive-dimensional half-space in the first factor has its constrained
coordinate permuted to the last position. -/
def exists_leftHalfSpace_productCoordinatesType : Prop :=
  ∀ n m : ℕ, ∃ C : ProductCoordinates (n + 1) .halfSpace m .euclidean .halfSpace,
    ∀ z, C.linearEquiv z ((Fin.last (n + m)).cast (Nat.add_right_comm n m 1)) = z.1 (Fin.last n)

/-- H^0 is a point with empty boundary, so its product with R^m is Euclidean. -/
def exists_zeroHalfSpace_productCoordinatesType : Prop :=
  (∀ m : ℕ, Nonempty (ProductCoordinates 0 .halfSpace m .euclidean .euclidean)) ∧
  (∀ n : ℕ, Nonempty (ProductCoordinates n .euclidean 0 .halfSpace .euclidean))

/-- Product charts and transitions give the product smooth structure for every
actual coordinate identification of the product model. Hausdorffness and second
countability are part of the returned smooth manifold on the product topology.
All product charts belong to its maximal atlas. No nonempty-factor hypothesis. -/
def exists_product_smoothManifoldType : Prop :=
  ∀ {n m : ℕ} {a b k : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : ProductCoordinates n a m b k),
    ∃ P : SmoothManifold (n + m) k (M × N),
      P.topologicalManifold.atlas = productAtlas C S.smoothStructure.val T.smoothStructure.val ∧
      P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (productAtlas C S.smoothStructure.val T.smoothStructure.val)

/-- The generating charts use exactly the declared coordinate map on exactly
the product of the original chart domains. -/
def productChart_source_applyType : Prop :=
  ∀ {n m : ℕ} {a b k : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinates n a m b k) (c : ModelChart n a M) (d : ModelChart m b N),
    (productChart C c d).source = c.source ×ˢ d.source ∧
    ∀ p : M × N, ((productChart C c d) p).val = C.linearEquiv ((c p.1).val, (d p.2).val)

/-- All transition maps of the generating product atlas satisfy the full local
ambient-extension test in both directions. -/
def productAtlas_isContDiffAtlasType : Prop :=
  ∀ {n m : ℕ} {a b k : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinates n a m b k) (r : ℕ∞)
    (A : Set (ModelChart n a M)) (B : Set (ModelChart m b N)),
    IsContDiffAtlas r A → IsContDiffAtlas r B →
    IsContDiffAtlas r (productAtlas C A B)

/-- Direct construction under precisely the ordinary-model cases. The disjunction
also includes a zero-dimensional half-space factor, since it has empty boundary.
Two positive-dimensional half-space models are deliberately excluded. -/
def exists_ordinaryProduct_smoothManifoldType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N),
    (a = .euclidean ∨ b = .euclidean ∨ n = 0 ∨ m = 0) →
    ∃ C : ProductCoordinates n a m b (productKind n a m b),
    ∃ P : SmoothManifold (n + m) (productKind n a m b) (M × N),
      P.topologicalManifold.atlas = productAtlas C S.smoothStructure.val T.smoothStructure.val ∧
      P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (productAtlas C S.smoothStructure.val T.smoothStructure.val)

/-- The Euclidean representation of a boundaryless manifold is available from
its actual intrinsic-boundary condition, regardless of its original model kind. -/
def exists_boundaryless_euclidean_smoothManifoldType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M), intrinsicBoundary S = ∅ →
    ∃ E : SmoothManifold n .euclidean M, IsSmoothMap S E id ∧ IsSmoothMap E S id

/-- Product construction with a boundaryless first factor. The identity maps
verify that the Euclidean representation has exactly the original smoothness. -/
def exists_product_leftBoundarylessType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N),
    intrinsicBoundary S = ∅ →
    ∃ E : SmoothManifold n .euclidean M,
      IsSmoothMap S E id ∧ IsSmoothMap E S id ∧
      ∃ C : ProductCoordinates n .euclidean m b (productKind n .euclidean m b),
      ∃ P : SmoothManifold (n + m) (productKind n .euclidean m b) (M × N),
        P.topologicalManifold.atlas = productAtlas C E.smoothStructure.val T.smoothStructure.val ∧
        P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
          (productAtlas C E.smoothStructure.val T.smoothStructure.val)

/-- Product construction with a boundaryless second factor. -/
def exists_product_rightBoundarylessType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N),
    intrinsicBoundary T = ∅ →
    ∃ E : SmoothManifold m .euclidean N,
      IsSmoothMap T E id ∧ IsSmoothMap E T id ∧
      ∃ C : ProductCoordinates n a m .euclidean (productKind n a m .euclidean),
      ∃ P : SmoothManifold (n + m) (productKind n a m .euclidean) (M × N),
        P.topologicalManifold.atlas = productAtlas C S.smoothStructure.val E.smoothStructure.val ∧
        P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
          (productAtlas C S.smoothStructure.val E.smoothStructure.val)

/-- Two intrinsically boundaryless factors have a Euclidean product structure;
the resulting product again has empty intrinsic boundary. -/
def exists_product_boundarylessType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N),
    intrinsicBoundary S = ∅ → intrinsicBoundary T = ∅ →
    ∃ E : SmoothManifold n .euclidean M, ∃ F : SmoothManifold m .euclidean N,
      IsSmoothMap S E id ∧ IsSmoothMap E S id ∧
      IsSmoothMap T F id ∧ IsSmoothMap F T id ∧
      ∃ C : ProductCoordinates n .euclidean m .euclidean .euclidean,
      ∃ P : SmoothManifold (n + m) .euclidean (M × N),
        P.topologicalManifold.atlas = productAtlas C E.smoothStructure.val F.smoothStructure.val ∧
        P.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
          (productAtlas C E.smoothStructure.val F.smoothStructure.val) ∧
        intrinsicBoundary P = ∅

end Specs.SmoothManifolds.Foundations.Products
