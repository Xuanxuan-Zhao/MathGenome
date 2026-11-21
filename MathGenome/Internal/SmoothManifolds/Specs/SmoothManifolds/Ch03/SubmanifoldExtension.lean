import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.Partitions

/-! Extension along an embedding, including both intrinsic boundaries.
The neighborhood extension is represented by a total function whose smoothness
is required only on the stated open neighborhood. Restriction gives the actual
smooth function on that neighborhood. No regularity is asserted outside it. -/
namespace Specs.SmoothManifolds.Ch03.SubmanifoldExtension
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.MapClassData _root_.SmoothManifolds.PartitionData Set
universe u v

def embedding_extension_neighborhoodType : Prop :=
  ∀ {m n k : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothEmbedding S T f → ∀ g : M → Euclidean k,
    (∀ x, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val g x) →
    ∃ U : Set N, IsOpen U ∧ range f ⊆ U ∧ ∃ G : N → Euclidean k,
      (∀ y ∈ U, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) T.smoothStructure.val G y) ∧
      ∀ x, G (f x) = g x

def embedding_extension_closedType : Prop :=
  ∀ {m n k : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothEmbedding S T f → IsClosed (range f) → ∀ g : M → Euclidean k,
    (∀ x, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val g x) →
    ∃ G : N → Euclidean k,
      (∀ y, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) T.smoothStructure.val G y) ∧
      ∀ x, G (f x) = g x

def scalar_embedding_extension_neighborhoodType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothEmbedding S T f → ∀ g : M → ℝ, ScalarSmooth S.smoothStructure.val g →
    ∃ U : Set N, IsOpen U ∧ range f ⊆ U ∧ ∃ G : N → ℝ,
      (∀ y ∈ U, ScalarContDiffAt (⊤ : ℕ∞) T.smoothStructure.val G y) ∧
      ∀ x, G (f x) = g x

def scalar_embedding_extension_closedType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothEmbedding S T f → IsClosed (range f) →
    ∀ g : M → ℝ, ScalarSmooth S.smoothStructure.val g →
    ∃ G : N → ℝ, ScalarSmooth T.smoothStructure.val G ∧ ∀ x, G (f x) = g x

/-- Explicit specialization to a subset with its given embedded smooth structure.
The chosen intrinsic topology is arbitrary; the embedding hypothesis enforces
agreement with the ambient subspace topology. -/
def submanifold_extensionType : Prop :=
  ∀ {m n k : ℕ} {a b : ModelKind} {N : Type v} [TopologicalSpace N]
    (T : SmoothManifold n b N) (s : Set N) (t : TopologicalSpace s)
    (S : @SmoothManifold m a s t),
    @IsSmoothEmbedding m n a b s N t _ S T Subtype.val →
    ∀ g : s → Euclidean k,
    (∀ x, @ManifoldContDiffToEuclideanAt m k a s t (⊤ : ℕ∞)
      S.smoothStructure.val g x) →
    (∃ (U : Set N) (hU : IsOpen U) (hsub : s ⊆ U), ∃ G : U → Euclidean k,
      (∀ y, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞)
        (openSubsetAtlas T.smoothStructure.val U hU) G y) ∧
      ∀ x : s, G ⟨x.val, hsub x.property⟩ = g x) ∧
    (IsClosed s → ∃ G : N → Euclidean k,
      (∀ y, ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) T.smoothStructure.val G y) ∧
      ∀ x : s, G x.val = g x)

/-- The real-valued version on the actual open neighborhood subtype. -/
def submanifold_scalar_extensionType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {N : Type v} [TopologicalSpace N]
    (T : SmoothManifold n b N) (s : Set N) (t : TopologicalSpace s)
    (S : @SmoothManifold m a s t),
    @IsSmoothEmbedding m n a b s N t _ S T Subtype.val →
    ∀ g : s → ℝ, @ScalarContDiff m a s t (⊤ : ℕ∞) S.smoothStructure.val g →
    (∃ (U : Set N) (hU : IsOpen U) (hsub : s ⊆ U), ∃ G : U → ℝ,
      ScalarSmooth (openSubsetAtlas T.smoothStructure.val U hU) G ∧
      ∀ x : s, G ⟨x.val, hsub x.property⟩ = g x) ∧
    (IsClosed s → ∃ G : N → ℝ, ScalarSmooth T.smoothStructure.val G ∧
      ∀ x : s, G x.val = g x)

end Specs.SmoothManifolds.Ch03.SubmanifoldExtension
