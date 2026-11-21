import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses

/-! Global embedding criteria, with no restriction on model kinds or dimensions.
The range in these statements always carries the target's subspace topology. -/
namespace Specs.SmoothManifolds.Ch03.ProperEmbedding
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.MapClassData
universe u v

/-- Compact inverse images make a continuous map into a manifold closed. -/
def proper_isClosedMapType : Prop :=
  ∀ {n : ℕ} {b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (_T : SmoothManifold n b N) (f : M → N),
    Continuous f → IsProper f → IsClosedMap f

/-- The inverse on the image is continuous, not merely a set-theoretic inverse. -/
def proper_injective_homeomorphType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → Function.Injective f → IsProper f →
      ∃ h : M ≃ₜ Set.range f, ∀ x, (h x).val = f x

/-- The global assertion of M03.02. -/
def proper_injective_immersionType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → Function.Injective f → IsImmersion S T f →
      IsProper f → IsSmoothEmbedding S T f

/-- A compact source supplies the manuscript's compact-inverse-image property. -/
def compact_isProperType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] [CompactSpace M]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → IsProper f

/-- The compact-source corollary of M03.02, including empty sources. -/
def compact_injective_immersionType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N] [CompactSpace M]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → Function.Injective f → IsImmersion S T f →
      IsSmoothEmbedding S T f

end Specs.SmoothManifolds.Ch03.ProperEmbedding
