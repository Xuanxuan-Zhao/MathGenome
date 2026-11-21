import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses
import Mathlib.Topology.Homeomorph.Lemmas

/-! Local part of p104:M03.02. The restriction has the topology induced from
M, and its range has exactly the topology induced from N. No condition is
imposed on the intrinsic boundaries of either manifold. The differential in
`IsImmersion` is the full tangent differential, including normal directions.
Smoothness and immersion on the open neighborhood are inherited from f. -/
namespace Specs.SmoothManifolds.Ch03.LocalEmbedding
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.MapClassData
open Set
universe u v

/-- Every smooth immersion restricts near each point to an injective immersion
which is a homeomorphism onto its image with the target subspace topology. -/
def local_embeddingType : Prop :=
  ∀ {m n : ℕ} {a b : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → IsImmersion S T f → ∀ p : M,
    ∃ (U : Set M) (hU : IsOpen U), p ∈ U ∧
      Topology.IsEmbedding (fun x : U => f x.val) ∧
      ManifoldContDiff (⊤ : ℕ∞) (openSubsetAtlas S.smoothStructure.val U hU)
        T.smoothStructure.val (fun x : U => f x.val) ∧
      (∀ x : U, IsImmersionAt S T f x.val) ∧
      ∃ H : U ≃ₜ Set.range (fun x : U => f x.val),
        ∀ x : U, (H x).val = f x.val

end Specs.SmoothManifolds.Ch03.LocalEmbedding
