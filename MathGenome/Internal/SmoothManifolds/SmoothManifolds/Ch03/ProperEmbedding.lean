import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.ProperEmbedding
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Homeomorph.Lemmas

namespace SmoothManifolds.ProperEmbedding
open ModelData AtlasData MapData MapClassData
universe u v

/-- A manifold is Hausdorff and locally compact, so compact inverse images
imply properness in Mathlib's closed-map sense. -/
theorem proper_isClosedMap :
    Specs.SmoothManifolds.Ch03.ProperEmbedding.proper_isClosedMapType.{u,v} := by
  intro n b M N _ _ T f hf hp
  let := T.topologicalManifold.hausdorff
  let := TopologicalManifold.locallyCompactSpace T.topologicalManifold
  have hproper : IsProperMap f :=
    isProperMap_iff_isCompact_preimage.mpr ⟨hf, fun {K} hK => hp K hK⟩
  exact hproper.isClosedMap

/-- Closedness and injectivity give an embedding, whose inverse to the range
is continuous with respect to precisely the subspace topology. -/
theorem proper_injective_homeomorph :
    Specs.SmoothManifolds.Ch03.ProperEmbedding.proper_injective_homeomorphType.{u,v} := by
  intro m n a b M N _ _ S T f hf hi hp
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).1)
  have he : Topology.IsClosedEmbedding f :=
    .of_continuous_injective_isClosedMap hc hi (proper_isClosedMap T f hc hp)
  exact ⟨he.isEmbedding.toHomeomorph, fun _ => rfl⟩

theorem proper_injective_immersion :
    Specs.SmoothManifolds.Ch03.ProperEmbedding.proper_injective_immersionType.{u,v} := by
  intro m n a b M N _ _ S T f hf hi him hp
  exact ⟨hf, hi, him, proper_injective_homeomorph S T f hf hi hp⟩

/-- Compact subsets of the Hausdorff target are closed, so their inverse
images are closed subsets of the compact source. -/
theorem compact_isProper :
    Specs.SmoothManifolds.Ch03.ProperEmbedding.compact_isProperType.{u,v} := by
  intro m n a b M N _ _ _ S T f hf K hK
  let := T.topologicalManifold.hausdorff
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).1)
  exact (hK.isClosed.preimage hc).isCompact

theorem compact_injective_immersion :
    Specs.SmoothManifolds.Ch03.ProperEmbedding.compact_injective_immersionType.{u,v} := by
  intro m n a b M N _ _ _ S T f hf hi him
  exact proper_injective_immersion S T f hf hi him (compact_isProper S T f hf)

end SmoothManifolds.ProperEmbedding
