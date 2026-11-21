import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Foundations.Models
import Mathlib.Topology.LocallyClosed

/-! Independent statement of `p104:shrink-along-section`.
`IsEmbedding` of the restricted map means precisely that it is a
homeomorphism onto its image, equipped with the subspace topology. -/
namespace Specs.SmoothManifolds.Ch04.InjectiveShrinking
open Set Topology
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
universe u v

/-- No separation, countability, or local compactness is required of the source.
The empty subset is permitted. -/
def injective_shrinkingType : Prop :=
  ∀ {U : Type u} {N : Type v} [TopologicalSpace U] [TopologicalSpace N]
    {n : ℕ} {kind : ModelKind} (A : TopologicalManifold n kind N)
    (F : U → N) (S : Set U),
    Continuous F → IsEmbedding (fun s : S => F s) →
    IsLocallyClosed (F '' S) →
    (∀ s ∈ S, ∃ W : Set U, IsOpen W ∧ s ∈ W ∧ InjOn F W) →
    ∃ V : Set U, IsOpen V ∧ S ⊆ V ∧ InjOn F V

end Specs.SmoothManifolds.Ch04.InjectiveShrinking
