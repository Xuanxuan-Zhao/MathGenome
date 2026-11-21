import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformConventions

/-! Independent statements of paper.tex, `d10:12:dense-extension`.
The subtype `A` has the uniformity induced from `Z`. All topologies are the
canonical topologies of those uniformities. Completeness, separation, and
uniform continuity use the manuscript's previously fixed definitions.
Neither the ambient space nor the target is assumed nonempty; no separation
or completeness assumption is placed on the ambient space.
-/

universe u v

namespace Specs.D10Topology.Ch12.DenseUniformExtension

open UniformConventions

/-- Every uniformly continuous map from a dense uniform subspace to a complete
separated uniform space has exactly one uniformly continuous extension. -/
def dense_uniform_extension : Prop :=
  ∀ {Z : Type u} {Y : Type v} [UniformSpace Z] [UniformSpace Y]
    (A : Set Z), Dense A → Complete Y → Separated (X := Y) →
    ∀ f : A → Y, EntourageContinuous f →
      ∃! g : Z → Y, EntourageContinuous g ∧ ∀ a : A, g a.val = f a

/-- Uniqueness holds even among continuous extensions. This part only needs
the target's separation, and does not need completeness or uniform continuity
of the map being extended. -/
def continuous_extension_unique : Prop :=
  ∀ {Z : Type u} {Y : Type v} [UniformSpace Z] [UniformSpace Y]
    (A : Set Z), Dense A → Separated (X := Y) →
    ∀ (f : A → Y) (g h : Z → Y),
      Continuous g → Continuous h →
      (∀ a : A, g a.val = f a) → (∀ a : A, h a.val = f a) → g = h

end Specs.D10Topology.Ch12.DenseUniformExtension
