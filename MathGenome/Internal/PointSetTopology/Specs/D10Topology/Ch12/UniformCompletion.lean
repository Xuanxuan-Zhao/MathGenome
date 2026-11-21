import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformConventions
import Mathlib.Topology.UniformSpace.Completion

/-! Independent statements for `d10:12:uniform-completion` and its arbitrary
separated applicability in `d10:12:completion-scope`.

The explicit witness is Mathlib's Cauchy-filter completion, with its canonical
uniformity. The predicates below are the previously fixed entourage predicates;
in particular `UniformEmbedding` includes equality of induced uniformities.
No countability, metrizability, or nonemptiness hypothesis is imposed. Target
spaces and alternative completions range over independent universes.
-/

universe u v w

namespace Specs.D10Topology.Ch12.UniformCompletion

open UniformConventions

/-- An explicit complete separated space and dense uniform embedding for every
separated uniform space. -/
def uniform_completion : Prop :=
  ∀ {X : Type u} [UniformSpace X], Separated (X := X) →
    Complete (UniformSpace.Completion X) ∧
    Separated (X := UniformSpace.Completion X) ∧
    UniformEmbedding ((↑) : X → UniformSpace.Completion X) ∧
    DenseRange ((↑) : X → UniformSpace.Completion X)

/-- Existential form of existence, with the same universe for the completion. -/
def uniform_completion_exists : Prop :=
  ∀ {X : Type u} [UniformSpace X], Separated (X := X) →
    ∃ (Z : Type u) (uZ : UniformSpace Z),
      letI := uZ
      ∃ j : X → Z, Complete Z ∧ Separated (X := Z) ∧
        UniformEmbedding j ∧ DenseRange j

/-- The universal property for maps into every complete separated uniform
space, including targets without a countable entourage base and empty targets. -/
def uniform_completion_extension : Prop :=
  ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y],
    Separated (X := X) → Complete Y → Separated (X := Y) →
    ∀ f : X → Y, EntourageContinuous f →
      ∃! g : UniformSpace.Completion X → Y,
        EntourageContinuous g ∧ ∀ x : X, g (x : UniformSpace.Completion X) = f x

/-- Any two complete separated spaces with dense uniform embeddings of X
are related by exactly one uniform isomorphism commuting with those embeddings.
No universal property is assumed of either pair. -/
def uniform_completions_unique : Prop :=
  ∀ {X : Type u} {Z : Type v} {W : Type w}
    [UniformSpace X] [UniformSpace Z] [UniformSpace W]
    (j : X → Z) (i : X → W),
    Complete Z → Separated (X := Z) →
    Complete W → Separated (X := W) →
    UniformEmbedding j → DenseRange j → UniformEmbedding i → DenseRange i →
      ∃! e : Z ≃ W, UniformIsomorphism e ∧ ∀ x : X, e (j x) = i x

/-- The explicit completion of an empty uniform space is empty. -/
def uniform_completion_empty : Prop :=
  ∀ {X : Type u} [UniformSpace X] [IsEmpty X],
    IsEmpty (UniformSpace.Completion X)

end Specs.D10Topology.Ch12.UniformCompletion
