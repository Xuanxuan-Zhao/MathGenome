import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformConventions
import Mathlib.Topology.UniformSpace.Completion

/-! Independent statements for `d10:12:separated-quotient` and the
nonseparated boundary in `d10:12:completion-scope`. The quotient representation
is Mathlib's separation quotient; the kernel statement below identifies its
classes with precisely the relation defined by all original entourages.
There are no separation, countability, metrizability or nonemptiness assumptions
on the source. -/

open Set Filter
open scoped Uniformity
universe u v

namespace Specs.D10Topology.Ch12.SeparatedUniformQuotient
open UniformConventions

def UniformRelated {X : Type u} [UniformSpace X] (x y : X) : Prop :=
  ∀ U ∈ 𝓤 X, (x, y) ∈ U

def UniformRelatedType := {X : Type u} → [UniformSpace X] → X → X → Prop
def UniformRelatedValue : UniformRelatedType := @UniformRelated

abbrev SeparatedQuotient (X : Type u) [UniformSpace X] : Type u := SeparationQuotient X

def SeparatedQuotientType := (X : Type u) → [UniformSpace X] → Type u
def SeparatedQuotientValue : SeparatedQuotientType := SeparatedQuotient

def separatedQuotientMap {X : Type u} [UniformSpace X] : X → SeparatedQuotient X :=
  SeparationQuotient.mk

def separatedQuotientMapType := {X : Type u} → [UniformSpace X] → X → SeparatedQuotient X
def separatedQuotientMapValue : separatedQuotientMapType := @separatedQuotientMap

abbrev SeparatedCompletion (X : Type u) [UniformSpace X] : Type u :=
  UniformSpace.Completion (SeparatedQuotient X)

def SeparatedCompletionType := (X : Type u) → [UniformSpace X] → Type u
def SeparatedCompletionValue : SeparatedCompletionType := SeparatedCompletion

def separatedCompletionMap {X : Type u} [UniformSpace X] (x : X) : SeparatedCompletion X :=
  (↑(separatedQuotientMap (X := X) x) : UniformSpace.Completion (SeparatedQuotient X))

def separatedCompletionMapType := {X : Type u} → [UniformSpace X] → X → SeparatedCompletion X
def separatedCompletionMapValue : separatedCompletionMapType := @separatedCompletionMap

/-- The relation in the paper is an equivalence relation. -/
def uniformRelated_equivalence : Prop :=
  ∀ {X : Type u} [UniformSpace X], Equivalence (UniformRelated (X := X))

/-- This checks the representation bridge to the topological separation quotient. -/
def uniformRelated_iff_inseparable : Prop :=
  ∀ {X : Type u} [UniformSpace X] (x y : X), UniformRelated x y ↔ Inseparable x y

def separatedQuotient_surjective : Prop :=
  ∀ {X : Type u} [UniformSpace X], Function.Surjective (separatedQuotientMap (X := X))

def separatedQuotient_kernel : Prop :=
  ∀ {X : Type u} [UniformSpace X] (x y : X),
    separatedQuotientMap x = separatedQuotientMap y ↔ UniformRelated x y

/-- The image relations form a base for the specified uniformity, including on
an empty source. -/
def separatedQuotient_entourages : Prop :=
  ∀ {X : Type u} [UniformSpace X] (V : Set (SeparatedQuotient X × SeparatedQuotient X)),
    V ∈ 𝓤 (SeparatedQuotient X) ↔ ∃ U ∈ 𝓤 X,
      Prod.map separatedQuotientMap separatedQuotientMap '' U ⊆ V

def separatedQuotient_separated : Prop :=
  ∀ {X : Type u} [UniformSpace X], Separated (X := SeparatedQuotient X)

/-- Equality of uniform structures, not merely continuity of the quotient map. -/
def separatedQuotient_induced : Prop :=
  ∀ {X : Type u} [uX : UniformSpace X], inducedUniformity (separatedQuotientMap (X := X)) = uX

/-- Factorization through q for arbitrary separated targets; completeness is
not required here. -/
def separatedQuotient_factorization : Prop :=
  ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y],
    Separated (X := Y) → ∀ f : X → Y, EntourageContinuous f →
      ∃! g : SeparatedQuotient X → Y,
        EntourageContinuous g ∧ ∀ x, g (separatedQuotientMap x) = f x

/-- The explicit completion is the separated completion of the quotient and
j is, by definition, the composite of q with its canonical dense inclusion. -/
def separatedCompletion_properties : Prop :=
  ∀ {X : Type u} [uX : UniformSpace X],
    Complete (SeparatedCompletion X) ∧ Separated (X := SeparatedCompletion X) ∧
    EntourageContinuous (separatedCompletionMap (X := X)) ∧
    DenseRange (separatedCompletionMap (X := X)) ∧
    inducedUniformity (separatedCompletionMap (X := X)) = uX

/-- Full extension property into arbitrary complete separated uniform spaces. -/
def separatedCompletion_extension : Prop :=
  ∀ {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y],
    Complete Y → Separated (X := Y) → ∀ f : X → Y, EntourageContinuous f →
      ∃! g : SeparatedCompletion X → Y,
        EntourageContinuous g ∧ ∀ x, g (separatedCompletionMap x) = f x

def separatedCompletion_kernel : Prop :=
  ∀ {X : Type u} [UniformSpace X] (x y : X),
    separatedCompletionMap x = separatedCompletionMap y ↔ UniformRelated x y

def separatedCompletion_injective_iff : Prop :=
  ∀ {X : Type u} [UniformSpace X],
    Function.Injective (separatedCompletionMap (X := X)) ↔ Separated (X := X)

def separatedCompletion_embedding_iff : Prop :=
  ∀ {X : Type u} [UniformSpace X],
    UniformEmbedding (separatedCompletionMap (X := X)) ↔ Separated (X := X)

/-- Both quotient and completion are empty when X is empty. -/
def separatedCompletion_empty : Prop :=
  ∀ {X : Type u} [UniformSpace X] [IsEmpty X],
    IsEmpty (SeparatedQuotient X) ∧ IsEmpty (SeparatedCompletion X)

end Specs.D10Topology.Ch12.SeparatedUniformQuotient
