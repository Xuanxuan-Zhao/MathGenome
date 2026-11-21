import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.SeparatedUniformQuotient
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformCompletion

open Set Filter
open scoped Uniformity
universe u v

namespace D10Topology.Ch12

/-- Belonging to every entourage of the original uniformity. -/
def UniformRelated {X : Type u} [UniformSpace X] (x y : X) : Prop :=
  ∀ U ∈ 𝓤 X, (x, y) ∈ U

abbrev SeparatedQuotient (X : Type u) [UniformSpace X] : Type u := SeparationQuotient X

def separatedQuotientMap {X : Type u} [UniformSpace X] : X → SeparatedQuotient X :=
  SeparationQuotient.mk

abbrev SeparatedCompletion (X : Type u) [UniformSpace X] : Type u :=
  UniformSpace.Completion (SeparatedQuotient X)

/-- The quotient map followed by the separated completion inclusion. -/
def separatedCompletionMap {X : Type u} [UniformSpace X] (x : X) : SeparatedCompletion X :=
  (↑(separatedQuotientMap (X := X) x) : UniformSpace.Completion (SeparatedQuotient X))

theorem uniformRelated_iff_inseparable {X : Type u} [UniformSpace X] (x y : X) :
    UniformRelated x y ↔ Inseparable x y :=
  inseparable_iff_ker_uniformity.symm

theorem uniformRelated_equivalence {X : Type u} [UniformSpace X] :
    Equivalence (UniformRelated (X := X)) := by
  refine ⟨fun x => ?_, fun {x y} h => ?_, fun {x y z} hxy hyz => ?_⟩
  · exact (uniformRelated_iff_inseparable x x).mpr (Inseparable.refl x)
  · exact (uniformRelated_iff_inseparable y x).mpr
      ((uniformRelated_iff_inseparable x y).mp h).symm
  · exact (uniformRelated_iff_inseparable x z).mpr
      (((uniformRelated_iff_inseparable x y).mp hxy).trans
        ((uniformRelated_iff_inseparable y z).mp hyz))

theorem separatedQuotient_surjective {X : Type u} [UniformSpace X] :
    Function.Surjective (separatedQuotientMap (X := X)) :=
  SeparationQuotient.surjective_mk

theorem separatedQuotient_kernel {X : Type u} [UniformSpace X] (x y : X) :
    separatedQuotientMap x = separatedQuotientMap y ↔ UniformRelated x y :=
  SeparationQuotient.mk_eq_mk.trans (uniformRelated_iff_inseparable x y).symm

theorem separatedQuotient_entourages {X : Type u} [UniformSpace X]
    (V : Set (SeparatedQuotient X × SeparatedQuotient X)) :
    V ∈ 𝓤 (SeparatedQuotient X) ↔ ∃ U ∈ 𝓤 X,
      Prod.map separatedQuotientMap separatedQuotientMap '' U ⊆ V := by
  exact ((𝓤 X).basis_sets.map (Prod.map separatedQuotientMap separatedQuotientMap)).mem_iff

theorem separatedQuotient_separated {X : Type u} [UniformSpace X] :
    Separated (X := SeparatedQuotient X) :=
  separated_iff_mathlib.mpr inferInstance

theorem separatedQuotient_induced {X : Type u} [uX : UniformSpace X] :
    inducedUniformity (separatedQuotientMap (X := X)) = uX :=
  SeparationQuotient.isUniformInducing_mk.comap_uniformSpace

theorem separatedQuotient_factorization
    {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y]
    (hY : Separated (X := Y)) (f : X → Y) (hf : EntourageContinuous f) :
    ∃! g : SeparatedQuotient X → Y,
      EntourageContinuous g ∧ ∀ x, g (separatedQuotientMap x) = f x := by
  let : T0Space Y := separated_iff_mathlib.mp hY
  have hfu : UniformContinuous f := hf
  refine ⟨SeparationQuotient.lift' f, ⟨SeparationQuotient.uniformContinuous_lift' f,
    SeparationQuotient.lift'_mk hfu⟩, ?_⟩
  intro g hg
  funext z
  obtain ⟨x, rfl⟩ := separatedQuotient_surjective z
  exact (hg.2 x).trans (SeparationQuotient.lift'_mk hfu x).symm

/-- Composition preserves the original uniformity, even though q may identify
points. No injectivity is asserted in this lemma. -/
private theorem separatedCompletion_isUniformInducing {X : Type u} [UniformSpace X] :
    IsUniformInducing (separatedCompletionMap (X := X)) :=
  (UniformSpace.Completion.isUniformInducing_coe (SeparatedQuotient X)).comp SeparationQuotient.isUniformInducing_mk

theorem separatedCompletion_properties {X : Type u} [uX : UniformSpace X] :
    Complete (SeparatedCompletion X) ∧ Separated (X := SeparatedCompletion X) ∧
    EntourageContinuous (separatedCompletionMap (X := X)) ∧
    DenseRange (separatedCompletionMap (X := X)) ∧
    inducedUniformity (separatedCompletionMap (X := X)) = uX := by
  obtain ⟨hc, hs, _, hd⟩ := uniform_completion (separatedQuotient_separated (X := X))
  refine ⟨hc, hs, separatedCompletion_isUniformInducing.uniformContinuous, ?_,
    separatedCompletion_isUniformInducing.comap_uniformSpace⟩
  exact hd.comp (separatedQuotient_surjective.denseRange)
    (UniformSpace.Completion.continuous_coe (SeparatedQuotient X))

theorem separatedCompletion_extension
    {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y]
    (hc : Complete Y) (hs : Separated (X := Y))
    (f : X → Y) (hf : EntourageContinuous f) :
    ∃! g : SeparatedCompletion X → Y,
      EntourageContinuous g ∧ ∀ x, g (separatedCompletionMap x) = f x := by
  obtain ⟨f₀, hf₀, _⟩ := separatedQuotient_factorization hs f hf
  obtain ⟨g, hg, huniq⟩ := uniform_completion_extension
    (separatedQuotient_separated (X := X)) hc hs f₀ hf₀.1
  refine ⟨g, ⟨hg.1, fun x => (hg.2 _).trans (hf₀.2 x)⟩, ?_⟩
  intro k hk
  apply huniq
  refine ⟨hk.1, ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := separatedQuotient_surjective z
  exact (hk.2 x).trans (hf₀.2 x).symm

theorem separatedCompletion_kernel {X : Type u} [UniformSpace X] (x y : X) :
    separatedCompletionMap x = separatedCompletionMap y ↔ UniformRelated x y := by
  exact ((UniformSpace.Completion.coe_injective (α := SeparatedQuotient X)).eq_iff).trans (separatedQuotient_kernel x y)

theorem separatedCompletion_injective_iff {X : Type u} [UniformSpace X] :
    Function.Injective (separatedCompletionMap (X := X)) ↔ Separated (X := X) := by
  rw [separated_iff_mathlib, t0Space_iff_uniformity]
  constructor
  · intro h x y hxy
    exact h ((separatedCompletion_kernel x y).mpr hxy)
  · intro h x y hxy
    exact h x y ((separatedCompletion_kernel x y).mp hxy)

theorem separatedCompletion_embedding_iff {X : Type u} [UniformSpace X] :
    UniformEmbedding (separatedCompletionMap (X := X)) ↔ Separated (X := X) := by
  constructor
  · intro h
    exact separatedCompletion_injective_iff.mp h.1
  · intro h
    exact ⟨separatedCompletion_injective_iff.mpr h,
      separatedCompletion_isUniformInducing.comap_uniformSpace⟩

theorem separatedCompletion_empty {X : Type u} [UniformSpace X] [IsEmpty X] :
    IsEmpty (SeparatedQuotient X) ∧ IsEmpty (SeparatedCompletion X) := by
  have hq : IsEmpty (SeparatedQuotient X) := ⟨fun z => by
    obtain ⟨x, _⟩ := separatedQuotient_surjective z
    exact isEmptyElim x⟩
  let := hq
  exact ⟨hq, uniform_completion_empty⟩

end D10Topology.Ch12
