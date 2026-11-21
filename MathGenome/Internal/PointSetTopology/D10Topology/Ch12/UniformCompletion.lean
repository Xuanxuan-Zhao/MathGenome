import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformCompletion
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformConventions

/-! Completion of arbitrary separated uniform spaces (`d10:12:uniform-completion`).

We use Mathlib's general Cauchy-filter construction, not its metric completion.
The accepted bridges identify filter completeness, separation, uniform continuity,
and equality of induced uniformities with the manuscript's entourage definitions.
The comparison argument assumes only completeness, separation, and dense uniform
embeddings of the two pairs, and derives their uniform isomorphism.
-/

universe u v w

namespace D10Topology.Ch12

theorem uniform_completion {X : Type u} [UniformSpace X]
    (hX : Separated (X := X)) :
    Complete (UniformSpace.Completion X) ∧
    Separated (X := UniformSpace.Completion X) ∧
    UniformEmbedding ((↑) : X → UniformSpace.Completion X) ∧
    DenseRange ((↑) : X → UniformSpace.Completion X) := by
  letI : T0Space X := separated_iff_mathlib.mp hX
  exact ⟨complete_iff_mathlib.mpr inferInstance,
    separated_iff_mathlib.mpr inferInstance,
    (uniformEmbedding_iff_mathlib _).mpr (UniformSpace.Completion.isUniformEmbedding_coe X),
    UniformSpace.Completion.denseRange_coe⟩

theorem uniform_completion_exists {X : Type u} [UniformSpace X]
    (hX : Separated (X := X)) :
    ∃ (Z : Type u) (uZ : UniformSpace Z),
      letI := uZ
      ∃ j : X → Z, Complete Z ∧ Separated (X := Z) ∧
        UniformEmbedding j ∧ DenseRange j := by
  exact ⟨UniformSpace.Completion X, inferInstance, (↑), uniform_completion hX⟩

theorem uniform_completion_extension
    {X : Type u} {Y : Type v} [UniformSpace X] [UniformSpace Y]
    (_hX : Separated (X := X)) (hY : Complete Y) (hsep : Separated (X := Y))
    (f : X → Y) (hf : EntourageContinuous f) :
    ∃! g : UniformSpace.Completion X → Y,
      EntourageContinuous g ∧ ∀ x : X, g (x : UniformSpace.Completion X) = f x := by
  letI : CompleteSpace Y := complete_iff_mathlib.mp hY
  letI : T0Space Y := separated_iff_mathlib.mp hsep
  have hfu : UniformContinuous f := (entourageContinuous_iff_mathlib f).mp hf
  refine ⟨UniformSpace.Completion.extension f, ⟨?_, ?_⟩, ?_⟩
  · exact (entourageContinuous_iff_mathlib _).mpr
      UniformSpace.Completion.uniformContinuous_extension
  · exact UniformSpace.Completion.extension_coe hfu
  · intro g hg
    exact (UniformSpace.Completion.extension_unique hfu
      ((entourageContinuous_iff_mathlib _).mp hg.1) (fun x => (hg.2 x).symm)).symm

theorem uniform_completions_unique
    {X : Type u} {Z : Type v} {W : Type w}
    [UniformSpace X] [UniformSpace Z] [UniformSpace W]
    (j : X → Z) (i : X → W)
    (hZ : Complete Z) (hsZ : Separated (X := Z))
    (hW : Complete W) (hsW : Separated (X := W))
    (hj : UniformEmbedding j) (hdj : DenseRange j)
    (hi : UniformEmbedding i) (hdi : DenseRange i) :
    ∃! e : Z ≃ W, UniformIsomorphism e ∧ ∀ x : X, e (j x) = i x := by
  letI : CompleteSpace Z := complete_iff_mathlib.mp hZ
  letI : T0Space Z := separated_iff_mathlib.mp hsZ
  letI : CompleteSpace W := complete_iff_mathlib.mp hW
  letI : T0Space W := separated_iff_mathlib.mp hsW
  let A : AbstractCompletion X :=
    { space := Z, coe := j, uniformStruct := inferInstance,
      complete := inferInstance, separation := inferInstance,
      isUniformInducing := ((uniformEmbedding_iff_mathlib j).mp hj).isUniformInducing,
      dense := hdj }
  let B : AbstractCompletion X :=
    { space := W, coe := i, uniformStruct := inferInstance,
      complete := inferInstance, separation := inferInstance,
      isUniformInducing := ((uniformEmbedding_iff_mathlib i).mp hi).isUniformInducing,
      dense := hdi }
  let e : Z ≃ᵤ W := A.compareEquiv B
  have he : ∀ x : X, e (j x) = i x := A.compare_coe B
  refine ⟨e.toEquiv, ⟨⟨e.uniformContinuous, e.uniformContinuous_symm⟩, he⟩, ?_⟩
  intro k hk
  apply Equiv.ext
  have heq : (k : Z → W) = (e : Z → W) :=
    hdj.equalizer ((entourageContinuous_iff_mathlib _).mp hk.1.1).continuous
      e.continuous (funext fun x => (hk.2 x).trans (he x).symm)
  exact congrFun heq

theorem uniform_completion_empty {X : Type u} [UniformSpace X] [IsEmpty X] :
    IsEmpty (UniformSpace.Completion X) := by
  refine ⟨fun z => ?_⟩
  have hne : Nonempty X := (UniformSpace.Completion.nonempty_completion_iff X).mp ⟨z⟩
  exact hne.elim isEmptyElim

end D10Topology.Ch12
