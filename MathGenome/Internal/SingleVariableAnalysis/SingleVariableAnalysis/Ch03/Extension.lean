import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Extension
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Analysis.Complex.Basic

/-!
# Uniformly continuous extension to the closure

K03.03.extension (paper.tex:608–619). The inclusion `E → closure E` is a
dense uniform embedding. Mathlib's `uniformly_extend_exists` obtains limits
by mapping Cauchy filters into the complete target; `IsDenseInducing.extend`
chooses those limits. `uniformContinuous_uniformly_extend` proves uniform
continuity, and `extend_unique` proves uniqueness among continuous maps.
The concrete conclusions below use canonical real and complex completeness.
No extension certificate, compactness, or nonemptiness is assumed.
The same argument applies to the empty set: its closure is empty too.
-/
namespace SingleVariableAnalysis

universe u v

private theorem complete_metric_closure_extension
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    (E : Set X) (f : E → Y) (hf : UniformContinuous f) :
    ∃ g : closure E → Y,
      Continuous g ∧ UniformContinuous g ∧
      (∀ x : E, g ⟨x.val, subset_closure x.property⟩ = f x) ∧
      ∀ h : closure E → Y, Continuous h →
        (∀ x : E, h ⟨x.val, subset_closure x.property⟩ = f x) → h = g := by
  let i : E → closure E := Set.inclusion subset_closure
  have hi : IsUniformInducing i :=
    (isUniformEmbedding_set_inclusion subset_closure).isUniformInducing
  have hd : DenseRange i := (denseRange_inclusion_iff subset_closure).mpr subset_rfl
  let di : IsDenseInducing i := hi.isDenseInducing hd
  let g : closure E → Y := di.extend f
  have hg : UniformContinuous g := uniformContinuous_uniformly_extend hi hd hf
  refine ⟨g, hg.continuous, hg, ?_, ?_⟩
  · intro x
    exact di.extend_eq hf.continuous x
  · intro h hh heq
    exact (di.extend_unique heq hh).symm

theorem real_closure_extension
    {X : Type u} [MetricSpace X] (E : Set X) (f : E → ℝ)
    (hf : UniformContinuous f) :
    ∃ g : closure E → ℝ,
      Continuous g ∧ UniformContinuous g ∧
      (∀ x : E, g ⟨x.val, subset_closure x.property⟩ = f x) ∧
      ∀ h : closure E → ℝ, Continuous h →
        (∀ x : E, h ⟨x.val, subset_closure x.property⟩ = f x) → h = g :=
  complete_metric_closure_extension E f hf

theorem complex_closure_extension
    {X : Type u} [MetricSpace X] (E : Set X) (f : E → ℂ)
    (hf : UniformContinuous f) :
    ∃ g : closure E → ℂ,
      Continuous g ∧ UniformContinuous g ∧
      (∀ x : E, g ⟨x.val, subset_closure x.property⟩ = f x) ∧
      ∀ h : closure E → ℂ, Continuous h →
        (∀ x : E, h ⟨x.val, subset_closure x.property⟩ = f x) → h = g :=
  complete_metric_closure_extension E f hf

end SingleVariableAnalysis
