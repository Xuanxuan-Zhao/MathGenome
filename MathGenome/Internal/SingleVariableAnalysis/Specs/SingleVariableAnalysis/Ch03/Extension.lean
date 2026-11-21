import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.UniformContinuity

/-!
Independent statements for K03.03.extension, paper.tex:608–619.
`E` and `closure E` carry their induced metrics. A function on `E` has
no prescribed values outside `E`. Agreement uses the canonical inclusion
of `E` in its closure. Uniqueness is among all continuous extensions.
There is no nonemptiness assumption, including on the ambient metric space,
and no extension or completeness certificate is an input hypothesis.
-/
namespace Specs.SingleVariableAnalysis.Ch03.Extension

universe u

def realClosureExtension : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X) (f : E → ℝ),
    UniformContinuous f →
    ∃ g : closure E → ℝ,
      Continuous g ∧ UniformContinuous g ∧
      (∀ x : E, g ⟨x.val, subset_closure x.property⟩ = f x) ∧
      ∀ h : closure E → ℝ, Continuous h →
        (∀ x : E, h ⟨x.val, subset_closure x.property⟩ = f x) → h = g

def complexClosureExtension : Prop :=
  ∀ {X : Type u} [MetricSpace X] (E : Set X) (f : E → ℂ),
    UniformContinuous f →
    ∃ g : closure E → ℂ,
      Continuous g ∧ UniformContinuous g ∧
      (∀ x : E, g ⟨x.val, subset_closure x.property⟩ = f x) ∧
      ∀ h : closure E → ℂ, Continuous h →
        (∀ x : E, h ⟨x.val, subset_closure x.property⟩ = f x) → h = g

end Specs.SingleVariableAnalysis.Ch03.Extension
