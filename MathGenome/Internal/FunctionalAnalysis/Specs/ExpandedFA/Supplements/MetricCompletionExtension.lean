import Mathlib.Topology.MetricSpace.Completion

/-!
Independent specifications for the existence and extension clauses of
`fa2:p1:metric-completion`, paper.tex lines 5848–5889.

No nonemptiness assumption is imposed on any space. The extension clauses
are stated for every complete metric space with a dense isometric embedding
of the source, so they apply to any construction of its completion.
Uniqueness of completions and comparison with the linear completion belong
to the downstream goal `mid_p1_metric_completion`.
-/

universe u v w

namespace Specs.ExpandedFA.Supplements.MetricCompletionExtension

/-- A complete metric space with a dense isometric embedding of any metric space. -/
def CompletionExists : Prop :=
  ∀ (X : Type u) [MetricSpace X],
    ∃ (H : Type u) (_ : MetricSpace H),
      CompleteSpace H ∧ ∃ j : X → H, Isometry j ∧ DenseRange j

/-- Every uniformly continuous map into a complete metric space has exactly
one uniformly continuous extension to any completion of its domain. -/
def UniformExtension : Prop :=
  ∀ (X : Type u) (H : Type v) [MetricSpace X] [MetricSpace H] [CompleteSpace H]
    (j : X → H), Isometry j → DenseRange j →
    ∀ (Y : Type w) [MetricSpace Y] [CompleteSpace Y] (f : X → Y),
      UniformContinuous f →
        ∃! g : H → Y, UniformContinuous g ∧ ∀ x, g (j x) = f x

/-- Every prescribed real Lipschitz bound, including zero, is preserved.
The extension is unique even among all uniformly continuous extensions. -/
def LipschitzExtension : Prop :=
  ∀ (X : Type u) (H : Type v) [MetricSpace X] [MetricSpace H] [CompleteSpace H]
    (j : X → H), Isometry j → DenseRange j →
    ∀ (Y : Type w) [MetricSpace Y] [CompleteSpace Y]
      (L : ℝ), 0 ≤ L → ∀ (f : X → Y),
      (∀ x y, dist (f x) (f y) ≤ L * dist x y) →
        ∃ g : H → Y,
          UniformContinuous g ∧
          (∀ x, g (j x) = f x) ∧
          (∀ z t, dist (g z) (g t) ≤ L * dist z t) ∧
          (∀ k : H → Y, UniformContinuous k →
            (∀ x, k (j x) = f x) → k = g)

/-- The standard completion of an empty metric space is empty as well. -/
def EmptyCompletion : Prop :=
  ∀ (X : Type u) [MetricSpace X] [IsEmpty X],
    IsEmpty (UniformSpace.Completion X)

end Specs.ExpandedFA.Supplements.MetricCompletionExtension
