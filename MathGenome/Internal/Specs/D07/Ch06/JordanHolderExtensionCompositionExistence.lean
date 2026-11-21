import MathGenome.Internal.Specs.D07.Ch06.CompositionSeriesDefinition

/-!
Independent specification of the existence assertion of
`K07.06.jordan_holder_extension` (paper.tex:1137–1143).
The shared `Series` records a finite strictly increasing chain from bottom
to top, adjacent normality, and nontrivial simple adjacent quotients.
There is no uniqueness hypothesis or assertion in this obligation.
-/

namespace Specs.D07.Ch06.JordanHolderExtensionCompositionExistence

open Specs.D07.Ch06.CompositionSeriesDefinition

universe u

def CompositionSeriesExists : Prop :=
  ∀ (G : Type u) [Group G] [Finite G], Nonempty (Series G)

/-- The trivial group is covered with no strict steps and no factors. -/
def TrivialCompositionSeries : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [Subsingleton G],
    ∃ s : Series G, s.length = 0 ∧ factorListValue s = []

end Specs.D07.Ch06.JordanHolderExtensionCompositionExistence
