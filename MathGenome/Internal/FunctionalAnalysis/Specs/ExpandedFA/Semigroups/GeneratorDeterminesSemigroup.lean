import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator

/-! Exact-domain generator uniqueness, paper.tex 14443–14457
(`fa2:p3:semigroup-basics`). Equality is equality of partial linear maps,
so it includes the entire generator domain. No regularity beyond the C₀
axioms on an arbitrary real or complex Banach space is assumed. -/

open scoped NNReal

namespace ExpandedFA.Semigroups.GeneratorDeterminesSemigroupSpec

/-- Two C₀ semigroups with identical generators agree at every nonnegative time. -/
def GeneratorDeterminesSemigroup : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    (S T : C0Semigroup 𝕜 X),
    C0SemigroupSpec.generatorValue S = C0SemigroupSpec.generatorValue T →
    ∀ t : ℝ≥0, S.operators t = T.operators t

end ExpandedFA.Semigroups.GeneratorDeterminesSemigroupSpec
