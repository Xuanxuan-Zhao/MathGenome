import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.SpectralInclusion
import Mathlib.Topology.Order.Basic

/-! Independent specification for paper.tex, fa2:p3:eventual-norm-spectral-mapping
(lines 16571–16628 in the current adopted source).
The operator space has its usual operator norm. Continuity is required only on
an open tail of nonnegative time. The generator is the canonical exact-domain
right norm derivative from the upstream interface. No nonzero-space assumption
is imposed, and no compactness hypothesis is added. -/

noncomputable section
open scoped NNReal

namespace ExpandedFA.Semigroups.EventuallyNormContinuousSpectralMappingSpec

/-- Operator-norm continuity at every time strictly beyond some nonnegative time. -/
def EventuallyNormContinuous {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] (T : C0Semigroup ℂ X) : Prop :=
  ∃ t₀ : ℝ≥0, ContinuousOn T.operators (Set.Ioi t₀)

/-- The full spectral mapping equality at every positive time. -/
def SpectralMapping : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : C0Semigroup ℂ X), EventuallyNormContinuous T →
    ∀ (t : ℝ≥0), 0 < t →
      _root_.spectrum ℂ (T.operators t) \ {0} =
        (fun ζ : ℂ => Complex.exp ((t : ℝ) • ζ)) ''
          C0SemigroupSpec.spectrumValue (C0SemigroupSpec.generatorValue T)

end ExpandedFA.Semigroups.EventuallyNormContinuousSpectralMappingSpec
