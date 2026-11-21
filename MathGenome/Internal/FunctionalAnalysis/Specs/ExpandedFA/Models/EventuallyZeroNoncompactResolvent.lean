import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.LaplaceResolvent
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! The infinite-multiplicity nilpotent translation example, paper.tex
14736–14738 in the adopted source. We use Lebesgue measure restricted to
(0,1); values of representatives outside that interval are immaterial. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace ExpandedFA.Models.EventuallyZeroNoncompactResolvent
open ExpandedFA.Semigroups ExpandedFA.Unbounded
universe u

abbrev intervalMeasure : Measure ℝ := volume.restrict (Ioo 0 1)
abbrev State (M : Type u) [NormedAddCommGroup M] := Lp M 2 intervalMeasure

variable {𝕜 : Type*} [RCLike 𝕜]
variable {M : Type u} [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [CompleteSpace M]

/-- Left translation, killed at the right endpoint. The representative formula
is asserted for every input and time, as an equality almost everywhere. -/
def ShiftFormula (T : C0Semigroup 𝕜 (State M)) : Prop :=
  ∀ (t : ℝ≥0) (f : State M),
    (T.operators t f : ℝ → M) =ᵐ[intervalMeasure]
      fun s => if s + (t : ℝ) < 1 then f (s + t) else 0

def Contractive (T : C0Semigroup 𝕜 (State M)) : Prop :=
  ∀ t, ‖T.operators t‖ ≤ 1

def EventuallyZero (T : C0Semigroup 𝕜 (State M)) : Prop :=
  ∀ t : ℝ≥0, 1 ≤ t → T.operators t = 0

def EventuallyCompact (T : C0Semigroup 𝕜 (State M)) : Prop :=
  ∀ t : ℝ≥0, 1 ≤ t → IsCompactOperator (T.operators t)

/-- No spectral parameter admits a compact bounded two-sided resolvent. -/
def NoCompactResolvent (T : C0Semigroup 𝕜 (State M)) : Prop :=
  ∀ (ζ : 𝕜) (R : ResolventInverse (C0SemigroupSpec.generatorValue T) ζ),
    ¬ IsCompactOperator R.inverse

namespace Spec

def Construction : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (M : Type u) [NormedAddCommGroup M]
    [InnerProductSpace 𝕜 M] [CompleteSpace M],
    ∃ T : C0Semigroup 𝕜 (State M),
      ShiftFormula T ∧ Contractive T ∧ EventuallyZero T

/-- The actual right-derivative generator has a bounded inverse at 1, and
that inverse is not compact. No resolvent existence is assumed. -/
def Counterexample : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (M : Type u) [NormedAddCommGroup M]
    [InnerProductSpace 𝕜 M] [CompleteSpace M],
    ¬ FiniteDimensional 𝕜 M →
    ∃ T : C0Semigroup 𝕜 (State M),
      ShiftFormula T ∧ Contractive T ∧ EventuallyZero T ∧ EventuallyCompact T ∧
      ∃ R : ResolventInverse (C0SemigroupSpec.generatorValue T) (1 : 𝕜),
        ¬ IsCompactOperator R.inverse ∧ NoCompactResolvent T

end Spec
end ExpandedFA.Models.EventuallyZeroNoncompactResolvent
