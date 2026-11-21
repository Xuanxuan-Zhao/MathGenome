import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.Complex.Exponential

/-! The general spectral inclusion in paper.tex, fa2:p3:adjoint-semigroup.
The generator spectrum uses the exact right-derivative domain and bounded
two-sided inverses. The time-operator spectrum is the usual Banach-algebra
spectrum over the original scalar field. The complex and real clauses concern
their actual complex and real Banach spaces, respectively. -/

noncomputable section
open scoped NNReal

namespace ExpandedFA.Semigroups.SpectralInclusionSpec

/-- Every complex Banach C₀ semigroup, every positive time, and the full
 generator spectrum. No spectral mapping equality is asserted. -/
def SpectralInclusion : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : C0Semigroup ℂ X) (t : ℝ≥0), 0 < t →
    (fun ζ : ℂ => Complex.exp ((t : ℝ) • ζ)) ''
      C0SemigroupSpec.spectrumValue (C0SemigroupSpec.generatorValue T) ⊆
    _root_.spectrum ℂ (T.operators t) \ {0}

/-- The original real-scalar conclusion on every real Banach space, using
the same exact generator domain and real bounded two-sided inverses. -/
def RealSpectralInclusion : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : C0Semigroup ℝ X) (t : ℝ≥0), 0 < t →
    (fun ζ : ℝ => Real.exp ((t : ℝ) * ζ)) ''
      C0SemigroupSpec.spectrumValue (C0SemigroupSpec.generatorValue T) ⊆
    _root_.spectrum ℝ (T.operators t) \ {0}

end ExpandedFA.Semigroups.SpectralInclusionSpec
