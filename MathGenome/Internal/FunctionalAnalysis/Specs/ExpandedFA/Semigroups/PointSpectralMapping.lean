import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator

/-! Independent statement of the point spectral mapping assertion in
paper.tex, Theorem `fa2:p3:semigroup-spectral-mapping` (14557–14559).
Both spectra mean existence of an actual nonzero eigenvector. The generator
uses its exact right-derivative domain; no compactness or norm continuity
is part of the hypotheses. -/
noncomputable section
open scoped NNReal

namespace ExpandedFA.Semigroups.PointSpectralMappingSpec

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Point spectrum of a bounded complex-linear operator. -/
def operatorPointSpectrum (B : X →L[ℂ] X) : Set ℂ :=
  {z | ∃ x : X, x ≠ 0 ∧ B x = z • x}

/-- Point spectrum of an operator with its specified linear domain. -/
def generatorPointSpectrum (A : Unbounded.Operator ℂ X X) : Set ℂ :=
  {ζ | ∃ x : A.domain, (x : X) ≠ 0 ∧ A x = ζ • (x : X)}

/-- Equality as sets, including both directions and omission of zero only
from the time-operator side. The zero Banach space is allowed. -/
def PointSpectralMapping : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : C0Semigroup ℂ X) (t : ℝ≥0), 0 < t →
    operatorPointSpectrum (T.operators t) \ {0} =
      (fun ζ : ℂ => Complex.exp ((t : ℂ) * ζ)) ''
        generatorPointSpectrum (C0SemigroupSpec.generatorValue T)

end ExpandedFA.Semigroups.PointSpectralMappingSpec
