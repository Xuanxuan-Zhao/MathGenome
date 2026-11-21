import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.ApproximateSpectrumBoundary
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.SemiFredholmPerturbations

/-! Full independent statements of `fa2:p2:local-spectrum`, paper.tex 10718–10761.
The local Hilbert alternatives are stated for both scalar fields. Dimensions
are extended natural dimensions over the original field of the kernel and the
quotient by the actual range. The real conclusions use punctured intervals and
the intrinsic real spectrum and frontier. No separability or nonzero-space
assumption is imposed. -/
namespace ExpandedFA.Fredholm.LocalSpectralAlternatives.Spec

open Set
universe u v w

abbrev UnitSequence : Prop := Specs.ExpandedFA.Fredholm.ApproximateSpectrumBoundary.UnitSequence.{u}
abbrev ClosedRangeComplement : Prop :=
  Specs.ExpandedFA.Fredholm.ApproximateSpectrumBoundary.ClosedRangeComplement.{u}
abbrev BoundaryInclusion : Prop :=
  Specs.ExpandedFA.Fredholm.ApproximateSpectrumBoundary.BoundaryInclusion.{u}

abbrev Perturbation : Prop := SemiFredholmPerturbations.Spec.Perturbation.{u,v,w}

/-- Constancy on one common punctured disk, including infinite defects.
The conclusion also records semi-Fredholmness throughout that disk. -/
def PuncturedConstancy : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (z : ℂ),
    DefinitionsSpec.IsSemiFredholmValue (T - z • (1 : H →L[ℂ] H)) →
    ∃ r : ℝ, 0 < r ∧ ∃ n d : ℕ∞, ∀ w : ℂ, w ≠ z → ‖w - z‖ < r →
      DefinitionsSpec.IsSemiFredholmValue (T - w • (1 : H →L[ℂ] H)) ∧
      (Module.rank ℂ (T - w • (1 : H →L[ℂ] H)).ker).toENat = n ∧
      (Module.rank ℂ (H ⧸ (T - w • (1 : H →L[ℂ] H)).range)).toENat = d

/-- The two essential spectra mean failure of left and right
semi-Fredholmness, respectively. Isolation is written explicitly as a spectral
disk with no other spectral point. -/
def BoundaryAlternative : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (z : ℂ), z ∈ frontier (spectrum ℂ T) →
    (∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, w ∈ spectrum ℂ T → ‖w - z‖ < r → w = z) ∨
    (¬ DefinitionsSpec.IsLeftSemiFredholmValue (T - z • (1 : H →L[ℂ] H)) ∧
     ¬ DefinitionsSpec.IsRightSemiFredholmValue (T - z • (1 : H →L[ℂ] H)))

abbrev RealUnitSequence : Prop :=
  Specs.ExpandedFA.Fredholm.ApproximateSpectrumBoundary.RealUnitSequence.{u}
abbrev RealClosedRangeComplement : Prop :=
  Specs.ExpandedFA.Fredholm.ApproximateSpectrumBoundary.RealClosedRangeComplement.{u}
abbrev RealBoundaryInclusion : Prop :=
  Specs.ExpandedFA.Fredholm.ApproximateSpectrumBoundary.RealBoundaryInclusion.{u}

/-- Real nullity and deficiency are constant on one common punctured real
neighborhood. The original real Hilbert space and actual range quotient are used,
and infinite defects are included. -/
def RealPuncturedConstancy : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (z : ℝ),
    DefinitionsSpec.IsSemiFredholmValue (T - z • (1 : H →L[ℝ] H)) →
    ∃ r : ℝ, 0 < r ∧ ∃ n d : ℕ∞, ∀ w : ℝ, w ≠ z → ‖w - z‖ < r →
      DefinitionsSpec.IsSemiFredholmValue (T - w • (1 : H →L[ℝ] H)) ∧
      (Module.rank ℝ (T - w • (1 : H →L[ℝ] H)).ker).toENat = n ∧
      (Module.rank ℝ (H ⧸ (T - w • (1 : H →L[ℝ] H)).range)).toENat = d

/-- The boundary and isolation are intrinsic to ℝ. The second alternative is
failure of both original real left and right semi-Fredholm predicates. -/
def RealBoundaryAlternative : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (z : ℝ), z ∈ frontier (spectrum ℝ T) →
    (∃ r : ℝ, 0 < r ∧ ∀ w : ℝ, w ∈ spectrum ℝ T → ‖w - z‖ < r → w = z) ∨
    (¬ DefinitionsSpec.IsLeftSemiFredholmValue (T - z • (1 : H →L[ℝ] H)) ∧
     ¬ DefinitionsSpec.IsRightSemiFredholmValue (T - z • (1 : H →L[ℝ] H)))

end ExpandedFA.Fredholm.LocalSpectralAlternatives.Spec
