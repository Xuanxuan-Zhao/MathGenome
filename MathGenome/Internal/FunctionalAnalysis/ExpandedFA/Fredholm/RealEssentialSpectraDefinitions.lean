import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RealEssentialSpectraDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.Definitions

/-!
Intrinsic real essential, Weyl and left/right essential spectra. All compact
real-linear perturbations are included in the Weyl intersection. Definitions
and elementary identities also apply to incomplete inner-product spaces and to
zero or finite-dimensional spaces. No real nonemptiness statement is asserted.
-/

namespace ExpandedFA.Fredholm

universe u

/-- Failure of Fredholmness over the original real scalar field. -/
def realEssentialSpectrum :
    RealEssentialSpectraDefinitionsSpec.RealOperatorSpectrumType.{u} :=
  RealEssentialSpectraDefinitionsSpec.realEssentialSpectrumValue

/-- The intersection of native real spectra over all compact real perturbations. -/
def realWeylSpectrum :
    RealEssentialSpectraDefinitionsSpec.RealOperatorSpectrumType.{u} :=
  RealEssentialSpectraDefinitionsSpec.realWeylSpectrumValue

/-- Failure of the existing real left semi-Fredholm predicate. -/
def realLeftEssentialSpectrum :
    RealEssentialSpectraDefinitionsSpec.RealOperatorSpectrumType.{u} :=
  RealEssentialSpectraDefinitionsSpec.realLeftEssentialSpectrumValue

/-- Failure of the existing real right semi-Fredholm predicate. -/
def realRightEssentialSpectrum :
    RealEssentialSpectraDefinitionsSpec.RealOperatorSpectrumType.{u} :=
  RealEssentialSpectraDefinitionsSpec.realRightEssentialSpectrumValue

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

@[simp] theorem mem_realEssentialSpectrum (T : H →L[ℝ] H) (z : ℝ) :
    z ∈ realEssentialSpectrum T ↔ ¬ IsFredholm (T - z • (1 : H →L[ℝ] H)) :=
  Iff.rfl

/-- This tests the source's exact compactness predicate in the original space. -/
theorem mem_realWeylSpectrum (T : H →L[ℝ] H) (z : ℝ) :
    z ∈ realWeylSpectrum T ↔
      ∀ K : H →L[ℝ] H, Compactness.IsCompactLinearMap K.toLinearMap →
        z ∈ spectrum ℝ (T + K) := by
  change (z ∈ ⋂ K : ↥(compactIdeal ℝ H), spectrum ℝ (T + K.val)) ↔ _
  simp only [Set.mem_iInter]
  constructor
  · intro h K hK
    exact h ⟨K, (mem_compactIdeal K).mpr hK⟩
  · intro h K
    exact h K.val ((mem_compactIdeal K.val).mp K.property)

@[simp] theorem mem_realLeftEssentialSpectrum (T : H →L[ℝ] H) (z : ℝ) :
    z ∈ realLeftEssentialSpectrum T ↔
      ¬ IsLeftSemiFredholm (T - z • (1 : H →L[ℝ] H)) :=
  Iff.rfl

@[simp] theorem mem_realRightEssentialSpectrum (T : H →L[ℝ] H) (z : ℝ) :
    z ∈ realRightEssentialSpectrum T ↔
      ¬ IsRightSemiFredholm (T - z • (1 : H →L[ℝ] H)) :=
  Iff.rfl

/-- Fredholmness is the conjunction of the two semi-Fredholm conditions. -/
theorem realEssentialSpectrum_eq_union (T : H →L[ℝ] H) :
    realEssentialSpectrum T = realLeftEssentialSpectrum T ∪ realRightEssentialSpectrum T := by
  classical
  ext z
  simp only [Set.mem_union, mem_realEssentialSpectrum, mem_realLeftEssentialSpectrum,
    mem_realRightEssentialSpectrum, fredholm_iff_left_and_right, not_and_or]

end ExpandedFA.Fredholm
