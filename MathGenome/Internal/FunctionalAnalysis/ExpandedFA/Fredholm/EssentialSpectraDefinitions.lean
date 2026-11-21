import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.EssentialSpectraDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.Definitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.Conventions

/-!
The four essential-spectrum conventions of paper.tex:10690–10701, 10718–10728.
The spectra below use the original bounded operators and all compact
perturbations. No nonzero, infinite-dimensional or separability hypothesis is
imposed. The later Calkin-spectrum and Weyl theorems have separate obligations.
-/

namespace ExpandedFA.Fredholm

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Scalars where `T - z I` fails to be Fredholm. -/
def essentialSpectrum (T : H →L[ℂ] H) : Set ℂ :=
  {z | ¬ IsFredholm (T - z • 1)}

/-- Intersection of the ordinary spectra of every compact perturbation. -/
def weylSpectrum (T : H →L[ℂ] H) : Set ℂ :=
  ⋂ (K : H →L[ℂ] H) (_ : Compactness.IsCompactLinearMap K.toLinearMap),
    BanachAlgebra.algebraSpectrum ℂ (H →L[ℂ] H) (T + K)

/-- Scalars where `T - z I` fails to have closed range and finite kernel. -/
def leftEssentialSpectrum (T : H →L[ℂ] H) : Set ℂ :=
  {z | ¬ IsLeftSemiFredholm (T - z • 1)}

/-- Scalars where `T - z I` fails to have closed range and finite cokernel. -/
def rightEssentialSpectrum (T : H →L[ℂ] H) : Set ℂ :=
  {z | ¬ IsRightSemiFredholm (T - z • 1)}

@[simp] theorem mem_essentialSpectrum (T : H →L[ℂ] H) (z : ℂ) :
    z ∈ essentialSpectrum T ↔ ¬ IsFredholm (T - z • 1) := Iff.rfl

@[simp] theorem mem_weylSpectrum (T : H →L[ℂ] H) (z : ℂ) :
    z ∈ weylSpectrum T ↔
      ∀ K : H →L[ℂ] H, Compactness.IsCompactLinearMap K.toLinearMap →
        z ∈ BanachAlgebra.algebraSpectrum ℂ (H →L[ℂ] H) (T + K) := by
  simp only [weylSpectrum, Set.mem_iInter]

@[simp] theorem mem_leftEssentialSpectrum (T : H →L[ℂ] H) (z : ℂ) :
    z ∈ leftEssentialSpectrum T ↔ ¬ IsLeftSemiFredholm (T - z • 1) := Iff.rfl

@[simp] theorem mem_rightEssentialSpectrum (T : H →L[ℂ] H) (z : ℂ) :
    z ∈ rightEssentialSpectrum T ↔ ¬ IsRightSemiFredholm (T - z • 1) := Iff.rfl

/-- Failure of Fredholmness is failure of at least one of its two sides. -/
theorem essentialSpectrum_eq_union (T : H →L[ℂ] H) :
    essentialSpectrum T = leftEssentialSpectrum T ∪ rightEssentialSpectrum T := by
  classical
  ext z
  simp only [Set.mem_union, mem_essentialSpectrum, mem_leftEssentialSpectrum,
    mem_rightEssentialSpectrum, fredholm_iff_left_and_right, not_and_or]

end ExpandedFA.Fredholm
