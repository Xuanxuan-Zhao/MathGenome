import MathGenome.Internal.FourierSobolev.Specs.P102.U3.SchwartzFourier

/-! Independent statements for Fourier inversion, paper.tex:1066–1076.
The function-space Fourier instances are the integral transforms on standard
Euclidean volume: `Real.fourier_eq'` has exponential -2πi⟪x,ξ⟫ and
`Real.fourierInv_eq'` has exponential +2πi⟪ξ,x⟫. Integrability is imposed on
the arbitrary chosen representative, with no continuity assumption for the
a.e. assertion. All natural dimensions, including zero, are quantified. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace P102.Specs.U3.FourierInversion

def l1Inversion_type : Prop :=
  ∀ (d : ℕ) (f : Euclidean d → ℂ),
    Integrable f → Integrable (𝓕 f) →
      Continuous (𝓕⁻ (𝓕 f)) ∧
      (𝓕⁻ (𝓕 f) =ᵐ[volume] f) ∧
      ∀ x, ContinuousAt f x → 𝓕⁻ (𝓕 f) x = f x

/-- The maps are already bundled as continuous complex-linear maps. The two
composition identities imply equality at every point of every Schwartz function. -/
def schwartzInversion_type : Prop :=
  ∀ d : ℕ,
    (checkValue d).comp (fourierValue d) = ContinuousLinearMap.id ℂ (Test d) ∧
    (fourierValue d).comp (checkValue d) = ContinuousLinearMap.id ℂ (Test d) ∧
    Continuous (fourierValue d) ∧ Continuous (checkValue d)

end P102.Specs.U3.FourierInversion
