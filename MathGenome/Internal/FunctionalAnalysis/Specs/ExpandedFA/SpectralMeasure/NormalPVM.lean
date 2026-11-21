import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.ContinuousNormalCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RepresentationPVM

/-!
Existence and uniqueness in `fa2:p2:normal-spectral`, paper.tex 12429–12454.
The spectrum is the actual complex algebraic spectrum in B(H). The integral
identity is expressed by all scalar coefficients, using finite regular complex
measures, so no single scalar control measure is posited. Equality of PVMs
means equality on Borel sets, as in the shared PVM interface. H can be zero.
-/
noncomputable section
open scoped InnerProductSpace
open MeasureTheory Set

namespace ExpandedFA.SpectralMeasure.NormalPVM.Spec
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A regular Borel PVM resolving N: its coefficient measures are finite
regular measures and the integral of the coordinate is N. This assumes no
continuous-calculus representation or uniqueness of E. -/
def Resolves (N : H →L[ℂ] H) (E : ProjectionValuedMeasure (spectrum ℂ N) H) : Prop :=
  ∃ μ : H → H → ComplexMeasure (spectrum ℂ N),
    (∀ x y, FunctionSpaces.ScalarRieszMarkovSpec.FiniteScalarRadon (μ x y)) ∧
    (∀ x y B, MeasurableSet B → μ x y B = ⟪x, E B y⟫_ℂ) ∧
    (∀ x y, Integrable (fun z : spectrum ℂ N => (z : ℂ)) (μ x y).variation ∧
      ⟪x, N y⟫_ℂ = FunctionSpaces.ScalarRieszMarkovSpec.scalarIntegral
        (μ x y) (fun z : spectrum ℂ N => (z : ℂ)))

/-- The unique regular Borel resolution of every bounded normal operator on
an arbitrary complex Hilbert space, with no nontriviality/separability premise. -/
def NormalSpectralTheorem : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsStarNormal N →
    ∃ E : ProjectionValuedMeasure (spectrum ℂ N) H,
      Resolves N E ∧ ∀ F : ProjectionValuedMeasure (spectrum ℂ N) H,
        Resolves N F → ∀ B, MeasurableSet B → F B = E B

/-- In the zero space the operator algebra is zero, the spectrum is empty,
and the resolution takes the zero value on every Borel set. -/
def ZeroSpace : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Subsingleton H] (N : H →L[ℂ] H),
    spectrum ℂ N = ∅ ∧
      ∃ E : ProjectionValuedMeasure (spectrum ℂ N) H,
        Resolves N E ∧ ∀ B, MeasurableSet B → E B = 0

end ExpandedFA.SpectralMeasure.NormalPVM.Spec
