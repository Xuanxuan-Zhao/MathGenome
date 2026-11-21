import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.MeasurableSpectralCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Scalar moments of the actual real spectral measure, as used in the
Hamburger and Stieltjes constructions (paper.tex 15466–15474, 16274–16284).
No normalization, positive mass, separability or bounded support is imposed. -/
noncomputable section
open MeasureTheory

namespace ExpandedFA.Unbounded.ScalarSpectralMoments.Spec
universe u

/-- All powers use the shared partial operator, with its domain witnesses. -/
def ScalarMoments : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : Operator ℂ H H) (E : SpectralMeasure.ProjectionValuedMeasure ℝ H)
    (C : MeasurableSpectralCalculus.BoundedRealization E),
    MeasurableSpectralCalculus.measurableIntegral C (fun t : ℝ => (t : ℂ)) = A →
    ∀ (e : H) (he : ∀ n : ℕ, e ∈ (OperatorDomainsSpec.powerValue A n).domain),
      IsFiniteMeasure (C.measure e) ∧ ∀ n : ℕ,
        Integrable (fun t : ℝ => t ^ n) (C.measure e) ∧
        (∫ t : ℝ, t ^ n ∂C.measure e) =
          (inner ℂ e (OperatorDomainsSpec.powerValue A n ⟨e, he n⟩)).re

end ExpandedFA.Unbounded.ScalarSpectralMoments.Spec
