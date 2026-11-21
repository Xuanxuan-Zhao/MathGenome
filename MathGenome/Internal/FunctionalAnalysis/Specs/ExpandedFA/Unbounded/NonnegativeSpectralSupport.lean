import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.MeasurableSpectralCalculus

/-! Nonnegative spectral support in the Stieltjes existence arguments,
`paper.tex`, fa2:p3:stieltjes-moment and fa2:p3:stieltjes-determinacy.
The given representation is the actual maximal measurable spectral integral.
There is no restriction on the dimension or on scalar spectral masses. -/
noncomputable section

namespace ExpandedFA.Unbounded.NonnegativeSpectralSupport.Spec
universe u

/-- Quadratic nonnegativity forces both operator and scalar spectral support
on the closed nonnegative half-line. -/
def NonnegativeSupport : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : Operator ℂ H H)
    (E : SpectralMeasure.ProjectionValuedMeasure ℝ H)
    (C : MeasurableSpectralCalculus.BoundedRealization E),
    MeasurableSpectralCalculus.measurableIntegral C (fun t : ℝ => (t : ℂ)) = A →
    (∀ x : A.domain, 0 ≤ (inner ℂ (x : H) (A x)).re) →
    E (Set.Iio 0) = 0 ∧ ∀ x : H, C.measure x (Set.Iio 0) = 0

end ExpandedFA.Unbounded.NonnegativeSpectralSupport.Spec
