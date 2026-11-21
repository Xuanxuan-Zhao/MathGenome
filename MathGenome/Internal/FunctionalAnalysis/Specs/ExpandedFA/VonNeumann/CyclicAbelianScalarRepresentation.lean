import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.ScalarMultiplicationCommutant
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.Subalgebra

/-! The conditional cyclic scalar representation used in
`fa2:p2:abelian-von-neumann`. Closedness is in the original operator norm.
No separability, nonzero vector, or positive total mass is required. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.VonNeumann.CyclicAbelianScalarRepresentation.Spec
universe u

/-- Every norm-closed abelian concrete unital star algebra with a supplied
cyclic vector admits a surjective scalar multiplication representation. -/
def CyclicScalarRepresentation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)),
    (∀ S ∈ A, ∀ T ∈ A, S * T = T * S) →
    IsClosed (A : Set (H →L[ℂ] H)) →
    ∀ e : H, DenseRange (fun a : A => (a : H →L[ℂ] H) e) →
    ∃ (X : Type u) (_ : MeasurableSpace X) (μ : Measure X) (hμ : IsFiniteMeasure μ),
      letI := hμ
      ∃ U : H ≃ₗᵢ[ℂ] Lp ℂ 2 μ,
        ∀ T ∈ A, ∃ h : Lp ℂ ∞ μ, ∀ x : H,
          U (T x) = ScalarMultiplicationCommutant.Spec.multiplier μ h (U x)

end ExpandedFA.VonNeumann.CyclicAbelianScalarRepresentation.Spec
