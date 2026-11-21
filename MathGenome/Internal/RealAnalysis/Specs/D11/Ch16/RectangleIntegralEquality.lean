import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.DarbouxIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.LebesgueCompletion
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-! The compact rectangle part of paper.tex:5108–5126.
The existing calculus objects use closed coordinate rectangles with ordered
endpoints, arbitrary finite coordinate partitions, and the common lower/upper
Darboux value. They admit zero side lengths. Their ambient Euclidean space is
literally the `Point n` used for D11 volume. Functions have no imposed values
outside the rectangle; the zero extension is used only to express integration
on that domain. Positive dimensions follow the paper's standing convention.
-/
noncomputable section
open Set MeasureTheory
namespace Specs.D11.Ch16.RectangleIntegralEquality

open Specs.D04.C06.DarbouxIntegral.Model

abbrev completedSpace (n : ℕ) :=
  Specs.D11.Ch02.Completion.completedSpace_value (volume : Measure (E n))

abbrev completedMeasure (n : ℕ) : @Measure (E n) (completedSpace n) :=
  Specs.D11.Ch02.Completion.completedMeasure_value (volume : Measure (E n))

/-- Actual measurability, absolute integrability and equality of values for
all bounded real Riemann-integrable representatives. -/
def real_rectangle_equality : Prop :=
  ∀ (n : ℕ) [NeZero n] (Q : Box n) (f : E n → ℝ) (hR : Integrable f Q),
    ∃ hL : @Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
      (E n) ℝ (completedSpace n) _ (borel ℝ) inferInstance
      (completedMeasure n) ((carrier Q).indicator f),
      integral f Q hR = @Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value
        (E n) ℝ (completedSpace n) _ (borel ℝ) inferInstance
        (completedMeasure n) ((carrier Q).indicator f) hL

/-- Complex Riemann integrability and its value are componentwise, as in the
source. The two hypotheses concern the original representative. -/
def complex_rectangle_equality : Prop :=
  ∀ (n : ℕ) [NeZero n] (Q : Box n) (f : E n → ℂ)
    (hr : Integrable (fun x => (f x).re) Q)
    (hi : Integrable (fun x => (f x).im) Q),
    ∃ hL : @Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
      (E n) ℂ (completedSpace n) _ (borel ℂ) inferInstance
      (completedMeasure n) ((carrier Q).indicator f),
      (integral (fun x => (f x).re) Q hr : ℂ) +
        (integral (fun x => (f x).im) Q hi : ℂ) * Complex.I =
      @Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value
        (E n) ℂ (completedSpace n) _ (borel ℂ) inferInstance
        (completedMeasure n) ((carrier Q).indicator f) hL

/-- Any bounded values on a zero-volume rectangle are admitted. -/
def real_degenerate : Prop :=
  ∀ (n : ℕ) [NeZero n] (Q : Box n), Degenerate Q →
    ∀ (f : E n → ℝ), Bounded f Q →
      ∃ hR : Integrable f Q,
      ∃ hL : @Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
        (E n) ℝ (completedSpace n) _ (borel ℝ) inferInstance
        (completedMeasure n) ((carrier Q).indicator f),
        integral f Q hR = 0 ∧
        @Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value
          (E n) ℝ (completedSpace n) _ (borel ℝ) inferInstance
          (completedMeasure n) ((carrier Q).indicator f) hL = 0

def complex_degenerate : Prop :=
  ∀ (n : ℕ) [NeZero n] (Q : Box n), Degenerate Q →
    ∀ (f : E n → ℂ), Bounded (fun x => (f x).re) Q →
      Bounded (fun x => (f x).im) Q →
      ∃ hr : Integrable (fun x => (f x).re) Q,
      ∃ hi : Integrable (fun x => (f x).im) Q,
      ∃ hL : @Specs.D11.Ch06.ScalarIntegral.scalarIntegrable_value
        (E n) ℂ (completedSpace n) _ (borel ℂ) inferInstance
        (completedMeasure n) ((carrier Q).indicator f),
        (integral (fun x => (f x).re) Q hr : ℂ) +
          (integral (fun x => (f x).im) Q hi : ℂ) * Complex.I = 0 ∧
        @Specs.D11.Ch06.ScalarIntegral.scalarIntegral_value
          (E n) ℂ (completedSpace n) _ (borel ℂ) inferInstance
          (completedMeasure n) ((carrier Q).indicator f) hL = 0

/-- In particular every lower-dimensional coordinate face, also an internal
partition face, is measurable and null for completed n-dimensional volume. -/
def coordinate_faces_null : Prop :=
  ∀ (n : ℕ) [NeZero n] (Q : Box n) (i : Fin n) (t : ℝ),
    MeasurableSet[completedSpace n] {x ∈ carrier Q | x i = t} ∧
      completedMeasure n {x ∈ carrier Q | x i = t} = 0

end Specs.D11.Ch16.RectangleIntegralEquality
