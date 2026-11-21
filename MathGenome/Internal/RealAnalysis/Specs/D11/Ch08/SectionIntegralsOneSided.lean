import MathGenome.Internal.RealAnalysis.Specs.D11.Ch08.Sections
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral

/-!
Independent statements for `D11.08.section_integrals_one_sided`,
paper.tex:2550–2578. The product measurable space is the ordinary product
`m.prod n`, as identified with rectangle generation in the upstream Specs.
Only Y carries a measure, and only that measure is assumed sigma-finite.
There is no completion, nonemptiness, or finite-total-mass assumption.

The function conclusion uses the shared source integral, defined as the
supremum of the integrals of finite nonnegative simple minorants.
-/

open Set MeasureTheory
open scoped ENNReal

universe u v

noncomputable section

namespace Specs.D11.Ch08.SectionIntegralsOneSided

/-- Measurability of section masses at every parameter. -/
def section_measure_measurable : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure Y), SigmaFinite ν →
    ∀ E : Set (X × Y), MeasurableSet E →
      Measurable (fun x : X => ν {y : Y | (x, y) ∈ E})

/-- Measurability of the extended nonnegative section integral. -/
def section_integral_measurable : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure Y), SigmaFinite ν →
    ∀ f : X × Y → ℝ≥0∞, Measurable f →
      Measurable (fun x : X =>
        _root_.Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value ν
          (fun y : Y => f (x, y)))

end Specs.D11.Ch08.SectionIntegralsOneSided
