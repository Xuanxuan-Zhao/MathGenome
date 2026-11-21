import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.AbsoluteContinuity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.DensityMeasureDomains
import Mathlib.MeasureTheory.Measure.Sub

/-! Independent specification of the maximizing-density stage of
`paper.tex:4831–4848`. The extended nonnegative integral is the native lower
integral, identified with the shared source integral by the upstream bridge.
All setwise assertions test the original sigma-algebra. No completion,
nonzero-mass assumption, or vanishing-residual certificate is introduced. -/

open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section

namespace D11.Ch15.MaximalAdmissibleDensity

/-- The measurable admissible nonnegative densities of the source proof. -/
def admissible {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    (g : X → ℝ≥0∞) : Prop :=
  Measurable g ∧ ∀ E, MeasurableSet E → (∫⁻ x in E, g x ∂μ) ≤ ν E

/-- The supremum is taken over all admissible total integrals. -/
def supremumIntegral {X : Type u} [MeasurableSpace X] (μ ν : Measure X) : ℝ≥0∞ :=
  sSup {a | ∃ g : X → ℝ≥0∞, admissible μ ν g ∧ (∫⁻ x, g x ∂μ) = a}

/-- Under admissibility and finite target mass this has precisely the
setwise difference prescription; that fact is an obligation below. -/
def residualMeasure {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    (h : X → ℝ≥0∞) : Measure X := ν - μ.withDensity h

end D11.Ch15.MaximalAdmissibleDensity

namespace Specs.D11.Ch15.MaximalAdmissibleDensity
open _root_.D11.Ch15.MaximalAdmissibleDensity

/-- Explicit interpretation in terms of the canonical source integral. -/
def admissible_iff_source : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X) (g : X → ℝ≥0∞),
    admissible μ ν g ↔ Measurable g ∧ ∀ E, MeasurableSet E →
      Ch05.NonnegativeIntegral.nonnegativeIntegral_value (μ.restrict E) g ≤ ν E

def zero_admissible : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X),
    admissible μ ν (fun _ => 0)

def max_admissible : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X) (f g : X → ℝ≥0∞),
    admissible μ ν f → admissible μ ν g →
      admissible μ ν (fun x => max (f x) (g x))

/-- Finite maxima include the empty maximum, interpreted as zero. -/
def finite_max_admissible : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {ι : Type*} (μ ν : Measure X)
    (s : Finset ι) (f : ι → X → ℝ≥0∞),
    (∀ i ∈ s, admissible μ ν (f i)) →
      admissible μ ν (fun x => s.sup (fun i => f i x))

def supremum_bound : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X),
    supremumIntegral μ ν ≤ ν univ

/-- This construction even works for arbitrary reference measure and finite ν.
The finite μ and ν ≪ μ hypotheses are retained on the assembled source result. -/
def exists_maximizer : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure ν],
    ∃ h : X → ℝ≥0∞, admissible μ ν h ∧
      (∫⁻ x, h x ∂μ) = supremumIntegral μ ν ∧
      (∀ᵐ x ∂μ, h x < ∞)

def residual_properties : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X) [IsFiniteMeasure ν]
    (h : X → ℝ≥0∞), admissible μ ν h → ν ≪ μ →
      IsFiniteMeasure (residualMeasure μ ν h) ∧ residualMeasure μ ν h ≪ μ ∧
      (∀ E, MeasurableSet E →
        residualMeasure μ ν h E = ν E - ∫⁻ x in E, h x ∂μ) ∧
      residualMeasure μ ν h + μ.withDensity h = ν

/-- The complete assigned construction, including zero μ and empty spaces.
No assertion that the residual vanishes is included. -/
def maximal_admissible_density : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν], ν ≪ μ →
    ∃ h : X → ℝ≥0∞, admissible μ ν h ∧
      (∫⁻ x, h x ∂μ) = supremumIntegral μ ν ∧
      supremumIntegral μ ν ≤ ν univ ∧ (∀ᵐ x ∂μ, h x < ∞) ∧
      IsFiniteMeasure (residualMeasure μ ν h) ∧ residualMeasure μ ν h ≪ μ ∧
      (∀ E, MeasurableSet E →
        residualMeasure μ ν h E = ν E - ∫⁻ x in E, h x ∂μ) ∧
      residualMeasure μ ν h + μ.withDensity h = ν

end Specs.D11.Ch15.MaximalAdmissibleDensity
