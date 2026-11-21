import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.NonnegativeIntegral
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-! Independent statements for the sigma-finite positive Radon–Nikodym theorem
of `paper.tex:4861–4874`. Both measures live on the original measurable space.
The set integrals use the shared source nonnegative integral, with values in
[0,∞]; no finiteness of the total integral or completeness is required. -/

open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section

namespace Specs.D11.Ch15.RNPositiveSigmaFinite

open Ch05.NonnegativeIntegral

def rn_positive_sigmafinite : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [SigmaFinite μ] [SigmaFinite ν], ν ≪ μ →
    ∃ h : X → ℝ≥0∞, Measurable h ∧ (∀ᵐ x ∂μ, h x < ∞) ∧
      ∀ E, MeasurableSet E →
        ν E = nonnegativeIntegral_value (μ.restrict E) h

/-- The measurable density can be selected finite at every point. -/
def rn_positive_sigmafinite_finite_everywhere : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [SigmaFinite μ] [SigmaFinite ν], ν ≪ μ →
    ∃ h : X → ℝ≥0∞, Measurable h ∧ (∀ x, h x < ∞) ∧
      ∀ E, MeasurableSet E →
        ν E = nonnegativeIntegral_value (μ.restrict E) h

/-- All measurable extended nonnegative densities are unique a.e.; the
competitors are not assumed to have finite total integrals. -/
def density_unique : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [SigmaFinite μ] [SigmaFinite ν] (h k : X → ℝ≥0∞),
    Measurable h → Measurable k →
    (∀ E, MeasurableSet E →
      ν E = nonnegativeIntegral_value (μ.restrict E) h) →
    (∀ E, MeasurableSet E →
      ν E = nonnegativeIntegral_value (μ.restrict E) k) → h =ᵐ[μ] k

/-- A finite representative is also an ordinary nonnegative real function.
The extended nonnegative integral remains appropriate on infinite-mass sets. -/
def rn_positive_sigmafinite_real : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [SigmaFinite μ] [SigmaFinite ν], ν ≪ μ →
    ∃ h : X → ℝ, Measurable h ∧ (∀ x, 0 ≤ h x) ∧
      ∀ E, MeasurableSet E →
        ν E = nonnegativeIntegral_value (μ.restrict E) (fun x => ENNReal.ofReal (h x))

end Specs.D11.Ch15.RNPositiveSigmaFinite
