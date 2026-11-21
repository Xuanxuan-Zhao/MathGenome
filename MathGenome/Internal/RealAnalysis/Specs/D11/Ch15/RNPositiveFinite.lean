import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.MaximalAdmissibleDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Independent statements for the finite positive Radon–Nikodym theorem,
`paper.tex:4831–4863`. Both measures are finite on the given sigma-algebra;
no completeness, topology, or nonzero-mass assumption is imposed. The extended
nonnegative integral is the shared source integral. The real-valued statement
also supplies integrability before any use of the linear integral. -/

open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section

namespace Specs.D11.Ch15.RNPositiveFinite

open _root_.D11.Ch15.MaximalAdmissibleDensity
open Ch05.NonnegativeIntegral

/-- Every admissible maximizer has zero residual, not merely a small residual. -/
def residual_vanishes : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : X → ℝ≥0∞),
    ν ≪ μ → admissible μ ν h →
    (∫⁻ x, h x ∂μ) = supremumIntegral μ ν → residualMeasure μ ν h = 0

/-- Reconstruction on every original measurable set, with finite total integral
and a representative that is finite at every point. -/
def rn_positive_finite : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν], ν ≪ μ →
    ∃ h : X → ℝ≥0∞, Measurable h ∧ (∀ x, h x < ∞) ∧
      nonnegativeIntegral_value μ h < ∞ ∧
      ∀ E, MeasurableSet E →
        ν E = nonnegativeIntegral_value (μ.restrict E) h

/-- Uniqueness covers all measurable extended nonnegative densities, including
ones that are only finite almost everywhere. -/
def density_unique : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h k : X → ℝ≥0∞),
    Measurable h → Measurable k →
    (∀ E, MeasurableSet E →
      ν E = nonnegativeIntegral_value (μ.restrict E) h) →
    (∀ E, MeasurableSet E →
      ν E = nonnegativeIntegral_value (μ.restrict E) k) → h =ᵐ[μ] k

/-- The finite-everywhere density is literally a nonnegative real measurable
L¹ function. Both the nonnegative and the linear integral reconstruct ν. -/
def rn_positive_finite_real : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν], ν ≪ μ →
    ∃ h : X → ℝ, Measurable h ∧ (∀ x, 0 ≤ h x) ∧ Integrable h μ ∧
      (∀ E, MeasurableSet E →
        ν E = nonnegativeIntegral_value (μ.restrict E) (fun x => ENNReal.ofReal (h x))) ∧
      ∀ E, MeasurableSet E → ν E = ENNReal.ofReal (∫ x in E, h x ∂μ)

def real_density_unique : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h k : X → ℝ),
    Measurable h → Measurable k → (∀ x, 0 ≤ h x) → (∀ x, 0 ≤ k x) →
    Integrable h μ → Integrable k μ →
    (∀ E, MeasurableSet E → ν E = ENNReal.ofReal (∫ x in E, h x ∂μ)) →
    (∀ E, MeasurableSet E → ν E = ENNReal.ofReal (∫ x in E, k x ∂μ)) → h =ᵐ[μ] k

end Specs.D11.Ch15.RNPositiveFinite
