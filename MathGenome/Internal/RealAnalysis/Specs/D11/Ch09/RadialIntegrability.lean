import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.PolarMeasure

/-! Radial power tests, paper.tex:3204–3218. `Point n` carries the Euclidean
norm and `lebesgue_value n` is the shared completed Lebesgue measure.
All positive dimensions, including one, are quantified. The infinite integrals
are nonnegative extended integrals, so no totalized scalar integral is used. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Specs.D11.Ch09.RadialIntegrability
open _root_.D11.Ch03 _root_.D11.Ch09.PolarMeasure
open Specs.D11.Ch03.LebesgueMeasures
open Specs.D11.Ch09.PolarMeasure

def near_integrable : Prop := ∀ n [NeZero n] (R α : ℝ), 0 < R →
  letI := lebesgueSpace_value n
  IntegrableOn (fun x : Point n => ‖x‖ ^ (-α))
    {x | 0 < ‖x‖ ∧ ‖x‖ < R} (lebesgue_value n) ↔ α < (n : ℝ)

def exterior_integrable : Prop := ∀ n [NeZero n] (R α : ℝ), 0 < R →
  letI := lebesgueSpace_value n
  IntegrableOn (fun x : Point n => ‖x‖ ^ (-α))
    {x | R < ‖x‖} (lebesgue_value n) ↔ (n : ℝ) < α

def near_threshold_infinite : Prop := ∀ n [NeZero n] (R : ℝ), 0 < R →
  letI := lebesgueSpace_value n
  (∫⁻ x : Point n in {x | 0 < ‖x‖ ∧ ‖x‖ < R},
    ENNReal.ofReal (‖x‖ ^ (-(n : ℝ))) ∂lebesgue_value n) = ∞

def exterior_threshold_infinite : Prop := ∀ n [NeZero n] (R : ℝ), 0 < R →
  letI := lebesgueSpace_value n
  (∫⁻ x : Point n in {x | R < ‖x‖},
    ENNReal.ofReal (‖x‖ ^ (-(n : ℝ))) ∂lebesgue_value n) = ∞

/-- The angular factor used in radial integration is finite and strictly positive. -/
def angular_mass_pos_finite : Prop := ∀ n [NeZero n],
  0 < angularMeasure_value n univ ∧ angularMeasure_value n univ < ∞

end Specs.D11.Ch09.RadialIntegrability
