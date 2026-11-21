import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.BohrMollerup
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Convexity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.GammaRecurrence
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The Bohr–Mollerup characterization of the source's improper Gamma integral.

Proof provenance: Mathlib's `Real.eq_Gamma_of_log_convex` proves uniqueness
on the whole positive half-line by the Euler squeeze, followed by recurrence.
Its hypotheses are exactly the source hypotheses, converted through the
upstream equivalence of the literal convexity formula with `ConvexOn`.
`gamma_eq_realGamma` transfers the conclusion to the source integral, whose
independent improper Riemann limits have already been established upstream.
The explicit multiplier 2 - cos(2*pi*x) shows the failure of uniqueness
when log convexity is omitted.
-/
noncomputable section
namespace SingleVariableAnalysis.SpecialIntegrals
namespace BM
export Specs.SingleVariableAnalysis.Ch18.BohrMollerup
  (gammaExtension multiplierValue)
end BM

private theorem gammaExtension_eq (x : ℝ) (hx : 0 < x) :
    BM.gammaExtension x =
      Specs.SingleVariableAnalysis.Ch18.GammaDefinition.gammaIntegralValue x hx := by
  simp [BM.gammaExtension, hx]

theorem bohr_mollerup :
    Specs.SingleVariableAnalysis.Ch18.BohrMollerup.uniqueness := by
  intro F hF x hx
  have hc : ConvexOn ℝ (Set.Ioi 0) (Real.log ∘ F) :=
    (convexFunctionOn_iff_convexOn _ Set.ordConnected_Ioi _).mp hF.2.2.2
  exact (Real.eq_Gamma_of_log_convex hc (fun hy => hF.2.2.1 _ hy)
    (fun hy => hF.1 _ hy) hF.2.1 hx).trans (gamma_eq_realGamma x hx).symm

theorem gamma_bohr_mollerup_properties :
    Specs.SingleVariableAnalysis.Ch18.BohrMollerup.gammaSatisfies := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [gammaExtension_eq x hx]
    exact gamma_positive x hx
  · rw [gammaExtension_eq 1 zero_lt_one]
    exact gamma_at_one
  · intro x hx
    rw [gammaExtension_eq (x + 1) (add_pos hx zero_lt_one), gammaExtension_eq x hx]
    exact gamma_recurrence x hx
  · change ConvexFunctionOn (Set.Ioi 0) (fun x => Real.log (BM.gammaExtension x))
    apply (convexFunctionOn_iff_convexOn _ Set.ordConnected_Ioi _).mpr
    apply Real.convexOn_log_Gamma.congr
    intro x hx
    simp only [Function.comp_apply]
    rw [gammaExtension_eq x hx, gamma_eq_realGamma x hx]

def bohrMollerupMultiplier : ℝ → ℝ := BM.multiplierValue

private theorem multiplier_one : BM.multiplierValue 1 = 1 := by
  change 2 - Real.cos (2 * Real.pi * 1) = 1
  rw [mul_one, Real.cos_two_pi]
  norm_num

private theorem multiplier_half : BM.multiplierValue (1 / 2) = 3 := by
  have h : 2 * Real.pi * (1 / 2) = Real.pi := by ring
  change 2 - Real.cos (2 * Real.pi * (1 / 2)) = 3
  rw [h, Real.cos_pi]
  norm_num

private theorem multiplier_positive (x : ℝ) : 0 < BM.multiplierValue x := by
  have h := Real.cos_le_one (2 * Real.pi * x)
  dsimp [BM.multiplierValue]
  linarith

private theorem multiplier_periodic : Function.Periodic BM.multiplierValue 1 := by
  intro x
  have h : 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi := by ring
  simp [BM.multiplierValue, h, Real.cos_add_two_pi]

theorem bohr_mollerup_multiplier_properties :
    Specs.SingleVariableAnalysis.Ch18.BohrMollerup.multiplierProperties := by
  refine ⟨multiplier_positive, multiplier_periodic, multiplier_one, 1 / 2, 1,
    by norm_num, zero_lt_one, ?_⟩
  rw [multiplier_half, multiplier_one]
  norm_num

theorem gamma_recurrence_not_unique :
    Specs.SingleVariableAnalysis.Ch18.BohrMollerup.recurrenceNotUnique := by
  dsimp only [Specs.SingleVariableAnalysis.Ch18.BohrMollerup.recurrenceNotUnique]
  refine ⟨?_, ?_, ?_, 1 / 2, by norm_num, ?_⟩
  · intro x hx
    exact mul_pos (gamma_bohr_mollerup_properties.1 x hx) (multiplier_positive x)
  · rw [gamma_bohr_mollerup_properties.2.1, multiplier_one, mul_one]
  · intro x hx
    rw [gamma_bohr_mollerup_properties.2.2.1 x hx, multiplier_periodic x]
    ring
  · rw [gammaExtension_eq (1 / 2) (by norm_num), multiplier_half]
    have h := gamma_positive (1 / 2) (by norm_num)
    nlinarith

end SingleVariableAnalysis.SpecialIntegrals
