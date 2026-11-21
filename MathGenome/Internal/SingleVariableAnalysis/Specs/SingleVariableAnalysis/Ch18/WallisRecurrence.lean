import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.PiPeriod
import Mathlib.Data.Nat.Choose.Basic

/-!
K03.18.wallis, paper.tex:4206–4231, finite-integral part.
The canonical sine and π agree with the upstream series and first-zero
constructions; `seriesRepresentation` explicitly retains this identification.
The value below is the lower Darboux integral of the continuous sine power.
`integrability` requires proper Darboux integrability and identifies its value,
so no total integral of nonintegrable data is used as an existence claim.
The product and asymptotic limits are separately allocated downstream.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch18.WallisRecurrence
open Ch08.Integral Ch08.DarbouxSums

def sinePower (n : ℕ) (x : ℝ) : ℝ := Real.sin x ^ n

theorem sinePowerBounded (n : ℕ) : boundedOnIntervalValue (sinePower n) 0 (Real.pi / 2) :=
  ⟨(isCompact_Icc.image (Real.continuous_sin.pow n)).bddBelow,
    (isCompact_Icc.image (Real.continuous_sin.pow n)).bddAbove⟩

def integralType : Type := ℕ → ℝ
def integralValue : integralType := fun n =>
  lowerIntegralValue (sinePower n) Real.pi_div_two_pos.le (sinePowerBounded n)

def coefficientType : Type := ℕ → ℝ
def coefficientValue : coefficientType := fun n => (Nat.choose (2 * n) n : ℝ) / 4 ^ n

def integrability : Prop := ∀ n : ℕ,
  ∃ h : realIntegrableValue (sinePower n) 0 (Real.pi / 2),
    integralValue n = realIntegralValue (sinePower n) h

def seriesRepresentation : Prop := ∀ n : ℕ,
  ∃ h : realIntegrableValue (fun x => Ch07.SinCos.realSeriesSinValue x ^ n)
      0 (Ch07.PiPeriod.analyticPiValue / 2),
    integralValue n = realIntegralValue _ h

def initialZero : Prop := integralValue 0 = Real.pi / 2
def initialOne : Prop := integralValue 1 = 1
def recurrence : Prop := ∀ n : ℕ, 2 ≤ n →
  integralValue n = ((n : ℝ) - 1) * integralValue (n - 2) / (n : ℝ)
def evenFormula : Prop := ∀ n : ℕ,
  integralValue (2 * n) = (Real.pi / 2) * coefficientValue n
def oddFormula : Prop := ∀ n : ℕ,
  integralValue (2 * n + 1) = 1 / ((2 * (n : ℝ) + 1) * coefficientValue n)
def sandwich : Prop := ∀ n : ℕ,
  integralValue (2 * n + 2) ≤ integralValue (2 * n + 1) ∧
    integralValue (2 * n + 1) ≤ integralValue (2 * n)

end Specs.SingleVariableAnalysis.Ch18.WallisRecurrence
