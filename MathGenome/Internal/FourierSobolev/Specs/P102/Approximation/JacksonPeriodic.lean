import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent statements for the periodic direct part of Theorem 1.15.
The norm on `AddCircle T` is the quotient norm, so its distance is arc length
in the original length units (rather than angular or chordal distance).
The errors use the actual finite-frequency spaces of the shared foundation. -/

noncomputable section
open Set Filter
open scoped Topology

namespace P102.Approximation.JacksonPeriodic.Expected

abbrev Circle := P102.Periodic.Expected.Circle

variable (T : ℝ) [Fact (0 < T)]

def modulusValue {E : Type*} [NormedAddCommGroup E]
    (f : C(Circle T, E)) (δ : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ x y : Circle T, dist x y ≤ δ ∧ r = ‖f x - f y‖}

def realBestErrorValue (f : C(Circle T, ℝ)) (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ p ∈ P102.Periodic.Expected.realTrigDegree T n, r = ‖f - p‖}

def complexBestErrorValue (f : C(Circle T, ℂ)) (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ p ∈ P102.Periodic.Expected.complexTrigDegree T n, r = ‖f - p‖}

def modulusType := ∀ (T : ℝ) {E : Type*} [NormedAddCommGroup E],
  C(Circle T, E) → ℝ → ℝ

def realBestErrorType := ∀ (T : ℝ) [Fact (0 < T)], C(Circle T, ℝ) → ℕ → ℝ

def complexBestErrorType := ∀ (T : ℝ) [Fact (0 < T)], C(Circle T, ℂ) → ℕ → ℝ

/-- One finite constant works simultaneously for all periods and both fields. -/
def directStatement : Prop := ∃ C : ℝ, 0 ≤ C ∧
  ∀ (T : ℝ) [Fact (0 < T)] (n : ℕ), 1 ≤ n →
    (∀ f : C(Circle T, ℝ),
      realBestErrorValue T f n ≤ C * modulusValue T f (T / (n : ℝ))) ∧
    (∀ f : C(Circle T, ℂ),
      complexBestErrorValue T f n ≤ C * modulusValue T f (T / (n : ℝ)))

/-- Hölder data give the asserted eventual Landau estimate for the same best
errors; the Hölder hypothesis uses the arc metric for the original period. -/
def holderStatement : Prop := ∀ (T : ℝ) [Fact (0 < T)] (α : ℝ),
  0 < α → α < 1 → ∀ (H : ℝ), 0 ≤ H →
    (∀ f : C(Circle T, ℝ),
      (∀ x y, ‖f x - f y‖ ≤ H * (dist x y) ^ α) →
      Asymptotics.IsBigO atTop (fun n : ℕ => realBestErrorValue T f n)
        (fun n : ℕ => (n : ℝ) ^ (-α))) ∧
    (∀ f : C(Circle T, ℂ),
      (∀ x y, ‖f x - f y‖ ≤ H * (dist x y) ^ α) →
      Asymptotics.IsBigO atTop (fun n : ℕ => complexBestErrorValue T f n)
        (fun n : ℕ => (n : ℝ) ^ (-α)))

end P102.Approximation.JacksonPeriodic.Expected
