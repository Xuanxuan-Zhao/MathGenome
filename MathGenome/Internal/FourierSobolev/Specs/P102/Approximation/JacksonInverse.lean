import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.JacksonPeriodic

/-! The classical periodic inverse in Theorem 1.15.  The best errors and the
arc metric are exactly those in the independent periodic direct specification.
The hypothesis is an eventual Landau estimate, including no assumption at zero.
-/
noncomputable section
open Filter

namespace P102.Approximation.JacksonInverse.Expected

open P102.Periodic.Expected
open P102.Approximation.JacksonPeriodic.Expected (realBestErrorValue complexBestErrorValue)

def inverseStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (α : ℝ), 0 < α → α < 1 →
    (∀ f : C(Circle T, ℝ),
      Asymptotics.IsBigO atTop (fun n : ℕ => realBestErrorValue T f n)
        (fun n : ℕ => (n : ℝ) ^ (-α)) →
      ∃ H : ℝ, 0 ≤ H ∧ ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α) ∧
    (∀ f : C(Circle T, ℂ),
      Asymptotics.IsBigO atTop (fun n : ℕ => complexBestErrorValue T f n)
        (fun n : ℕ => (n : ℝ) ^ (-α)) →
      ∃ H : ℝ, 0 ≤ H ∧ ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α)

def equivalenceStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (α : ℝ), 0 < α → α < 1 →
    (∀ f : C(Circle T, ℝ),
      Asymptotics.IsBigO atTop (fun n : ℕ => realBestErrorValue T f n)
        (fun n : ℕ => (n : ℝ) ^ (-α)) ↔
      ∃ H : ℝ, 0 ≤ H ∧ ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α) ∧
    (∀ f : C(Circle T, ℂ),
      Asymptotics.IsBigO atTop (fun n : ℕ => complexBestErrorValue T f n)
        (fun n : ℕ => (n : ℝ) ^ (-α)) ↔
      ∃ H : ℝ, 0 ≤ H ∧ ∀ x y, ‖f x - f y‖ ≤ H * dist x y ^ α)

end P102.Approximation.JacksonInverse.Expected
