import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation

/-! The derivative is taken after lifting the continuous function to ℝ.
The witness is a continuous function on the original circle, so its norm is
exactly the supremum norm of the periodic derivative. -/
noncomputable section

namespace P102.Approximation.Expected
open P102.Periodic.Expected

def bernsteinComplexStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (n : ℕ) (P : C(Circle T, ℂ)),
    P ∈ complexTrigDegree T n →
    ∃ Q : C(Circle T, ℂ),
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => P (s : Circle T)) (Q (t : Circle T)) t) ∧
      ‖Q‖ ≤ (2 * Real.pi / T) * n * ‖P‖

def bernsteinRealStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (n : ℕ) (P : C(Circle T, ℝ)),
    P ∈ realTrigDegree T n →
    ∃ Q : C(Circle T, ℝ),
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => P (s : Circle T)) (Q (t : Circle T)) t) ∧
      ‖Q‖ ≤ (2 * Real.pi / T) * n * ‖P‖

end P102.Approximation.Expected
