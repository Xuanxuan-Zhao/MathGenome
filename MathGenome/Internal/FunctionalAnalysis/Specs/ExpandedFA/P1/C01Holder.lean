import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm

/-!
Independent statements for `fa2:p1:c01:holder`, paper.tex 231–256.
The sequence objects and their norm formulas are the accepted canonical ones.
Extended nonnegative real exponents include both endpoint orders `(1,∞)` and
`(∞,1)`: inversion sends `∞` to zero. No nonzero-vector hypothesis is imposed.
-/

noncomputable section
open scoped ENNReal

universe u
namespace ExpandedFA.P1.C01Holder
open C01SequenceSpaces C01Norm

namespace Spec

/-- Absolute convergence and the discrete Hölder bound over either scalar field. -/
def Holder : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)],
    p⁻¹ + q⁻¹ = 1 → ∀ (x : SequenceLp 𝕜 p) (y : SequenceLp 𝕜 q),
      Summable (fun n => ‖x n * y n‖) ∧
      Summable (fun n => x n * y n) ∧
      (∑' n, ‖x n * y n‖) ≤ ‖x‖ * ‖y‖

/-- Membership of the coordinatewise sum, stated on unbundled sequences. -/
def AddMembership : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) (_hp : 1 ≤ p)
    (x y : ScalarSequence 𝕜), Memℓp x p → Memℓp y p →
      Memℓp (fun n => x n + y n) p

/-- Minkowski, with explicit identification of the sum's coordinates. -/
def Minkowski : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (x y : SequenceLp 𝕜 p),
      (∀ n, (x + y) n = x n + y n) ∧ ‖x + y‖ ≤ ‖x‖ + ‖y‖

/-- The manuscript power-sum formula is a norm for every finite real `p ≥ 1`. -/
def FiniteFormulaNorm : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (_hp : 1 ≤ p),
    NormAxioms 𝕜 (fun x : SequenceLp 𝕜 (ENNReal.ofReal p) =>
      (∑' n, ‖x n‖ ^ p) ^ (1 / p))

/-- The supremum formula is a norm, including at the zero sequence. -/
def InfinityFormulaNorm : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    NormAxioms 𝕜 (fun x : SequenceLInfinity 𝕜 => ⨆ n, ‖x n‖)

end Spec
end ExpandedFA.P1.C01Holder
