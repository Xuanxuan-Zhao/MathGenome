import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.LacunaryNorms
import Mathlib.Analysis.Normed.Operator.Banach

/-! Completion and the unbounded member in paper.tex:19744–19788.
The harmonic coefficients are 1/j for j≥1; the zeroth coefficient is zero. All spaces use the same angular circle and Haar probability measure. -/
noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology

namespace ExpandedFA.PartIV.LacunarySubspaceSpec
open LacunaryNormsSpec

abbrev Coeff := lp (fun _ : ℕ => ℂ) 2
abbrev Space (p : ℝ≥0∞) := Lp ℂ p μ

def mode (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) : Space p :=
  fourierLp p (frequency j : ℤ)

def closedSpan (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℂ (Space p) :=
  (Submodule.span ℂ (Set.range (mode p))).topologicalClosure

/-- The isomorphism is the coefficient-sum map, including convergence for every
square-summable family, surjectivity onto the actual closed span, and both bounds. -/
def CompletionIdentification : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∃ S : Coeff ≃L[ℂ] closedSpan p, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ a, c * ‖a‖ ≤ ‖S a‖ ∧ ‖S a‖ ≤ C * ‖a‖) ∧
      ∀ a, HasSum (fun j => a j • mode p j) (S a).val

/-- The resulting closed spaces are infinite dimensional. -/
def InfiniteDimensionalSpans : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ → ¬ Module.Finite ℂ (closedSpan p)

def harmonic (j : ℕ) : ℂ := (j : ℂ)⁻¹

/-- The same L² Fourier sum has a representative in each finite-p closed span.
Essential unboundedness is measured on the a.e. class, not a chosen representative. -/
def CommonUnboundedMember : Prop :=
  ∃ f : Space 2,
    HasSum (fun j => harmonic j • mode 2 j) f ∧
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
      ∃ g : closedSpan p, (g.val : LacunaryNormsSpec.Circle → ℂ) =ᵐ[μ] (f : LacunaryNormsSpec.Circle → ℂ)) ∧
    ¬ ∃ M : ℝ, ∀ᵐ t ∂μ, ‖f t‖ ≤ M

/-- Positive Poisson values at angle zero provide the unboundedness argument.
The identity is with the actual normalized Poisson integral of the L² sum. -/
def PositivePoissonValues : Prop :=
  ∃ f : Space 2,
    HasSum (fun j => harmonic j • mode 2 j) f ∧
    (∀ r : ℝ, 0 ≤ r → r < 1 →
      (∫ t : LacunaryNormsSpec.Circle, ((1 - r ^ 2) / ‖fourier (T := 2 * π) 1 t - (r : ℂ)‖ ^ 2) •
        f t ∂μ) = ((∑' j : ℕ, r ^ frequency j / (j : ℕ)) : ℝ)) ∧
    Tendsto (fun r : ℝ => ∑' j : ℕ, r ^ frequency j / (j : ℕ))
      (𝓝[<] (1 : ℝ)) atTop

end ExpandedFA.PartIV.LacunarySubspaceSpec
