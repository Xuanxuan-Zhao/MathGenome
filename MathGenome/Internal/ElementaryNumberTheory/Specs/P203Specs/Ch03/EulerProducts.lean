import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.Multiplicativity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.NumberTheory.PrimeCounting

/-! Analytic part of paper.tex, Theorem 3.2 (nt:C02), lines 910–918.
All series indexed by ℕ+ have precisely the positive-input domain of the paper.
The real power in each denominator is cast to ℂ after taking the power. -/
namespace P203Specs.EulerProducts

open Filter
open scoped Topology

noncomputable def dirichletTerm (f : PositiveFunction ℂ) (s : ℝ) : PositiveFunction ℂ := fun n =>
  f n / (((n : ℕ) : ℝ) ^ s : ℝ)

noncomputable def absoluteTerm (f : PositiveFunction ℂ) (s : ℝ) (n : ℕ+) : ℝ :=
  ‖f n‖ * ((n : ℕ) : ℝ) ^ (-s)

noncomputable def localTerm (f : PositiveFunction ℂ) (s : ℝ) (p j : ℕ) : ℂ :=
  zeroExtend f (p ^ j) / ((p : ℝ) ^ ((j : ℝ) * s) : ℝ)

/-- The floor plus one makes the cutoff inclusive, also at integral y. -/
noncomputable def primesAtMost (y : ℝ) : Finset ℕ :=
  Nat.primesBelow (⌊y⌋₊ + 1)

def PrimeCutoff : Prop :=
  ∀ (y : ℝ) (p : ℕ), p ∈ primesAtMost y ↔ p.Prime ∧ (p : ℝ) ≤ y

def AbsoluteConvergence : Prop :=
  ∀ (f : PositiveFunction ℂ) (s : ℝ),
    Summable (absoluteTerm f s) →
      Summable (fun n => ‖dirichletTerm f s n‖) ∧ Summable (dirichletTerm f s)

def LocalAbsoluteConvergence : Prop :=
  ∀ (f : PositiveFunction ℂ) (s : ℝ),
    Summable (absoluteTerm f s) → ∀ p : ℕ, p.Prime →
      Summable (fun j => ‖localTerm f s p j‖) ∧ Summable (localTerm f s p)

/-- No lower bound on s is assumed in this general assertion. -/
def EulerProduct : Prop :=
  ∀ (f : PositiveFunction ℂ) (s : ℝ), Multiplicativity.IsMultiplicative f →
    Summable (absoluteTerm f s) →
      Tendsto (fun y : ℝ => ∏ p ∈ primesAtMost y, ∑' j, localTerm f s p j)
        atTop (𝓝 (∑' n : ℕ+, dirichletTerm f s n))

def ZetaSeriesConvergence : Prop :=
  ∀ s : ℝ, 1 < s → Summable (fun n : ℕ+ => ((n : ℕ) : ℝ) ^ (-s))

/-- The zeta value is expressed as its positive real Dirichlet series;
no separate analytic continuation or naming convention is needed. -/
def ZetaEulerProduct : Prop :=
  ∀ s : ℝ, 1 < s →
    Tendsto (fun y : ℝ => ∏ p ∈ primesAtMost y, (1 - (p : ℝ) ^ (-s))⁻¹)
      atTop (𝓝 (∑' n : ℕ+, ((n : ℕ) : ℝ) ^ (-s)))

end P203Specs.EulerProducts
