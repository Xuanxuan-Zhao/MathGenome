import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Independent statements for the necessary condition in paper.tex:3059–3089.
A sum over distinct points with the natural zero order as weight is precisely
the sum over zeros repeated with multiplicity. Zero orders are finite under
the hypotheses, and no value of f at the center is required to be nonzero. -/
noncomputable section
open Complex Metric Set Filter
open scoped Topology Classical

namespace Specs.D12Complex.Ch17.BlaschkeNecessity
open _root_.D12Complex

/-- Local center factor and the sharp finite-subset logarithmic bound.
The bound M is any positive bound for the modulus on the open disk. -/
def finite_log_bound_type : Prop :=
  ∀ (f : ℂ → ℂ) (M : ℝ), HolomorphicOn (ball 0 1) f →
    ¬ EqOn f (fun _ => 0) (ball 0 1) → 0 < M →
    (∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M) →
    ∃ (m : ℕ) (g : ℂ → ℂ),
      (∃ V : Set ℂ, 0 ∈ V ∧ HolomorphicOn V g) ∧ g 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), f z = z ^ m * g z) ∧
      analyticOrderAt f 0 = (m : ℕ∞) ∧
      ∀ s : Finset ℂ, (∀ a ∈ s, a ≠ 0 ∧ ‖a‖ < 1) →
        ∑ a ∈ s, ((analyticOrderAt f a).toNat : ℝ) * Real.log (1 / ‖a‖) ≤
          Real.log M - Real.log ‖g 0‖

/-- Finite orders and positive multiplicities are those of the actual zeros. -/
def multiplicity_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn (ball 0 1) f →
    ¬ EqOn f (fun _ => 0) (ball 0 1) →
    ∀ a ∈ ball (0 : ℂ) 1, analyticOrderAt f a ≠ ⊤ ∧
      (0 < (analyticOrderAt f a).toNat ↔ f a = 0)

/-- The necessary Blaschke condition, weighted by the exact zero multiplicities.
The indicator omits the center and every point outside the open unit disk. -/
def blaschke_necessity_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn (ball 0 1) f →
    ¬ EqOn f (fun _ => 0) (ball 0 1) →
    (∃ M : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M) →
    Summable (fun a : ℂ => if a ≠ 0 ∧ ‖a‖ < 1 then
      ((analyticOrderAt f a).toNat : ℝ) * (1 - ‖a‖) else 0)

/-- The same condition as an unweighted sum over each individual occurrence
of every nonzero zero. This index type includes exactly its multiplicity
many copies of each zero, and also handles finite or empty zero divisors. -/
def repeated_zeros_type : Prop :=
  ∀ (f : ℂ → ℂ), HolomorphicOn (ball 0 1) f →
    ¬ EqOn f (fun _ => 0) (ball 0 1) →
    (∃ M : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M) →
    Summable (fun p : (Σ a : {a : ℂ // a ≠ 0 ∧ ‖a‖ < 1 ∧ f a = 0},
      Fin (analyticOrderAt f a).toNat) => 1 - ‖p.1.1‖)

end Specs.D12Complex.Ch17.BlaschkeNecessity
