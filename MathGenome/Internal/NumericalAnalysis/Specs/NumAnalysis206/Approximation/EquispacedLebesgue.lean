import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.InterpolationNorm
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
namespace Specs.NumAnalysis206.Approximation
open _root_.NumAnalysis206.Approximation

/-- The endpoint grid, with its actual interval membership. -/
def equispacedNodesValue (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    Fin (n + 1) → Set.Icc a b := fun i =>
  ⟨a + (b - a) * (i : ℝ) / n, by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hi : (i : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    constructor
    · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (sub_nonneg.mpr hab.le)
        (Nat.cast_nonneg _)) hn'.le)
    · have := (div_le_iff₀ hn').mpr (mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hab.le))
      linarith⟩

def equispacedNodesType := ∀ (a b : ℝ), a < b → ∀ n : ℕ, 0 < n →
  (Fin (n + 1) → Set.Icc a b)

def equispacedNodesInjective : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n),
    Function.Injective (equispacedNodesValue a b hab n hn)

def equispacedLebesgueLower : Prop :=
  ∀ (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 2 ≤ n),
    (2 : ℝ) ^ n / (2 * (n : ℝ) * ((n : ℝ) + 1) ^ 2) ≤
      lebesgueConstantValue (equispacedNodesValue a b hab n (lt_of_lt_of_le (by decide) hn))

end Specs.NumAnalysis206.Approximation
