import MathGenome.Internal.DiscreteMarkovMartingales.P207.Foundation.TwoTimeAndExamples
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.L2OrthogonalIncrements
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207
namespace L2OrthogonalIncrements

variable {Ω : Type u} [m : MeasurableSpace Ω]

theorem increment_memLp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → Ω → ℝ) (hL : ∀ n, MemLp (M n) 2 μ) (k : ℕ) :
    MemLp (fun ω => M (k + 1) ω - M k ω) 2 μ :=
  (hL (k + 1)).sub (hL k)

theorem products_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → Ω → ℝ) (hL : ∀ n, MemLp (M n) 2 μ) :
    (∀ n, Integrable (fun ω => M n ω ^ 2) μ) ∧
    (∀ k, Integrable (fun ω => (M (k + 1) ω - M k ω) ^ 2) μ) ∧
    (∀ i j, Integrable
      (fun ω => (M (i + 1) ω - M i ω) * (M (j + 1) ω - M j ω)) μ) ∧
    (∀ i j, Integrable (fun ω => M i ω * (M (j + 1) ω - M j ω)) μ) := by
  exact ⟨fun n => (hL n).integrable_sq,
    fun k => (increment_memLp μ M hL k).integrable_sq,
    fun i j => (increment_memLp μ M hL i).integrable_mul (increment_memLp μ M hL j),
    fun i j => (hL i).integrable_mul (increment_memLp μ M hL j)⟩

/-- A martingale increment has zero conditional expectation at its left endpoint. -/
theorem increment_condExp_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ) (k : ℕ) :
    μ[fun ω => M (k + 1) ω - M k ω | ℱ k] =ᵐ[μ] fun _ => (0 : ℝ) := by
  have hsub := condExp_sub (hM.2.1 (k + 1)) (hM.2.1 k) (ℱ k)
  have hself := condExp_of_stronglyMeasurable (ℱ.le k)
    (hM.1 k).stronglyMeasurable (hM.2.1 k)
  filter_upwards [hsub, hM.2.2 k] with ω hω hstep
  change μ[M (k + 1) - M k | ℱ k] ω = 0
  rw [hω]
  change μ[M (k + 1) | ℱ k] ω - μ[M k | ℱ k] ω = 0
  rw [hstep, hself, sub_self]

/-- An integrable product with a measurable past factor has expectation zero.
Hölder's inequality will supply product integrability for all the L² applications. -/
theorem integral_mul_increment_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (k : ℕ) (Z : Ω → ℝ) (hZ : StronglyMeasurable[ℱ k] Z)
    (hprod : Integrable (fun ω => Z ω * (M (k + 1) ω - M k ω)) μ) :
    (∫ ω, Z ω * (M (k + 1) ω - M k ω) ∂μ) = 0 := by
  have hpull := condExp_mul_of_stronglyMeasurable_left hZ hprod
    ((hM.2.1 (k + 1)).sub (hM.2.1 k))
  have hzero : μ[fun ω => Z ω * (M (k + 1) ω - M k ω) | ℱ k] =ᵐ[μ]
      fun _ => (0 : ℝ) := by
    filter_upwards [hpull, increment_condExp_zero μ ℱ M hM k] with ω hp hz
    calc
      _ = Z ω * μ[fun ω => M (k + 1) ω - M k ω | ℱ k] ω := hp
      _ = 0 := by rw [hz, mul_zero]
  calc
    (∫ ω, Z ω * (M (k + 1) ω - M k ω) ∂μ) =
        ∫ ω, μ[fun ω => Z ω * (M (k + 1) ω - M k ω) | ℱ k] ω ∂μ :=
      (integral_condExp (ℱ.le k)).symm
    _ = ∫ _ : Ω, (0 : ℝ) ∂μ := integral_congr_ae hzero
    _ = 0 := by simp

/-- Orthogonality to any process value at or before the increment's left endpoint. -/
theorem past_value_increment_orthogonal (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (hL : ∀ n, MemLp (M n) 2 μ) (i k : ℕ) (hik : i ≤ k) :
    (∫ ω, M i ω * (M (k + 1) ω - M k ω) ∂μ) = 0 := by
  exact integral_mul_increment_zero μ ℱ M hM k (M i)
    (((hM.1 i).mono (ℱ.mono hik) le_rfl).stronglyMeasurable)
    ((hL i).integrable_mul (increment_memLp μ M hL k))

private theorem increments_orthogonal_of_lt (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (hL : ∀ n, MemLp (M n) 2 μ) (i j : ℕ) (hij : i < j) :
    (∫ ω, (M (i + 1) ω - M i ω) * (M (j + 1) ω - M j ω) ∂μ) = 0 := by
  apply integral_mul_increment_zero μ ℱ M hM j
    (fun ω => M (i + 1) ω - M i ω)
  · exact ((((hM.1 (i + 1)).mono (ℱ.mono (Nat.succ_le_of_lt hij)) le_rfl).sub
      ((hM.1 i).mono (ℱ.mono hij.le) le_rfl)).stronglyMeasurable)
  · exact (increment_memLp μ M hL i).integrable_mul (increment_memLp μ M hL j)

theorem increments_orthogonal (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (hL : ∀ n, MemLp (M n) 2 μ) (i j : ℕ) (hij : i ≠ j) :
    (∫ ω, (M (i + 1) ω - M i ω) * (M (j + 1) ω - M j ω) ∂μ) = 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact increments_orthogonal_of_lt μ ℱ M hM hL i j hlt
  · simpa only [mul_comm] using increments_orthogonal_of_lt μ ℱ M hM hL j i hgt

theorem initial_increment_orthogonal (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (hL : ∀ n, MemLp (M n) 2 μ) (k : ℕ) :
    (∫ ω, M 0 ω * (M (k + 1) ω - M k ω) ∂μ) = 0 :=
  past_value_increment_orthogonal μ ℱ M hM hL 0 k (Nat.zero_le k)

theorem energy_identity (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (hM : IsMartingale M ℱ μ)
    (hL : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    (∫ ω, M n ω ^ 2 ∂μ) = (∫ ω, M 0 ω ^ 2 ∂μ) +
      ∑ k ∈ Finset.range n, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsq := (hL n).integrable_sq
    have hd := (increment_memLp μ M hL n).integrable_sq
    have hp := (hL n).integrable_mul (increment_memLp μ M hL n)
    have hstep : (∫ ω, M (n + 1) ω ^ 2 ∂μ) =
        (∫ ω, M n ω ^ 2 ∂μ) + ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ := by
      calc
        (∫ ω, M (n + 1) ω ^ 2 ∂μ) =
            ∫ ω, (M n ω ^ 2 + (M (n + 1) ω - M n ω) ^ 2) +
              2 * (M n ω * (M (n + 1) ω - M n ω)) ∂μ := by
          congr 1
          funext ω
          ring
        _ = ((∫ ω, M n ω ^ 2 ∂μ) + ∫ ω, (M (n + 1) ω - M n ω) ^ 2 ∂μ) +
            2 * (∫ ω, M n ω * (M (n + 1) ω - M n ω) ∂μ) := by
          rw [integral_add (f := fun ω => M n ω ^ 2 + (M (n + 1) ω - M n ω) ^ 2)
            (g := fun ω => 2 * (M n ω * (M (n + 1) ω - M n ω)))
            (hsq.add hd) (hp.const_mul 2)]
          rw [integral_add hsq hd, integral_const_mul]
        _ = _ := by rw [past_value_increment_orthogonal μ ℱ M hM hL n n le_rfl]; ring
    rw [hstep, ih, Finset.sum_range_succ]
    ring

end L2OrthogonalIncrements
end P207
