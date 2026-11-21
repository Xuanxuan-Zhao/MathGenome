import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.SubtractionTrace
import Mathlib.Tactic.Ring

/-! Exact inversion of a finite sequential multiply-subtract trace, paper.tex (4.1).
No relative-error bound is used here: the factors may be arbitrary real numbers,
provided the subtraction factors being inverted are nonzero.
-/

namespace NumAnalysis206.LinearAlgebra.SubtractionTrace

/-- Undo one subtraction rounding factor. -/
theorem one_step_inverse (a b μ σ sPrev sNext : ℝ)
    (hstep : sNext = (sPrev - a * b * (1 + μ)) * (1 + σ))
    (hnonzero : 1 + σ ≠ 0) :
    sPrev = sNext / (1 + σ) + a * b * (1 + μ) := by
  rw [hstep, mul_div_cancel_right₀ _ hnonzero]
  ring

/-- Substituting the inverse step successively gives the complete finite trace.
The terminal term contains every inverse subtraction factor; summand t contains
only the factors with indices strictly less than t. This includes k = 0.
-/
theorem subtraction_trace (k : ℕ) (a b μ σ s : ℕ → ℝ)
    (hstep : ∀ t ∈ Finset.Icc 1 k,
      s t = (s (t - 1) - a t * b t * (1 + μ t)) * (1 + σ t))
    (hnonzero : ∀ t ∈ Finset.Icc 1 k, 1 + σ t ≠ 0) :
    s 0 = s k * (∏ j ∈ Finset.Icc 1 k, (1 + σ j)⁻¹) +
      ∑ t ∈ Finset.Icc 1 k,
        a t * b t * (1 + μ t) * (∏ j ∈ Finset.Ico 1 t, (1 + σ j)⁻¹) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hle : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have hlast : k + 1 ∈ Finset.Icc 1 (k + 1) := Finset.mem_Icc.mpr ⟨hle, le_rfl⟩
    have hinverse := one_step_inverse (a (k + 1)) (b (k + 1))
      (μ (k + 1)) (σ (k + 1)) (s k) (s (k + 1))
      (by simpa using hstep (k + 1) hlast) (hnonzero (k + 1) hlast)
    have hsubset : Finset.Icc 1 k ⊆ Finset.Icc 1 (k + 1) := by
      intro t ht
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1,
        (Finset.mem_Icc.mp ht).2.trans (Nat.le_succ k)⟩
    calc
      s 0 = s k * (∏ j ∈ Finset.Icc 1 k, (1 + σ j)⁻¹) +
          ∑ t ∈ Finset.Icc 1 k,
            a t * b t * (1 + μ t) * (∏ j ∈ Finset.Ico 1 t, (1 + σ j)⁻¹) :=
        ih (fun t ht => hstep t (hsubset ht))
          (fun t ht => hnonzero t (hsubset ht))
      _ = _ := by
        rw [Finset.prod_Icc_succ_top hle, Finset.sum_Icc_succ_top hle,
          Finset.Ico_add_one_right_eq_Icc, hinverse]
        simp only [div_eq_mul_inv]
        ring

end NumAnalysis206.LinearAlgebra.SubtractionTrace
