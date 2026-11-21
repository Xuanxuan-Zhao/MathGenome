import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.NoBoundedCommutator
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace ExpandedFA.Models

private lemma commutator_pow {R : Type*} [Ring R] {A B : R}
    (h : A * B - B * A = 1) (n : ℕ) :
    A * B ^ (n + 1) - B ^ (n + 1) * A = (n + 1) • B ^ n := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    calc
      A * B ^ (n + 1 + 1) - B ^ (n + 1 + 1) * A =
          (A * B ^ (n + 1) - B ^ (n + 1) * A) * B +
            B ^ (n + 1) * (A * B - B * A) := by
              rw [pow_succ B (n + 1)]
              noncomm_ring
      _ = (n + 1 + 1) • B ^ (n + 1) := by
        rw [ih, h, smul_mul_assoc, mul_one, ← pow_succ]
        simp only [add_nsmul, one_nsmul]

/-- Bounded operators on a nonzero real or complex Banach space cannot have
commutator equal to the identity (paper.tex, no bounded canonical commutator). -/
theorem no_bounded_commutator : Specs.ExpandedFA.Models.NoBoundedCommutator := by
  intro 𝕜 E _ _ _ _ _ A B h
  have hp (n : ℕ) : B ^ n ≠ 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro hz
      have hn : (n + 1) • B ^ n = 0 :=
        (commutator_pow h n).symm.trans (by simp [hz])
      have hnNorm := congrArg norm hn
      rw [RCLike.norm_nsmul (K := 𝕜), norm_zero, nsmul_eq_mul] at hnNorm
      exact ih (norm_eq_zero.mp ((mul_eq_zero.mp hnNorm).resolve_left (by positivity)))
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖A‖ * ‖B‖)
  have hnorm : (n + 1 : ℝ) * ‖B ^ n‖ ≤ 2 * ‖A‖ * ‖B‖ * ‖B ^ n‖ := by
    calc
      (n + 1 : ℝ) * ‖B ^ n‖ = ‖(n + 1) • B ^ n‖ := by
        rw [RCLike.norm_nsmul (K := 𝕜), nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      _ = ‖A * B ^ (n + 1) - B ^ (n + 1) * A‖ :=
        congrArg norm (commutator_pow h n).symm
      _ ≤ ‖A * B ^ (n + 1)‖ + ‖B ^ (n + 1) * A‖ := norm_sub_le _ _
      _ ≤ ‖A‖ * ‖B ^ (n + 1)‖ + ‖B ^ (n + 1)‖ * ‖A‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2 * ‖A‖ * ‖B ^ (n + 1)‖ := by ring
      _ ≤ 2 * ‖A‖ * (‖B ^ n‖ * ‖B‖) := by
        gcongr
        rw [pow_succ]
        exact norm_mul_le _ _
      _ = 2 * ‖A‖ * ‖B‖ * ‖B ^ n‖ := by ring
  have hpos : 0 < ‖B ^ n‖ := norm_pos_iff.mpr (hp n)
  have := (mul_le_mul_iff_left₀ hpos).mp hnorm
  linarith

end ExpandedFA.Models
