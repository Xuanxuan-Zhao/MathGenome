import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SequenceLimit
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Squeeze

/-!
# Squeeze and absolute estimates

The two assertions of `K03.01.squeeze`. The proofs use the explicit epsilon
definitions and take maxima of the finitely many tail thresholds. The scalar
absolute estimate is provided for both canonical scalar choices, `ℝ` and `ℂ`.
-/

namespace SingleVariableAnalysis

/-- On a common tail, the lower sequence gives the lower epsilon bound and
the upper sequence gives the upper epsilon bound. -/
theorem realSequenceConverges_squeeze (a b c : ℕ → ℝ) (L : ℝ)
    (horder : SequenceEventually (fun n => a n ≤ b n ∧ b n ≤ c n))
    (ha : RealSequenceConverges a L) (hc : RealSequenceConverges c L) :
    RealSequenceConverges b L := by
  intro ε hε
  obtain ⟨N, hN⟩ := horder
  obtain ⟨A, hA⟩ := ha ε hε
  obtain ⟨C, hC⟩ := hc ε hε
  refine ⟨max N (max A C), ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnA : A ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnC : C ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hab, hbc⟩ := hN n hnN
  exact abs_lt.mpr
    ⟨lt_of_lt_of_le (abs_lt.mp (hA n hnA)).1 (sub_le_sub_right hab L),
      lt_of_le_of_lt (sub_le_sub_right hbc L) (abs_lt.mp (hC n hnC)).2⟩

/-- An eventual real error bound tending to zero forces convergence. -/
theorem realSequenceConverges_of_abs_le (z : ℕ → ℝ) (L : ℝ) (d : ℕ → ℝ)
    (hbound : SequenceEventually (fun n => |z n - L| ≤ d n))
    (hd : RealSequenceConverges d 0) : RealSequenceConverges z L := by
  intro ε hε
  obtain ⟨N, hN⟩ := hbound
  obtain ⟨D, hD⟩ := hd ε hε
  refine ⟨max N D, ?_⟩
  intro n hn
  have hsmall : |d n| < ε := by
    simpa only [sub_zero] using hD n (le_trans (le_max_right _ _) hn)
  exact lt_of_le_of_lt (hN n (le_trans (le_max_left _ _) hn))
    (lt_of_le_of_lt (le_abs_self _) hsmall)

/-- The same argument for complex errors uses the canonical complex modulus. -/
theorem complexSequenceConverges_of_norm_le (z : ℕ → ℂ) (L : ℂ) (d : ℕ → ℝ)
    (hbound : SequenceEventually (fun n => ‖z n - L‖ ≤ d n))
    (hd : RealSequenceConverges d 0) : ComplexSequenceConverges z L := by
  intro ε hε
  obtain ⟨N, hN⟩ := hbound
  obtain ⟨D, hD⟩ := hd ε hε
  refine ⟨max N D, ?_⟩
  intro n hn
  have hsmall : |d n| < ε := by
    simpa only [sub_zero] using hD n (le_trans (le_max_right _ _) hn)
  exact lt_of_le_of_lt (hN n (le_trans (le_max_left _ _) hn))
    (lt_of_le_of_lt (le_abs_self _) hsmall)

end SingleVariableAnalysis
