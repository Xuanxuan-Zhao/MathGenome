import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Sequential
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.PathDependence

/-!
K03.02.path_dependence. The quotient is constant on each open half-line.
A two-sided epsilon estimate with epsilon 1, applied at ±δ/2, would put
both 1 and -1 strictly within distance 1 of the same real L, impossible.
The positive and negative reciprocal sequences are genuine nonzero-domain
approaches with different image limits. No value at zero is used.
-/
namespace SingleVariableAnalysis

theorem ratioAbs_positive (x : ℝ) (hx : 0 < x) : x / |x| = 1 := by
  rw [abs_of_pos hx, div_self (ne_of_gt hx)]

theorem ratioAbs_negative (x : ℝ) (hx : x < 0) : x / |x| = -1 := by
  rw [abs_of_neg hx, div_neg, div_self (ne_of_lt hx)]

theorem ratioAbs_right_limit :
    RightRelativeLimit (fun x : ℝ => x / |x|) ({0}ᶜ : Set ℝ) 0 1 := by
  apply (rightRelativeLimit_iff _ _ _ _).mpr
  constructor
  · intro δ hδ
    refine ⟨δ / 2, ?_, ?_⟩
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (ne_of_gt (half_pos hδ))
    · change 0 < δ / 2 ∧ δ / 2 < 0 + δ
      constructor <;> linarith
  · intro ε hε
    refine ⟨1, zero_lt_one, fun x _ hx _ => ?_⟩
    simpa only [ratioAbs_positive x hx, dist_self] using hε

theorem ratioAbs_left_limit :
    LeftRelativeLimit (fun x : ℝ => x / |x|) ({0}ᶜ : Set ℝ) 0 (-1) := by
  apply (leftRelativeLimit_iff _ _ _ _).mpr
  constructor
  · intro δ hδ
    refine ⟨-(δ / 2), ?_, ?_⟩
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (ne_of_lt (neg_neg_of_pos (half_pos hδ)))
    · change 0 - δ < -(δ / 2) ∧ -(δ / 2) < 0
      constructor <;> linarith
  · intro ε hε
    refine ⟨1, zero_lt_one, fun x _ _ hx => ?_⟩
    simpa only [ratioAbs_negative x hx, dist_self] using hε

theorem ratioAbs_no_twoSided_limit :
    ¬ ∃ L : ℝ, RelativePuncturedLimit (fun x : ℝ => x / |x|)
      ({0}ᶜ : Set ℝ) 0 L := by
  rintro ⟨L, hL⟩
  obtain ⟨δ, hδ, hb⟩ := hL 1 zero_lt_one
  have hp : 0 < δ / 2 := half_pos hδ
  have hn : -(δ / 2) < 0 := neg_neg_of_pos hp
  have hpos := hb (δ / 2) (by simpa using ne_of_gt hp)
    (by simpa [Real.dist_eq, abs_of_pos hp] using hp)
    (by simp only [Real.dist_eq, sub_zero, abs_of_pos hp]; linarith)
  have hneg := hb (-(δ / 2)) (by simpa using ne_of_lt hn)
    (by simpa [Real.dist_eq, abs_neg, abs_of_pos hp] using hp)
    (by simp only [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hp]; linarith)
  dsimp only at hpos hneg
  rw [ratioAbs_positive _ hp, Real.dist_eq] at hpos
  rw [ratioAbs_negative _ hn, Real.dist_eq] at hneg
  have hpos' := (abs_lt.mp hpos).2
  have hneg' := (abs_lt.mp hneg).1
  linarith

theorem ratioAbs_reciprocal_values (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) / |1 / (n : ℝ)| = 1 :=
  ratioAbs_positive _ (one_div_pos.mpr (Nat.cast_pos.mpr hn))

theorem ratioAbs_neg_reciprocal_values (n : ℕ) (hn : 0 < n) :
    (-(1 / (n : ℝ))) / |-(1 / (n : ℝ))| = -1 :=
  ratioAbs_negative _ (neg_neg_of_pos (one_div_pos.mpr (Nat.cast_pos.mpr hn)))

theorem ratioAbs_sampling_approaches :
    (∀ n : ℕ, (1 / ((n : ℝ) + 1)) ∈ ({0}ᶜ : Set ℝ) ∧
      (-(1 / ((n : ℝ) + 1))) ∈ ({0}ᶜ : Set ℝ)) ∧
    RealSequenceConverges (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 ∧
    RealSequenceConverges (fun n : ℕ => -(1 / ((n : ℝ) + 1))) 0 := by
  have hp (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hc : RealSequenceConverges (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 := by
    intro ε hε
    obtain ⟨N, _, hN⟩ := reciprocal_tail ε hε
    refine ⟨N, fun n hn => ?_⟩
    simpa only [sub_zero, Nat.cast_add, Nat.cast_one] using
      hN (n + 1) (hn.trans (Nat.le_succ n))
  refine ⟨fun n => ?_, hc, ?_⟩
  · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      And.intro (ne_of_gt (hp n)) (ne_of_lt (neg_neg_of_pos (hp n)))
  · intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    exact ⟨N, fun n hn => by simpa only [sub_zero, abs_neg] using hN n hn⟩

theorem ratioAbs_sampling_limits :
    RealSequenceConverges
      (fun n : ℕ => (1 / ((n : ℝ) + 1)) / |1 / ((n : ℝ) + 1)|) 1 ∧
    RealSequenceConverges
      (fun n : ℕ => (-(1 / ((n : ℝ) + 1))) / |-(1 / ((n : ℝ) + 1))|) (-1) ∧
    (1 : ℝ) ≠ -1 := by
  refine ⟨?_, ?_, by norm_num⟩
  · intro ε hε
    refine ⟨0, fun n _ => ?_⟩
    dsimp only
    rw [ratioAbs_positive _ (by positivity), sub_self, abs_zero]
    exact hε
  · intro ε hε
    refine ⟨0, fun n _ => ?_⟩
    dsimp only
    rw [ratioAbs_negative _ (neg_neg_of_pos (by positivity)), sub_self, abs_zero]
    exact hε

end SingleVariableAnalysis
