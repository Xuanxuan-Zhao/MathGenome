import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.PartialPivotGrowth
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.PivotedLU
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

noncomputable section
namespace NumAnalysis206.PartialPivotGrowth
open NumAnalysis206.MatrixDefinitions NumAnalysis206.PivotedLU
variable {n : ℕ}

theorem maxAbs_nonneg (A : Mat ℝ n n) : 0 ≤ maxAbs A := NNReal.coe_nonneg _

theorem abs_le_maxAbs (A : Mat ℝ n n) (i j : Fin n) : |A i j| ≤ maxAbs A := by
  have h := Finset.le_sup (s := Finset.univ)
    (f := fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) (Finset.mem_univ (i, j))
  exact_mod_cast h

theorem maxAbs_le {A : Mat ℝ n n} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i j, |A i j| ≤ M) : maxAbs A ≤ M := by
  change ((Finset.univ.sup (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) : NNReal) : ℝ) ≤ M
  rw [← Real.coe_toNNReal M hM, NNReal.coe_le_coe]
  apply Finset.sup_le
  intro ij _
  apply NNReal.coe_le_coe.mp
  simpa only [Real.coe_toNNReal _ hM, coe_nnnorm, Real.norm_eq_abs] using h ij.1 ij.2

theorem partial_run_to_lu : Specs.NumAnalysis206.PartialPivotGrowth.partial_run_to_lu := by
  intro n first r c A U history swaps h
  induction h with
  | stop hz => exact ⟨_, _, _, .stop hz⟩
  | skip hc hz ht ih =>
    obtain ⟨p, L, ps, hrun⟩ := ih
    exact ⟨p, L, ps, .skip hc hz hrun⟩
  | pivot hr hc q choice ht ih =>
    obtain ⟨p, L, ps, hrun⟩ := ih
    exact ⟨_, _, _, .pivot hr hc q choice.1 choice.2.1 hrun⟩

theorem PartialRun.output_mem {first r c A U history swaps}
    (h : PartialRun (n := n) first r c A U history swaps) : U ∈ history := by
  induction h with
  | stop => simp
  | skip _ _ _ ih => exact List.mem_cons_of_mem _ ih
  | pivot _ _ _ _ _ ih => exact List.mem_cons_of_mem _ ih

/-- Partial pivoting bounds each actual multiplier, including zero multipliers. -/
theorem multiplier_abs_le_one {first : Bool} {A : Mat ℝ n n} {r q d : Fin n}
    (h : PivotChoice first A r q d) (i : Fin n) :
    |multipliers A r q d i| ≤ 1 := by
  classical
  unfold multipliers
  split_ifs with hi
  · rw [abs_div]
    apply (div_le_one (abs_pos.mpr h.2.1)).mpr
    apply h.2.2.1
    by_cases hiq : i = q
    · subst i; simp
    · simpa [Equiv.swap_apply_of_ne_of_ne (ne_of_gt hi) hiq] using le_of_lt hi
  · norm_num

/-- A growth-producing update at most doubles the previous full-matrix bound. -/
theorem eliminate_bound {first : Bool} {A : Mat ℝ n n} {r q d : Fin n}
    (h : PivotChoice first A r q d) {M : ℝ} (_hM : 0 ≤ M)
    (hA : ∀ i j, |A i j| ≤ M) :
    ∀ i j, |eliminate A r q d i j| ≤ 2 * M := by
  intro i j
  calc
    |eliminate A r q d i j| ≤ |A (Equiv.swap r q i) j| +
        |multipliers A r q d i| * |A q j| := by
      simpa only [eliminate, abs_mul] using
        abs_sub (A (Equiv.swap r q i) j) (multipliers A r q d i * A q j)
    _ ≤ M + 1 * M := add_le_add (hA _ _) (mul_le_mul
      (multiplier_abs_le_one h i) (hA _ _) (abs_nonneg _) (by norm_num))
    _ = 2 * M := by ring

/-- The last row cannot cause another doubling: it has no rows below it. -/
theorem eliminate_last {first : Bool} {A : Mat ℝ n n} {r q d : Fin n}
    (h : PivotChoice first A r q d) (hr : r.val = n - 1) :
    eliminate A r q d = A := by
  classical
  have hq : q = r := Fin.ext (by have := q.isLt; have := h.1; change r.val ≤ q.val at this; omega)
  subst q
  ext i j
  have hi : ¬r < i := by have := i.isLt; change ¬r.val < i.val; omega
  simp [eliminate, multipliers, hi]

/-- Capped stage exponent: only the first n-1 pivots can create growth. -/
theorem PartialRun.bound {first r c A U history swaps}
    (h : PartialRun (n := n) first r c A U history swaps) {M : ℝ}
    (hM : 0 ≤ M) (hA : ∀ i j, |A i j| ≤ 2 ^ min r (n - 1) * M) :
    ∀ B ∈ history, ∀ i j, |B i j| ≤ 2 ^ (n - 1) * M := by
  induction h with
  | stop hz =>
    intro B hB i j
    simp only [List.mem_singleton] at hB
    subst B
    exact (hA i j).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.min_le_right _ _)) hM)
  | skip hc hz ht ih =>
    intro B hB
    rcases List.mem_cons.mp hB with heq | hmem
    · subst B
      intro i j
      exact (hA i j).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.min_le_right _ _)) hM)
    · exact ih hA B hmem
  | @pivot r c A U history swaps hr hc q choice ht ih =>
    have hnext : ∀ i j, |eliminate A ⟨r, hr⟩ q ⟨c, hc⟩ i j| ≤
        2 ^ min (r + 1) (n - 1) * M := by
      by_cases hlast : r = n - 1
      · rw [eliminate_last choice hlast]
        simpa [hlast, Nat.min_eq_right (by omega : n - 1 ≤ n - 1 + 1)] using hA
      · have hlt : r + 1 ≤ n - 1 := by omega
        have h := eliminate_bound choice (mul_nonneg (by positivity) hM) hA
        simpa only [Nat.min_eq_left (by omega : r ≤ n - 1),
          Nat.min_eq_left hlt, pow_succ, mul_assoc, mul_left_comm, mul_comm] using h
    intro B hB
    rcases List.mem_cons.mp hB with heq | hmem
    · subst B
      intro i j
      exact (hA i j).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.min_le_right _ _)) hM)
    · exact ih hnext B hmem

theorem partial_pivot_growth : Specs.NumAnalysis206.PartialPivotGrowth.partial_pivot_growth := by
  intro n A hA first U history swaps h
  have hb := h.bound (maxAbs_nonneg A) (by simpa using abs_le_maxAbs A)
  exact ⟨hb, hb U h.output_mem⟩

/-- A largest available entry exists; taking the least maximizer implements
first-row tie breaking, and is also admissible when ties are unrestricted. -/
theorem pivotChoice_exists (first : Bool) (A : Mat ℝ n n) (r d : Fin n)
    (hex : ∃ i, r ≤ i ∧ A i d ≠ 0) : ∃ q, PivotChoice first A r q d := by
  classical
  let s := Finset.univ.filter (fun i : Fin n => r ≤ i)
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image s (fun i => |A i d|)
    ⟨r, by simp [s]⟩
  let t := s.filter (fun i => |A i d| = |A v d|)
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image t (fun i => i)
    ⟨v, by simp [t, hv]⟩
  have hqr : r ≤ q := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
  have hqv : |A q d| = |A v d| := (Finset.mem_filter.mp hq).2
  have hm : ∀ i, r ≤ i → |A i d| ≤ |A q d| := by
    intro i hi
    rw [hqv]
    exact hmax i (by simp [s, hi])
  have hqn : A q d ≠ 0 := by
    obtain ⟨i, hi, hni⟩ := hex
    have hp := lt_of_lt_of_le (abs_pos.mpr hni) (hm i hi)
    exact abs_pos.mp hp
  refine ⟨q, hqr, hqn, hm, ?_⟩
  intro _ i hi heq
  apply hmin i
  simp [t, s, hi, heq.trans hqv]

/-- Termination follows by scanning the finitely many columns, whether a
column is skipped or a maximum-magnitude pivot is selected. -/
theorem partial_run_exists_from (first : Bool) (A : Mat ℝ n n) (r c : ℕ)
    (hz : LowerZero A r c) :
    ∃ U history swaps, PartialRun first r c A U history swaps := by
  classical
  have aux : ∀ k c r (A : Mat ℝ n n), n - c ≤ k → LowerZero A r c →
      ∃ U history swaps, PartialRun first r c A U history swaps := by
    intro k
    induction k with
    | zero =>
      intro c r A hk hz
      refine ⟨A, [A], [], .stop ?_⟩
      intro i hi j
      exact hz i j hi (by have := j.isLt; omega)
    | succ k ih =>
      intro c r A hk hz
      by_cases hc : c < n
      · by_cases hr : r < n
        · by_cases hcol : ∀ i : Fin n, r ≤ i.val → A i ⟨c, hc⟩ = 0
          · have hz' : LowerZero A r (c + 1) := by
              intro i j hi hj
              by_cases hjc : j.val < c
              · exact hz i j hi hjc
              · have heq : j = (⟨c, hc⟩ : Fin n) := Fin.ext (by change j.val = c; omega)
                subst j
                exact hcol i hi
            obtain ⟨U, history, swaps, ht⟩ := ih (c + 1) r A (by omega) hz'
            exact ⟨U, _, swaps, .skip hc hcol ht⟩
          · push Not at hcol
            obtain ⟨q, choice⟩ := pivotChoice_exists first A ⟨r, hr⟩ ⟨c, hc⟩ hcol
            have hz' := eliminate_lowerZero A ⟨r, hr⟩ q ⟨c, hc⟩
              choice.1 choice.2.1 hz
            obtain ⟨U, history, swaps, ht⟩ := ih (c + 1) (r + 1) _ (by omega) hz'
            exact ⟨U, _, _, .pivot hr hc q choice ht⟩
        · refine ⟨A, [A], [], .stop ?_⟩
          intro i hi
          have := i.isLt
          omega
      · refine ⟨A, [A], [], .stop ?_⟩
        intro i hi j
        exact hz i j hi (by have := j.isLt; omega)
  exact aux (n - c) c r A le_rfl hz

theorem partial_run_exists : Specs.NumAnalysis206.PartialPivotGrowth.partial_run_exists := by
  intro n first A
  exact partial_run_exists_from first A 0 0 (by intro i j _ hj; omega)

/-- Explicit matrix after k unexchanged pivots of Wilkinson's example. -/
def wilkinsonStage (n k : ℕ) : Mat ℝ n n := fun i j =>
  if j.val + 1 = n then (2 : ℝ) ^ min i.val k
  else if i = j then 1 else if k ≤ j.val ∧ j < i then -1 else 0

@[simp] theorem wilkinsonStage_zero (n : ℕ) : wilkinsonStage n 0 = wilkinson n := by
  ext i j
  simp [wilkinsonStage, wilkinson]

/-- The diagonal row is always a permissible first largest pivot. -/
theorem wilkinsonStage_choice (k : Fin n) :
    PivotChoice true (wilkinsonStage n k.val) k k k := by
  refine ⟨le_rfl, ?_, ?_, ?_⟩
  · simp only [wilkinsonStage, Nat.min_self, ↓reduceIte]
    split_ifs <;> positivity
  · intro i hi
    by_cases hk : k.val + 1 = n
    · have hieq : i = k := Fin.ext (by have := i.isLt; change k.val ≤ i.val at hi; omega)
      subst i; exact le_rfl
    · simp only [wilkinsonStage, hk, ↓reduceIte]
      split_ifs <;> norm_num
  · intro _ i hi _
    exact hi

/-- Completed rows remain fixed in the explicit stage formula. -/
theorem wilkinsonStage_fixed (k : ℕ) (i : Fin n) (hi : i.val ≤ k) (j : Fin n) :
    wilkinsonStage n (k + 1) i j = wilkinsonStage n k i j := by
  by_cases hj : j.val + 1 = n
  · simp [wilkinsonStage, hj, Nat.min_eq_left hi,
      Nat.min_eq_left (by omega : i.val ≤ k + 1)]
  · have hzero : ¬(k ≤ j.val ∧ j < i) := by
      rintro ⟨ha, hb⟩; change j.val < i.val at hb; omega
    have hzero' : ¬(k + 1 ≤ j.val ∧ j < i) := by
      rintro ⟨ha, hb⟩; change j.val < i.val at hb; omega
    simp only [wilkinsonStage, ite_eq_right hj, ite_eq_right hzero, ite_eq_right hzero']

/-- A pivot doubles the active last column and clears its own column. -/
theorem wilkinsonStage_eliminate (k : Fin n) :
    eliminate (wilkinsonStage n k.val) k k k = wilkinsonStage n (k.val + 1) := by
  classical
  ext i j
  by_cases hi : i ≤ k
  · have hnot : ¬k < i := not_lt.mpr hi
    simp only [eliminate, multipliers, hnot, ↓reduceIte, Equiv.swap_self,
      Equiv.refl_apply, zero_mul, sub_zero]
    exact (wilkinsonStage_fixed k.val i hi j).symm
  · have hki : k < i := lt_of_not_ge hi
    have hk : k.val + 1 ≠ n := by have := i.isLt; change k.val < i.val at hki; omega
    have hm : multipliers (wilkinsonStage n k.val) k k k i = -1 := by
      simp [multipliers, hki, wilkinsonStage, hk, ne_of_gt hki]
    simp only [eliminate, Equiv.swap_self, Equiv.refl_apply, hm, neg_one_mul, sub_neg_eq_add]
    by_cases hj : j.val + 1 = n
    · simp only [wilkinsonStage, hj, ↓reduceIte, Nat.min_self,
        Nat.min_eq_right (le_of_lt hki), Nat.min_eq_right hki]
      rw [pow_succ]
      ring
    · by_cases hjk : j = k
      · subst j
        have hnot : ¬k.val + 1 ≤ k.val := by omega
        simp [wilkinsonStage, hk, ne_of_gt hki, hki, hnot]
      · have hrow : wilkinsonStage n k.val k j = 0 := by
          have hnot : ¬(k.val ≤ j.val ∧ j < k) := by
            rintro ⟨ha, hb⟩; change j.val < k.val at hb; omega
          simp only [wilkinsonStage, ite_eq_right hj, ite_eq_right (Ne.symm hjk), ite_eq_right hnot]
        rw [hrow, add_zero]
        have heq : (k.val ≤ j.val ∧ j < i) ↔ (k.val + 1 ≤ j.val ∧ j < i) := by
          have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
          constructor <;> intro h <;> constructor <;> omega
        simp only [wilkinsonStage, hj, ↓reduceIte, heq]

/-- A complete first-tie run of the explicit stages uses no exchanges. -/
theorem wilkinsonStage_run (n : ℕ) :
    ∃ history swaps, PartialRun true 0 0 (wilkinson n) (wilkinsonStage n n) history swaps ∧
      ∀ s ∈ swaps, s.1 = s.2 := by
  have aux : ∀ t k : ℕ, k + t = n →
      ∃ history swaps,
        PartialRun true k k (wilkinsonStage n k) (wilkinsonStage n n) history swaps ∧
        ∀ s ∈ swaps, s.1 = s.2 := by
    intro t
    induction t with
    | zero =>
      intro k hk
      have heq : k = n := by omega
      subst k
      refine ⟨_, [], .stop ?_, ?_⟩
      · intro i hi
        have := i.isLt
        omega
      · simp
    | succ t ih =>
      intro k hk
      have hkn : k < n := by omega
      let row : Fin n := ⟨k, hkn⟩
      obtain ⟨history, swaps, ht, hs⟩ := ih (k + 1) (by omega)
      refine ⟨wilkinsonStage n k :: history, (row, row) :: swaps, .pivot hkn hkn row (wilkinsonStage_choice row) ?_, ?_⟩
      · rw [wilkinsonStage_eliminate (⟨k, hkn⟩ : Fin n)]
        exact ht
      · intro s hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · subst s; rfl
        · exact hs s hmem
  simpa only [wilkinsonStage_zero] using aux n 0 (by omega)

theorem wilkinson_sharpness : Specs.NumAnalysis206.PartialPivotGrowth.wilkinson_sharpness := by
  intro n hn
  let last : Fin n := ⟨n - 1, by omega⟩
  have hlast : last.val + 1 = n := by dsimp [last]; omega
  have hentry : wilkinson n last last = 1 := by simp [wilkinson, hlast]
  have hnz : wilkinson n ≠ 0 := by
    intro h
    have hz : wilkinson n last last = 0 := congrFun (congrFun h last) last
    exact one_ne_zero (hentry.symm.trans hz)
  have hmax : maxAbs (wilkinson n) = 1 := by
    apply le_antisymm
    · apply maxAbs_le (by norm_num)
      intro i j
      unfold wilkinson
      split_ifs <;> norm_num
    · simpa [hentry] using abs_le_maxAbs (wilkinson n) last last
  obtain ⟨history, swaps, ht, hs⟩ := wilkinsonStage_run n
  refine ⟨hnz, hmax, wilkinsonStage n n, history, swaps, ht, hs, ?_⟩
  change wilkinsonStage n n last last = _
  simp [wilkinsonStage, hlast, last]

end NumAnalysis206.PartialPivotGrowth
