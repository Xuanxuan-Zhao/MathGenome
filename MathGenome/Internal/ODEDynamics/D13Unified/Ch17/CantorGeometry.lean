import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.CantorGeometry
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.ShiftCompactness
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace D13Unified.Ch17.CantorGeometry
open Set Topology
open D13Unified.Ch17.ShiftSpaces
noncomputable section
abbrev coding := Specs.D13Unified.Ch17.CantorGeometry.coding
abbrev cantorSet := Specs.D13Unified.Ch17.CantorGeometry.cantorSet
abbrev branch := Specs.D13Unified.Ch17.CantorGeometry.branch
abbrev wordMap (r : ℝ) {n : ℕ} (w : Fin n → Binary) (x : ℝ) :=
  Specs.D13Unified.Ch17.CantorGeometry.wordMap r w x
abbrev levelInterval (r : ℝ) {n : ℕ} (w : Fin n → Binary) :=
  Specs.D13Unified.Ch17.CantorGeometry.levelInterval r w
abbrev levelIntervals := Specs.D13Unified.Ch17.CantorGeometry.levelIntervals

lemma digit_bounds (a : Binary) : 0 ≤ (a.val : ℝ) ∧ (a.val : ℝ) ≤ 1 := by
  fin_cases a <;> norm_num

lemma geometric_summable {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) :
    Summable (fun j : ℕ => r^j) :=
  summable_geometric_of_abs_lt_one (by rw [abs_of_pos hr]; linarith)

lemma digit_term_bound {r : ℝ} (hr : 0 < r) (s : OneSided) (j : ℕ) :
    ‖((s j).val : ℝ) * r^j‖ ≤ r^j := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (digit_bounds _).1 (pow_nonneg hr.le _))]
  exact mul_le_of_le_one_left (pow_nonneg hr.le _) (digit_bounds _).2

theorem series_summable : Specs.D13Unified.Ch17.CantorGeometry.series_summableStatement := by
  intro r hr hrh s
  exact Summable.of_norm_bounded (geometric_summable hr hrh) (digit_term_bound hr s)

theorem series_uniform : Specs.D13Unified.Ch17.CantorGeometry.series_uniformStatement := by
  intro r hr hrh
  exact tendstoUniformly_tsum_nat (geometric_summable hr hrh) (fun j s => digit_term_bound hr s j)

theorem coding_continuous : Specs.D13Unified.Ch17.CantorGeometry.coding_continuousStatement := by
  intro r hr hrh
  apply Continuous.const_mul
  apply continuous_tsum (u := fun j : ℕ => r^j) _ (geometric_summable hr hrh)
    (fun j s => digit_term_bound hr s j)
  intro j
  exact ((continuous_of_discreteTopology : Continuous (fun a : Binary => (a.val : ℝ))).comp
    (continuous_apply j)).mul_const _

lemma coding_mem_unit {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) (s : OneSided) :
    coding r s ∈ Icc 0 1 := by
  have hr1 : r < 1 := by linarith
  have hg := geometric_summable hr hrh
  have hs := series_summable r hr hrh s
  constructor
  · exact mul_nonneg (by linarith) (tsum_nonneg fun j =>
      mul_nonneg (digit_bounds _).1 (pow_nonneg hr.le _))
  · have hle : (∑' j : ℕ, ((s j).val : ℝ) * r^j) ≤ ∑' j : ℕ, r^j :=
      Summable.tsum_le_tsum (fun j =>
        mul_le_of_le_one_left (pow_nonneg hr.le j) (digit_bounds _).2) hs hg
    change (1-r) * _ ≤ 1
    calc
      _ ≤ (1-r) * (∑' j : ℕ, r^j) := mul_le_mul_of_nonneg_left hle (by linarith)
      _ = 1 := by
        rw [tsum_geometric_of_abs_lt_one (by rw [abs_of_pos hr]; exact hr1)]
        exact mul_inv_cancel₀ (by linarith)

theorem cantor_subset_unit : Specs.D13Unified.Ch17.CantorGeometry.cantor_subset_unitStatement := by
  rintro r hr hrh x ⟨s, rfl⟩
  exact coding_mem_unit hr hrh s

theorem cantor_compact : Specs.D13Unified.Ch17.CantorGeometry.cantor_compactStatement := by
  intro r hr hrh
  exact isCompact_range (coding_continuous r hr hrh)

lemma coding_cons {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) (s : OneSided) :
    coding r s = branch r (s 0) (coding r (fun j => s (j+1))) := by
  have h := (series_summable r hr hrh s).tsum_eq_zero_add
  have htail : (∑' j : ℕ, ((s (j+1)).val : ℝ) * r^(j+1)) =
      r * ∑' j : ℕ, ((s (j+1)).val : ℝ) * r^j := by
    simp_rw [pow_succ]
    rw [← tsum_mul_left]
    congr 1
    funext j
    ring
  unfold coding Specs.D13Unified.Ch17.CantorGeometry.coding branch
    Specs.D13Unified.Ch17.CantorGeometry.branch
  rw [h, htail]
  simp only [pow_zero, mul_one]
  ring

theorem branch_zero : Specs.D13Unified.Ch17.CantorGeometry.branch_zeroStatement := by
  intro r x
  simp [Specs.D13Unified.Ch17.CantorGeometry.branch]

theorem branch_one : Specs.D13Unified.Ch17.CantorGeometry.branch_oneStatement := by
  intro r x
  simp [Specs.D13Unified.Ch17.CantorGeometry.branch]
  ring

/-- Strict separation of the two first-level branches. -/
lemma branch_collision {r : ℝ} (hr : 0 < r) (hrh : r < 1/2)
    {a b : Binary} {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1)
    (h : branch r a x = branch r b y) : a = b ∧ x = y := by
  have hab : a = b := by
    by_contra hab
    fin_cases a <;> fin_cases b
    all_goals norm_num at hab
    all_goals norm_num [branch, Specs.D13Unified.Ch17.CantorGeometry.branch] at h
    all_goals nlinarith [hx.1, hx.2, hy.1, hy.2]
  subst b
  refine ⟨rfl, ?_⟩
  dsimp [branch, Specs.D13Unified.Ch17.CantorGeometry.branch] at h
  nlinarith

lemma coding_head_tail {r : ℝ} (hr : 0 < r) (hrh : r < 1/2)
    {s t : OneSided} (h : coding r s = coding r t) :
    s 0 = t 0 ∧ coding r (fun j => s (j+1)) = coding r (fun j => t (j+1)) := by
  rw [coding_cons hr hrh s, coding_cons hr hrh t] at h
  exact branch_collision hr hrh (coding_mem_unit hr hrh _) (coding_mem_unit hr hrh _) h

theorem coding_injective : Specs.D13Unified.Ch17.CantorGeometry.coding_injectiveStatement := by
  intro r hr hrh s t h
  have htail : ∀ n : ℕ, coding r (fun j => s (j+n)) = coding r (fun j => t (j+n)) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (coding_head_tail hr hrh ih).2
  funext n
  simpa using (coding_head_tail hr hrh (htail n)).1

theorem coding_homeomorph : Specs.D13Unified.Ch17.CantorGeometry.coding_homeomorphStatement := by
  intro r hr hrh
  let e : OneSided ≃ cantorSet r := Equiv.ofInjective (coding r) (coding_injective r hr hrh)
  have he : Continuous e := (coding_continuous r hr hrh).subtype_mk _
  exact ⟨e.toHomeomorphOfContinuousClosed he he.isClosedMap, fun _ => rfl⟩

theorem wordMap_affine : Specs.D13Unified.Ch17.CantorGeometry.wordMap_affineStatement := by
  intro r n
  induction n with
  | zero => intro w x; simp [Specs.D13Unified.Ch17.CantorGeometry.wordMap]
  | succ n ih =>
    intro w x
    change branch r (w 0) (wordMap r (Fin.tail w) x) =
      branch r (w 0) (wordMap r (Fin.tail w) 0) + r^(n+1)*x
    simp only [wordMap]
    rw [ih (Fin.tail w) x]
    dsimp [branch, Specs.D13Unified.Ch17.CantorGeometry.branch]
    rw [pow_succ]
    ring

theorem levelInterval_length : Specs.D13Unified.Ch17.CantorGeometry.levelInterval_lengthStatement := by
  intro r _ _ n w
  rw [wordMap_affine r n w 1]
  ring

lemma wordMap_mem_unit {r : ℝ} (hr : 0 < r) (hrh : r < 1/2)
    (n : ℕ) (w : Fin n → Binary) {x : ℝ} (hx : x ∈ Icc 0 1) :
    wordMap r w x ∈ Icc 0 1 := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    have h := ih (Fin.tail w)
    change branch r (w 0) (wordMap r (Fin.tail w) x) ∈ Icc 0 1
    dsimp [branch, Specs.D13Unified.Ch17.CantorGeometry.branch]
    constructor
    · exact add_nonneg (mul_nonneg hr.le h.1)
        (mul_nonneg (by linarith) (digit_bounds _).1)
    · have hd := digit_bounds (w 0)
      have hmul := mul_le_mul_of_nonneg_left h.2 hr.le
      have hmul' := mul_le_mul_of_nonneg_left hd.2 (show 0 ≤ 1-r by linarith)
      nlinarith

theorem levelInterval_image : Specs.D13Unified.Ch17.CantorGeometry.levelInterval_imageStatement := by
  intro r hr _ n w
  have hp : 0 < r^n := pow_pos hr n
  ext y
  constructor
  · rintro ⟨hl, hu⟩
    refine ⟨(y-wordMap r w 0) / r^n, ⟨div_nonneg (sub_nonneg.mpr hl) hp.le, ?_⟩, ?_⟩
    · rw [div_le_one hp]
      have hh := wordMap_affine r n w 1
      linarith
    · rw [wordMap_affine r n w]
      field_simp
      ring
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    change wordMap r w 0 ≤ wordMap r w x ∧ wordMap r w x ≤ wordMap r w 1
    simp only [wordMap]
    rw [wordMap_affine r n w x, wordMap_affine r n w 1]
    constructor <;> nlinarith

/-- The series point lies in the interval determined by any initial word. -/
lemma coding_prefix {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) (s : OneSided) (n : ℕ) :
    coding r s = wordMap r (fun i : Fin n => s i) (coding r (fun j => s (j+n))) := by
  induction n generalizing s with
  | zero => simp [Specs.D13Unified.Ch17.CantorGeometry.wordMap]
  | succ n ih =>
    rw [coding_cons hr hrh s]
    rw [ih (fun j => s (j+1))]
    rfl

theorem level_cover : Specs.D13Unified.Ch17.CantorGeometry.level_coverStatement := by
  rintro r hr hrh n x ⟨s, rfl⟩
  refine mem_iUnion.mpr ⟨fun i : Fin n => s i, ?_⟩
  rw [levelInterval_image r hr hrh]
  exact ⟨coding r (fun j => s (j+n)), coding_mem_unit hr hrh _, (coding_prefix hr hrh s n).symm⟩

/-- Quantitative first-level gap. -/
lemma branch_gap {r : ℝ} (hr : 0 < r) (_hrh : r < 1/2)
    {a b : Binary} {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1)
    (hab : a ≠ b) : 1-2*r ≤ |branch r a x - branch r b y| := by
  have hx0 := mul_nonneg hr.le hx.1
  have hy0 := mul_nonneg hr.le hy.1
  have hx1 := mul_le_mul_of_nonneg_left hx.2 hr.le
  have hy1 := mul_le_mul_of_nonneg_left hy.2 hr.le
  have ha := le_abs_self (branch r a x - branch r b y)
  have hb := neg_le_abs (branch r a x - branch r b y)
  fin_cases a <;> fin_cases b
  all_goals norm_num at hab
  all_goals norm_num [branch, Specs.D13Unified.Ch17.CantorGeometry.branch] at ha hb ⊢
  all_goals linarith

/-- Removing a common first symbol scales the gap by exactly r. -/
lemma word_gap {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) (n : ℕ)
    (u v : Fin (n+1) → Binary) (huv : u ≠ v)
    {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    (1-2*r)*r^n ≤ |wordMap r u x - wordMap r v y| := by
  induction n with
  | zero =>
    have hhead : u 0 ≠ v 0 := by
      intro h
      apply huv
      funext i
      fin_cases i
      exact h
    simpa [wordMap, Specs.D13Unified.Ch17.CantorGeometry.wordMap] using
      branch_gap hr hrh hx hy hhead
  | succ n ih =>
    by_cases hhead : u 0 = v 0
    · have htail : Fin.tail u ≠ Fin.tail v := by
        intro h
        apply huv
        exact Fin.cons_self_tail u ▸ Fin.cons_self_tail v ▸ congrArg₂ Fin.cons hhead h
      have h := ih (Fin.tail u) (Fin.tail v) htail
      have heq : wordMap r u x - wordMap r v y =
          r * (wordMap r (Fin.tail u) x - wordMap r (Fin.tail v) y) := by
        change branch r (u 0) _ - branch r (v 0) _ = _
        rw [hhead]
        dsimp [branch, Specs.D13Unified.Ch17.CantorGeometry.branch]
        ring
      rw [heq, abs_mul, abs_of_pos hr, pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left h hr.le]
    · have h := branch_gap hr hrh (wordMap_mem_unit hr hrh _ (Fin.tail u) hx)
        (wordMap_mem_unit hr hrh _ (Fin.tail v) hy) hhead
      have hp : r^(n+1) ≤ 1 := pow_le_one₀ hr.le (by linarith)
      have hg : 0 ≤ 1-2*r := by linarith
      exact (mul_le_of_le_one_right hg hp).trans h

theorem level_gap : Specs.D13Unified.Ch17.CantorGeometry.level_gapStatement := by
  rintro r hr hrh n hn u v huv x hx y hy
  rw [levelInterval_image r hr hrh] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  cases n with
  | zero => omega
  | succ n => simpa using word_gap hr hrh n u v huv ha hb

theorem level_disjoint : Specs.D13Unified.Ch17.CantorGeometry.level_disjointStatement := by
  intro r hr hrh n u v huv
  by_cases hn : n = 0
  · subst n
    exact (huv (Subsingleton.elim _ _)).elim
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h := level_gap r hr hrh n (by omega) u v huv x hx x hy
  have hp : 0 < (1-2*r)*r^(n-1) := mul_pos (by linarith) (pow_pos hr _)
  simp only [sub_self, abs_zero] at h
  linarith

lemma levelInterval_injective {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) (n : ℕ) :
    Function.Injective (fun w : Fin n → Binary => levelInterval r w) := by
  intro u v h
  by_contra huv
  have hmem : wordMap r u 0 ∈ levelInterval r u := by
    change wordMap r u 0 ≤ wordMap r u 0 ∧ wordMap r u 0 ≤ wordMap r u 1
    refine ⟨le_rfl, ?_⟩
    have hl := levelInterval_length r hr hrh n u
    have hp := pow_nonneg hr.le n
    linarith
  exact Set.disjoint_left.mp (level_disjoint r hr hrh n huv) hmem ((congrArg (fun S : Set ℝ => wordMap r u 0 ∈ S) h).mp hmem)

theorem level_card : Specs.D13Unified.Ch17.CantorGeometry.level_cardStatement := by
  intro r hr hrh n
  classical
  change (Finset.univ.image (fun w : Fin n → Binary => levelInterval r w)).card = _
  rw [Finset.card_image_of_injective _ (levelInterval_injective hr hrh n)]
  simp [Binary, Specs.D13Unified.Ch17.ShiftSpaces.Binary]

theorem coding_mem_level_iff :
    Specs.D13Unified.Ch17.CantorGeometry.coding_mem_level_iffStatement := by
  intro r hr hrh n w s
  have hprefix : coding r s ∈ levelInterval r (fun i : Fin n => s i) := by
    simp only [levelInterval]
    rw [levelInterval_image r hr hrh]
    exact ⟨coding r (fun j => s (j+n)), coding_mem_unit hr hrh _, (coding_prefix hr hrh s n).symm⟩
  constructor
  · intro hw
    have heq : (fun i : Fin n => s i) = w := by
      by_contra hne
      exact Set.disjoint_left.mp (level_disjoint r hr hrh n hne) hprefix hw
    exact congrFun heq
  · intro h
    have heq : (fun i : Fin n => s i) = w := funext h
    simpa only [heq] using hprefix

end
end D13Unified.Ch17.CantorGeometry
