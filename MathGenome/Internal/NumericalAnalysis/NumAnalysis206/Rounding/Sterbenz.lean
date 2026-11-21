import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.RadixModel
import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Rounding.Sterbenz
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace NumAnalysis206.Rounding

lemma neg_mem_F_iff (P : RadixFormat) (x : ℝ) : -x ∈ F P ↔ x ∈ F P := by
  rw [mem_F, mem_F]
  constructor <;> intro h
  · rcases h with hz | ⟨m, e, hm, hm', he, he', hx | hx⟩ | ⟨hg, m, hm, hm', hx | hx⟩
    · exact Or.inl (neg_eq_zero.mp hz)
    · exact Or.inr (Or.inl ⟨m, e, hm, hm', he, he', Or.inr (by linarith)⟩)
    · exact Or.inr (Or.inl ⟨m, e, hm, hm', he, he', Or.inl (by linarith)⟩)
    · exact Or.inr (Or.inr ⟨hg, m, hm, hm', Or.inr (by linarith)⟩)
    · exact Or.inr (Or.inr ⟨hg, m, hm, hm', Or.inl (by linarith)⟩)
  · rcases h with hz | ⟨m, e, hm, hm', he, he', hx | hx⟩ | ⟨hg, m, hm, hm', hx | hx⟩
    · exact Or.inl (by simp [hz])
    · exact Or.inr (Or.inl ⟨m, e, hm, hm', he, he', Or.inr (by linarith)⟩)
    · exact Or.inr (Or.inl ⟨m, e, hm, hm', he, he', Or.inl (by linarith)⟩)
    · exact Or.inr (Or.inr ⟨hg, m, hm, hm', Or.inr (by linarith)⟩)
    · exact Or.inr (Or.inr ⟨hg, m, hm, hm', Or.inl (by linarith)⟩)

lemma radix_pos (P : RadixFormat) : (0 : ℝ) < P.β := by
  exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℤ) < 2) P.radix_ge_two)

lemma radix_pow_precision (P : RadixFormat) :
    P.β ^ P.p = P.β ^ (P.p - 1) * P.β := by
  conv_lhs => rw [← Nat.sub_add_cancel P.precision_pos]
  exact pow_succ _ _

/-- A short coefficient on any in-range grid can be normalized, stopping at
    the minimum exponent where gradual underflow permits the short coefficient. -/
lemma short_grid_mem (P : RadixFormat) (hg : P.gradual = true)
    (e : ℤ) (he : P.emin ≤ e) (he' : e ≤ P.emax)
    (m : ℤ) (hm : 0 ≤ m) (hm' : m < P.β ^ P.p) :
    (m : ℝ) * (P.β : ℝ) ^ e ∈ F P := by
  have induction_step : ∀ n : ℕ, ∀ e : ℤ, e - P.emin = n →
      e ≤ P.emax → ∀ m : ℤ, 0 ≤ m → m < P.β ^ P.p →
      (m : ℝ) * (P.β : ℝ) ^ e ∈ F P := by
    intro n
    induction n with
    | zero =>
      intro e heq hemax m hm hmmax
      have hemin : e = P.emin := by omega
      subst e
      by_cases hz : m = 0
      · simp [hz]
      by_cases hn : P.β ^ (P.p - 1) ≤ m
      · exact (mem_F _ _).mpr (Or.inr (Or.inl
          ⟨m, P.emin, hn, hmmax, le_rfl, hemax, Or.inl rfl⟩))
      · exact (mem_F _ _).mpr (Or.inr (Or.inr
          ⟨hg, m, by omega, by omega, Or.inl rfl⟩))
    | succ n ih =>
      intro e heq hemax m hm hmmax
      by_cases hn : P.β ^ (P.p - 1) ≤ m
      · exact (mem_F _ _).mpr (Or.inr (Or.inl
          ⟨m, e, hn, hmmax, by omega, hemax, Or.inl rfl⟩))
      · have hβ : (0 : ℤ) < P.β := by linarith [P.radix_ge_two]
        have hmul : m * P.β < P.β ^ P.p := by
          rw [radix_pow_precision]
          exact mul_lt_mul_of_pos_right (by omega) hβ
        have h := ih (e - 1) (by omega) (by omega) (m * P.β)
          (mul_nonneg hm hβ.le) hmul
        have hp := zpow_add₀ (ne_of_gt (radix_pos P)) (e - 1) (1 : ℤ)
        have heid : e - 1 + 1 = e := by ring
        rw [heid, zpow_one] at hp
        convert h using 1
        push_cast
        rw [hp]
        ring
  exact induction_step (e - P.emin).toNat e (by omega) he' m hm hm'

/-- Positive stored inputs admit a short coefficient on an in-range grid. -/
lemma positive_grid (P : RadixFormat) (a : ℝ) (ha : a ∈ F P) (ha0 : 0 < a) :
    ∃ m e : ℤ, 0 < m ∧ m < P.β ^ P.p ∧ P.emin ≤ e ∧ e ≤ P.emax ∧
      a = (m : ℝ) * (P.β : ℝ) ^ e := by
  have hβ : (0 : ℤ) < P.β := by linarith [P.radix_ge_two]
  rcases (mem_F P a).mp ha with hz | ⟨m, e, hm, hm', he, he', hx⟩ |
      ⟨hg, m, hm, hm', hx⟩
  · linarith
  · have hm0 : (0 : ℤ) < m := lt_of_lt_of_le (pow_pos hβ _) hm
    have hv : 0 < (m : ℝ) * (P.β : ℝ) ^ e :=
      mul_pos (by exact_mod_cast hm0) (zpow_pos (radix_pos P) _)
    rcases hx with hx | hx
    · exact ⟨m, e, hm0, hm', he, he', hx⟩
    · linarith
  · have hm0 : (0 : ℤ) < m := by omega
    have hv : 0 < (m : ℝ) * (P.β : ℝ) ^ P.emin :=
      mul_pos (by exact_mod_cast hm0) (zpow_pos (radix_pos P) _)
    rcases hx with hx | hx
    · refine ⟨m, P.emin, hm0, ?_, le_rfl, P.exponent_order, hx⟩
      have hp : P.β ^ (P.p - 1) ≤ P.β ^ P.p := by
        exact pow_le_pow_right₀ (by linarith : (1 : ℤ) ≤ P.β) (by omega)
      exact hm'.trans_le hp
    · linarith

/-- A value on a coarser grid is an integer multiple of a finer grid. -/
lemma grid_refine (P : RadixFormat) (m e f : ℤ) (hef : e ≤ f) :
    (m : ℝ) * (P.β : ℝ) ^ f =
      ((m * P.β ^ (f - e).toNat : ℤ) : ℝ) * (P.β : ℝ) ^ e := by
  have heq : ((f - e).toNat : ℤ) + e = f := by omega
  push_cast
  rw [← zpow_natCast, mul_assoc, ← zpow_add₀ (ne_of_gt (radix_pos P)), heq]

lemma signed_short_grid_mem (P : RadixFormat) (hg : P.gradual = true)
    (e : ℤ) (he : P.emin ≤ e) (he' : e ≤ P.emax)
    (m : ℤ) (hm : |m| < P.β ^ P.p) :
    (m : ℝ) * (P.β : ℝ) ^ e ∈ F P := by
  by_cases hm0 : 0 ≤ m
  · exact short_grid_mem P hg e he he' m hm0 (by simpa [abs_of_nonneg hm0] using hm)
  · have h := short_grid_mem P hg e he he' (-m) (by omega)
      (by simpa [abs_of_neg (show m < 0 by omega)] using hm)
    have hneg := (neg_mem_F_iff P _).mpr h
    simpa using hneg

/-- Grid alignment plus a bound by the input's coefficient. -/
lemma grid_sub_mem (P : RadixFormat) (hg : P.gradual = true)
    (e : ℤ) (he : P.emin ≤ e) (he' : e ≤ P.emax)
    (m n : ℤ) (hm : m < P.β ^ P.p)
    (hd : |(m : ℝ) * (P.β : ℝ) ^ e - (n : ℝ) * (P.β : ℝ) ^ e| ≤
      (m : ℝ) * (P.β : ℝ) ^ e) :
    (m : ℝ) * (P.β : ℝ) ^ e - (n : ℝ) * (P.β : ℝ) ^ e ∈ F P := by
  have hp := zpow_pos (radix_pos P) e
  have hcoeff : (|(m - n : ℤ)| : ℝ) ≤ (m : ℝ) := by
    have hd' : |(m : ℝ) - (n : ℝ)| * (P.β : ℝ) ^ e ≤
        (m : ℝ) * (P.β : ℝ) ^ e := by
      simpa only [← sub_mul, abs_mul, abs_of_pos hp] using hd
    exact_mod_cast (le_of_mul_le_mul_right hd' hp)
  have hcoeff' : |m - n| < P.β ^ P.p := (by exact_mod_cast hcoeff : |m - n| ≤ m).trans_lt hm
  have h := signed_short_grid_mem P hg e he he' (m - n) hcoeff'
  convert h using 1
  push_cast
  ring

lemma sterbenz_mem (P : RadixFormat) (hg : P.gradual = true)
    (a b : ℝ) (ha : a ∈ F P) (hb : b ∈ F P) (ha0 : 0 < a) (hb0 : 0 < b)
    (hab : a / 2 ≤ b) (hba : b ≤ 2 * a) : a - b ∈ F P := by
  obtain ⟨m, e, hm0, hm, he, he', hax⟩ := positive_grid P a ha ha0
  obtain ⟨n, f, hn0, hn, hf, hf', hbx⟩ := positive_grid P b hb hb0
  have hda : |a - b| ≤ a := (abs_le).mpr ⟨by linarith, by linarith⟩
  have hdb : |a - b| ≤ b := (abs_le).mpr ⟨by linarith, by linarith⟩
  rcases le_total e f with hef | hfe
  · rw [hax, hbx, grid_refine P n e f hef] at hda ⊢
    exact grid_sub_mem P hg e he he' m _ hm hda
  · have h : b - a ∈ F P := by
      have hd : |b - a| ≤ b := by rwa [abs_sub_comm]
      rw [hax, hbx, grid_refine P m f e hfe] at hd ⊢
      exact grid_sub_mem P hg f hf hf' n _ hn hd
    have hneg := (neg_mem_F_iff P (b - a)).mpr h
    simpa only [neg_sub] using hneg

theorem sterbenz_positive : Specs.sterbenzPositive := by
  intro P hg a b ha hb ha0 hb0 hab hba
  have h := sterbenz_mem P hg a b ha hb ha0 hb0 hab hba
  exact ⟨h, fl_fixes P (a - b) h⟩

theorem sterbenz_negative : Specs.sterbenzNegative := by
  intro P hg a b ha hb ha0 hb0 hab hba
  have h := sterbenz_mem P hg (-a) (-b) ((neg_mem_F_iff P a).mpr ha)
    ((neg_mem_F_iff P b).mpr hb) (by linarith) (by linarith) hab hba
  have hd : a - b ∈ F P := by
    have hneg := (neg_mem_F_iff P (-a - -b)).mpr h
    simpa [sub_eq_add_neg, add_comm] using hneg
  exact ⟨hd, fl_fixes P _ hd⟩

theorem subtraction_equal : Specs.subtractionEqual := by
  intro P a
  change a - a ∈ F P ∧ fl P (a - a) = 0
  rw [sub_self]
  exact ⟨zero_mem_F P, fl_fixes P 0 (zero_mem_F P)⟩

theorem subtraction_sensitivity : Specs.subtractionSensitivity := by
  intro a b ε da db hε hda hdb
  have h := (abs_sub da db).trans (add_le_add hda hdb)
  calc
    |((a + da) - (b + db)) - (a - b)| = |da - db| := by congr 1; ring
    _ ≤ ε * (|a| + |b|) := by nlinarith [h]

theorem subtraction_sensitivity_sharp : Specs.subtractionSensitivitySharp := by
  intro a b ε hε
  refine ⟨ε * |a|, -(ε * |b|), ?_, ?_, ?_⟩
  · rw [abs_of_nonneg (mul_nonneg hε (abs_nonneg a))]
  · rw [abs_neg, abs_of_nonneg (mul_nonneg hε (abs_nonneg b))]
  · have hid : (a + ε * |a| - (b + -(ε * |b|))) - (a - b) =
        ε * (|a| + |b|) := by ring
    rw [hid, abs_of_nonneg (mul_nonneg hε (add_nonneg (abs_nonneg a) (abs_nonneg b)))]

theorem subtraction_relative_sensitivity : Specs.subtractionRelativeSensitivity := by
  intro a b ε hε hab
  have hp : 0 < |a - b| := abs_pos.mpr hab
  constructor
  · intro da db hda hdb
    have h := div_le_div_of_nonneg_right
      (subtraction_sensitivity a b ε da db hε hda hdb) hp.le
    simpa only [mul_div_assoc] using h
  · obtain ⟨da, db, hda, hdb, heq⟩ := subtraction_sensitivity_sharp a b ε hε
    exact ⟨da, db, hda, hdb, by rw [heq, mul_div_assoc]⟩

private def binaryExampleFormat (n : ℕ) : RadixFormat where
  β := 2
  p := n + 2
  emin := 0
  emax := 0
  gradual := true
  radix_ge_two := by norm_num
  precision_pos := by omega
  exponent_order := le_rfl

theorem exact_subtraction_unbounded_condition : Specs.exactSubtractionUnboundedCondition := by
  intro C
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
  let P := binaryExampleFormat n
  let q : ℤ := 2 ^ (n + 1)
  have hq2 : 2 ≤ q := by
    have h : (0 : ℤ) < 2 ^ n := pow_pos (by norm_num) _
    dsimp [q]
    rw [pow_succ]
    omega
  have hq : (0 : ℝ) < q := by exact_mod_cast (by omega : (0 : ℤ) < q)
  have hC : C < (q : ℝ) := by
    have heq : (q : ℝ) = (2 : ℝ) ^ n * 2 := by simp [q, pow_succ]
    rw [heq]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]
  have hlower : P.β ^ (P.p - 1) = q := by
    dsimp [P, binaryExampleFormat, q]
  have hupper : P.β ^ P.p = q * 2 := by
    change (2 : ℤ) ^ (n + 2) = 2 ^ (n + 1) * 2
    exact pow_succ 2 (n + 1)
  have ha : (q : ℝ) + 1 ∈ F P := by
    apply (mem_F P _).mpr
    refine Or.inr (Or.inl ⟨q + 1, 0, ?_, ?_, le_rfl, le_rfl, Or.inl ?_⟩)
    · rw [hlower]; omega
    · rw [hupper]; omega
    · simp
  have hb : (q : ℝ) ∈ F P := by
    apply (mem_F P _).mpr
    refine Or.inr (Or.inl ⟨q, 0, ?_, ?_, le_rfl, le_rfl, Or.inl ?_⟩)
    · rw [hlower]
    · rw [hupper]; omega
    · simp
  have hab : ((q : ℝ) + 1) / 2 ≤ q := by
    have h : (2 : ℝ) ≤ q := by exact_mod_cast hq2
    linarith
  have hba : (q : ℝ) ≤ 2 * ((q : ℝ) + 1) := by linarith
  have hd := sterbenz_mem P rfl _ _ ha hb (by linarith) hq hab hba
  refine ⟨P, (q : ℝ) + 1, (q : ℝ), rfl, ha, hb, by linarith, hq,
    hab, hba, by norm_num, fl_fixes P _ hd, ?_⟩
  rw [abs_of_pos (by linarith : (0 : ℝ) < (q : ℝ) + 1), abs_of_pos hq]
  have heq : ((q : ℝ) + 1) - q = 1 := by ring
  rw [heq]
  norm_num
  linarith

end NumAnalysis206.Rounding
