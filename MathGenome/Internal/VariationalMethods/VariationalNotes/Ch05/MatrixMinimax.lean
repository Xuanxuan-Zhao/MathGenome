import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.MatrixMinimax
import Mathlib.Topology.Sion
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

open scoped BigOperators
open Set

namespace VariationalNotes.Ch05.MatrixGame

lemma payoff_columns {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin m → ℝ) (q : Fin n → ℝ) :
    payoff M p q = ∑ j, q j * columnPayoff M p j := by
  simp only [payoff, columnPayoff, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext j
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma payoff_rows {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin m → ℝ) (q : Fin n → ℝ) :
    payoff M p q = ∑ i, p i * rowPayoff M q i := by
  simp [payoff, rowPayoff, Finset.mul_sum, mul_assoc]

lemma payoff_single_column {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin m → ℝ) (j : Fin n) :
    payoff M p (Pi.single j 1) = columnPayoff M p j := by
  rw [payoff_columns]
  simp [Pi.single_apply]

lemma payoff_single_row {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) (i : Fin m) :
    payoff M (Pi.single i 1) q = rowPayoff M q i := by
  rw [payoff_rows]
  simp [Pi.single_apply]

lemma weighted_min {k : ℕ} (f w : Fin k → ℝ) (hw : w ∈ simplex k)
    (j : Fin k) (hj : ∀ i, f j ≤ f i) : f j ≤ ∑ i, w i * f i := by
  calc
    f j = ∑ i, w i * f j := by rw [← Finset.sum_mul, hw.2, one_mul]
    _ ≤ ∑ i, w i * f i := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hj i) (hw.1 i)

lemma weighted_max {k : ℕ} (f w : Fin k → ℝ) (hw : w ∈ simplex k)
    (j : Fin k) (hj : ∀ i, f i ≤ f j) : (∑ i, w i * f i) ≤ f j := by
  calc
    (∑ i, w i * f i) ≤ ∑ i, w i * f j :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hj i) (hw.1 i)
    _ = f j := by rw [← Finset.sum_mul, hw.2, one_mul]

theorem fixed_minimum : Specs.FixedMinimum := by
  intro m n hm hn M p hp
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ (columnPayoff M p) Finset.univ_nonempty
  have hj' : ∀ i, columnPayoff M p j ≤ columnPayoff M p i := fun i => hj i (Finset.mem_univ i)
  have hleast : IsLeast (range (columnPayoff M p)) (columnPayoff M p j) :=
    ⟨⟨j, rfl⟩, by rintro _ ⟨i, rfl⟩; exact hj' i⟩
  have hleast' : IsLeast ((payoff M p) '' simplex n) (columnPayoff M p j) := by
    constructor
    · exact ⟨Pi.single j 1, single_mem_stdSimplex ℝ j, payoff_single_column M p j⟩
    · rintro _ ⟨q, hq, rfl⟩
      rw [payoff_columns]
      exact weighted_min _ _ hq j hj'
  exact ⟨j, hleast, hleast', hleast'.csInf_eq.trans hleast.csInf_eq.symm⟩

theorem fixed_maximum : Specs.FixedMaximum := by
  intro m n hm hn M q hq
  have : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (rowPayoff M q) Finset.univ_nonempty
  have hi' : ∀ j, rowPayoff M q j ≤ rowPayoff M q i := fun j => hi j (Finset.mem_univ j)
  have hgreat : IsGreatest (range (rowPayoff M q)) (rowPayoff M q i) :=
    ⟨⟨i, rfl⟩, by rintro _ ⟨j, rfl⟩; exact hi' j⟩
  have hgreat' : IsGreatest ((fun p => payoff M p q) '' simplex m) (rowPayoff M q i) := by
    constructor
    · exact ⟨Pi.single i 1, single_mem_stdSimplex ℝ i, payoff_single_row M q i⟩
    · rintro _ ⟨p, hp, rfl⟩
      change payoff M p q ≤ _
      rw [payoff_rows]
      exact weighted_max _ _ hp i hi'
  exact ⟨i, hgreat, hgreat', hgreat'.csSup_eq.trans hgreat.csSup_eq.symm⟩

/-- The payoff as a linear functional of the row strategy. -/
def rowLinear {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (q : Fin n → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun p := payoff M p q
  map_add' p r := by simp [payoff, add_mul, Finset.sum_add_distrib]
  map_smul' a p := by simp [payoff, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- The payoff as a linear functional of the column strategy. -/
def columnLinear {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (p : Fin m → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun q := payoff M p q
  map_add' q r := by simp [payoff, mul_add, Finset.sum_add_distrib]
  map_smul' a q := by
    simp [payoff, smul_eq_mul, mul_left_comm, mul_comm, Finset.mul_sum]

lemma continuous_payoff_left {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (q : Fin n → ℝ) : Continuous (fun p => payoff M p q) := by
  unfold payoff
  fun_prop

lemma continuous_payoff_right {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin m → ℝ) : Continuous (payoff M p) := by
  unfold payoff
  fun_prop

lemma exists_saddle {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (M : Matrix (Fin m) (Fin n) ℝ) :
    ∃ p ∈ simplex m, ∃ q ∈ simplex n,
      (∀ p' ∈ simplex m, payoff M p' q ≤ payoff M p q) ∧
      (∀ q' ∈ simplex n, payoff M p q ≤ payoff M p q') := by
  have neM : (simplex m).Nonempty :=
    ⟨Pi.single ⟨0, hm⟩ 1, single_mem_stdSimplex ℝ _⟩
  have neN : (simplex n).Nonempty :=
    ⟨Pi.single ⟨0, hn⟩ 1, single_mem_stdSimplex ℝ _⟩
  obtain ⟨q, hq, p, hp, h⟩ := Sion.exists_isSaddlePointOn
    (X := simplex n) (Y := simplex m) (f := fun q p => payoff M p q)
    neN (convex_stdSimplex ℝ _) (isCompact_stdSimplex ℝ _)
    (fun p _ => (continuous_payoff_right M p).continuousOn.lowerSemicontinuousOn)
    (fun p _ => (columnLinear M p).convexOn (convex_stdSimplex ℝ _) |>.quasiconvexOn)
    (convex_stdSimplex ℝ _) neM (isCompact_stdSimplex ℝ _)
    (fun q _ => (continuous_payoff_left M q).continuousOn.upperSemicontinuousOn)
    (fun q _ => (rowLinear M q).concaveOn (convex_stdSimplex ℝ _) |>.quasiconcaveOn)
  exact ⟨p, hp, q, hq, fun p' hp' => h q hq p' hp', fun q' hq' => h q' hq' p hp⟩

lemma lower_le_payoff {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (M : Matrix (Fin m) (Fin n) ℝ) {p : Fin m → ℝ} {q : Fin n → ℝ}
    (hp : p ∈ simplex m) (hq : q ∈ simplex n) : lower M p ≤ payoff M p q := by
  obtain ⟨j, _, hmin, _⟩ := fixed_minimum hm hn M p hp
  change sInf _ ≤ _
  rw [hmin.csInf_eq]
  exact hmin.2 ⟨q, hq, rfl⟩

lemma payoff_le_upper {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (M : Matrix (Fin m) (Fin n) ℝ) {p : Fin m → ℝ} {q : Fin n → ℝ}
    (hp : p ∈ simplex m) (hq : q ∈ simplex n) : payoff M p q ≤ upper M q := by
  obtain ⟨i, _, hmax, _⟩ := fixed_maximum hm hn M q hq
  change _ ≤ sSup _
  rw [hmax.csSup_eq]
  exact hmax.2 ⟨p, hp, rfl⟩

/-- The finite matrix game theorem, with real attained extrema. -/
theorem matrix_minimax : Specs.MatrixMinimax := by
  intro m n hm hn M
  obtain ⟨p, hp, q, hq, hleft, hright⟩ := exists_saddle hm hn M
  have hmin : IsLeast ((payoff M p) '' simplex n) (payoff M p q) := by
    refine ⟨⟨q, hq, rfl⟩, ?_⟩
    rintro _ ⟨q', hq', rfl⟩
    exact hright q' hq'
  have hmax : IsGreatest ((fun p' => payoff M p' q) '' simplex m) (payoff M p q) := by
    refine ⟨⟨p, hp, rfl⟩, ?_⟩
    rintro _ ⟨p', hp', rfl⟩
    exact hleft p' hp'
  have hlower : lower M p = payoff M p q := hmin.csInf_eq
  have hupper : upper M q = payoff M p q := hmax.csSup_eq
  have houterMax : IsGreatest (lower M '' simplex m) (payoff M p q) := by
    refine ⟨⟨p, hp, hlower⟩, ?_⟩
    rintro _ ⟨p', hp', rfl⟩
    exact (lower_le_payoff hm hn M hp' hq).trans (hleft p' hp')
  have houterMin : IsLeast (upper M '' simplex n) (payoff M p q) := by
    refine ⟨⟨q, hq, hupper⟩, ?_⟩
    rintro _ ⟨q', hq', rfl⟩
    exact (hright q' hq').trans (payoff_le_upper hm hn M hp hq')
  exact ⟨p, hp, q, hq, hleft, hright, hlower, hupper, houterMax, houterMin,
    houterMax.csSup_eq.trans houterMin.csInf_eq.symm⟩

end VariationalNotes.Ch05.MatrixGame
