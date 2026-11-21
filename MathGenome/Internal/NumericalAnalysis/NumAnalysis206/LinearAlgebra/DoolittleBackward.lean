import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.DoolittleBackward
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.PivotedLU
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.SubtractionTrace
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.GammaProducts
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.Operations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.LinearAlgebra.Doolittle
open NumAnalysis206.MatrixDefinitions NumAnalysis206.Rounding

namespace Run
variable {n : ℕ} {round : ℝ → ℝ} {D : Set ℝ} {A : Mat ℝ n n}

/-- The zero-dimensional execution exists without any arithmetic or pivot
hypotheses; hence the main theorem's n=0 instance is not vacuous. -/
def emptyRun (round : ℝ → ℝ) (D : Set ℝ) (A : Mat ℝ 0 0) : Run round D A where
  order _ := Equiv.refl _
  state _ := A
  choice := Fin.elim0
  ell := Fin.elim0
  order_zero := rfl
  state_zero := rfl
  choice_ge t := Fin.elim0 t
  exchange t := Fin.elim0 t
  division t := Fin.elim0 t
  safety t := Fin.elim0 t
  update t := Fin.elim0 t

/-- The physical matrix in current row positions, before stage s. -/
def current (R : Run round D A) (s : ℕ) : Mat ℝ n n :=
  fun i j => R.state s (R.order s i) j

/-- The identity-row representation is exactly a swap followed by the usual
separate rounded multiplication and subtraction on the trailing submatrix. -/
theorem current_step (R : Run round D A) (t i j : Fin n) :
    R.current (t.val + 1) i j =
      if t.val < i.val ∧ t < j then
        round (R.current t.val (Equiv.swap t (R.choice t) i) j -
          round (R.ell t (R.order (t.val + 1) i) * R.current t.val (R.choice t) j))
      else R.current t.val (Equiv.swap t (R.choice t) i) j := by
  have h := R.update t (R.order (t.val + 1) i) j
  simp only [Equiv.symm_apply_apply] at h
  simpa only [current, R.exchange t, Equiv.trans_apply, Equiv.swap_apply_left] using h

/-- The initial matrix in current positions is exactly the input. -/
theorem current_zero (R : Run round D A) : R.current 0 = A := by
  ext i j
  simp [current, R.order_zero, R.state_zero]

/-- The multiplier is the actual rounded quotient by the chosen nonzero pivot,
with its individual safe-domain check. -/
theorem current_division (R : Run round D A) (t i : Fin n) (hti : t < i) :
    R.current t.val (R.choice t) t ≠ 0 ∧
    R.current t.val (Equiv.swap t (R.choice t) i) t /
      R.current t.val (R.choice t) t ∈ D ∧
    R.ell t (R.order (t.val + 1) i) =
      round (R.current t.val (Equiv.swap t (R.choice t) i) t /
        R.current t.val (R.choice t) t) := by
  have ha : t.val < ((R.order (t.val + 1)).symm (R.order (t.val + 1) i)).val := by
    simpa only [Equiv.symm_apply_apply, Fin.lt_def] using hti
  have h := R.division t (R.order (t.val + 1) i) ha
  simpa only [current, R.exchange t, Equiv.trans_apply, Equiv.swap_apply_left] using h

/-- The very same exchange also moves every previously stored multiplier. -/
theorem old_multiplier_exchange (R : Run round D A) (t i j : Fin n) :
    R.ell j (R.order (t.val + 1) i) =
      R.ell j (R.order t.val (Equiv.swap t (R.choice t) i)) := by
  rw [R.exchange]
  rfl

/-- A stage fixes every position above its cursor. -/
theorem order_step (R : Run round D A) (t : Fin n) (i : Fin n) (hi : i < t) :
    R.order (t.val + 1) i = R.order t.val i := by
  rw [R.exchange]
  have hic : i ≠ R.choice t := ne_of_lt (lt_of_lt_of_le hi (R.choice_ge t))
  simp [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (ne_of_lt hi) hic]

/-- Once a row has been chosen as pivot, all later exchanges fix it. -/
theorem order_stable (R : Run round D A) (i : Fin n) {a b : ℕ}
    (hi : i.val < a) (hab : a ≤ b) (hb : b ≤ n) :
    R.order b i = R.order a i := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases he : a = b + 1
    · rw [he]
    · have hab' : a ≤ b := by omega
      exact (R.order_step ⟨b, by omega⟩ i (by change i.val < b; omega)).trans
        (ih hab' (by omega))

/-- The pivot at stage t is the row in final position t. -/
theorem pivot_identity (R : Run round D A) (t : Fin n) :
    R.order (t.val + 1) t = R.permutation t := by
  exact (R.order_stable t (by omega) (by omega) le_rfl).symm

/-- A pivot row's stored entries are unaffected by all later updates. -/
theorem state_pivot_step (R : Run round D A) (t i j : Fin n) (hi : i ≤ t) :
    R.state (t.val + 1) (R.permutation i) j = R.state t.val (R.permutation i) j := by
  have hp : R.permutation i = R.order (t.val + 1) i :=
    R.order_stable i (by omega) (by omega) le_rfl
  have ha : (R.order (t.val + 1)).symm (R.permutation i) = i := by rw [hp]; simp
  rw [R.update, ha, ite_eq_right (by omega)]

/-- Reading the final upper triangle is the same as harvesting each pivot row
when it is formed, as in the definition of `upper`. -/
theorem upper_final (R : Run round D A) (i j : Fin n) (hij : i ≤ j) :
    R.upper i j = R.current n i j := by
  have hstable : ∀ b : ℕ, i.val ≤ b → b ≤ n →
      R.state b (R.permutation i) j = R.state i.val (R.permutation i) j := by
    intro b
    induction b with
    | zero =>
      intro hi hb
      have hzero : i.val = 0 := by omega
      rw [hzero]
    | succ b ih =>
      intro hi hb
      by_cases he : i.val = b + 1
      · rw [he]
      · exact (R.state_pivot_step ⟨b, by omega⟩ i j (by change i.val ≤ b; omega)).trans
          (ih (by omega) (by omega))
  simpa only [upper, ite_eq_left hij, current, permutation] using
    (hstable n (by omega) le_rfl).symm

/-- A row in a later final position is still strictly below the pivot. -/
theorem active (R : Run round D A) (t i : Fin n) (hti : t < i) :
    t.val < ((R.order (t.val + 1)).symm (R.permutation i)).val := by
  let a := (R.order (t.val + 1)).symm (R.permutation i)
  by_contra h
  have ha : a.val < t.val + 1 := by dsimp [a]; omega
  have he : R.permutation a = R.order (t.val + 1) a :=
    R.order_stable a ha (by omega) le_rfl
  have hai : a = i := R.permutation.injective (he.trans (by simp [a]))
  have : i.val ≤ t.val := by subst a; omega
  exact (not_le_of_gt hti) this

/-- The declared outputs have the intended triangular shapes. -/
theorem triangular (R : Run round D A) :
    IsUnitLowerTriangular R.lower ∧ IsUpperTriangular R.upper := by
  constructor
  · constructor
    · intro i j hij
      simp [lower, show ¬ j < i by omega, show i ≠ j by omega]
    · intro i; simp [lower]
  · intro i j hji
    simp [upper, show ¬ i ≤ j by omega]
end Run

/-- A product containing one signed primitive factor and k inverse subtraction
factors has k+1 factors, irrespective of the total arithmetic operation count. -/
theorem weight_bound {u d : ℝ} (σ : ℕ → ℝ) (r : ℤ) (k : ℕ)
    (hu : BudgetDomain (k + 1) u) (hd : |d| ≤ u)
    (hσ : ∀ i < k, |σ i| ≤ u) (hr : r = -1 ∨ r = 1) :
    |(1 + d) ^ r * (∏ i ∈ Finset.range k, (1 + σ i)⁻¹) - 1| ≤
      gamma (k + 1) u := by
  let δ : ℕ → ℝ := fun i => if i = 0 then d else σ (i - 1)
  let ρ : ℕ → ℤ := fun i => if i = 0 then r else -1
  have hδ : ∀ i < k + 1, |δ i| ≤ u := by
    intro i hi
    by_cases hz : i = 0
    · simpa [δ, hz] using hd
    · simpa [δ, hz] using hσ (i - 1) (by omega)
  have hρ : ∀ i < k + 1, ρ i = -1 ∨ ρ i = 1 := by
    intro i hi
    by_cases hz : i = 0
    · simpa [ρ, hz] using hr
    · simp [ρ, hz]
  obtain ⟨θ, he, hb, _⟩ := signed_products δ ρ hu hδ hρ
  have hp : (∏ i ∈ Finset.range (k + 1), (1 + δ i) ^ (ρ i)) =
      (1 + d) ^ r * (∏ i ∈ Finset.range k, (1 + σ i)⁻¹) := by
    rw [Finset.prod_range_succ']
    simp [δ, ρ, mul_comm]
  rw [hp] at he
  have ht : (1 + d) ^ r * (∏ i ∈ Finset.range k, (1 + σ i)⁻¹) - 1 = θ := by
    linarith
  rw [ht]
  exact hb

/-- Exact inversion of the zero-based sequential kernel. -/
theorem trace_identity (k : ℕ) (c μ σ s : ℕ → ℝ)
    (hs : ∀ t < k, s (t + 1) = (s t - c t * (1 + μ t)) * (1 + σ t))
    (hn : ∀ t < k, 1 + σ t ≠ 0) :
    s 0 = s k * (∏ t ∈ Finset.range k, (1 + σ t)⁻¹) +
      ∑ t ∈ Finset.range k,
        c t * (1 + μ t) * (∏ j ∈ Finset.range t, (1 + σ j)⁻¹) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp := SubtractionTrace.one_step_inverse (c k) 1 (μ k) (σ k)
      (s k) (s (k + 1)) (by simpa using hs k (by omega)) (hn k (by omega))
    rw [ih (fun t ht => hs t (by omega)) (fun t ht => hn t (by omega))]
    rw [Finset.prod_range_succ, Finset.sum_range_succ, hp]
    simp only [div_eq_mul_inv]
    ring

/-- The scalar quantitative estimate used for each matrix entry. The terminal
factor is the inverse division factor, or 1 (δ=0) for an entry of U. -/
theorem trace_error (k : ℕ) (c μ σ s : ℕ → ℝ) (δ u : ℝ)
    (hu : BudgetDomain (k + 1) u)
    (hμ : ∀ t < k, |μ t| ≤ u) (hσ : ∀ t < k, |σ t| ≤ u) (hδ : |δ| ≤ u)
    (hs : ∀ t < k, s (t + 1) = (s t - c t * (1 + μ t)) * (1 + σ t))
    (hend : s k = c k / (1 + δ)) :
    |(∑ t ∈ Finset.range (k + 1), c t) - s 0| ≤
      gamma (k + 1) u * ∑ t ∈ Finset.range (k + 1), |c t| := by
  have hn : ∀ t < k, 1 + σ t ≠ 0 := by
    intro t ht
    have := (abs_le.mp (hσ t ht)).1
    have : 0 < 1 + σ t := by linarith [hu.2.1]
    exact ne_of_gt this
  let w : ℕ → ℝ := fun t => if t < k then
    (1 + μ t) * (∏ j ∈ Finset.range t, (1 + σ j)⁻¹)
    else (1 + δ)⁻¹ * (∏ j ∈ Finset.range k, (1 + σ j)⁻¹)
  have hw : ∀ t < k + 1, |w t - 1| ≤ gamma (k + 1) u := by
    intro t ht
    by_cases htk : t < k
    · have hu' := budgetDomain_mono (show t + 1 ≤ k + 1 by omega) hu
      have hb := weight_bound σ 1 t hu' (hμ t htk)
        (fun j hj => hσ j (by omega)) (Or.inr rfl)
      simp only [zpow_one] at hb
      have hb' : |w t - 1| ≤ gamma (t + 1) u := by simpa [w, htk] using hb
      exact hb'.trans (gamma_mono (by omega) hu)
    · have he : t = k := by omega
      subst t
      simpa [w] using weight_bound σ (-1) k hu hδ hσ (Or.inl rfl)
  have he : s 0 = ∑ t ∈ Finset.range (k + 1), c t * w t := by
    rw [Finset.sum_range_succ]
    have hh := trace_identity k c μ σ s hs hn
    rw [hend] at hh
    rw [hh]
    have hsum : (∑ t ∈ Finset.range k, c t * w t) =
        ∑ t ∈ Finset.range k,
          c t * (1 + μ t) * (∏ j ∈ Finset.range t, (1 + σ j)⁻¹) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp [w, Finset.mem_range.mp ht, mul_assoc]
    rw [hsum]
    simp [w, div_eq_mul_inv, mul_assoc, add_comm]
  rw [he, ← Finset.sum_sub_distrib]
  calc
    |∑ t ∈ Finset.range (k + 1), (c t - c t * w t)| ≤
        ∑ t ∈ Finset.range (k + 1), |c t - c t * w t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range (k + 1), |c t| * gamma (k + 1) u := by
      apply Finset.sum_le_sum
      intro t ht
      have heq : c t - c t * w t = -(c t * (w t - 1)) := by ring
      rw [heq, abs_neg, abs_mul]
      exact mul_le_mul_of_nonneg_left (hw t (Finset.mem_range.mp ht)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

namespace Run
variable {n : ℕ} {round : ℝ → ℝ} {D : Set ℝ} {A : Mat ℝ n n}

/-- Extend the exact LU summands by zero outside the matrix dimension. -/
def term (R : Run round D A) (i j : Fin n) (t : ℕ) : ℝ :=
  if ht : t < n then R.lower i ⟨t, ht⟩ * R.upper ⟨t, ht⟩ j else 0

/-- Each entry follows precisely the finite sequential subtraction kernel in
final row positions. Division affects only the terminal term. -/
theorem entry_trace (R : Run round D A) (u : ℝ)
    (hm : RelativeModel round u D) (i j : Fin n) :
    ∃ (μ σ : ℕ → ℝ) (δ : ℝ),
      (∀ t < min i.val j.val, |μ t| ≤ u) ∧
      (∀ t < min i.val j.val, |σ t| ≤ u) ∧ |δ| ≤ u ∧
      (∀ t < min i.val j.val,
        R.state (t + 1) (R.permutation i) j =
          (R.state t (R.permutation i) j - R.term i j t * (1 + μ t)) * (1 + σ t)) ∧
      R.state (min i.val j.val) (R.permutation i) j =
        R.term i j (min i.val j.val) / (1 + δ) := by
  have hsteps : ∀ t : ℕ, ∃ μ σ : ℝ, |μ| ≤ u ∧ |σ| ≤ u ∧
      (t < min i.val j.val →
        R.state (t + 1) (R.permutation i) j =
          (R.state t (R.permutation i) j - R.term i j t * (1 + μ)) * (1 + σ)) := by
    intro t
    by_cases ht : t < min i.val j.val
    · let tf : Fin n := ⟨t, by have := i.isLt; omega⟩
      have hti : tf < i := by change t < i.val; omega
      have htj : tf < j := by change t < j.val; omega
      have ha := R.active tf i hti
      obtain ⟨hprod, hsub⟩ := R.safety tf (R.permutation i) j ha htj
      obtain ⟨μ, hμ, hbμ⟩ := relativeModel_error round u D hm _ hprod
      obtain ⟨σ, hσ, hbσ⟩ := relativeModel_error round u D hm _ hsub
      refine ⟨μ, σ, hbμ, hbσ, ?_⟩
      intro _
      have hup := R.update tf (R.permutation i) j
      rw [ite_eq_left ⟨ha, htj⟩, hσ, hμ] at hup
      have hc : R.term i j t =
          R.ell tf (R.permutation i) * R.state t (R.order (tf.val + 1) tf) j := by
        have htn : t < n := tf.isLt
        simp only [term, dite_eq_left htn]
        change R.lower i tf * R.upper tf j = _
        rw [lower, ite_eq_left hti, upper, ite_eq_left (le_of_lt htj), R.pivot_identity tf]
      -- `tf.val = t`; all operations here are the actually executed ones.
      simpa only [Fin.val_mk, hc] using hup
    · exact ⟨0, 0, by simpa using hm.1, by simpa using hm.1, by omega⟩
  choose μ σ hμ hσ hs using hsteps
  have hhead : ∃ δ : ℝ, |δ| ≤ u ∧
      R.state (min i.val j.val) (R.permutation i) j =
        R.term i j (min i.val j.val) / (1 + δ) := by
    by_cases hij : i ≤ j
    · refine ⟨0, by simpa using hm.1, ?_⟩
      have hk : min i.val j.val = i.val := min_eq_left hij
      rw [hk]
      simp [term, i.isLt, lower, upper, hij]
    · have hji : j < i := lt_of_not_ge hij
      have hk : min i.val j.val = j.val := min_eq_right (le_of_lt hji)
      obtain ⟨hp, hz, he⟩ := R.division j (R.permutation i) (R.active j i hji)
      obtain ⟨δ, hδ, hbδ⟩ := relativeModel_error round u D hm _ hz
      have hd : 1 + δ ≠ 0 := by
        have := (abs_le.mp hbδ).1
        have : 0 < 1 + δ := by linarith [hm.2.1]
        exact ne_of_gt this
      refine ⟨δ, hbδ, ?_⟩
      rw [hk]
      have hc : R.term i j j.val =
          R.ell j (R.permutation i) * R.state j.val (R.order (j.val + 1) j) j := by
        simp [term, j.isLt, lower, upper, hji, R.pivot_identity]
      rw [hc, he, hδ]
      field_simp [hp, hd]
  obtain ⟨δ, hbδ, he⟩ := hhead
  exact ⟨μ, σ, δ, fun t _ => hμ t, fun t _ => hσ t, hbδ, hs, he⟩
end Run

namespace Run
variable {n : ℕ} {round : ℝ → ℝ} {D : Set ℝ} {A : Mat ℝ n n}

/-- Triangularity makes every LU summand beyond min(i,j) vanish. -/
theorem term_zero (R : Run round D A) (i j : Fin n) (t : ℕ)
    (ht : min i.val j.val < t) : R.term i j t = 0 := by
  unfold term
  split_ifs with htn
  · let tf : Fin n := ⟨t, htn⟩
    change R.lower i tf * R.upper tf j = 0
    by_cases hit : i.val < t
    · rw [R.triangular.1.1 i tf hit, zero_mul]
    · have hjt : j.val < t := by omega
      rw [R.triangular.2 tf j hjt, mul_zero]
  · rfl

/-- Truncation of the matrix-product sum, also usable after taking absolute
values. No term outside the triangular overlap contributes. -/
theorem sum_terms (R : Run round D A) (i j : Fin n)
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    (∑ t ∈ Finset.range (min i.val j.val + 1), f (R.term i j t)) =
      ∑ t : Fin n, f (R.lower i t * R.upper t j) := by
  have hk : min i.val j.val + 1 ≤ n := by have := i.isLt; omega
  calc
    _ = ∑ t ∈ Finset.range n, f (R.term i j t) := by
      apply Finset.sum_subset (Finset.range_mono hk)
      intro t ht hn
      rw [R.term_zero i j t (by have := Finset.mem_range.not.mp hn; omega), hf]
    _ = _ := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro t _
      simp only [term, dite_eq_left t.isLt, Fin.eta]

/-- The sharper γ_n entry estimate underlying the advertised γ_(3n) bound. -/
theorem entry_error (R : Run round D A) (u : ℝ)
    (hm : RelativeModel round u D) (hu : BudgetDomain n u) (i j : Fin n) :
    |(R.lower * R.upper) i j - A (R.permutation i) j| ≤
      gamma n u * (entrywiseAbs R.lower * entrywiseAbs R.upper) i j := by
  obtain ⟨μ, σ, δ, hμ, hσ, hδ, hs, hend⟩ := R.entry_trace u hm i j
  have hk : min i.val j.val + 1 ≤ n := by have := i.isLt; omega
  have hb := trace_error (min i.val j.val) (R.term i j) μ σ
    (fun t => R.state t (R.permutation i) j) δ u
    (budgetDomain_mono hk hu) hμ hσ hδ hs hend
  have hterms := R.sum_terms i j id rfl
  simp only [id_eq] at hterms
  rw [R.state_zero, hterms, R.sum_terms i j abs abs_zero] at hb
  change |(∑ t : Fin n, R.lower i t * R.upper t j) - A (R.permutation i) j| ≤
    gamma n u * (∑ t : Fin n, ‖R.lower i t‖ * ‖R.upper t j‖)
  have hsum : (∑ t : Fin n, |R.lower i t * R.upper t j|) =
      ∑ t : Fin n, ‖R.lower i t‖ * ‖R.upper t j‖ := by
    simp only [abs_mul, Real.norm_eq_abs]
  change |(∑ t : Fin n, R.lower i t * R.upper t j) - A (R.permutation i) j| ≤ _ at hb
  rw [hsum] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (gamma_mono hk hu)
    (Finset.sum_nonneg (fun t _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))))
end Run

/-- W22, including the empty matrix and a possibly zero terminal diagonal. -/
theorem backward_error : Specs.NumAnalysis206.LinearAlgebra.Doolittle.backward_error := by
  intro n round u D A hm R hnu
  have hu3 : BudgetDomain (3 * n) u := by
    refine ⟨hm.1, hm.2.1, ?_⟩
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnu
  have hn3 : n ≤ 3 * n := by omega
  have hu := budgetDomain_mono hn3 hu3
  let Δ : Mat ℝ n n := R.lower * R.upper - NumAnalysis206.PivotedLU.permutationMatrix R.permutation * A
  refine ⟨Δ, by dsimp [Δ]; abel, ?_⟩
  intro i j
  have hb := R.entry_error u hm hu i j
  have hnonneg : 0 ≤ (entrywiseAbs R.lower * entrywiseAbs R.upper) i j := by
    change 0 ≤ ∑ t : Fin n, ‖R.lower i t‖ * ‖R.upper t j‖
    exact Finset.sum_nonneg (fun t _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hbig := hb.trans (mul_le_mul_of_nonneg_right (gamma_mono hn3 hu3) hnonneg)
  simpa only [Δ, Matrix.sub_apply, NumAnalysis206.PivotedLU.permutationMatrix_mul,
    NumAnalysis206.PivotedLU.permuteRows, entrywiseAbs, Real.norm_eq_abs,
    Matrix.smul_apply, smul_eq_mul, gamma,
    Specs.NumAnalysis206.Rounding.gammaValue] using hbig

end NumAnalysis206.LinearAlgebra.Doolittle
