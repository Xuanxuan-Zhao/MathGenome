import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.CholeskyBackward
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.GammaProducts
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.SubtractionTrace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.GCongr

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.LinearAlgebra.CholeskyBackward
open NumAnalysis206.Rounding
open NumAnalysis206.MatrixDefinitions
open NumAnalysis206.LinearAlgebra.CholeskyData

/-- A subtraction prefix followed by two final rounding factors. A zero error
can pad a path with only one final factor. -/
private theorem path_bound {k N : ℕ} {u : ℝ} (σ : ℕ → ℝ) (d e : ℝ) (r q : ℤ)
    (hu : BudgetDomain N u) (hk : k + 2 ≤ N)
    (hσ : ∀ t < k, |σ t| ≤ u) (hd : |d| ≤ u) (he : |e| ≤ u)
    (hr : r = -1 ∨ r = 1) (hq : q = -1 ∨ q = 1) :
    |(∏ t ∈ Finset.range k, (1 + σ t)⁻¹) * (1 + d)^r * (1 + e)^q - 1| ≤
      gamma N u := by
  let δ : ℕ → ℝ := fun i => if i < k then σ i else if i = k then d else e
  let ρ : ℕ → ℤ := fun i => if i < k then -1 else if i = k then r else q
  obtain ⟨θ, hθ, hb, _⟩ := signed_products δ ρ (budgetDomain_mono hk hu)
    (by
      intro i hi
      dsimp [δ]
      split_ifs with h h
      · exact hσ i h
      · exact hd
      · exact he)
    (by
      intro i hi
      dsimp [ρ]
      split_ifs
      · exact Or.inl rfl
      · exact hr
      · exact hq)
  have hp : (∏ i ∈ Finset.range (k + 2), (1 + δ i) ^ ρ i) =
      (∏ t ∈ Finset.range k, (1 + σ t)⁻¹) * (1 + d)^r * (1 + e)^q := by
    rw [show k + 2 = (k + 1) + 1 by omega, Finset.prod_range_succ,
      Finset.prod_range_succ]
    have hpre : (∏ i ∈ Finset.range k, (1 + δ i)^ρ i) =
        ∏ i ∈ Finset.range k, (1 + σ i)⁻¹ := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [δ, ρ, Finset.mem_range.mp hi]
    rw [hpre]
    simp [δ, ρ]
  rw [hp] at hθ
  calc
    _ = |θ| := by congr 1; linarith [hθ]
    _ ≤ gamma (k + 2) u := hb
    _ ≤ gamma N u := gamma_mono hk hu

/-- The zero-based form of the accepted sequential subtraction identity. -/
private theorem inverse_trace (k : ℕ) (a b μ σ s : ℕ → ℝ)
    (hstep : ∀ t < k, s (t + 1) = (s t - a t * b t * (1 + μ t)) * (1 + σ t))
    (hnz : ∀ t < k, 1 + σ t ≠ 0) :
    s 0 = s k * (∏ t ∈ Finset.range k, (1 + σ t)⁻¹) +
      ∑ t ∈ Finset.range k,
        a t * b t * (1 + μ t) * (∏ r ∈ Finset.range t, (1 + σ r)⁻¹) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hlast := SubtractionTrace.one_step_inverse (a k) (b k) (μ k) (σ k)
      (s k) (s (k + 1)) (hstep k (by omega)) (hnz k (by omega))
    rw [ih (fun t ht => hstep t (by omega)) (fun t ht => hnz t (by omega))]
    rw [Finset.prod_range_succ, Finset.sum_range_succ, hlast]
    simp only [div_eq_mul_inv]
    ring

/-- A scalar residual reconstructed from its actual multiply-subtract steps.
The two terminal inverse factors include the repeated square-root factor. -/
private theorem residual_bound {k N : ℕ} {u c d e : ℝ}
    (a b μ σ s : ℕ → ℝ) (hu : BudgetDomain N u) (hk : k + 2 ≤ N)
    (hμ : ∀ t < k, |μ t| ≤ u) (hσ : ∀ t < k, |σ t| ≤ u)
    (hd : |d| ≤ u) (he : |e| ≤ u)
    (hstep : ∀ t < k, s (t + 1) = (s t - a t * b t * (1 + μ t)) * (1 + σ t))
    (hend : s k = c * (1 + d)⁻¹ * (1 + e)⁻¹) :
    |s 0 - (c + ∑ t ∈ Finset.range k, a t * b t)| ≤
      gamma N u * (|c| + ∑ t ∈ Finset.range k, |a t * b t|) := by
  have hnz : ∀ t < k, 1 + σ t ≠ 0 := by
    intro t ht
    have := (abs_le.mp (hσ t ht)).1
    have := hu.2.1
    exact ne_of_gt (by linarith)
  have htrace := inverse_trace k a b μ σ s hstep hnz
  have hterminal := path_bound σ d e (-1) (-1) hu hk hσ hd he (Or.inl rfl) (Or.inl rfl)
  simp only [zpow_neg_one] at hterminal
  have hterm (t : ℕ) (ht : t ∈ Finset.range k) :
      |(1 + μ t) * (∏ r ∈ Finset.range t, (1 + σ r)⁻¹) - 1| ≤ gamma N u := by
    have ht' := Finset.mem_range.mp ht
    have hb := path_bound (k := t) σ (μ t) 0 1 1 hu (by omega)
      (fun r hr => hσ r (by omega)) (hμ t ht') (by simpa using hu.1)
      (Or.inr rfl) (Or.inr rfl)
    simpa [mul_comm] using hb
  have hid : s 0 - (c + ∑ t ∈ Finset.range k, a t * b t) =
      c * ((∏ t ∈ Finset.range k, (1 + σ t)⁻¹) * (1 + d)⁻¹ * (1 + e)⁻¹ - 1) +
      ∑ t ∈ Finset.range k, a t * b t *
        ((1 + μ t) * (∏ r ∈ Finset.range t, (1 + σ r)⁻¹) - 1) := by
    rw [htrace, hend]
    simp_rw [mul_sub, mul_one, ← mul_assoc]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid]
  calc
    _ ≤ |c * ((∏ t ∈ Finset.range k, (1 + σ t)⁻¹) * (1 + d)⁻¹ * (1 + e)⁻¹ - 1)| +
        |∑ t ∈ Finset.range k, a t * b t *
          ((1 + μ t) * (∏ r ∈ Finset.range t, (1 + σ r)⁻¹) - 1)| := abs_add_le _ _
    _ ≤ |c| * gamma N u + ∑ t ∈ Finset.range k, |a t * b t| * gamma N u := by
      gcongr
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hterminal (abs_nonneg c)
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro t ht
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hterm t ht) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Undo the final division, or undo the rounded square root twice. -/
private theorem terminal_factors {n : ℕ} {round : ℝ → ℝ} {u : ℝ} {D : Set ℝ}
    {A L : Mat ℝ n n} {s : Fin n → Fin n → ℕ → ℝ}
    (T : SafeTrace round u D A L s) (i j : Fin n) (hji : j ≤ i) :
    ∃ d e : ℝ, |d| ≤ u ∧ |e| ≤ u ∧
      s i j j.val = (L i j * L j j) * (1 + d)⁻¹ * (1 + e)⁻¹ := by
  by_cases hij : i = j
  · subst i
    obtain ⟨d, hd, hb⟩ := T.model.2.2 _ (T.sqrt_safe j)
    have hnz : 1 + d ≠ 0 := ne_of_gt (by
      have := (abs_le.mp hb).1
      have := T.model.2.1
      linarith)
    refine ⟨d, d, hb, hb, ?_⟩
    have hid : (L j j * L j j) * (1 + d)⁻¹ * (1 + d)⁻¹ =
        (Real.sqrt (s j j j.val)) ^ 2 := by
      rw [T.primitive.diagonal, hd]
      field_simp
    rw [hid, Real.sq_sqrt (T.positive j).le]
  · have hlt : j < i := lt_of_le_of_ne hji (Ne.symm hij)
    obtain ⟨d, hd, hb⟩ := T.model.2.2 _ (T.div_safe i j hlt)
    have hnz : 1 + d ≠ 0 := ne_of_gt (by
      have := (abs_le.mp hb).1
      have := T.model.2.1
      linarith)
    refine ⟨d, 0, hb, by simpa using T.model.1, ?_⟩
    rw [T.primitive.offDiagonal i j hlt, hd]
    simp only [add_zero, inv_one, mul_one]
    field_simp [T.nonzero i j hlt, hnz]

/-- The estimate for a lower-triangular entry, before matrix notation. -/
private theorem lower_entry_bound {n : ℕ} {round : ℝ → ℝ} {u : ℝ} {D : Set ℝ}
    {A L : Mat ℝ n n} {s : Fin n → Fin n → ℕ → ℝ}
    (T : SafeTrace round u D A L s) (hu : BudgetDomain (3 * n + 3) u)
    (i j : Fin n) (hji : j ≤ i) :
    |A i j - (L i j * L j j +
      ∑ t ∈ Finset.range j.val, entry L i t * entry L j t)| ≤
      gamma (3 * n + 3) u * (|L i j * L j j| +
        ∑ t ∈ Finset.range j.val, |entry L i t * entry L j t|) := by
  have hm : ∀ t : ℕ, ∃ d : ℝ, |d| ≤ u ∧
      (t < j.val → round (entry L i t * entry L j t) =
        entry L i t * entry L j t * (1 + d)) := by
    intro t
    by_cases ht : t < j.val
    · obtain ⟨d, hd, hb⟩ := T.model.2.2 _ (T.mul_safe i j hji t ht)
      exact ⟨d, hb, fun _ => hd⟩
    · exact ⟨0, by simpa using hu.1, fun h => (ht h).elim⟩
  choose μ hμ hm using hm
  have hs : ∀ t : ℕ, ∃ d : ℝ, |d| ≤ u ∧
      (t < j.val → round (s i j t - round (entry L i t * entry L j t)) =
        (s i j t - round (entry L i t * entry L j t)) * (1 + d)) := by
    intro t
    by_cases ht : t < j.val
    · obtain ⟨d, hd, hb⟩ := T.model.2.2 _ (T.sub_safe i j hji t ht)
      exact ⟨d, hb, fun _ => hd⟩
    · exact ⟨0, by simpa using hu.1, fun h => (ht h).elim⟩
  choose σ hσ hs using hs
  obtain ⟨d, e, hd, he, hend⟩ := terminal_factors T i j hji
  have hb := residual_bound (entry L i) (entry L j) μ σ (s i j) hu
    (show j.val + 2 ≤ 3 * n + 3 by have := j.isLt; omega)
    (fun t _ => hμ t) (fun t _ => hσ t) hd he
    (by
      intro t ht
      rw [T.primitive.step i j hji t ht, hs t ht, hm t ht]) hend
  rwa [T.primitive.initial i j hji] at hb

/-- Terms after column j vanish because row j is lower triangular. -/
private theorem prefix_sum {n : ℕ} (L : Mat ℝ n n) (hl : IsLowerTriangular L)
    (i j : Fin n) (g : ℝ → ℝ) (hg : g 0 = 0) :
    (∑ t : Fin n, g (L i t * L j t)) = g (L i j * L j j) +
      ∑ t ∈ Finset.range j.val, g (entry L i t * entry L j t) := by
  have hext : (∑ t : Fin n, g (L i t * L j t)) =
      ∑ t ∈ Finset.range n, g (entry L i t * entry L j t) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t _
    simp [entry, t.isLt]
  rw [hext]
  have hs : (∑ t ∈ Finset.range n, g (entry L i t * entry L j t)) =
      ∑ t ∈ Finset.range (j.val + 1), g (entry L i t * entry L j t) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by have := j.isLt; omega))
    intro t ht hnot
    have htn := Finset.mem_range.mp ht
    have hjt : j.val < t := by simpa using hnot
    simp [entry, htn, hl j ⟨t, htn⟩ hjt, hg]
  rw [hs, Finset.sum_range_succ]
  simp only [entry, j.isLt, dite_true, Fin.eta]
  ring

private theorem product_entry {n : ℕ} (L : Mat ℝ n n) (hl : IsLowerTriangular L)
    (i j : Fin n) :
    (L * adjoint L) i j = L i j * L j j +
      ∑ t ∈ Finset.range j.val, entry L i t * entry L j t := by
  simpa [Matrix.mul_apply, adjoint] using prefix_sum L hl i j id rfl

private theorem absolute_product_entry {n : ℕ} (L : Mat ℝ n n)
    (hl : IsLowerTriangular L) (i j : Fin n) :
    (entrywiseAbs L * entrywiseAbs (adjoint L)) i j = |L i j * L j j| +
      ∑ t ∈ Finset.range j.val, |entry L i t * entry L j t| := by
  simpa only [Matrix.mul_apply, entrywiseAbs, adjoint, Matrix.conjTranspose_apply,
    star_trivial, Real.norm_eq_abs, ← abs_mul] using prefix_sum L hl i j abs (abs_zero)

private theorem product_symmetric {n : ℕ} (L : Mat ℝ n n) (i j : Fin n) :
    (L * adjoint L) i j = (L * adjoint L) j i := by
  simp only [Matrix.mul_apply, adjoint, Matrix.conjTranspose_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro t _
  ring

private theorem absolute_product_symmetric {n : ℕ} (L : Mat ℝ n n) (i j : Fin n) :
    (entrywiseAbs L * entrywiseAbs (adjoint L)) i j =
      (entrywiseAbs L * entrywiseAbs (adjoint L)) j i := by
  simp only [Matrix.mul_apply, entrywiseAbs, adjoint, Matrix.conjTranspose_apply,
    star_trivial]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- W26, including the empty matrix: a successful columnwise real Cholesky run
has the stated componentwise backward error with the conservative budget. -/
theorem backward : Specs.NumAnalysis206.LinearAlgebra.CholeskyBackward.backward := by
  intro n round u D A L s hA T hbudget
  have hu : BudgetDomain (3 * n + 3) u := ⟨T.model.1, T.model.2.1, hbudget⟩
  have hentry (i j : Fin n) (hji : j ≤ i) :
      |(L * adjoint L) i j - A i j| ≤ gamma (3 * n + 3) u *
        (entrywiseAbs L * entrywiseAbs (adjoint L)) i j := by
    rw [abs_sub_comm, product_entry L T.primitive.lower i j,
      absolute_product_entry L T.primitive.lower i j]
    exact lower_entry_bound T hu i j hji
  refine ⟨L * adjoint L - A, ?_, ?_⟩
  · abel
  · intro i j
    change |(L * adjoint L) i j - A i j| ≤ _
    change _ ≤ gamma (3 * n + 3) u *
      (entrywiseAbs L * entrywiseAbs (adjoint L)) i j
    rcases le_total j i with hji | hij
    · exact hentry i j hji
    · rw [product_symmetric L i j, absolute_product_symmetric L i j,
        show A i j = A j i from congrFun (congrFun hA.symm i) j]
      exact hentry j i hij

end NumAnalysis206.LinearAlgebra.CholeskyBackward
