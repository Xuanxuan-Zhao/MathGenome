import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.TriangularBackward
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.SubtractionTrace
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.GammaProducts
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Rounding.Operations
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Convert

/-! Componentwise triangular-solve backward error (W21). Inverting the accepted
subtraction trace attaches at most k inverse subtraction factors and one division
factor to the diagonal, and one multiplication factor plus the earlier inverse
subtraction factors to each off-diagonal coefficient. The finite signed-product
bound gives the uniform γ_n estimate. The final correction is Tᵢⱼ(cᵢⱼ - 1). -/

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.LinearAlgebra.TriangularSolve
open Rounding MatrixDefinitions

/-- The signed-product estimate transported to an arbitrary finite index type. -/
theorem finite_signed_product {α : Type*} [Fintype α] (d : α → ℝ) (r : α → ℤ)
    {u : ℝ} (hu : BudgetDomain (Fintype.card α) u)
    (hd : ∀ i, |d i| ≤ u) (hr : ∀ i, r i = -1 ∨ r i = 1) :
    |(∏ i, (1 + d i) ^ r i) - 1| ≤ gamma (Fintype.card α) u := by
  classical
  let e := (Fintype.equivFin α).symm
  let d' : ℕ → ℝ := fun t => if h : t < Fintype.card α then d (e ⟨t, h⟩) else 0
  let r' : ℕ → ℤ := fun t => if h : t < Fintype.card α then r (e ⟨t, h⟩) else 1
  obtain ⟨θ, heq, hθ, _⟩ := signed_products d' r' hu
    (fun t ht => by simpa [d', ht] using hd (e ⟨t, ht⟩))
    (fun t ht => by simpa [r', ht] using hr (e ⟨t, ht⟩))
  have hp : (∏ t ∈ Finset.range (Fintype.card α), (1 + d' t) ^ r' t) =
      ∏ i, (1 + d i) ^ r i := by
    rw [← Fin.prod_univ_eq_prod_range]
    simpa [d', r'] using e.prod_comp (fun i => (1 + d i) ^ r i)
  rw [hp] at heq
  simpa [heq] using hθ

/-- One additional factor and any finite collection of inverse subtraction factors. -/
theorem coefficient_bound (s : Finset ℕ) (σ : ℕ → ℝ) (d : ℝ) (r : ℤ)
    {N : ℕ} {u : ℝ} (hu : BudgetDomain N u) (hlen : s.card + 1 ≤ N)
    (hσ : ∀ j ∈ s, |σ j| ≤ u) (hd : |d| ≤ u) (hr : r = -1 ∨ r = 1) :
    |(1 + d) ^ r * (∏ j ∈ s, (1 + σ j)⁻¹) - 1| ≤ gamma N u := by
  classical
  let ds : Option ↥s → ℝ := fun j => match j with | none => d | some j => σ j
  let rs : Option ↥s → ℤ := fun j => match j with | none => r | some _ => -1
  have hc : Fintype.card (Option ↥s) = s.card + 1 := by simp
  have hb := finite_signed_product ds rs
    (budgetDomain_mono (by simpa [hc] using hlen) hu)
    (by intro j; cases j with
        | none => exact hd
        | some j => exact hσ j j.property)
    (by intro j; cases j with
        | none => exact hr
        | some j => exact Or.inl rfl)
  have hp : (∏ j, (1 + ds j) ^ rs j) =
      (1 + d) ^ r * ∏ j ∈ s, (1 + σ j)⁻¹ := by
    rw [Fintype.prod_option]
    simp [ds, rs, ← Finset.prod_attach s (fun j => (1 + σ j)⁻¹)]
  rw [hp] at hb
  exact hb.trans (gamma_mono (by simpa [hc] using hlen) hu)

private theorem predecessor_ne {n : ℕ} (f : Bool) (i : Fin n) :
    i ∉ predecessors f i := by cases f <;> simp [predecessors]

private theorem predecessor_card_lt {n : ℕ} (f : Bool) (i : Fin n) :
    (predecessors f i).card < n := by
  have hs : predecessors f i ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro h
    have := predecessor_ne f i
    simp [h] at this
  simpa using Finset.card_lt_card hs

private theorem column_mem {n : ℕ} {f : Bool} {i : Fin n}
    (e : Fin (predecessors f i).card ≃ ↥(predecessors f i))
    {t : ℕ} (ht : t ∈ Finset.Icc 1 (predecessors f i).card) :
    column e t ∈ predecessors f i := by
  have h : t - 1 < (predecessors f i).card := by
    have := Finset.mem_Icc.mp ht; omega
  simp [column, h]

private theorem column_index {n : ℕ} {f : Bool} {i : Fin n}
    (e : Fin (predecessors f i).card ≃ ↥(predecessors f i))
    (j : ↥(predecessors f i)) :
    column e ((e.symm j).val + 1) = j.val := by
  simp [column, (e.symm j).isLt]

private theorem index_column {n : ℕ} {f : Bool} {i : Fin n}
    (e : Fin (predecessors f i).card ≃ ↥(predecessors f i))
    {t : ℕ} (ht : t ∈ Finset.Icc 1 (predecessors f i).card) :
    (e.symm ⟨column e t, column_mem e ht⟩).val + 1 = t := by
  have h : t - 1 < (predecessors f i).card := by
    have := Finset.mem_Icc.mp ht; omega
  have he : (⟨column e t, column_mem e ht⟩ : ↥(predecessors f i)) = e ⟨t-1,h⟩ := by
    apply Subtype.ext
    simp [column, h]
  rw [he, e.symm_apply_apply]
  have := Finset.mem_Icc.mp ht
  dsimp
  omega

private theorem triangular_zero {n : ℕ} {f : Bool} {T : Mat ℝ n n}
    (hT : if f then IsLowerTriangular T else IsUpperTriangular T)
    (i j : Fin n) (hne : j ≠ i) (hj : j ∉ predecessors f i) : T i j = 0 := by
  cases f with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hT
    have hn : ¬ i < j := by simpa [predecessors] using hj
    exact hT i j (show j.val < i.val from by
      have : j.val ≠ i.val := fun h => hne (Fin.ext h)
      simp only [Fin.lt_def] at hn
      omega)
  | true =>
    simp only [↓reduceIte] at hT
    have hn : ¬ j < i := by simpa [predecessors] using hj
    exact hT i j (show i.val < j.val from by
      have : j.val ≠ i.val := fun h => hne (Fin.ext h)
      simp only [Fin.lt_def] at hn
      omega)

/-- Recover all coefficients in one row from its actual primitive operations. -/
theorem row_backward {n : ℕ} (round : ℝ → ℝ) (u : ℝ) (D : Set ℝ)
    (f : Bool) (T : Mat ℝ n n) (b x : Fin n → ℝ)
    (hm : RelativeModel round u D)
    (hT : if f then IsLowerTriangular T else IsUpperTriangular T)
    (hdiag : ∀ i, T i i ≠ 0) (hrun : SafeRun round D f T b x)
    (hnu : (n : ℝ) * u < 1) (i : Fin n) :
    ∃ c : Fin n → ℝ, (∀ j, |c j - 1| ≤ gamma n u) ∧
      (∑ j, T i j * c j * x j) = b i := by
  classical
  have hu : BudgetDomain n u := ⟨hm.1, hm.2.1, hnu⟩
  obtain ⟨e, s, hs0, hsteps, hsafeDiv, hx⟩ := hrun i
  let k := (predecessors f i).card
  have hk : k < n := predecessor_card_lt f i
  have hex : ∀ t : ℕ, ∃ μ σ : ℝ, |μ| ≤ u ∧ |σ| ≤ u ∧
      (t ∈ Finset.Icc 1 k →
        s t = (s (t - 1) - T i (column e t) * x (column e t) * (1 + μ)) * (1 + σ)) := by
    intro t
    by_cases ht : t ∈ Finset.Icc 1 k
    · obtain ⟨hprod, hsub, hstep⟩ := hsteps t ht
      obtain ⟨μ, hμ, hbμ⟩ := hm.2.2 _ hprod
      obtain ⟨σ, hσ, hbσ⟩ := hm.2.2 _ hsub
      refine ⟨μ, σ, hbμ, hbσ, fun _ => ?_⟩
      rw [hstep, hσ, hμ]
    · exact ⟨0, 0, by simpa using hm.1, by simpa using hm.1, fun h => (ht h).elim⟩
  choose μ σ hμ hσ hstep using hex
  obtain ⟨δ, hδ, hbδ⟩ := hm.2.2 _ hsafeDiv
  have factor_ne (d : ℝ) (hd : |d| ≤ u) : 1 + d ≠ 0 := by
    have := (abs_le.mp hd).1
    have := hm.2.1
    linarith
  have hterminal : s k = T i i * x i * (1 + δ)⁻¹ := by
    rw [hx, hδ]
    field_simp [hdiag i, factor_ne δ hbδ]
    rfl
  have htrace := SubtractionTrace.subtraction_trace k
    (fun t => T i (column e t)) (fun t => x (column e t)) μ σ s hstep
    (fun t _ => factor_ne (σ t) (hσ t))
  rw [hs0, hterminal] at htrace
  let c : Fin n → ℝ := fun j => if j = i then
      (1 + δ)⁻¹ * ∏ l ∈ Finset.Icc 1 k, (1 + σ l)⁻¹
    else if hj : j ∈ predecessors f i then
      (1 + μ ((e.symm ⟨j, hj⟩).val + 1)) *
        ∏ l ∈ Finset.Ico 1 ((e.symm ⟨j, hj⟩).val + 1), (1 + σ l)⁻¹
    else 1
  refine ⟨c, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [c] using coefficient_bound (Finset.Icc 1 k) σ δ (-1) hu
        (by simp only [Nat.card_Icc]; omega)
        (fun l _ => hσ l) hbδ (Or.inl rfl)
    · by_cases hj : j ∈ predecessors f i
      · have ht : (e.symm ⟨j, hj⟩).val < k := (e.symm ⟨j, hj⟩).isLt
        simpa [c, hji, hj] using coefficient_bound
          (Finset.Ico 1 ((e.symm ⟨j, hj⟩).val + 1)) σ
          (μ ((e.symm ⟨j, hj⟩).val + 1)) 1 hu
          (by simp only [Nat.card_Ico]; omega)
          (fun l _ => hσ l) (hμ _) (Or.inr rfl)
      · simpa [c, hji, hj] using gamma_nonneg hu
  · have hsum : (∑ t ∈ Finset.Icc 1 k,
          T i (column e t) * x (column e t) * (1 + μ t) *
            ∏ l ∈ Finset.Ico 1 t, (1 + σ l)⁻¹) =
          ∑ j ∈ predecessors f i, T i j * c j * x j := by
      apply Finset.sum_bij (fun t _ => column e t)
      · intro t ht
        exact column_mem e ht
      · intro t ht v hv heq
        have hi := index_column e ht
        have hj := index_column e hv
        have heq' : (⟨column e t, column_mem e ht⟩ : ↥(predecessors f i)) =
            ⟨column e v, column_mem e hv⟩ := Subtype.ext heq
        rw [heq'] at hi
        omega
      · intro j hj
        refine ⟨(e.symm ⟨j, hj⟩).val + 1, ?_, column_index e ⟨j,hj⟩⟩
        exact Finset.mem_Icc.mpr ⟨by omega, by have := (e.symm ⟨j,hj⟩).isLt; omega⟩
      · intro t ht
        have hmcol := column_mem e ht
        have hne : column e t ≠ i := by
          intro heq
          rw [heq] at hmcol
          exact predecessor_ne f i hmcol
        simp only [c, ite_eq_right hne, dite_eq_left hmcol, index_column e ht]
        ring
    have hsumall : (∑ j, T i j * c j * x j) =
        T i i * c i * x i + ∑ j ∈ predecessors f i, T i j * c j * x j := by
      calc
        _ = ∑ j ∈ insert i (predecessors f i), T i j * c j * x j := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          have hji : j ≠ i := by
            intro he
            subst j
            exact hj (Finset.mem_insert_self _ _)
          have hjp : j ∉ predecessors f i := fun h => hj (Finset.mem_insert_of_mem h)
          rw [triangular_zero hT i j hji hjp]
          simp
        _ = _ := Finset.sum_insert (predecessor_ne f i)
    rw [hsumall, ← hsum]
    simp only [c, ite_eq_left rfl]
    calc
      _ = (T i i * x i * (1 + δ)⁻¹) * (∏ l ∈ Finset.Icc 1 k, (1 + σ l)⁻¹) +
        ∑ t ∈ Finset.Icc 1 k, T i (column e t) * x (column e t) * (1 + μ t) *
          ∏ l ∈ Finset.Ico 1 t, (1 + σ l)⁻¹ := by ring
      _ = b i := htrace.symm

/-- W21: the correction preserves every zero entry and the triangular pattern. -/
theorem backward_error : Specs.NumAnalysis206.LinearAlgebra.TriangularBackward.backwardError := by
  intro n round u D f T b x hm hT hdiag hrun hnu
  have hm' : RelativeModel round u D := hm
  choose c hc hrow using row_backward round u D f T b x hm' hT hdiag hrun hnu
  let Δ : Mat ℝ n n := fun i j => T i j * (c i j - 1)
  have hzero : ∀ i j, T i j = 0 → Δ i j = 0 := by
    intro i j hij
    simp [Δ, hij]
  refine ⟨Δ, ?_, ?_, hzero, ?_⟩
  · funext i
    change (∑ j, (T i j + Δ i j) * x j) = b i
    convert hrow i using 1
    apply Finset.sum_congr rfl
    intro j _
    dsimp [Δ]
    ring
  · intro i j
    change |T i j * (c i j - 1)| ≤ gamma n u * |T i j|
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hc i j) (abs_nonneg _)
  · cases f with
    | false => exact fun i j hij => hzero i j (hT i j hij)
    | true => exact fun i j hij => hzero i j (hT i j hij)

end NumAnalysis206.LinearAlgebra.TriangularSolve
