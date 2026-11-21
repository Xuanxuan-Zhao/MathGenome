import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.IntegrableDiscontinuities
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Criterion
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.OscillationSets
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.ZeroCovers
import Mathlib.Logic.Equiv.Fin.Basic

/-!
The forward Lebesgue criterion, proved from closed-cell Darboux sums.
For α > 0, the total length of cells with supremum minus infimum at least α
is bounded by (U-L)/α. Points of the superlevel inside a cell force that
inequality on the cell; partition endpoints are covered separately by
singleton intervals, all of which are enlarged with arbitrarily small total
added length. Finally use the upstream countable superlevel decomposition.
No measure integral or Riemann-to-Lebesgue comparison is used.
-/
namespace SingleVariableAnalysis
open Set Riemann
open scoped BigOperators ENNReal

/-- Enlarge a finite family of closed intervals, including singleton intervals,
and add summably small padding intervals to obtain a countable open cover.
The added total length is less than any prescribed positive ε. -/
theorem finite_closed_intervals_open_cover {ι : Type*} [Fintype ι]
    (l u : ι → ℝ) (hlu : ∀ i, l i ≤ u i) (ε : ℝ) (hε : 0 < ε) :
    ∃ A B : ℕ → ℝ, (∀ n, A n < B n) ∧
      (⋃ i, Icc (l i) (u i)) ⊆ ⋃ n, Ioo (A n) (B n) ∧
      nonnegativeExtendedSum (fun n => B n - A n) <
        ENNReal.ofReal ((∑ i, (u i - l i)) + ε) := by
  classical
  let e : (ι ⊕ ℕ) ≃ ℕ :=
    (Equiv.sumCongr (Fintype.equivFin ι) (Equiv.refl ℕ)).trans
      (finSumNatEquiv (Fintype.card ι))
  let L : ι ⊕ ℕ → ℝ := Sum.elim l (fun _ => 0)
  let U : ι ⊕ ℕ → ℝ := Sum.elim u (fun _ => 0)
  have hlen : ∀ j, 0 ≤ U j - L j := by
    intro j; cases j with
    | inl i => exact sub_nonneg.mpr (hlu i)
    | inr n => simp [U, L]
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.ofReal_pos.mpr hε).ne' (ι ⊕ ℕ)
  let A : ι ⊕ ℕ → ℝ := fun j => L j - (δ j : ℝ) / 2
  let B : ι ⊕ ℕ → ℝ := fun j => U j + (δ j : ℝ) / 2
  have hpos (j) : A j < B j := by
    have := NNReal.coe_pos.mpr (hδ j)
    dsimp [A, B]
    linarith [hlen j]
  refine ⟨A ∘ e.symm, B ∘ e.symm, fun n => hpos _, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    apply mem_iUnion.mpr
    refine ⟨e (Sum.inl i), ?_⟩
    simp only [Function.comp_apply, e.symm_apply_apply]
    have := NNReal.coe_pos.mpr (hδ (Sum.inl i))
    change l i - (δ (Sum.inl i) : ℝ) / 2 < x ∧
      x < u i + (δ (Sum.inl i) : ℝ) / 2
    constructor <;> linarith [hi.1, hi.2]
  · change (∑' n, ENNReal.ofReal (B (e.symm n) - A (e.symm n))) < _
    rw [e.symm.tsum_eq (fun j => ENNReal.ofReal (B j - A j))]
    have hlength (j) : ENNReal.ofReal (B j - A j) =
        ENNReal.ofReal (U j - L j) + (δ j : ℝ≥0∞) := by
      have heq : B j - A j = (U j - L j) + (δ j : ℝ) := by dsimp [A, B]; ring
      rw [heq, ENNReal.ofReal_add (hlen j) (δ j).coe_nonneg,
        ENNReal.ofReal_coe_nnreal]
    simp_rw [hlength]
    rw [ENNReal.tsum_add]
    have hbase : (∑' j, ENNReal.ofReal (U j - L j)) =
        ENNReal.ofReal (∑ i, (u i - l i)) := by
      rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
      simp only [U, L, Sum.elim_inl, Sum.elim_inr, sub_self, ENNReal.ofReal_zero,
        tsum_zero, add_zero, tsum_fintype]
      exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hlu i))).symm
    rw [hbase, ENNReal.ofReal_add
      (Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hlu i))) hε.le]
    exact ENNReal.add_lt_add_left ENNReal.ofReal_ne_top hsum

/-- Every non-endpoint of a strict partition lies in the interior of a cell. -/
theorem partition_interior_cell {a b : ℝ} (P : Partition a b) {x : ℝ}
    (hx : x ∈ Icc a b) (hnot : x ∉ points P) :
    ∃ i : Fin P.n, x ∈ Ioo (P.point i.castSucc) (P.point i.succ) := by
  classical
  have hne (j : Fin (P.n + 1)) : x ≠ P.point j := by
    intro heq
    exact hnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq.symm⟩)
  let s := Finset.univ.filter (fun j : Fin (P.n + 1) => P.point j < x)
  have hs : s.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [P.first]
    exact lt_of_le_of_ne hx.1 (by simpa [P.first] using (hne 0).symm)
  let j := s.max' hs
  have hj : P.point j < x := (Finset.mem_filter.mp (Finset.max'_mem s hs)).2
  have hjn : j.val < P.n := by
    have hlast : j ≠ Fin.last P.n := by
      intro heq
      rw [heq, P.last] at hj
      exact (not_lt_of_ge hx.2) hj
    have := j.isLt
    have : j.val ≠ P.n := fun h => hlast (Fin.ext h)
    omega
  let i : Fin P.n := ⟨j.val, hjn⟩
  have hij : i.castSucc = j := Fin.ext rfl
  refine ⟨i, ?_, ?_⟩
  · simpa only [hij] using hj
  · have hnotlt : ¬ P.point i.succ < x := by
      intro hi
      have hm : i.succ ≤ j := Finset.le_max' s i.succ
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      have : i.succ.val ≤ j.val := hm
      dsimp [i] at this
      omega
    exact lt_of_le_of_ne (le_of_not_gt hnotlt) (hne i.succ)

/-- The finite supremum minus infimum bounds the ENNReal pairwise oscillation. -/
theorem cell_oscillation_le (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (i : Fin P.n) :
    Oscillation f (cell P i) ≤
      ENNReal.ofReal (cellSupremum f P hf i - cellInfimum f P hf i) := by
  apply oscillation_le
  intro x hx y hy
  apply ENNReal.ofReal_le_ofReal
  rw [Real.dist_eq, abs_le]
  have hxl := cellInfimum_le f P hf i hx
  have hxu := le_cellSupremum f P hf i hx
  have hyl := cellInfimum_le f P hf i hy
  have hyu := le_cellSupremum f P hf i hy
  constructor <;> linarith

/-- At an interior point of a cell, relative local oscillation is no larger
than that cell's oscillation. No assertion is made at its endpoints. -/
theorem intervalOscillation_le_cell (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (i : Fin P.n) {x : ℝ}
    (hx : x ∈ Ioo (P.point i.castSucc) (P.point i.succ)) :
    intervalOscillation f a b x ≤
      ENNReal.ofReal (cellSupremum f P hf i - cellInfimum f P hf i) := by
  let r := min (x - P.point i.castSucc) (P.point i.succ - x)
  have hr : 0 < r := lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  rw [intervalOscillation_formula]
  apply (iInf_le _ (⟨r, hr⟩ : {r : ℝ // 0 < r})).trans
  apply (oscillation_mono f ?_).trans (cell_oscillation_le f P hf i)
  intro y hy
  have h₁ := min_le_left (x - P.point i.castSucc) (P.point i.succ - x)
  have h₂ := min_le_right (x - P.point i.castSucc) (P.point i.succ - x)
  change y ∈ Icc (P.point i.castSucc) (P.point i.succ)
  dsimp only [r] at hy
  constructor <;> linarith [hy.1.1, hy.1.2]

/-- A two-sided order bound is equivalently an absolute bound on the interval. -/
theorem boundedOnInterval_abs_bound (f : ℝ → ℝ) {a b : ℝ}
    (hf : BoundedOnInterval f a b) : ∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M := by
  obtain ⟨⟨l, hl⟩, ⟨u, hu⟩⟩ := hf
  refine ⟨max (-l) u, ?_⟩
  intro x hx
  apply abs_le.mpr
  have h₁ := hl (mem_image_of_mem f hx)
  have h₂ := hu (mem_image_of_mem f hx)
  constructor
  · linarith [le_max_left (-l) u]
  · exact h₂.trans (le_max_right _ _)

/-- The bad cells have arbitrarily small total length. Singleton intervals at
all partition endpoints are included in the finite cover before enlargement. -/
theorem integrable_superlevel_lengthZero (f : ℝ → ℝ) {a b : ℝ}
    (hi : RealIntegrable f a b) (α : ℝ) (hα : 0 < α) :
    LengthZero (oscillationSuperlevel f a b α) := by
  classical
  have hab := hi.choose
  have hf := hi.choose_spec.choose
  by_cases hab' : a < b
  · intro ε hε
    obtain ⟨P, hgap⟩ := (darboux_criterion f hab' hf).mp hi
      (α * (ε / 2)) (mul_pos hα (half_pos hε))
    let g : Fin P.n → ℝ := fun i => cellSupremum f P hf i - cellInfimum f P hf i
    have hg (i : Fin P.n) : 0 ≤ g i := by
      obtain ⟨x, hx⟩ := cell_nonempty P i
      exact sub_nonneg.mpr ((cellInfimum_le f P hf i hx).trans
        (le_cellSupremum f P hf i hx))
    let w : Fin P.n → ℝ := fun i => if α ≤ g i then cellLength P i else 0
    have hweighted : α * (∑ i, w i) ≤ upperSum f P hf - lowerSum f P hf := by
      rw [Finset.mul_sum]
      have heq : upperSum f P hf - lowerSum f P hf =
          ∑ i, g i * cellLength P i := by
        simp only [upperSum, lowerSum, D.upperSumValue, D.lowerSumValue,
          ← Finset.sum_sub_distrib, ← sub_mul]
        rfl
      rw [heq]
      apply Finset.sum_le_sum
      intro i _
      dsimp only [w]
      split_ifs with hb
      · exact mul_le_mul_of_nonneg_right hb (cell_positive P i).le
      · exact (by simp : α * 0 = 0).le.trans (mul_nonneg (hg i) (cell_positive P i).le)
    have hsmall : (∑ i, w i) < ε / 2 := by nlinarith
    let l : Fin P.n ⊕ Fin (P.n + 1) → ℝ := Sum.elim
      (fun i => if α ≤ g i then P.point i.castSucc else a) P.point
    let u : Fin P.n ⊕ Fin (P.n + 1) → ℝ := Sum.elim
      (fun i => if α ≤ g i then P.point i.succ else a) P.point
    have hlu : ∀ j, l j ≤ u j := by
      intro j
      cases j with
      | inl i =>
        dsimp only [l, u, Sum.elim_inl]
        split_ifs
        · exact (P.strictMono (Fin.castSucc_lt_succ (i := i))).le
        · exact le_rfl
      | inr j => exact le_rfl
    have hlength : (∑ j, (u j - l j)) = ∑ i, w i := by
      rw [Fintype.sum_sum_type]
      have hend : (∑ j : Fin (P.n + 1), (u (Sum.inr j) - l (Sum.inr j))) = 0 := by
        simp [u, l]
      rw [hend, add_zero]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [l, u, w, Sum.elim_inl]
      split_ifs <;> simp [cellLength, S.lengthValue]
    have hcover : oscillationSuperlevel f a b α ⊆ ⋃ j, Icc (l j) (u j) := by
      intro x hx
      by_cases he : x ∈ points P
      · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp he
        apply mem_iUnion.mpr
        exact ⟨Sum.inr j, by change P.point j ≤ x ∧ x ≤ P.point j; rw [hj]; exact ⟨le_rfl, le_rfl⟩⟩
      · obtain ⟨i, hxi⟩ := partition_interior_cell P hx.1 he
        have hb : α ≤ g i := by
          have hb' := hx.2.trans (intervalOscillation_le_cell f P hf i hxi)
          exact (ENNReal.ofReal_le_ofReal_iff (hg i)).mp hb'
        apply mem_iUnion.mpr
        refine ⟨Sum.inl i, ?_⟩
        simpa only [l, u, Sum.elim_inl, ite_eq_left hb, mem_Icc] using ⟨hxi.1.le, hxi.2.le⟩
    obtain ⟨A, B, hAB, hC, hsum⟩ := finite_closed_intervals_open_cover l u hlu
      (ε / 2) (half_pos hε)
    refine ⟨A, B, hAB, hcover.trans hC, hsum.trans_le ?_⟩
    apply ENNReal.ofReal_le_ofReal
    rw [hlength]
    linarith
  · have heq : a = b := le_antisymm hab (le_of_not_gt hab')
    apply lengthZero_subset _ {a} ?_ (lengthZero_singleton a)
    intro x hx
    apply mem_singleton_iff.mpr
    exact le_antisymm (heq ▸ hx.1.2) hx.1.1

/-- The discontinuity set is the countable union of the positive oscillation
superlevels, so their countable covers give the required length-zero cover. -/
theorem integrable_discontinuities_lengthZero (f : ℝ → ℝ) {a b : ℝ}
    (hi : RealIntegrable f a b) : LengthZero (intervalDiscontinuities f a b) := by
  rw [intervalDiscontinuities_eq_union f a b (boundedOnInterval_abs_bound f hi.choose_spec.choose)]
  apply lengthZero_iUnion
  intro n
  exact integrable_superlevel_lengthZero f hi _ (one_div_pos.mpr (by positivity))

end SingleVariableAnalysis
