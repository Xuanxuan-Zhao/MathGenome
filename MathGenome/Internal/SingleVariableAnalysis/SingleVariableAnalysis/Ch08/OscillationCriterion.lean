import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.OscillationCriterion
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.IntegrableDiscontinuities
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.MetricCompactness

/-!
# Riemann integrability and length-zero discontinuity sets

The converse in K03.08.oscillation_criterion, using finite covers of compact
positive oscillation superlevels and a Lebesgue number for an open cover.
All length estimates are finite telescoping sums. No measure or Lebesgue
integral is used.
-/
namespace SingleVariableAnalysis
open Set Riemann
open scoped BigOperators ENNReal

/-- Clipping the endpoint list to [c,d] bounds the total length of any
selection of partition cells contained in that interval. -/
theorem sum_cellLength_le_interval {a b c d : ℝ} (P : Partition a b)
    (s : Finset (Fin P.n)) (hcd : c ≤ d)
    (hs : ∀ i ∈ s, c ≤ P.point i.castSucc ∧ P.point i.succ ≤ d) :
    ∑ i ∈ s, cellLength P i ≤ d - c := by
  classical
  let q : ℝ → ℝ := fun x => min d (max c x)
  have hq : Monotone q := by
    intro x y hxy
    exact min_le_min_left d (max_le_max_left c hxy)
  have hqlo (x) : c ≤ q x := le_min hcd (le_max_left _ _)
  have hqhi (x) : q x ≤ d := min_le_left _ _
  have heq (i : Fin P.n) (hi : i ∈ s) :
      q (P.point i.succ) - q (P.point i.castSucc) = cellLength P i := by
    obtain ⟨hl, hu⟩ := hs i hi
    have hmono := (P.strictMono (Fin.castSucc_lt_succ (i := i))).le
    simp only [q, max_eq_right hl, max_eq_right (hl.trans hmono),
      min_eq_right hu, min_eq_right (hmono.trans hu)]
    rfl
  calc
    ∑ i ∈ s, cellLength P i =
        ∑ i ∈ s, (q (P.point i.succ) - q (P.point i.castSucc)) := by
      exact Finset.sum_congr rfl (fun i hi => (heq i hi).symm)
    _ ≤ ∑ i : Fin P.n, (q (P.point i.succ) - q (P.point i.castSucc)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      exact sub_nonneg.mpr (hq (P.strictMono (Fin.castSucc_lt_succ (i := i))).le)
    _ = q b - q a := by
      simpa only [P.last, P.first] using
        sum_cell_differences (fun j => q (P.point j))
    _ ≤ d - c := sub_le_sub (hqhi b) (hqlo a)

/-- Finite interval covers bound the total length of covered partition cells.
The intervals may overlap; the partition cell interiors are disjoint. -/
theorem sum_cellLength_le_cover {a b : ℝ} (P : Partition a b)
    (s : Finset (Fin P.n)) (t : Finset ℕ) (l u : ℕ → ℝ)
    (hlu : ∀ j ∈ t, l j ≤ u j)
    (hcover : ∀ i ∈ s, ∃ j ∈ t, cell P i ⊆ Ioo (l j) (u j)) :
    ∑ i ∈ s, cellLength P i ≤ ∑ j ∈ t, (u j - l j) := by
  classical
  calc
    ∑ i ∈ s, cellLength P i ≤
        ∑ i ∈ s, ∑ j ∈ t, if cell P i ⊆ Ioo (l j) (u j) then cellLength P i else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨j, hj, hij⟩ := hcover i hi
      have hh := Finset.single_le_sum (s := t)
        (f := fun k => if cell P i ⊆ Ioo (l k) (u k) then cellLength P i else 0)
        (fun k _ => by
          split_ifs
          · exact (cell_positive P i).le
          · exact le_rfl) hj
      simpa only [ite_eq_left hij] using hh
    _ = ∑ j ∈ t, ∑ i ∈ s, if cell P i ⊆ Ioo (l j) (u j) then cellLength P i else 0 :=
      Finset.sum_comm
    _ ≤ ∑ j ∈ t, (u j - l j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← Finset.sum_filter]
      apply sum_cellLength_le_interval P _ (hlu j hj)
      intro i hi
      obtain ⟨_, hsub⟩ := Finset.mem_filter.mp hi
      have hle := (P.strictMono (Fin.castSucc_lt_succ (i := i))).le
      exact ⟨(hsub ⟨le_rfl, hle⟩).1.le, (hsub ⟨hle, le_rfl⟩).2.le⟩

/-- A pairwise oscillation bound bounds the real supremum-minus-infimum on
a nonempty bounded cell, without assuming that extrema are attained. -/
theorem cell_gap_le_of_oscillation_le (f : ℝ → ℝ) {a b α : ℝ}
    (P : Partition a b) (hf : BoundedOnInterval f a b) (i : Fin P.n)
    (hα : 0 ≤ α) (h : Oscillation f (cell P i) ≤ ENNReal.ofReal α) :
    cellSupremum f P hf i - cellInfimum f P hf i ≤ α := by
  have hp (x) (hx : x ∈ cell P i) (y) (hy : y ∈ cell P i) : f x - f y ≤ α := by
    have hh := (distance_le_oscillation f (cell P i) hx hy).trans h
    have hh' : dist (f x) (f y) ≤ α := (ENNReal.ofReal_le_ofReal_iff hα).mp hh
    exact (le_abs_self _).trans (by simpa only [Real.dist_eq] using hh')
  apply sub_le_iff_le_add.mpr
  apply csSup_le ((cell_nonempty P i).image f)
  rintro _ ⟨x, hx, rfl⟩
  have hh : f x - α ≤ cellInfimum f P hf i := by
    apply le_csInf ((cell_nonempty P i).image f)
    rintro _ ⟨y, hy, rfl⟩
    linarith [hp x hx y hy]
  linarith

/-- A compact length-zero set has finite open interval covers with arbitrarily
small total real length. Compactness is essential for the finite conclusion. -/
theorem compact_lengthZero_finite_cover (E : Set ℝ) (hE : IsCompact E)
    (hz : LengthZero E) (η : ℝ) (hη : 0 < η) :
    ∃ (l u : ℕ → ℝ) (t : Finset ℕ), (∀ j, l j < u j) ∧
      E ⊆ ⋃ j ∈ t, Ioo (l j) (u j) ∧ ∑ j ∈ t, (u j - l j) < η := by
  obtain ⟨l, u, hlu, hcover, hsum⟩ := hz η hη
  obtain ⟨t, ht⟩ := hE.elim_finite_subcover (fun j => Ioo (l j) (u j))
    (fun _ => isOpen_Ioo) hcover
  refine ⟨l, u, t, hlu, ht, ?_⟩
  have hle : ENNReal.ofReal (∑ j ∈ t, (u j - l j)) ≤
      nonnegativeExtendedSum (fun j => u j - l j) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => (sub_pos.mpr (hlu j)).le)]
    exact ENNReal.sum_le_tsum t
  exact (ENNReal.ofReal_lt_ofReal_iff hη).mp (hle.trans_lt hsum)

/-- For sufficiently fine meshes, cells with gap above α have small total
length. Cover E_α finitely and use a Lebesgue number for that cover together
with all relative neighborhoods of oscillation below α. -/
theorem small_mesh_bad_cell_length (f : ℝ → ℝ) {a b α η : ℝ}
    (hf : BoundedOnInterval f a b) (hα : 0 < α) (hη : 0 < η)
    (hz : LengthZero (oscillationSuperlevel f a b α)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : Partition a b, mesh P < δ →
      ∑ i ∈ Finset.univ.filter (fun i : Fin P.n =>
        α < cellSupremum f P hf i - cellInfimum f P hf i), cellLength P i < η := by
  classical
  obtain ⟨l, u, t, hlu, hcover, hlength⟩ := compact_lengthZero_finite_cover
    (oscillationSuperlevel f a b α)
    (oscillationSuperlevel_compact f a b (boundedOnInterval_abs_bound f hf) α hα)
    hz η hη
  let C : Set (Set ℝ) := {V | (∃ j ∈ t, V = Ioo (l j) (u j)) ∨
    (IsOpen V ∧ Oscillation f (V ∩ Icc a b) < ENNReal.ofReal α)}
  have hCopen : ∀ V ∈ C, IsOpen V := by
    intro V hV
    rcases hV with ⟨j, _, rfl⟩ | ⟨hV, _⟩
    · exact isOpen_Ioo
    · exact hV
  have hCcover : Icc a b ⊆ ⋃₀ C := by
    intro x hx
    by_cases hbad : x ∈ oscillationSuperlevel f a b α
    · obtain ⟨j, hj, hxj⟩ : ∃ j ∈ t, x ∈ Ioo (l j) (u j) := by
        simpa only [mem_iUnion, exists_prop] using hcover hbad
      exact mem_sUnion.mpr ⟨Ioo (l j) (u j), Or.inl ⟨j, hj, rfl⟩, hxj⟩
    · have hxlt : intervalOscillation f a b x < ENNReal.ofReal α := by
        exact lt_of_not_ge (fun h => hbad ⟨hx, h⟩)
      rw [intervalOscillation_formula] at hxlt
      obtain ⟨r, hr⟩ := iInf_lt_iff.mp hxlt
      refine mem_sUnion.mpr ⟨Ioo (x - r.val) (x + r.val),
        Or.inr ⟨isOpen_Ioo, hr⟩, ?_⟩
      constructor <;> linarith [r.property]
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric_sUnion
    (real_closed_interval_compact a b) hCopen hCcover
  refine ⟨δ, hδ, ?_⟩
  intro P hP
  apply lt_of_le_of_lt (sum_cellLength_le_cover P _ t l u
    (fun j _ => (hlu j).le) ?_) hlength
  intro i hi
  have hbad := (Finset.mem_filter.mp hi).2
  have hmono := (P.strictMono (Fin.castSucc_lt_succ (i := i))).le
  have hleft : P.point i.castSucc ∈ Icc a b :=
    cell_subset_interval P i ⟨le_rfl, hmono⟩
  obtain ⟨V, hV, hsub⟩ := hball _ hleft
  have hcell : cell P i ⊆ V := by
    intro y hy
    apply hsub
    change dist y (P.point i.castSucc) < δ
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1)]
    exact lt_of_le_of_lt (sub_le_sub_right hy.2 _) ((cellLength_le_mesh P i).trans_lt hP)
  rcases hV with ⟨j, hj, rfl⟩ | ⟨_, hosc⟩
  · exact ⟨j, hj, hcell⟩
  · have hosc' : Oscillation f (cell P i) ≤ ENNReal.ofReal α := by
      apply (oscillation_mono f ?_).trans hosc.le
      intro y hy
      exact ⟨hcell hy, cell_subset_interval P i hy⟩
    exact False.elim ((not_le_of_gt hbad)
      (cell_gap_le_of_oscillation_le f P hf i hα.le hosc'))

/-- The finite Darboux gap estimate separating small-oscillation cells from
exceptional cells. Both sums are the original closed-cell Darboux sums. -/
theorem darboux_gap_le_bad_cell_length (f : ℝ → ℝ) {a b M α : ℝ}
    (P : Partition a b) (hf : BoundedOnInterval f a b) (hα : 0 ≤ α)
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) :
    upperSum f P hf - lowerSum f P hf ≤ α * (b - a) + 2 * M *
      (∑ i ∈ Finset.univ.filter (fun i : Fin P.n =>
        α < cellSupremum f P hf i - cellInfimum f P hf i), cellLength P i) := by
  classical
  let g : Fin P.n → ℝ := fun i => cellSupremum f P hf i - cellInfimum f P hf i
  have hg (i : Fin P.n) : g i ≤ 2 * M := by
    have hu : cellSupremum f P hf i ≤ M := by
      apply csSup_le ((cell_nonempty P i).image f)
      rintro _ ⟨x, hx, rfl⟩
      exact (le_abs_self _).trans (hM x (cell_subset_interval P i hx))
    have hl : -M ≤ cellInfimum f P hf i := by
      apply le_csInf ((cell_nonempty P i).image f)
      rintro _ ⟨x, hx, rfl⟩
      exact (abs_le.mp (hM x (cell_subset_interval P i hx))).1
    dsimp [g]
    linarith
  have hsum : (∑ i : Fin P.n, cellLength P i) = b - a := by
    simpa only [cellLength, S.lengthValue, P.last, P.first] using
      sum_cell_differences P.point
  calc
    upperSum f P hf - lowerSum f P hf = ∑ i : Fin P.n, g i * cellLength P i := by
      simp only [upperSum, lowerSum, D.upperSumValue, D.lowerSumValue,
        ← Finset.sum_sub_distrib, ← sub_mul]
      rfl
    _ ≤ ∑ i : Fin P.n, (α * cellLength P i +
        2 * M * (if α < g i then cellLength P i else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · have hh := mul_le_mul_of_nonneg_right (hg i) (cell_positive P i).le
        have hh' := mul_nonneg hα (cell_positive P i).le
        linarith
      · simpa only [mul_zero, add_zero] using
          mul_le_mul_of_nonneg_right (le_of_not_gt hi) (cell_positive P i).le
    _ = α * (b - a) + 2 * M *
        (∑ i ∈ Finset.univ.filter (fun i : Fin P.n => α < g i), cellLength P i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum,
        Finset.sum_filter]

/-- Length-zero relative discontinuities imply bounded Darboux integrability.
The finite covers are obtained for compact E_α, not for the possibly dense
full discontinuity set. -/
theorem lengthZero_discontinuities_integrable :
    Specs.SingleVariableAnalysis.Ch08.OscillationCriterion.lengthZeroDiscontinuitiesIntegrable := by
  intro f a b hab hf hz
  rcases lt_or_eq_of_le hab with hab' | rfl
  · obtain ⟨M, hM⟩ := boundedOnInterval_abs_bound f hf
    have hM0 : 0 ≤ M := (abs_nonneg (f a)).trans (hM a ⟨le_rfl, hab⟩)
    apply (darboux_criterion f hab' hf).mpr
    intro ε hε
    let α := ε / (2 * (b - a + 1))
    let η := ε / (4 * (M + 1))
    have hdenα : 0 < 2 * (b - a + 1) := by linarith
    have hdenη : 0 < 4 * (M + 1) := by linarith
    have hα : 0 < α := div_pos hε hdenα
    have hη : 0 < η := div_pos hε hdenη
    have hαeq : α * (2 * (b - a + 1)) = ε :=
      div_mul_cancel₀ ε hdenα.ne'
    have hηeq : η * (4 * (M + 1)) = ε :=
      div_mul_cancel₀ ε hdenη.ne'
    have hzα : LengthZero (oscillationSuperlevel f a b α) := by
      apply lengthZero_subset _ (intervalDiscontinuities f a b) ?_ hz
      intro x hx
      refine ⟨hx.1, ?_⟩
      intro hc
      have hzero := (intervalOscillation_zero_iff_continuous f a b ⟨M, hM⟩ x hx.1).mpr hc
      have hpos : 0 < ENNReal.ofReal α := ENNReal.ofReal_pos.mpr hα
      exact (not_le_of_gt hpos) (hzero ▸ hx.2)
    obtain ⟨δ, hδ, hbad⟩ := small_mesh_bad_cell_length f hf hα hη hzα
    obtain ⟨P, _, hP⟩ := arbitrarily_fine hab' δ hδ
    refine ⟨P, ?_⟩
    have hgap := darboux_gap_le_bad_cell_length f P hf hα.le hM
    have hbad' := mul_le_mul_of_nonneg_left (hbad P hP).le (by linarith : 0 ≤ 2 * M)
    have hαsmall : α * (b - a) < ε / 2 := by nlinarith
    have hηsmall : 2 * M * η < ε / 2 := by nlinarith
    linarith
  · exact realIntegrable_degenerate f a

/-- The full discontinuity criterion, with the established forward direction. -/
theorem discontinuity_criterion :
    Specs.SingleVariableAnalysis.Ch08.OscillationCriterion.discontinuityCriterion := by
  intro f a b hab hf
  exact ⟨integrable_discontinuities_lengthZero f,
    lengthZero_discontinuities_integrable f hab hf⟩

end SingleVariableAnalysis
