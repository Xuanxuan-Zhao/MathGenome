import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.DarbouxSums
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Partitions
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.SupInf
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin

/-! Closed-cell Darboux sums for bounded real functions. The refinement proof
uses the increasing inclusion of endpoint lists and finite telescoping sums. -/

namespace SingleVariableAnalysis.Riemann
open scoped BigOperators
namespace D
export Specs.SingleVariableAnalysis.Ch08.DarbouxSums
  (boundedOnIntervalValue cellValue cellSupremumValue cellInfimumValue
   upperSumValue lowerSumValue)
end D

abbrev BoundedOnInterval := D.boundedOnIntervalValue
abbrev cell := @D.cellValue
noncomputable abbrev cellSupremum := @D.cellSupremumValue
noncomputable abbrev cellInfimum := @D.cellInfimumValue
noncomputable abbrev upperSum := @D.upperSumValue
noncomputable abbrev lowerSum := @D.lowerSumValue

theorem cell_nonempty {a b : ℝ} (P : Partition a b) (i : Fin P.n) :
    (cell P i).Nonempty :=
  ⟨P.point i.castSucc, le_rfl,
    (P.strictMono (Fin.castSucc_lt_succ (i := i))).le⟩

theorem cell_subset_interval {a b : ℝ} (P : Partition a b) (i : Fin P.n) :
    cell P i ⊆ Set.Icc a b := by
  intro x hx
  have hlo : a ≤ P.point i.castSucc := by
    simpa only [P.first] using P.strictMono.monotone (Fin.zero_le i.castSucc)
  have hhi : P.point i.succ ≤ b := by
    simpa only [P.last] using P.strictMono.monotone (Fin.le_last i.succ)
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

theorem cell_image_bounded (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (i : Fin P.n) :
    BddBelow (f '' cell P i) ∧ BddAbove (f '' cell P i) :=
  ⟨hf.1.mono (Set.image_mono (cell_subset_interval P i)),
   hf.2.mono (Set.image_mono (cell_subset_interval P i))⟩

theorem cell_bounds : Specs.SingleVariableAnalysis.Ch08.DarbouxSums.cellBounds := by
  intro f a b P hf i
  exact ⟨isGLB_csInf ((cell_nonempty P i).image f) (cell_image_bounded f P hf i).1,
    isLUB_csSup ((cell_nonempty P i).image f) (cell_image_bounded f P hf i).2⟩

theorem cellInfimum_le (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (i : Fin P.n) {x : ℝ} (hx : x ∈ cell P i) :
    cellInfimum f P hf i ≤ f x :=
  (cell_bounds f P hf i).1.1 (Set.mem_image_of_mem f hx)

theorem le_cellSupremum (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) (i : Fin P.n) {x : ℝ} (hx : x ∈ cell P i) :
    f x ≤ cellSupremum f P hf i :=
  (cell_bounds f P hf i).2.1 (Set.mem_image_of_mem f hx)

theorem tagged_bounds : Specs.SingleVariableAnalysis.Ch08.DarbouxSums.taggedBounds := by
  intro f a b P hf ξ
  have hsum : taggedSum P ξ f = ∑ i : Fin P.n, f (ξ i) * cellLength P i := by
    simp only [taggedSum, S.sumValue, smul_eq_mul, mul_comm]
  change lowerSum f P hf ≤ taggedSum P ξ f ∧ taggedSum P ξ f ≤ upperSum f P hf
  rw [hsum]
  constructor
  · exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (cellInfimum_le f P hf i (ξ i).property)
        (cell_positive P i).le
  · exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (le_cellSupremum f P hf i (ξ i).property)
        (cell_positive P i).le

theorem lowerSum_le_upperSum (f : ℝ → ℝ) {a b : ℝ} (P : Partition a b)
    (hf : BoundedOnInterval f a b) : lowerSum f P hf ≤ upperSum f P hf := by
  obtain ⟨ξ⟩ := tags_exist P
  exact (tagged_bounds f P hf ξ).1.trans (tagged_bounds f P hf ξ).2

theorem degenerate_sums : Specs.SingleVariableAnalysis.Ch08.DarbouxSums.degenerateSums := by
  intro f a P hf
  have : IsEmpty (Fin P.n) := Fin.isEmpty_iff.mpr (n_eq_zero_of_degenerate a P)
  simp [D.lowerSumValue, D.upperSumValue]

/-- An old endpoint occurs at an index in every refinement. -/
theorem exists_refinementIndex {a b : ℝ} {P Q : Partition a b}
    (h : Refines Q P) (i : Fin (P.n + 1)) :
    ∃ j : Fin (Q.n + 1), Q.point j = P.point i := by
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp
    (h (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  exact ⟨j, hj⟩

noncomputable def refinementIndex {a b : ℝ} {P Q : Partition a b}
    (h : Refines Q P) (i : Fin (P.n + 1)) : Fin (Q.n + 1) :=
  Classical.choose (exists_refinementIndex h i)

theorem point_refinementIndex {a b : ℝ} {P Q : Partition a b}
    (h : Refines Q P) (i : Fin (P.n + 1)) :
    Q.point (refinementIndex h i) = P.point i :=
  Classical.choose_spec (exists_refinementIndex h i)

theorem refinementIndex_strictMono {a b : ℝ} {P Q : Partition a b}
    (h : Refines Q P) : StrictMono (refinementIndex h) := by
  intro i j hij
  apply Q.strictMono.lt_iff_lt.mp
  rw [point_refinementIndex, point_refinementIndex]
  exact P.strictMono hij

theorem refinementIndex_zero {a b : ℝ} {P Q : Partition a b}
    (h : Refines Q P) : refinementIndex h 0 = 0 := by
  apply Q.strictMono.injective
  rw [point_refinementIndex, P.first, Q.first]

theorem refinementIndex_last {a b : ℝ} {P Q : Partition a b}
    (h : Refines Q P) : refinementIndex h (Fin.last P.n) = Fin.last Q.n := by
  apply Q.strictMono.injective
  rw [point_refinementIndex, P.last, Q.last]

/-- Extend an endpoint list constantly after its last point, for natural-index
finite-sum identities. On actual endpoint indices this is the original list. -/
def endpointAt {a b : ℝ} (P : Partition a b) (k : ℕ) : ℝ :=
  P.point ⟨min k P.n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem endpointAt_eq {a b : ℝ} (P : Partition a b) (i : Fin (P.n + 1)) :
    endpointAt P i.val = P.point i := by
  unfold endpointAt
  congr 1
  exact Fin.ext (Nat.min_eq_left (Nat.le_of_lt_succ i.isLt))

/-- The telescoping identity for successive entries of a finite endpoint list. -/
theorem sum_cell_differences {n : ℕ} (g : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (g i.succ - g i.castSucc)) = g (Fin.last n) - g 0 := by
  have h₁ := Fin.sum_univ_succ g
  have h₂ := Fin.sum_univ_castSucc g
  rw [Finset.sum_sub_distrib]
  linarith

/-- A refinement decreases any cell-weighted sum when the coefficient on each
new cell is at most the coefficient on its containing old cell. -/
theorem weighted_sum_refinement_le {a b : ℝ} (P Q : Partition a b)
    (h : Refines Q P) (cP : Fin P.n → ℝ) (cQ : Fin Q.n → ℝ)
    (hc : ∀ (i : Fin P.n) (j : Fin Q.n), cell Q j ⊆ cell P i → cQ j ≤ cP i) :
    (∑ j : Fin Q.n, cQ j * cellLength Q j) ≤
      ∑ i : Fin P.n, cP i * cellLength P i := by
  classical
  let e := refinementIndex h
  let w : ℕ → ℝ := fun k => if hk : k < Q.n then
    cQ ⟨k, hk⟩ * cellLength Q ⟨k, hk⟩ else 0
  let F : ℕ → ℝ := fun k => ∑ t ∈ Finset.range k, w t
  have hsegment (i : Fin P.n) :
      F (e i.succ).val - F (e i.castSucc).val ≤ cP i * cellLength P i := by
    have hlr : (e i.castSucc).val ≤ (e i.succ).val :=
      ((refinementIndex_strictMono h) (Fin.castSucc_lt_succ (i := i))).le
    have hterm (k : ℕ) (hk : k ∈ Finset.Ico (e i.castSucc).val (e i.succ).val) :
        w k ≤ cP i * (endpointAt Q (k + 1) - endpointAt Q k) := by
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
      have hkQ : k < Q.n := by have := (e i.succ).isLt; omega
      let j : Fin Q.n := ⟨k, hkQ⟩
      have hsub : cell Q j ⊆ cell P i := by
        intro x hx
        have hl : Q.point (e i.castSucc) ≤ Q.point j.castSucc :=
          Q.strictMono.monotone (show e i.castSucc ≤ j.castSucc from hlo)
        have hr : Q.point j.succ ≤ Q.point (e i.succ) :=
          Q.strictMono.monotone (show j.succ ≤ e i.succ from Nat.succ_le_of_lt hhi)
        rw [point_refinementIndex] at hl hr
        exact ⟨hl.trans hx.1, hx.2.trans hr⟩
      dsimp only [w]
      rw [dite_eq_left hkQ]
      change cQ j * cellLength Q j ≤
        cP i * (endpointAt Q (k + 1) - endpointAt Q k)
      rw [show endpointAt Q (k + 1) = Q.point j.succ from endpointAt_eq Q j.succ,
        show endpointAt Q k = Q.point j.castSucc from endpointAt_eq Q j.castSucc]
      exact mul_le_mul_of_nonneg_right (hc i j hsub) (cell_positive Q j).le
    calc
      F (e i.succ).val - F (e i.castSucc).val =
          ∑ k ∈ Finset.Ico (e i.castSucc).val (e i.succ).val, w k :=
        (Finset.sum_Ico_eq_sub w hlr).symm
      _ ≤ ∑ k ∈ Finset.Ico (e i.castSucc).val (e i.succ).val,
          cP i * (endpointAt Q (k + 1) - endpointAt Q k) :=
        Finset.sum_le_sum hterm
      _ = cP i * (endpointAt Q (e i.succ).val - endpointAt Q (e i.castSucc).val) := by
        rw [← Finset.mul_sum, Finset.sum_Ico_sub _ hlr]
      _ = cP i * cellLength P i := by
        rw [endpointAt_eq, endpointAt_eq, point_refinementIndex, point_refinementIndex]
        rfl
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hsegment i)
  rw [sum_cell_differences (fun i => F (e i).val)] at hs
  change F (refinementIndex h (Fin.last P.n)).val -
    F (refinementIndex h 0).val ≤ _ at hs
  rw [refinementIndex_last, refinementIndex_zero] at hs
  have htotal : F Q.n = ∑ j : Fin Q.n, cQ j * cellLength Q j :=
    (Finset.sum_fin_eq_sum_range (fun j : Fin Q.n => cQ j * cellLength Q j)).symm
  have hzero : F 0 = 0 := Finset.sum_range_zero w
  simpa only [Fin.val_last, Fin.val_zero, htotal, hzero, sub_zero] using hs

theorem cellSupremum_mono (f : ℝ → ℝ) {a b : ℝ} (P Q : Partition a b)
    (hf : BoundedOnInterval f a b) (i : Fin P.n) (j : Fin Q.n)
    (hcell : cell Q j ⊆ cell P i) :
    cellSupremum f Q hf j ≤ cellSupremum f P hf i := by
  apply csSup_le ((cell_nonempty Q j).image f)
  rintro _ ⟨x, hx, rfl⟩
  exact le_cellSupremum f P hf i (hcell hx)

theorem cellInfimum_mono (f : ℝ → ℝ) {a b : ℝ} (P Q : Partition a b)
    (hf : BoundedOnInterval f a b) (i : Fin P.n) (j : Fin Q.n)
    (hcell : cell Q j ⊆ cell P i) :
    cellInfimum f P hf i ≤ cellInfimum f Q hf j := by
  apply le_csInf ((cell_nonempty Q j).image f)
  rintro _ ⟨x, hx, rfl⟩
  exact cellInfimum_le f P hf i (hcell hx)

theorem upper_refinement : Specs.SingleVariableAnalysis.Ch08.DarbouxSums.upperRefinement := by
  intro f a b P Q hf h
  exact weighted_sum_refinement_le P Q h (cellSupremum f P hf) (cellSupremum f Q hf)
    (fun i j hcell => cellSupremum_mono f P Q hf i j hcell)

theorem lower_refinement : Specs.SingleVariableAnalysis.Ch08.DarbouxSums.lowerRefinement := by
  intro f a b P Q hf h
  have hs := weighted_sum_refinement_le P Q h
    (fun i => -cellInfimum f P hf i) (fun j => -cellInfimum f Q hf j)
    (fun i j hcell => neg_le_neg (cellInfimum_mono f P Q hf i j hcell))
  change (∑ i : Fin P.n, cellInfimum f P hf i * cellLength P i) ≤
    ∑ j : Fin Q.n, cellInfimum f Q hf j * cellLength Q j
  simpa only [neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff] using hs

theorem lower_le_upper : Specs.SingleVariableAnalysis.Ch08.DarbouxSums.lowerLeUpper := by
  intro f a b P Q hf
  obtain ⟨R, _, hRP, hRQ⟩ := common_refinement P Q
  exact (lower_refinement f P R hf hRP).trans
    ((lowerSum_le_upperSum f R hf).trans (upper_refinement f Q R hf hRQ))

end SingleVariableAnalysis.Riemann
