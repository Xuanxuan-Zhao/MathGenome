import MathGenome.Internal.SingleVariableAnalysis.D03Insertion.CellGeometry
import MathGenome.Internal.SingleVariableAnalysis.Specs.D03Insertion.CellLengthSums
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

noncomputable section
namespace D03Insertion

/-- Consecutive increments of any real-valued finite sequence telescope. -/
theorem sum_consecutive_increments {t : ℕ} (v : Fin (t + 1) → ℝ) :
    ∑ j : Fin t, (v j.succ - v j.castSucc) = v (Fin.last t) - v 0 := by
  rw [Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_succ v
  have h₂ := Fin.sum_univ_castSucc v
  linarith

/-- Length conservation needs only valid endpoints and containment in old
cells. The exact node-union hypothesis used by the public theorem supplies
such assignments upstream, but no conservation certificate is assumed. -/
theorem cell_length_sum_of_containment {a b : ℝ} {n t : ℕ}
    {q : Fin (n + 1) → ℝ} {r : Fin (t + 1) → ℝ}
    (hq : ValidPartition a b q) (hr : ValidPartition a b r)
    (c : Fin t → Fin n)
    (hc : ∀ j, left q (c j) ≤ left r j ∧ right r j ≤ right q (c j))
    (i : Fin n) :
    ∑ j ∈ Finset.univ.filter (fun j => c j = i), width r j = width q i := by
  classical
  let L := left q i
  let U := right q i
  let F : ℝ → ℝ := fun x => min (max x L) U
  have hLU : L ≤ U := (sub_pos.mp (width_pos hq i)).le
  have hbelow : ∀ x, x ≤ L → F x = L := by
    intro x hx
    simp only [F, max_eq_right hx, min_eq_left hLU]
  have habove : ∀ x, U ≤ x → F x = U := by
    intro x hx
    exact min_eq_right (hx.trans (le_max_left _ _))
  have hwithin : ∀ x, L ≤ x → x ≤ U → F x = x := by
    intro x hL hU
    simp only [F, max_eq_left hL, min_eq_left hU]
  have hinc : ∀ j : Fin t,
      (if c j = i then width r j else 0) = F (right r j) - F (left r j) := by
    intro j
    have hpos : left r j ≤ right r j := (sub_pos.mp (width_pos hr j)).le
    by_cases hji : c j = i
    · have hj := hc j
      rw [hji] at hj
      rw [ite_eq_left hji, hwithin _ (hj.1.trans hpos) hj.2,
        hwithin _ hj.1 (hpos.trans hj.2)]
      rfl
    · rw [ite_eq_right hji]
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · have hstep : (c j).succ ≤ i.castSucc := by
          change (c j).val + 1 ≤ i.val
          exact hlt
        have hsep : right q (c j) ≤ L := hq.2.1.monotone hstep
        have hjU : right r j ≤ L := (hc j).2.trans hsep
        rw [hbelow _ hjU, hbelow _ (hpos.trans hjU), sub_self]
      · have hstep : i.succ ≤ (c j).castSucc := by
          change i.val + 1 ≤ (c j).val
          exact hgt
        have hsep : U ≤ left q (c j) := hq.2.1.monotone hstep
        have hjL : U ≤ left r j := hsep.trans (hc j).1
        rw [habove _ (hjL.trans hpos), habove _ hjL, sub_self]
  have hFa : F a = L := hbelow a (cell_endpoint_bounds hq i).1
  have hFb : F b = U := habove b (cell_endpoint_bounds hq i).2
  calc
    ∑ j ∈ Finset.univ.filter (fun j => c j = i), width r j =
        ∑ j : Fin t, if c j = i then width r j else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ j : Fin t, (F (right r j) - F (left r j)) :=
      Finset.sum_congr rfl (fun j _ => hinc j)
    _ = F (r (Fin.last t)) - F (r 0) :=
      sum_consecutive_increments (fun k => F (r k))
    _ = width q i := by rw [hr.2.2.2, hr.2.2.1, hFb, hFa]; rfl

/-- Exact conservation for the arbitrary sorted node union in the source. -/
theorem refined_cell_length_sum : Specification.refined_cell_length_sumType := by
  intro a b hab s n t p q r hp hq hr hu c hc i
  exact cell_length_sum_of_containment hq hr c hc i

/-- Regrouping is purely finite and holds for any additive commutative monoid. -/
theorem parent_fiber_sum : Specification.parent_fiber_sumType := by
  intro K _ n t c H
  classical
  exact (Finset.sum_fiberwise Finset.univ c H).symm

end D03Insertion
