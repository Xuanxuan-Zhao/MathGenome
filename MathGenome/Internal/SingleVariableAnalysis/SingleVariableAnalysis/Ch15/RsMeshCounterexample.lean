import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsMeshCounterexample
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsSums
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SingleVariableAnalysis.Stieltjes.MeshCounterexample
open Riemann
open scoped BigOperators
namespace Spec
export Specs.SingleVariableAnalysis.Ch15.RsMeshCounterexample
  (uniqueIncrement refinementSums refinementIntegral crossingSums fineCrossingSums noMeshLimit)
end Spec

private theorem zero_mem_base : (0 : ℝ) ∈ points base := by
  apply Finset.mem_image.mpr
  refine ⟨⟨1, by decide⟩, Finset.mem_univ _, ?_⟩
  unfold base
  norm_num

/-- Locate the zero node, which cannot be the final endpoint. -/
theorem unique_increment : Spec.uniqueIncrement := by
  intro P hP
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (hP zero_mem_base)
  have hjn : j.val < P.n := by
    have hne : j ≠ Fin.last P.n := by
      intro h
      rw [h, P.last] at hj
      norm_num at hj
    have := j.isLt
    have : j.val ≠ P.n := fun h => hne (Fin.ext h)
    omega
  let i : Fin P.n := ⟨j.val, hjn⟩
  have hleft : P.point i.castSucc = 0 := by
    have : i.castSucc = j := Fin.ext rfl
    rwa [this]
  have hright : 0 < P.point i.succ := by
    rw [← hleft]
    exact P.strictMono (Fin.castSucc_lt_succ (i := i))
  refine ⟨i, hleft, hright, ?_, ?_⟩
  · intro k
    split_ifs with hki
    · subst k
      simp [integrator, hleft, not_le.mpr hright]
    · rcases lt_or_gt_of_ne hki with hki | hik
      · have hk : P.point k.succ ≤ 0 := by
          rw [← hleft]
          apply P.strictMono.monotone
          change k.val + 1 ≤ i.val
          exact hki
        have hl : P.point k.castSucc ≤ 0 :=
          (P.strictMono.monotone (Fin.castSucc_le_succ k)).trans hk
        simp [integrator, hk, hl]
      · have hk : 0 < P.point k.castSucc := by
          rw [← hleft]
          apply P.strictMono
          exact hik
        have hr : 0 < P.point k.succ :=
          hk.trans_le (P.strictMono.monotone (Fin.castSucc_le_succ k))
        simp [integrator, not_le.mpr hk, not_le.mpr hr]
  · intro t
    have ht : 0 ≤ (t i : ℝ) := by simpa [hleft] using (t i).property.1
    simp [integrand, not_lt.mpr ht]

theorem refinement_sums : Spec.refinementSums := by
  classical
  intro P hP t
  obtain ⟨i, _, _, hi, ht⟩ := unique_increment P hP
  change (∑ j : Fin P.n, (integrator (P.point j.succ) -
    integrator (P.point j.castSucc)) * integrand (t j)) = 1
  simp_rw [hi]
  simp [ht]

theorem refinement_integral : Spec.refinementIntegral := by
  apply (integral_iff_of_le (-1) 1 (by norm_num) integrand integrator 1).mpr
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨1, fun x _ => ?_⟩
    simp only [integrand]
    split_ifs <;> norm_num
  · refine ⟨1, fun x _ => ?_⟩
    simp only [integrator]
    split_ifs <;> norm_num
  · intro ε hε
    refine ⟨base, fun P hP t => ?_⟩
    rw [refinement_sums P hP t, sub_self, norm_zero]
    exact hε

private theorem telescoping (n : ℕ) (g : Fin (n+1) → ℝ) :
    ∑ i : Fin n, (g i.succ - g i.castSucc) = g (Fin.last n) - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [← Fin.castSucc_succ]
    rw [ih (fun i => g i.castSucc)]
    simp only [Fin.castSucc_zero, Fin.succ_last]
    ring

/-- Right endpoint tags always give sum one. -/
def rightTags (P : Partition (-1) 1) : Tagging P := fun i =>
  ⟨P.point i.succ, (P.strictMono.monotone (Fin.castSucc_le_succ i)), le_rfl⟩

def leftTags (P : Partition (-1) 1) : Tagging P := fun i =>
  ⟨P.point i.castSucc, le_rfl, P.strictMono.monotone (Fin.castSucc_le_succ i)⟩

theorem right_sum (P : Partition (-1) 1) :
    Stieltjes.taggedSum P (rightTags P) integrand integrator = 1 := by
  change (∑ i : Fin P.n, (integrator (P.point i.succ) -
    integrator (P.point i.castSucc)) * integrand (P.point i.succ)) = 1
  have heq (i : Fin P.n) :
      (integrator (P.point i.succ) - integrator (P.point i.castSucc)) *
      integrand (P.point i.succ) = integrator (P.point i.succ) - integrator (P.point i.castSucc) := by
    have h := P.strictMono (Fin.castSucc_lt_succ (i := i))
    by_cases hr : P.point i.succ < 0
    · simp [integrand, integrator, hr, hr.le, (h.trans hr).le]
    · simp [integrand, hr]
  simp_rw [heq]
  rw [telescoping P.n (fun j => integrator (P.point j)), P.last, P.first]
  norm_num [integrator]

theorem left_sum (P : Partition (-1) 1) (hz : (0 : ℝ) ∉ points P) :
    Stieltjes.taggedSum P (leftTags P) integrand integrator = 0 := by
  change (∑ i : Fin P.n, (integrator (P.point i.succ) -
    integrator (P.point i.castSucc)) * integrand (P.point i.castSucc)) = 0
  apply Finset.sum_eq_zero
  intro i _
  by_cases hl : P.point i.castSucc < 0
  · simp [integrand, hl]
  · have hne : P.point i.castSucc ≠ 0 := by
      intro h
      apply hz
      exact Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, h⟩
    have hp : 0 < P.point i.castSucc := lt_of_le_of_ne (not_lt.mp hl) (Ne.symm hne)
    have hr : 0 < P.point i.succ := hp.trans (P.strictMono (Fin.castSucc_lt_succ (i := i)))
    simp [integrator, not_le.mpr hp, not_le.mpr hr]

/-- Strictly ordered nodes make all increments outside the crossing cell zero. -/
theorem crossing_sums : Spec.crossingSums := by
  classical
  intro P i hl hr
  have hi (j : Fin P.n) : integrator (P.point j.succ) -
      integrator (P.point j.castSucc) = if j = i then 1 else 0 := by
    split_ifs with hji
    · subst j
      simp [integrator, hl.le, not_le.mpr hr]
    · rcases lt_or_gt_of_ne hji with hji | hij
      · have hle : P.point j.succ ≤ P.point i.castSucc := by
          apply P.strictMono.monotone
          change j.val + 1 ≤ i.val
          exact hji
        have hjr : P.point j.succ ≤ 0 := hle.trans hl.le
        have hjl : P.point j.castSucc ≤ 0 :=
          (P.strictMono.monotone (Fin.castSucc_le_succ j)).trans hjr
        simp [integrator, hjr, hjl]
      · have hle : P.point i.succ ≤ P.point j.castSucc := by
          apply P.strictMono.monotone
          change i.val + 1 ≤ j.val
          exact hij
        have hjl : 0 < P.point j.castSucc := hr.trans_le hle
        have hjr : 0 < P.point j.succ :=
          hjl.trans_le (P.strictMono.monotone (Fin.castSucc_le_succ j))
        simp [integrator, not_le.mpr hjl, not_le.mpr hjr]
  refine ⟨hi, fun t => ?_⟩
  change (∑ j : Fin P.n, (integrator (P.point j.succ) -
    integrator (P.point j.castSucc)) * integrand (t j)) = integrand (t i)
  simp_rw [hi]
  simp

-- The odd uniform grid has central cell [-1/(2N+1),1/(2N+1)].
theorem fine_crossing_sums : Spec.fineCrossingSums := by
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  let m := 2*N+1
  have hm : 0 < m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hmval : (m : ℝ) = 2*(N : ℝ)+1 := by dsimp [m]; push_cast; rfl
  have hNm : (1 : ℝ) < δ * N := by simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hN
  have hsmall : (2 : ℝ) / m < δ := by
    apply (div_lt_iff₀ hmR).mpr
    rw [hmval]
    nlinarith
  let P := uniformPartition (show (-1 : ℝ) < 1 by norm_num) m hm
  have hmesh : mesh P = 2 / (m : ℝ) := by
    simpa only [P, show (1 : ℝ) - -1 = 2 by norm_num] using
      uniform_mesh (show (-1 : ℝ) < 1 by norm_num) m hm
  have hz : (0 : ℝ) ∉ points P := by
    intro hz
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hz
    change -1 + (j.val : ℝ) * (1 - -1) / (m : ℝ) = 0 at hj
    have heq : (2 : ℝ) * (j.val : ℝ) = (m : ℝ) := by
      have heq := (div_eq_iff hmne).mp
        (show (j.val : ℝ) * (1 - -1) / (m : ℝ) = 1 by linarith)
      linarith
    rw [hmval] at heq
    have heqN : 2*j.val = 2*N+1 := by exact_mod_cast heq
    omega
  let i : Fin P.n := ⟨N, by change N < 2*N+1; omega⟩
  have hl : P.point i.castSucc = -(1 / (m : ℝ)) := by
    change -1 + (N : ℝ) * (1 - -1) / (m : ℝ) = _
    rw [← neg_div]
    apply (eq_div_iff hmne).mpr
    field_simp
    rw [hmval]
    ring
  have hr : P.point i.succ = 1 / (m : ℝ) := by
    change -1 + ((N+1 : ℕ) : ℝ) * (1 - -1) / (m : ℝ) = _
    apply (eq_div_iff hmne).mpr
    field_simp
    rw [hmval]
    push_cast
    ring
  have hh : 0 < (1 : ℝ) / m := div_pos one_pos hmR
  refine ⟨P, ?_, ?_, hz, 1 / (m : ℝ), i, hh, ?_, hl, hr, ?_, ?_, ?_⟩
  · change 0 < mesh P
    rw [hmesh]; exact div_pos (by norm_num) hmR
  · change mesh P < δ
    rw [hmesh]; exact hsmall
  · have heq : (2 : ℝ) / m = 2 * (1 / (m : ℝ)) := by ring
    rw [heq] at hsmall
    linarith
  · refine ⟨leftTags P, ?_, left_sum P hz⟩
    change P.point i.castSucc < 0
    rw [hl]; linarith
  · refine ⟨rightTags P, ?_, right_sum P⟩
    change 0 < P.point i.succ
    rw [hr]; exact hh
  · have hli : P.point i.castSucc < 0 := by rw [hl]; linarith
    have hri : 0 < P.point i.succ := by rw [hr]; exact hh
    classical
    let t : Tagging P := fun j => if hji : j = i then
      ⟨0, by simpa only [hji] using hli.le, by simpa only [hji] using hri.le⟩
      else leftTags P j
    have ht : (t i : ℝ) = 0 := by simp [t]
    refine ⟨t, ht, ?_⟩
    rw [(crossing_sums P i hli hri).2 t, ht]
    norm_num [integrand]

theorem no_mesh_limit : Spec.noMeshLimit := by
  rintro ⟨I, hI⟩
  obtain ⟨δ, hδ, hclose⟩ := hI (1/3) (by norm_num)
  obtain ⟨P, _, hmesh, _, h, i, _, _, _, _, ⟨t, _, ht⟩, ⟨u, _, hu⟩, _⟩ :=
    fine_crossing_sums δ hδ
  have h₀ := hclose P hmesh t
  have h₁ := hclose P hmesh u
  rw [ht] at h₀
  rw [hu] at h₁
  rw [Real.norm_eq_abs] at h₀ h₁
  have ha := (abs_lt.mp h₀).1
  have hb := (abs_lt.mp h₁).2
  linarith

end SingleVariableAnalysis.Stieltjes.MeshCounterexample
