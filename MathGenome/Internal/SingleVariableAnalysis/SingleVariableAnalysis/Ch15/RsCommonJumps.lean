import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsCommonJumps
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch15.RsDarboux
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.MonotoneLimits

namespace SingleVariableAnalysis.Stieltjes.CommonJumps
open Riemann Set Filter
open scoped Topology BigOperators
namespace C
export Specs.SingleVariableAnalysis.Ch15.RsCommonJumps (rightValue leftValue)
end C

/-- Insert one prescribed point, retaining every old partition point. -/
theorem insert_point {a b c : ℝ} (P : Partition a b) (hc : c ∈ Icc a b) :
    ∃ Q : Partition a b, Refines Q P ∧ c ∈ points Q := by
  classical
  obtain ⟨Q, hQ⟩ := finite_representation (insert c (points P))
    (Finset.mem_insert_of_mem (endpoints P).1)
    (Finset.mem_insert_of_mem (endpoints P).2.1)
    (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hc
        · exact (endpoints P).2.2 x hx)
  change points Q = insert c (points P) at hQ
  refine ⟨Q, ?_, ?_⟩
  · change points P ⊆ points Q
    rw [hQ]
    exact Finset.subset_insert _ _
  · rw [hQ]; exact Finset.mem_insert_self _ _

theorem right_cell {a b c : ℝ} (P : Partition a b)
    (hc : c ∈ points P) (hcb : c < b) :
    ∃ i : Fin P.n, P.point i.castSucc = c := by
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
  have hjn : j.val < P.n := by
    by_contra hn
    have he : j = Fin.last P.n := Fin.ext (by have := j.isLt; simp; omega)
    rw [he, P.last] at hj
    linarith
  exact ⟨⟨j.val, hjn⟩, hj⟩

theorem left_cell {a b c : ℝ} (P : Partition a b)
    (hc : c ∈ points P) (hac : a < c) :
    ∃ i : Fin P.n, P.point i.succ = c := by
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
  have hjpos : 0 < j.val := by
    by_contra hn
    have he : j = 0 := Fin.ext (by change j.val = 0; omega)
    rw [he, P.first] at hj
    linarith
  let i : Fin P.n := ⟨j.val - 1, by have := j.isLt; omega⟩
  have he : i.succ = j := Fin.ext (by dsimp [i]; omega)
  exact ⟨i, by rw [he]; exact hj⟩

/-- A single closed cell already supplies a lower bound for the whole
weighted Darboux gap. The two point values need not be attained extrema. -/
theorem cell_gap_le {a b : ℝ} (f α : ℝ → ℝ)
    (hf : BoundedOnInterval f a b) (hα : MonotoneOn α (Icc a b))
    (P : Partition a b) (i : Fin P.n) {x y : ℝ}
    (hx : x ∈ cell P i) (hy : y ∈ cell P i) :
    |f x - f y| * Darboux.weight α P i ≤
      Darboux.upperSum f α P hf - Darboux.lowerSum f α P hf := by
  have hb : |f x - f y| ≤ cellSupremum f P hf i - cellInfimum f P hf i := by
    have hxs := le_cellSupremum f P hf i hx
    have hys := le_cellSupremum f P hf i hy
    have hix := cellInfimum_le f P hf i hx
    have hiy := cellInfimum_le f P hf i hy
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hn (j : Fin P.n) :
      0 ≤ (cellSupremum f P hf j - cellInfimum f P hf j) * Darboux.weight α P j := by
    obtain ⟨z, hz⟩ := cell_nonempty P j
    exact mul_nonneg (sub_nonneg.mpr ((cellInfimum_le f P hf j hz).trans
      (le_cellSupremum f P hf j hz))) (Darboux.weight_nonneg hα P j)
  calc
    _ ≤ (cellSupremum f P hf i - cellInfimum f P hf i) * Darboux.weight α P i :=
      mul_le_mul_of_nonneg_right hb (Darboux.weight_nonneg hα P i)
    _ ≤ ∑ j : Fin P.n,
        (cellSupremum f P hf j - cellInfimum f P hf j) * Darboux.weight α P j :=
      Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
    _ = _ := by simp only [sub_mul, Finset.sum_sub_distrib]; rfl

/-- Real one-sided values are legitimate finite limits, also at the available
endpoints. Monotonicity bounds the nonempty image before csInf is used. -/
theorem right_limit_identity :
    Specs.SingleVariableAnalysis.Ch15.RsCommonJumps.rightLimitIdentity := by
  intro a b c α hac hcb hα
  have hne : (α '' Ioc c b).Nonempty := ⟨α b, mem_image_of_mem α ⟨hcb, le_rfl⟩⟩
  have hb : α c ∈ lowerBounds (α '' Ioc c b) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hα ⟨hac, hcb.le⟩ ⟨hac.trans hx.1.le, hx.2⟩ hx.1.le
  have hglb := isGLB_csInf hne ⟨α c, hb⟩
  have heq : Icc c b ∩ Ioi c = Ioc c b := by
    ext x
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h', h.2⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨h.le, h'⟩, h⟩
  have hmono : MonotoneOn α (Icc c b) := hα.mono (Icc_subset_Icc hac le_rfl)
  have ht := monotoneOn_tendsto_right_of_isGLB hmono (heq.symm ▸ hglb)
  rw [heq, nhdsWithin_Ioc_eq_nhdsGT hcb] at ht
  exact ⟨ht, le_csInf hne hb⟩

theorem left_limit_identity :
    Specs.SingleVariableAnalysis.Ch15.RsCommonJumps.leftLimitIdentity := by
  intro a b c α hac hcb hα
  have hne : (α '' Ico a c).Nonempty := ⟨α a, mem_image_of_mem α ⟨le_rfl, hac⟩⟩
  have hb : α c ∈ upperBounds (α '' Ico a c) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hα ⟨hx.1, hx.2.le.trans hcb⟩ ⟨hac.le, hcb⟩ hx.2.le
  have hlub := isLUB_csSup hne ⟨α c, hb⟩
  have heq : Icc a c ∩ Iio c = Ico a c := by
    ext x
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h.1, h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨h, h'.le⟩, h'⟩
  have hmono : MonotoneOn α (Icc a c) := hα.mono (Icc_subset_Icc le_rfl hcb)
  have ht := monotoneOn_tendsto_left_of_isLUB hmono (heq.symm ▸ hlub)
  rw [heq, nhdsWithin_Ico_eq_nhdsLT hac] at ht
  exact ⟨ht, csSup_le hne hb⟩

/-- Positive limsup supplies a fixed deviation occurring arbitrarily close
on the chosen side. Only nonnegativity is needed for this extraction. -/
theorem deviation_frequently {l : Filter ℝ} [NeBot l] (f : ℝ → ℝ) (c : ℝ)
    (h : 0 < limsup (fun x => |f x - f c|) l) :
    ∃ η : ℝ, 0 < η ∧ ∃ᶠ x in l, η < |f x - f c| := by
  refine ⟨_, half_pos h, ?_⟩
  exact frequently_lt_of_lt_limsup
    (isCoboundedUnder_le_of_le l (fun x => abs_nonneg (f x - f c)))
    (half_lt_self h)

theorem right_obstruction :
    Specs.SingleVariableAnalysis.Ch15.RsCommonJumps.rightObstruction := by
  intro a b c f α hac hcb hf hα hJ hosc
  rintro ⟨I, hI⟩
  obtain ⟨η, hη, hfreq⟩ := deviation_frequently f c hosc
  let J := C.rightValue α c b - α c
  obtain ⟨P, hP⟩ := Darboux.epsilon_of_integral (hac.trans hcb.le) f α hf hα hI
    (η * J) (mul_pos hη hJ)
  obtain ⟨Q, hQP, hcQ⟩ := insert_point P ⟨hac, hcb.le⟩
  obtain ⟨i, hi⟩ := right_cell Q hcQ hcb
  have hcu : c < Q.point i.succ := by
    rw [← hi]; exact Q.strictMono (Fin.castSucc_lt_succ (i := i))
  have hn : ∀ᶠ x in 𝓝[>] c, x ∈ Ioc c (Q.point i.succ) := by
    rw [← nhdsWithin_Ioc_eq_nhdsGT hcu]
    exact self_mem_nhdsWithin
  obtain ⟨x, hx, hfx⟩ := (hfreq.and_eventually hn).exists
  have hxcell : x ∈ cell Q i := ⟨by rw [hi]; exact hfx.1.le, hfx.2⟩
  have hccell : c ∈ cell Q i := ⟨by rw [hi], hcu.le⟩
  have hw : J ≤ Darboux.weight α Q i := by
    have hb : BddBelow (α '' Ioc c b) := ⟨α c, by
      rintro _ ⟨t, ht, rfl⟩
      exact hα ⟨hac, hcb.le⟩ ⟨hac.trans ht.1.le, ht.2⟩ ht.1.le⟩
    have hu := csInf_le hb (mem_image_of_mem α
      (show Q.point i.succ ∈ Ioc c b from ⟨hcu, (Darboux.point_mem Q _).2⟩))
    change C.rightValue α c b - α c ≤ α (Q.point i.succ) - α (Q.point i.castSucc)
    rw [hi]
    exact sub_le_sub_right hu _
  have hgap := cell_gap_le f α hf hα Q i hxcell hccell
  have hmul : η * J ≤ |f x - f c| * Darboux.weight α Q i :=
    mul_le_mul hx.le hw (le_of_lt hJ) (abs_nonneg _)
  have href := Darboux.refinement a b f α hf hα P Q hQP
  linarith

theorem left_obstruction :
    Specs.SingleVariableAnalysis.Ch15.RsCommonJumps.leftObstruction := by
  intro a b c f α hac hcb hf hα hJ hosc
  rintro ⟨I, hI⟩
  obtain ⟨η, hη, hfreq⟩ := deviation_frequently f c hosc
  let J := α c - C.leftValue α a c
  obtain ⟨P, hP⟩ := Darboux.epsilon_of_integral (hac.le.trans hcb) f α hf hα hI
    (η * J) (mul_pos hη hJ)
  obtain ⟨Q, hQP, hcQ⟩ := insert_point P ⟨hac.le, hcb⟩
  obtain ⟨i, hi⟩ := left_cell Q hcQ hac
  have hlc : Q.point i.castSucc < c := by
    rw [← hi]; exact Q.strictMono (Fin.castSucc_lt_succ (i := i))
  have hn : ∀ᶠ x in 𝓝[<] c, x ∈ Ico (Q.point i.castSucc) c := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hlc]
    exact self_mem_nhdsWithin
  obtain ⟨x, hx, hfx⟩ := (hfreq.and_eventually hn).exists
  have hxcell : x ∈ cell Q i := ⟨hfx.1, by rw [hi]; exact hfx.2.le⟩
  have hccell : c ∈ cell Q i := ⟨hlc.le, by rw [hi]⟩
  have hw : J ≤ Darboux.weight α Q i := by
    have hb : BddAbove (α '' Ico a c) := ⟨α c, by
      rintro _ ⟨t, ht, rfl⟩
      exact hα ⟨ht.1, ht.2.le.trans hcb⟩ ⟨hac.le, hcb⟩ ht.2.le⟩
    have hl := le_csSup hb (mem_image_of_mem α
      (show Q.point i.castSucc ∈ Ico a c from ⟨(Darboux.point_mem Q _).1, hlc⟩))
    change α c - C.leftValue α a c ≤ α (Q.point i.succ) - α (Q.point i.castSucc)
    rw [hi]
    exact sub_le_sub_left hl _
  have hgap := cell_gap_le f α hf hα Q i hxcell hccell
  have hmul : η * J ≤ |f x - f c| * Darboux.weight α Q i :=
    mul_le_mul hx.le hw (le_of_lt hJ) (abs_nonneg _)
  have href := Darboux.refinement a b f α hf hα P Q hQP
  linarith

theorem right_common_jump :
    Specs.SingleVariableAnalysis.Ch15.RsCommonJumps.rightCommonJump := by
  intro a b c L f α hac hcb hf hα hJ hL hne
  apply right_obstruction a b c f α hac hcb hf hα hJ
  have ht := (hL.sub_const (f c)).abs
  rw [ht.limsup_eq]
  exact abs_pos.mpr (sub_ne_zero.mpr hne)

theorem left_common_jump :
    Specs.SingleVariableAnalysis.Ch15.RsCommonJumps.leftCommonJump := by
  intro a b c L f α hac hcb hf hα hJ hL hne
  apply left_obstruction a b c f α hac hcb hf hα hJ
  have ht := (hL.sub_const (f c)).abs
  rw [ht.limsup_eq]
  exact abs_pos.mpr (sub_ne_zero.mpr hne)

/-- A node at zero prevents any adjacent cell from straddling zero. -/
theorem cell_not_crossing_zero {a b : ℝ} (P : Partition a b) (h0 : (0 : ℝ) ∈ points P)
    (i : Fin P.n) (hl : P.point i.castSucc < 0) : P.point i.succ ≤ 0 := by
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h0
  by_contra hu
  have hij : i.castSucc < j := P.strictMono.lt_iff_lt.mp (by rw [hj]; exact hl)
  have hji : j < i.succ := P.strictMono.lt_iff_lt.mp (by rw [hj]; exact lt_of_not_ge hu)
  have h₁ : i.val < j.val := hij
  have h₂ : j.val < i.val + 1 := hji
  omega

/-- On any partition containing zero all the nonzero integrator increments
are to its right, where every allowed tag has integrand value one. -/
theorem opposite_tagged_sum (P : Partition (-1 : ℝ) 1) (h0 : (0 : ℝ) ∈ points P)
    (t : Tagging P) :
    taggedSum P t (fun x => if 0 ≤ x then (1 : ℝ) else 0)
      (fun x => if 0 < x then (1 : ℝ) else 0) = 1 := by
  let α : ℝ → ℝ := fun x => if 0 < x then 1 else 0
  have hterm (i : Fin P.n) :
      (α (P.point i.succ) - α (P.point i.castSucc)) *
        (if 0 ≤ (t i).val then (1 : ℝ) else 0) =
      α (P.point i.succ) - α (P.point i.castSucc) := by
    by_cases hl : 0 ≤ P.point i.castSucc
    · have ht : 0 ≤ (t i).val := hl.trans (t i).property.1
      rw [ite_eq_left ht, mul_one]
    · have hu : P.point i.succ ≤ 0 := cell_not_crossing_zero P h0 i (lt_of_not_ge hl)
      have hnl : ¬ 0 < P.point i.castSucc := (lt_of_not_ge hl).le.not_gt
      have hnu : ¬ 0 < P.point i.succ := hu.not_gt
      simp only [α, ite_eq_right hnl, ite_eq_right hnu, sub_self, zero_mul]
  change (∑ i : Fin P.n, (α (P.point i.succ) - α (P.point i.castSucc)) *
    (if 0 ≤ (t i).val then (1 : ℝ) else 0)) = 1
  simp_rw [hterm]
  rw [sum_cell_differences (fun j => α (P.point j)), P.last, P.first]
  norm_num [α]

theorem opposite_sided :
    Specs.SingleVariableAnalysis.Ch15.RsCommonJumps.oppositeSided := by
  classical
  let α : ℝ → ℝ := fun x => if 0 < x then 1 else 0
  let f : ℝ → ℝ := fun x => if 0 ≤ x then 1 else 0
  have hα : MonotoneOn α (Icc (-1) 1) := by
    intro x _ y _ hxy
    dsimp [α]
    split_ifs with hx hy
    · exact le_rfl
    · exact False.elim (hy (hx.trans_le hxy))
    · norm_num
    · exact le_rfl
  have hf : BoundedOnInterval f (-1) 1 := by
    constructor
    · refine ⟨0, ?_⟩
      rintro _ ⟨x, _, rfl⟩
      dsimp [f]; split_ifs <;> norm_num
    · refine ⟨1, ?_⟩
      rintro _ ⟨x, _, rfl⟩
      dsimp [f]; split_ifs <;> norm_num
  have hr : C.rightValue α 0 1 = 1 := by
    have he : α '' Ioc 0 1 = {1} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp [α, hx.1]
      · intro hy
        have hy' : y = 1 := mem_singleton_iff.mp hy
        subst y
        exact ⟨1, ⟨by norm_num, le_rfl⟩, by norm_num [α]⟩
    change sInf (α '' Ioc 0 1) = 1
    rw [he, csInf_singleton]
  have hl : C.leftValue f (-1) 0 = 0 := by
    have he : f '' Ico (-1) 0 = {0} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp [f, not_le.mpr hx.2]
      · intro hy
        have hy' : y = 0 := mem_singleton_iff.mp hy
        subst y
        exact ⟨-1, ⟨le_rfl, by norm_num⟩, by norm_num [f]⟩
    change sSup (f '' Ico (-1) 0) = 0
    rw [he, csSup_singleton]
  refine ⟨hα, hf, ?_, ?_, ?_⟩
  · rw [hr]; norm_num [α]
  · rw [hl]; norm_num [f]
  · apply (integral_iff_of_le (-1) 1 (by norm_num) f α 1).mpr
    refine ⟨Darboux.boundedOn_of_boundedOnInterval hf,
      Darboux.monotone_boundedOn (by norm_num) hα, ?_⟩
    intro ε hε
    let P : Partition (-1 : ℝ) 1 := uniformPartition (by norm_num) 2 (by decide)
    obtain ⟨Q, _, hQ⟩ := insert_point P (show (0 : ℝ) ∈ Icc (-1) 1 by norm_num)
    refine ⟨Q, ?_⟩
    intro R hR t
    have h0R : (0 : ℝ) ∈ points R := hR hQ
    have hs : taggedSum R t f α = 1 := opposite_tagged_sum R h0R t
    change ‖taggedSum R t f α - 1‖ < ε
    rw [hs, sub_self, norm_zero]
    exact hε

end SingleVariableAnalysis.Stieltjes.CommonJumps
