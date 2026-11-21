import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.ExceptionalSlices
import MathGenome.Internal.MultivariableAnalysis.D04.C06.DarbouxFubini
import MathGenome.Internal.MultivariableAnalysis.D04.C06.ExceptionalSets

noncomputable section
open Set
open scoped BigOperators Classical
namespace D04.ExceptionalSlices
open Darboux NullCovers ExceptionalSets

abbrev sliceGap := @Specs.D04.C06.ExceptionalSlices.Model.sliceGap
abbrev sliceGapReverse := @Specs.D04.C06.ExceptionalSlices.Model.sliceGapReverse
abbrev exceptionalSet := @Specs.D04.C06.ExceptionalSlices.Model.exceptionalSet
abbrev exceptionalSetReverse := @Specs.D04.C06.ExceptionalSlices.Model.exceptionalSetReverse
abbrev badSlice := Specs.D04.C06.ExceptionalSlices.Model.badSlice

lemma degenerate_contentZero {n : ℕ} (Q : Box n) (hQ : Degenerate Q) :
    ContentZero (carrier Q) := by
  intro ε hε
  refine ⟨Unit, inferInstance, fun _ => Q, ?_, ?_⟩
  · intro x hx
    exact mem_iUnion.mpr ⟨(), hx⟩
  · simpa [content_degenerate Q hQ] using ENNReal.ofReal_pos.mpr hε

/-- The cover consists of exactly the grid cells whose supremum reaches η.
Nonnegativity makes all omitted contributions to the upper sum nonnegative. -/
theorem zero_integral_level_contentZero :
    Specs.D04.C06.ExceptionalSlices.zero_integral_level_contentZeroType := by
  classical
  intro n Q w hw hw0 hwI η hη
  by_cases hd : Degenerate Q
  · exact contentZero_mono (fun _ hx => hx.1) (degenerate_contentZero Q hd)
  have hQ := nondegenerate_of_not_degenerate hd
  intro ε hε
  have hu : upperIntegral w Q = 0 := hw.2.symm.trans hwI
  obtain ⟨v, ⟨P, rfl⟩, _, hP⟩ := (upperIntegral_isGLB w Q hw.1).exists_between
    (show upperIntegral w Q < ε * η by rw [hu]; positivity)
  let F : Finset (CellIndex P) := Finset.univ.filter (fun c => η ≤ cellSupremum w P c)
  have hsup0 (c : CellIndex P) : 0 ≤ cellSupremum w P c := by
    obtain ⟨x, hx⟩ := cell_nonempty P c
    exact (hw0 x (cell_subset P c hx)).trans (le_cellSupremum w hw.1 P c hx)
  have hsum : η * (∑ c ∈ F, cellContent P c) ≤ upperSum w P := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ c ∈ F, cellSupremum w P c * cellContent P c := by
        apply Finset.sum_le_sum
        intro c hc
        exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hc).2
          (cellContent_nonneg P c)
      _ ≤ upperSum w P := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
        intro c _ _
        exact mul_nonneg (hsup0 c) (cellContent_nonneg P c)
  have hsmall : (∑ c ∈ F, cellContent P c) < ε := by nlinarith
  refine ⟨F, inferInstance, fun c => cellBox P c.val, ?_, ?_⟩
  · rintro x ⟨hx, hxw⟩
    obtain ⟨c, hc⟩ := mem_iUnion.mp (by rw [← cells_cover Q hQ P]; exact hx)
    have hcF : c ∈ F := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hxw.trans (le_cellSupremum w hw.1 P c hc)⟩
    exact mem_iUnion.mpr ⟨⟨c, hcF⟩, hc⟩
  · rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun c _ => content_nonneg _)]
    change ENNReal.ofReal (∑ c : F, cellContent P c.val) < _
    rw [Finset.sum_coe_sort]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr hsmall

lemma positive_set_null {n : ℕ} (Q : Box n) (w : E n → ℝ)
    (hlevel : ∀ η > 0, ContentZero {x | x ∈ carrier Q ∧ η ≤ w x}) :
    Null {x | x ∈ carrier Q ∧ 0 < w x} := by
  have heq : {x | x ∈ carrier Q ∧ 0 < w x} =
      ⋃ k : ℕ, {x | x ∈ carrier Q ∧ 1 / (k + 1 : ℝ) ≤ w x} := by
    ext x
    constructor
    · rintro ⟨hx, hw⟩
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hw
      exact mem_iUnion.mpr ⟨k, hx, hk.le⟩
    · intro hx
      obtain ⟨k, hx, hk⟩ := mem_iUnion.mp hx
      exact ⟨hx, lt_of_lt_of_le (by positivity) hk⟩
  rw [heq]
  exact null_iUnion _ (fun k => contentZero_null (hlevel _ (by positivity)))

/-- The proof works for either coordinate ordering via the upstream block API. -/
lemma block_exceptional {p q n : ℕ} (e : Fin p ⊕ Fin q ≃ Fin n)
    (A : Box p) (B : Box q) (f : E n → ℝ)
    (hf : Integrable f (Specs.D04.C06.DarbouxFubini.Model.blockBox e A B)) :
    let l := fun x => lowerIntegral (fun y => f
      (Specs.D04.C06.DarbouxFubini.Model.blockPoint e x y)) B
    let u := fun x => upperIntegral (fun y => f
      (Specs.D04.C06.DarbouxFubini.Model.blockPoint e x y)) B
    ∃ hw : Integrable (fun x => u x - l x) A,
      (∀ x ∈ carrier A, 0 ≤ u x - l x) ∧ integral _ A hw = 0 ∧
      (∀ η > 0, ContentZero {x | x ∈ carrier A ∧ η ≤ u x - l x}) ∧
      {x | x ∈ carrier A ∧ 0 < u x - l x} =
        {x | x ∈ carrier A ∧ ¬ Integrable (fun y => f
          (Specs.D04.C06.DarbouxFubini.Model.blockPoint e x y)) B} ∧
      Null {x | x ∈ carrier A ∧ ¬ Integrable (fun y => f
          (Specs.D04.C06.DarbouxFubini.Model.blockPoint e x y)) B} := by
  dsimp only
  let l := fun x => lowerIntegral (fun y => f
      (Specs.D04.C06.DarbouxFubini.Model.blockPoint e x y)) B
  let u := fun x => upperIntegral (fun y => f
      (Specs.D04.C06.DarbouxFubini.Model.blockPoint e x y)) B
  have hlu (x) (hx : x ∈ carrier A) : l x ≤ u x :=
    lowerIntegral_le_upperIntegral _ _ (Fubini.slice_bounded e hf.1 hx)
  obtain ⟨hl, hIl⟩ := Fubini.block_fubini e hf l (fun _ _ => le_rfl) hlu
  obtain ⟨hu, hIu⟩ := Fubini.block_fubini e hf u hlu (fun _ _ => le_rfl)
  have hw : Integrable (fun x => u x - l x) A := by
    simpa only [neg_one_mul, sub_eq_add_neg] using integrable_add hu (integrable_smul (-1) hl)
  have hIw : integral (fun x => u x - l x) A hw = 0 := by
    have hh := integral_add hu (integrable_smul (-1) hl)
      (integrable_add hu (integrable_smul (-1) hl))
    rw [integral_smul (-1) hl, hIu, hIl] at hh
    simpa only [neg_one_mul, sub_eq_add_neg, add_neg_cancel] using hh
  have hw0 : ∀ x ∈ carrier A, 0 ≤ u x - l x := fun x hx => sub_nonneg.mpr (hlu x hx)
  have hlevel := zero_integral_level_contentZero A _ hw hw0 hIw
  have heq : {x | x ∈ carrier A ∧ 0 < u x - l x} =
      {x | x ∈ carrier A ∧ ¬ Integrable (fun y => f
        (Specs.D04.C06.DarbouxFubini.Model.blockPoint e x y)) B} := by
    ext x
    constructor
    · rintro ⟨hx, hp⟩
      exact ⟨hx, fun hs => (ne_of_gt hp) (sub_eq_zero.mpr hs.2.symm)⟩
    · rintro ⟨hx, hn⟩
      refine ⟨hx, sub_pos.mpr (lt_of_le_of_ne (hlu x hx) ?_)⟩
      exact fun he => hn ⟨Fubini.slice_bounded e hf.1 hx, he⟩
  exact ⟨hw, hw0, hIw, hlevel, heq, heq ▸ positive_set_null A _ hlevel⟩

theorem exceptional_slices : Specs.D04.C06.ExceptionalSlices.exceptional_slicesType := by
  intro p q _ _ A B f hf
  exact block_exceptional finSumFinEquiv A B f hf

theorem exceptional_slices_reverse :
    Specs.D04.C06.ExceptionalSlices.exceptional_slices_reverseType := by
  intro p q _ _ A B f hf
  have hf' : Integrable f (Specs.D04.C06.DarbouxFubini.Model.blockBox
      (Fubini.swapBlocks p q) B A) := by rw [Fubini.blockBox_swap]; exact hf
  unfold Specs.D04.C06.ExceptionalSlices.Model.sliceGapReverse
    Specs.D04.C06.DarbouxFubini.Model.upperSliceReverse
    Specs.D04.C06.DarbouxFubini.Model.lowerSliceReverse
    Specs.D04.C06.ExceptionalSlices.Model.exceptionalSetReverse
  simpa only [Fubini.blockPoint_swap] using
    block_exceptional (Fubini.swapBlocks p q) B A f hf'

/-- Darboux integrals depend only on the values in the closed box, including faces. -/
lemma darboux_congr_on {n : ℕ} {Q : Box n} {f g : E n → ℝ}
    (heq : ∀ x ∈ carrier Q, f x = g x) :
    lowerIntegral f Q = lowerIntegral g Q ∧ upperIntegral f Q = upperIntegral g Q := by
  have hc (P : Grid Q) (c : CellIndex P) : f '' cell P c = g '' cell P c :=
    image_congr (fun x hx => heq x (cell_subset P c hx))
  have hl : lowerSum f (Q := Q) = lowerSum g (Q := Q) := by
    funext P
    apply Finset.sum_congr rfl
    intro c _
    change sInf (f '' cell P c) * _ = sInf (g '' cell P c) * _
    rw [hc]
  have hu : upperSum f (Q := Q) = upperSum g (Q := Q) := by
    funext P
    apply Finset.sum_congr rfl
    intro c _
    change sSup (f '' cell P c) * _ = sSup (g '' cell P c) * _
    rw [hc]
  exact ⟨congrArg (fun h => sSup (Set.range h)) hl,
    congrArg (fun h => sInf (Set.range h)) hu⟩

lemma integrable_congr_on {n : ℕ} {Q : Box n} {f g : E n → ℝ}
    (heq : ∀ x ∈ carrier Q, f x = g x) : Integrable f Q ↔ Integrable g Q := by
  have hb : Bounded f Q ↔ Bounded g Q := by
    change (BddBelow (f '' carrier Q) ∧ BddAbove (f '' carrier Q)) ↔ _
    rw [image_congr heq]
    rfl
  have h := darboux_congr_on heq
  change (Bounded f Q ∧ lowerIntegral f Q = upperIntegral f Q) ↔ _
  rw [hb, h.1, h.2]
  rfl

lemma dirichlet_values (x : E 1) : 0 ≤ dirichlet x ∧ dirichlet x ≤ 1 := by
  classical
  by_cases hx : x ∈ rationalUnit <;>
    simp [dirichlet, Specs.D04.C06.ExceptionalSets.Model.dirichlet, hx]

lemma dirichlet_cell_extrema (P : Grid unitBox) (c : CellIndex P) :
    cellInfimum dirichlet P c = 0 ∧ cellSupremum dirichlet P c = 1 := by
  classical
  have hab : (P 0).point (c 0).castSucc < (P 0).point (c 0).succ :=
    (P 0).strictMono (Fin.castSucc_lt_succ (i := c 0))
  obtain ⟨r, hrl, hru⟩ := exists_rat_btwn hab
  have hr : scalarPoint (r : ℝ) ∈ cell P c := by
    intro i
    fin_cases i
    exact ⟨hrl.le, hru.le⟩
  have hrQ := cell_subset P c hr
  have hrr : scalarPoint (r : ℝ) ∈ rationalUnit := ⟨⟨r, rfl⟩, hrQ 0⟩
  have hrv : dirichlet (scalarPoint (r : ℝ)) = 1 := by
    simp [dirichlet, Specs.D04.C06.ExceptionalSets.Model.dirichlet, hrr]
  obtain ⟨t, hti, htl, htu⟩ := exists_irrational_btwn hab
  have ht : scalarPoint t ∈ cell P c := by
    intro i
    fin_cases i
    exact ⟨htl.le, htu.le⟩
  have htt : scalarPoint t ∉ rationalUnit := fun h => hti h.1
  have htv : dirichlet (scalarPoint t) = 0 := dirichlet_eq_zero_off _ htt
  constructor
  · apply le_antisymm
    · simpa only [htv] using cellInfimum_le dirichlet dirichlet_bounded P c ht
    · apply le_csInf ((cell_nonempty P c).image dirichlet)
      rintro _ ⟨x, _, rfl⟩
      exact (dirichlet_values x).1
  · apply le_antisymm
    · apply csSup_le ((cell_nonempty P c).image dirichlet)
      rintro _ ⟨x, _, rfl⟩
      exact (dirichlet_values x).2
    · simpa only [hrv] using le_cellSupremum dirichlet dirichlet_bounded P c hr

lemma unitBox_content : content unitBox = 1 := by
  norm_num [content, Specs.D04.C06.DarbouxIntegral.Model.content,
    unitBox, Specs.D04.C06.ExceptionalSets.Model.unitBox,
    intervalBox, Specs.D04.C06.DarbouxIntegral.Model.intervalBox,
    scalarPoint, Specs.D04.C06.DarbouxIntegral.Model.scalarPoint]

lemma dirichlet_darboux : lowerIntegral dirichlet unitBox = 0 ∧
    upperIntegral dirichlet unitBox = 1 := by
  have hl (P : Grid unitBox) : lowerSum dirichlet P = 0 := by
    change (∑ c, cellInfimum dirichlet P c * cellContent P c) = 0
    simp [(dirichlet_cell_extrema P _).1]
  have hu (P : Grid unitBox) : upperSum dirichlet P = 1 := by
    change (∑ c, cellSupremum dirichlet P c * cellContent P c) = 1
    simp_rw [(dirichlet_cell_extrema P _).2, one_mul]
    rw [content_partition, unitBox_content]
  obtain ⟨P⟩ := grid_exists unitBox
  constructor
  · apply le_antisymm
    · apply (lowerIntegral_isLUB dirichlet unitBox dirichlet_bounded).2
      rintro _ ⟨R, rfl⟩
      exact (hl R).le
    · simpa only [hl] using (lowerIntegral_isLUB dirichlet unitBox dirichlet_bounded).1 ⟨P, rfl⟩
  · apply le_antisymm
    · simpa only [hu] using (upperIntegral_isGLB dirichlet unitBox dirichlet_bounded).1 ⟨P, rfl⟩
    · apply (upperIntegral_isGLB dirichlet unitBox dirichlet_bounded).2
      rintro _ ⟨R, rfl⟩
      exact (hu R).ge

lemma badSlice_product (x y : E 1) : badSlice (productPoint x y) =
    (if x 0 = 0 then 1 else 0) *
      (if y 0 ∈ Set.range (fun r : ℚ => (r : ℝ)) then 1 else 0) := by
  classical
  rfl

lemma badSlice_slice_on (x y : E 1) (hy : y ∈ carrier unitBox) :
    badSlice (productPoint x y) = if x 0 = 0 then dirichlet y else 0 := by
  classical
  have hy0 : y 0 ∈ Icc (0 : ℝ) 1 := hy 0
  rw [badSlice_product]
  by_cases hx : x 0 = 0
  · rw [if_pos hx, if_pos hx, one_mul]
    by_cases hrat : y 0 ∈ Set.range (fun r : ℚ => (r : ℝ))
    · have h : y ∈ rationalUnit := ⟨hrat, hy0⟩
      simp [hrat, dirichlet, Specs.D04.C06.ExceptionalSets.Model.dirichlet, h]
    · have h : y ∉ rationalUnit := fun hh => hrat hh.1
      simp [hrat, dirichlet_eq_zero_off y h]
  · rw [if_neg hx, if_neg hx, zero_mul]

lemma badSlice_integral_zero : ∃ hf : Integrable badSlice (productBox unitBox unitBox),
    integral badSlice (productBox unitBox unitBox) hf = 0 := by
  classical
  let Q := productBox unitBox unitBox
  have hb : Bounded badSlice Q := by
    apply bounded_of_abs_le (M := 1)
    intro z _
    simp only [badSlice, Specs.D04.C06.ExceptionalSlices.Model.badSlice]
    split_ifs <;> norm_num
  have hS : ContentZero (coordinateFace Q 0 0) := by
    simpa using finite_faces_contentZero Q {(0, 0)}
  apply zero_off_contentZero (by decide) hb hS
  intro z hz hzS
  have hz0 : z 0 ≠ 0 := fun h => hzS ⟨hz, h⟩
  simp [badSlice, Specs.D04.C06.ExceptionalSlices.Model.badSlice, hz0]

lemma badSlice_slice_darboux (x : E 1) : lowerSlice badSlice unitBox x = 0 ∧
    upperSlice badSlice unitBox x = if x 0 = 0 then 1 else 0 := by
  classical
  by_cases hx : x 0 = 0
  · have hh := darboux_congr_on (fun y hy =>
      (badSlice_slice_on x y hy).trans (if_pos hx))
    exact ⟨hh.1.trans dirichlet_darboux.1,
      hh.2.trans (dirichlet_darboux.2.trans (if_pos hx).symm)⟩
  · have hh := darboux_congr_on (fun y hy =>
      (badSlice_slice_on x y hy).trans (if_neg hx))
    have hz := constant_integrals unitBox 0
    exact ⟨hh.1.trans (by simpa using hz.1),
      hh.2.trans (by simpa [hx] using hz.2)⟩

theorem bad_slice_example : Specs.D04.C06.ExceptionalSlices.bad_slice_exampleType := by
  obtain ⟨hf, hI⟩ := badSlice_integral_zero
  refine ⟨⟨hf, hI⟩, ?_, badSlice_slice_darboux, ?_⟩
  · intro hs
    apply dirichlet_not_integrable
    have hh := (integrable_congr_on (fun y hy => badSlice_slice_on (0 : E 1) y hy)).mp hs
    simpa using hh
  · obtain ⟨hl, hu, hIl, hIu⟩ := fubini_lower_upper unitBox unitBox badSlice hf
    exact ⟨hl, hu, hIl.trans hI, hIu.trans hI⟩

end D04.ExceptionalSlices
