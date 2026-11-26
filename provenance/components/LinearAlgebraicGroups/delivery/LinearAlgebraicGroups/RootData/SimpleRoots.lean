import Specs.LinearAlgebraicGroups.RootData.SimpleRoots
import Mathlib.LinearAlgebra.RootSystem.BaseExists
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.BaseChange

import LinearAlgebraicGroups.RootData.DatumAndWeyl
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.RootData.SimpleRoots

open Specs.SimpleRoots
open Function Set Submodule RootPairing

noncomputable section

variable {Idx X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootPairing Idx ℤ X Y)

private lemma linearCombination_injective {s : Finset Idx}
    (hind : LinearIndepOn ℤ P.root s) :
    Injective (fun c : s → ℤ ↦ ∑ j, c j • P.root j.val) :=
  fun _ _ h ↦ funext (Fintype.linearIndependent_iffₛ.mp hind _ _ h)

private lemma root_reflection_sum (i j : Idx) :
    P.root (P.reflectionPerm j i) = P.root i - P.pairing i j • P.root j := by
  rw [root_reflectionPerm, reflection_apply_root]

private lemma reflection_conjugate (w : P.weylGroup) (i : Idx) :
    weylGroup.ofIdx P (P.weylGroupToPerm w i) = w * weylGroup.ofIdx P i * w⁻¹ := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective P
  ext x
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, LinearEquiv.mul_apply]
  change P.reflection (P.weylGroupToPerm w i) x =
    w.val.weightEquiv (P.reflection i (w.val.weightEquiv.symm x))
  rw [w.val.weightEquiv_reflection]
  simp

private lemma positive_height (b : P.Base) {i : Idx}
    (c : b.support → ℤ) (hc : ∀ j, 0 ≤ c j)
    (he : ∑ j, c j • P.root j.val = P.root i) : b.IsPos i := by
  classical
  let d (j : Idx) : ℤ := if h : j ∈ b.support then c ⟨j, h⟩ else 0
  have hd (j : b.support) : d j.val = c j := by simp [d, j.property]
  have he' : P.root i = ∑ j ∈ b.support, d j • P.root j := by
    rw [← Finset.sum_finset_coe, he.symm]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hd]
  have hs : b.height i = ∑ j, c j := by
    rw [b.height_eq_sum he', ← Finset.sum_finset_coe]
    exact Finset.sum_congr rfl fun j _ ↦ hd j
  exact (b.isPos_iff' (i := i)).mpr (hs ▸ Finset.sum_nonneg (fun j _ ↦ hc j))

section BaseConstruction

variable [Finite Idx] (f : X →ₗ[ℤ] ℤ) (hf : ∀ i, f (P.root i) ≠ 0)

private def simpleIndices : Finset Idx := (toFinite (IsAddIndecomposable.baseOf P.root f.toAddMonoidHom)).toFinset

private lemma mem_simpleIndices (i : Idx) : i ∈ simpleIndices P f ↔
    i ∈ positive P f ∧ ∀ j ∈ positive P f, ∀ l ∈ positive P f,
      P.root i ≠ P.root j + P.root l := by
  simp [simpleIndices, IsAddIndecomposable.baseOf, IsAddIndecomposable, positive, P.ne_zero]

private lemma simple_positive (j : simpleIndices P f) : 0 < f (P.root j.val) :=
  ((mem_simpleIndices P f _).mp j.property).1

include hf in
private lemma simple_independent : LinearIndepOn ℤ P.root (simpleIndices P f) := by
  rw [show (simpleIndices P f : Set Idx) = IsAddIndecomposable.baseOf P.root f.toAddMonoidHom by
    simp only [simpleIndices, Set.Finite.coe_toFinset]]
  exact P.linearIndepOn_root_baseOf' (S := ℤ) f hf

private lemma positive_sum {i : Idx} (hi : 0 < f (P.root i)) :
    ∃ c : simpleIndices P f → ℤ, (∀ j, 0 ≤ c j) ∧ ∑ j, c j • P.root j.val = P.root i := by
  classical
  have hm : P.root i ∈ AddSubmonoid.closure (P.root '' (simpleIndices P f : Set Idx)) := by
    simp only [simpleIndices, Set.Finite.coe_toFinset]
    rw [AddSubmonoid.closure_image_isAddIndecomposable_baseOf]
    exact AddSubmonoid.subset_closure (mem_image_of_mem _ hi)
  rw [← span_nat_eq_addSubmonoidClosure, Submodule.mem_toAddSubmonoid,
    Fintype.mem_span_image_iff_exists_fun] at hm
  obtain ⟨c, hc⟩ := hm
  exact ⟨fun j ↦ c j, fun _ ↦ by positivity, by simpa using hc⟩

variable [P.IsReduced]

include hf in
private lemma reflect_positive {i : Idx} (hi : 0 < f (P.root i))
    (j : simpleIndices P f) (hij : i ≠ j.val) :
    0 < f (P.root (P.reflectionPerm j.val i)) := by
  classical
  let := P.indexNeg
  obtain ⟨c, hc, hsum⟩ := positive_sum P f hi
  by_contra! h
  have hp : 0 < f (P.root (-(P.reflectionPerm j.val i))) := by
    change 0 < f (P.root (P.reflectionPerm (P.reflectionPerm j.val i) (P.reflectionPerm j.val i)))
    rw [root_reflectionPerm, reflection_apply_self, map_neg]
    exact neg_pos.mpr (lt_of_le_of_ne h (hf _))
  obtain ⟨d, hd, hsum'⟩ := positive_sum P f hp
  have heq : (fun l ↦ c l + d l) = Pi.single j (P.pairing i j.val) := by
    apply linearCombination_injective P (simple_independent P f hf)
    simp only [add_smul, Finset.sum_add_distrib, hsum, hsum']
    change P.root i + P.root (P.reflectionPerm _ _) = _
    rw [root_reflectionPerm, reflection_apply_self, root_reflection_sum]
    simp [Pi.single_apply]
  have hz (l : simpleIndices P f) (hl : l ≠ j) : c l = 0 := by
    have hzero : c l + d l = 0 := by simpa [Pi.single_apply, hl] using congrFun heq l
    linarith [hc l, hd l]
  have hsingle : c = Pi.single j (c j) := by
    funext l
    by_cases hlj : l = j
    · subst l; simp
    · simp [hlj, hz l hlj]
  rw [hsingle] at hsum
  have hmul : (c j) • P.root j.val = P.root i := by simpa [Pi.single_apply] using hsum
  have hn : ¬ LinearIndependent ℤ ![P.root i, P.root j.val] := by
    rw [LinearIndependent.pair_iff]
    push Not
    refine ⟨1, -c j, ?_, by simp⟩
    simp [← hmul]
  rcases IsReduced.eq_or_eq_neg i j.val hn with he | he
  · exact hij (P.root.injective he)
  · have := congrArg f he
    simp only [map_neg] at this
    linarith [simple_positive P f j]

include hf in
private lemma positive_orbit {i : Idx} (hi : 0 < f (P.root i)) :
    ∃ (w : P.weylGroup) (j : simpleIndices P f),
      w ∈ Subgroup.closure (Set.range (fun j : simpleIndices P f ↦ weylGroup.ofIdx P j.val)) ∧
      P.weylGroupToPerm w j.val = i := by
  classical
  generalize hn : (f (P.root i)).toNat = n
  induction n using Nat.strongRecOn generalizing i with
  | ind n ih =>
    by_cases hs : i ∈ simpleIndices P f
    · exact ⟨1, ⟨i, hs⟩, one_mem _, by simp⟩
    obtain ⟨c, _, hc⟩ := positive_sum P f hi
    have hnc : ¬ c ≤ 0 := by
      intro h
      have hle : ∑ j, c j * f (P.root j.val) ≤ 0 :=
        Finset.sum_nonpos fun j _ ↦ mul_nonpos_of_nonpos_of_nonneg (h j) (simple_positive P f j).le
      have hsum : ∑ j, c j * f (P.root j.val) = f (P.root i) := by
        rw [← hc, map_sum]
        simp only [map_smul, smul_eq_mul]
      linarith
    obtain ⟨j, _, hj⟩ := P.exists_pos_pairingIn (simple_independent P f hf)
      (by simpa [simpleIndices] using P.baseOf_pairwise_pairing_le_zero f.toAddMonoidHom hf) hc hnc
    let a := P.reflectionPerm j.val i
    have ha : 0 < f (P.root a) :=
      reflect_positive P f hf hi j fun e ↦ hs (e ▸ j.property)
    have hlt : f (P.root a) < f (P.root i) := by
      simp only [a, root_reflection_sum, map_sub, map_smul, smul_eq_mul]
      apply sub_lt_self
      have hpair := P.algebraMap_pairingIn ℤ i j.val
      rw [Algebra.algebraMap_self_apply] at hpair
      exact mul_pos (hpair ▸ hj) (simple_positive P f j)
    obtain ⟨w, l, hw, he⟩ := ih (m := (f (P.root a)).toNat) (by omega) ha rfl
    refine ⟨weylGroup.ofIdx P j.val * w, l, mul_mem (Subgroup.subset_closure (mem_range_self j)) hw, ?_⟩
    rw [map_mul, Equiv.Perm.mul_apply, he]
    exact P.reflectionPerm_self j.val i

include hf in
private lemma simple_orbit (i : Idx) :
    ∃ (w : P.weylGroup) (j : simpleIndices P f),
      w ∈ Subgroup.closure (Set.range (fun j : simpleIndices P f ↦ weylGroup.ofIdx P j.val)) ∧
      P.weylGroupToPerm w j.val = i := by
  let := P.indexNeg
  rcases lt_or_gt_of_ne (hf i) with hn | hp
  · have hni : 0 < f (P.root (P.reflectionPerm i i)) := by
      rw [root_reflectionPerm, reflection_apply_self, map_neg]
      exact neg_pos.mpr hn
    obtain ⟨w, j, hw, he⟩ := positive_orbit P f hf hni
    refine ⟨w * weylGroup.ofIdx P j.val, j,
      mul_mem hw (Subgroup.subset_closure (mem_range_self j)), ?_⟩
    apply P.root.injective
    rw [map_mul, Equiv.Perm.mul_apply]
    change P.root (P.weylGroupToPerm w (P.reflectionPerm j.val j.val)) = P.root i
    rw [← P.weylGroup_apply_root, root_reflectionPerm, reflection_apply_self, smul_neg,
      P.weylGroup_apply_root, he, root_reflectionPerm, reflection_apply_self, neg_neg]
  · exact positive_orbit P f hf hp

include hf in
private lemma coroot_in_span (i : Idx) :
    P.coroot i ∈ span ℤ (P.coroot '' (simpleIndices P f : Set Idx)) := by
  let L := span ℤ (P.coroot '' (simpleIndices P f : Set Idx))
  obtain ⟨w, j, hw, e⟩ := simple_orbit P f hf i
  rw [← e]
  have hsimple (l : simpleIndices P f) {y : Y} (hy : y ∈ L) :
      P.coreflection l.val y ∈ L := by
    rw [coreflection_apply]
    exact L.sub_mem hy (L.smul_mem _ (subset_span (mem_image_of_mem _ l.property)))
  have hpres (g : P.weylGroup)
      (hg : g ∈ Subgroup.closure (Set.range (fun j : simpleIndices P f ↦ weylGroup.ofIdx P j.val))) :
      ∀ y ∈ L, (g⁻¹).val.coweightEquiv y ∈ L := by
    induction hg using Subgroup.closure_induction'' with
    | one => simp
    | mem g hg =>
      obtain ⟨l, rfl⟩ := hg
      simpa [weylGroup.ofIdx] using fun y hy ↦ hsimple l (y := y) hy
    | inv_mem g hg =>
      obtain ⟨l, rfl⟩ := hg
      simpa [weylGroup.ofIdx] using fun y hy ↦ hsimple l (y := y) hy
    | mul g h hg hh IHg IHh =>
      intro y hy
      rw [mul_inv_rev, Subgroup.coe_mul, RootPairing.Equiv.mul_eq_comp,
        RootPairing.Equiv.coweightEquiv_comp_toLin, LinearEquiv.trans_apply]
      exact IHg _ (IHh _ hy)
  have hmem := hpres w hw (P.coroot j.val) (subset_span (mem_image_of_mem _ j.property))
  change w.val.coweightEquiv.symm (P.coroot j.val) ∈ L at hmem
  have he : w.val.coweightEquiv (P.coroot (P.weylGroupToPerm w j.val)) = P.coroot j.val := by
    rw [RootPairing.Equiv.coweightEquiv_apply, Hom.coroot_coweightMap_apply]
    change P.coroot (w.val.indexEquiv.symm (w.val.indexEquiv j.val)) = _
    simp
  exact (LinearEquiv.symm_apply_eq _).mpr he.symm ▸ hmem

include hf in
private def chosenBase : P.Base := by
  classical
  refine RootPairing.Base.mkOfPairwiseLEZero P (simple_independent P f hf)
    (by simpa [simpleIndices] using P.baseOf_pairwise_pairing_le_zero f.toAddMonoidHom hf)
    (coroot_in_span P f hf) ?_
  let := P.indexNeg
  have rootSpanOfPositive {i : Idx} (hi : 0 < f (P.root i)) :
      P.root i ∈ span ℤ (P.root '' (simpleIndices P f : Set Idx)) := by
    rw [Fintype.mem_span_image_iff_exists_fun]
    obtain ⟨c, -, hc⟩ := positive_sum P f hi
    exact ⟨c, hc⟩
  intro i
  rcases lt_or_gt_of_ne (hf i) with hn | hp
  · have h : 0 < f (P.root (P.reflectionPerm i i)) := by
      rw [root_reflectionPerm, reflection_apply_self, map_neg]
      exact neg_pos.mpr hn
    have := rootSpanOfPositive h
    rw [root_reflectionPerm, reflection_apply_self] at this
    exact neg_mem_iff.mp this
  · exact rootSpanOfPositive hp

include hf in
private lemma chosenBase_support : (chosenBase P f hf).support = simpleIndices P f := by
  unfold chosenBase
  exact RootPairing.Base.mkOfPairwiseLEZero_support ..

include hf in
private lemma chosenBase_positive (i : Idx) :
    (chosenBase P f hf).IsPos i ↔ i ∈ positive P f := by
  let b := chosenBase P f hf
  have h (j : Idx) (hj : 0 < f (P.root j)) : b.IsPos j := by
    have hs := positive_sum P f hj
    rw [← chosenBase_support P f hf] at hs
    obtain ⟨c, hc, he⟩ := hs
    exact positive_height P b c hc he
  refine ⟨fun hi ↦ ?_, h i⟩
  change 0 < f (P.root i)
  by_contra! hneg
  let := P.indexNeg
  have h' : 0 < f (P.root (-i)) := by
    change 0 < f (P.root (P.reflectionPerm i i))
    rw [root_reflectionPerm, reflection_apply_self, map_neg]
    exact neg_pos.mpr (lt_of_le_of_ne hneg (hf _))
  exact ((RootPairing.Base.IsPos.neg_iff_not b i).mp (h _ h')) hi

include hf in
private lemma chosenBase_generates :
    Subgroup.closure (Set.range (fun i : (chosenBase P f hf).support ↦
      weylGroup.ofIdx P i.val)) = ⊤ := by
  classical
  rw [chosenBase_support]
  let S := Subgroup.closure (Set.range (fun i : simpleIndices P f ↦ weylGroup.ofIdx P i.val))
  have hgen (i : Idx) : weylGroup.ofIdx P i ∈ S := by
    obtain ⟨w, j, hw, he⟩ := simple_orbit P f hf i
    rw [← he, reflection_conjugate]
    exact S.mul_mem (S.mul_mem hw (Subgroup.subset_closure (mem_range_self j))) (S.inv_mem hw)
  apply top_unique
  rintro ⟨w, hw⟩ -
  induction hw using weylGroup.induction with
  | mem i => exact hgen i
  | one => exact S.one_mem
  | mul g h hg hh hg' hh' => exact S.mul_mem hg' hh'

end BaseConstruction

section WordLength

variable (b : P.Base)

@[simp] private lemma word_nil : wordProduct P b [] = 1 := rfl

@[simp] private lemma word_cons (j : b.support) (l : List b.support) :
    wordProduct P b (j :: l) = weylGroup.ofIdx P j.val * wordProduct P b l := rfl

@[simp] private lemma word_append (l r : List b.support) :
    wordProduct P b (l ++ r) = wordProduct P b l * wordProduct P b r := by
  simp [wordProduct, List.prod_append]

@[simp] private lemma reflection_inverse (i : Idx) :
    (weylGroup.ofIdx P i)⁻¹ = weylGroup.ofIdx P i := by
  exact Subtype.ext (RootPairing.Equiv.reflection_inv P i)

@[simp] private lemma reflection_cancel (i : Idx) :
    weylGroup.ofIdx P i * weylGroup.ofIdx P i = 1 := by
  exact mul_eq_one_iff_inv_eq.mpr (reflection_inverse P i)

@[simp] private lemma word_reverse (l : List b.support) :
    wordProduct P b l.reverse = (wordProduct P b l)⁻¹ := by
  induction l with
  | nil => simp
  | cons j l ih => simp [List.reverse_cons, ih, mul_inv_rev]

private lemma exists_word (hgen : Subgroup.closure
    (Set.range (fun j : b.support ↦ weylGroup.ofIdx P j.val)) = ⊤) (w : P.weylGroup) :
    ∃ l, wordProduct P b l = w := by
  have hw : w ∈ Subgroup.closure (Set.range (fun j : b.support ↦ weylGroup.ofIdx P j.val)) := by
    rw [hgen]; trivial
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨j, rfl⟩ := hw
    exact ⟨[j], by simp⟩
  | one => exact ⟨[], rfl⟩
  | mul g h _ _ hg hh =>
    obtain ⟨l, hl⟩ := hg
    obtain ⟨r, hr⟩ := hh
    exact ⟨l ++ r, by simp [hl, hr]⟩
  | inv g _ hg =>
    obtain ⟨l, hl⟩ := hg
    exact ⟨l.reverse, by simp [hl]⟩

private lemma exists_shortest_word (hgen : Subgroup.closure
    (Set.range (fun j : b.support ↦ weylGroup.ofIdx P j.val)) = ⊤) (w : P.weylGroup) :
    ∃ l, wordProduct P b l = w ∧ l.length = wordLength P b w ∧
      ∀ k, wordProduct P b k = w → l.length ≤ k.length := by
  obtain ⟨l, hl⟩ := exists_word P b hgen w
  have hne : {n | ∃ l : List b.support, l.length = n ∧ wordProduct P b l = w}.Nonempty :=
    ⟨l.length, l, rfl, hl⟩
  obtain ⟨k, hk, hkw⟩ := csInf_mem hne
  exact ⟨k, hkw, hk, fun r hr ↦ hk.trans_le (csInf_le' ⟨r, rfl, hr⟩)⟩

private lemma length_inverse (w : P.weylGroup) :
    wordLength P b w⁻¹ = wordLength P b w := by
  unfold wordLength
  congr 1
  ext n
  constructor <;> rintro ⟨l, hl, hw⟩
  · exact ⟨l.reverse, by simpa, by simp [hw]⟩
  · exact ⟨l.reverse, by simpa, by simp [hw]⟩

private lemma perm_mul (w z : P.weylGroup) (i : Idx) :
    P.weylGroupToPerm (w * z) i = P.weylGroupToPerm w (P.weylGroupToPerm z i) := by
  rw [map_mul, Equiv.Perm.mul_apply]

private lemma perm_reflection (j i : Idx) :
    P.weylGroupToPerm (weylGroup.ofIdx P j) i = P.reflectionPerm j i := rfl

variable [Finite Idx] [P.IsReduced]
  (f : X →ₗ[ℤ] ℤ) (hf : ∀ i, f (P.root i) ≠ 0)
  (hb : ∀ i, b.IsPos i ↔ i ∈ positive P f)

omit [Finite Idx] [P.IsReduced] in
include hb in
private lemma simple_value (j : b.support) : 0 < f (P.root j.val) :=
  (hb _).mp (b.isPos_of_mem_support j.property)

omit [Finite Idx] [P.IsReduced] in
private lemma reflected_value (w : P.weylGroup) (i : Idx) :
    f (P.root (P.weylGroupToPerm w (P.reflectionPerm i i))) =
      -f (P.root (P.weylGroupToPerm w i)) := by
  rw [← P.weylGroup_apply_root, root_reflectionPerm, reflection_apply_self, smul_neg,
    P.weylGroup_apply_root, map_neg]

include hb in
private lemma simple_reflection_positive (j : b.support) {i : Idx}
    (hi : 0 < f (P.root i)) (hij : i ≠ j.val) :
    0 < f (P.root (P.reflectionPerm j.val i)) :=
  (hb _).mp (((hb _).mpr hi).reflectionPerm j.property hij)

include hf hb in
private lemma delete_of_signChange (l : List b.support) {i : Idx}
    (hi : 0 < f (P.root i)) (hneg : f (P.root (P.weylGroupToPerm (wordProduct P b l) i)) < 0) :
    ∃ k, wordProduct P b k = wordProduct P b l * weylGroup.ofIdx P i ∧
      k.length + 1 = l.length := by
  induction l with
  | nil =>
    simp only [word_nil, map_one, Equiv.Perm.one_apply] at hneg
    exact (not_lt_of_gt hi hneg).elim
  | cons j l ih =>
    by_cases hn : f (P.root (P.weylGroupToPerm (wordProduct P b l) i)) < 0
    · obtain ⟨k, hk, hlen⟩ := ih hn
      refine ⟨j :: k, by simp [hk, mul_assoc], ?_⟩
      simp only [List.length_cons]
      omega
    · have hpos : 0 < f (P.root (P.weylGroupToPerm (wordProduct P b l) i)) :=
        lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (hf _))
      have he : P.weylGroupToPerm (wordProduct P b l) i = j.val := by
        by_contra hne
        have h := simple_reflection_positive P b f hb j hpos hne
        rw [word_cons, perm_mul, perm_reflection] at hneg
        exact not_lt_of_gt h hneg
      have hj := reflection_conjugate P (wordProduct P b l) i
      rw [he] at hj
      exact ⟨l, by simp [hj, mul_assoc], rfl⟩

private def rightInversions (w : P.weylGroup) : Set Idx :=
  {i | 0 < f (P.root i) ∧ f (P.root (P.weylGroupToPerm w i)) < 0}

include hb in
private lemma rightInversions_mul (w : P.weylGroup) (j : b.support)
    (hpos : 0 < f (P.root (P.weylGroupToPerm w j.val))) :
    rightInversions P f (w * weylGroup.ofIdx P j.val) =
    insert j.val (P.reflectionPerm j.val '' rightInversions P f w) := by
  ext i
  simp only [rightInversions, mem_ofPred_eq, mem_insert_iff, mem_image, perm_mul, perm_reflection]
  constructor
  · intro h
    by_cases he : i = j.val
    · exact Or.inl he
    · exact Or.inr ⟨P.reflectionPerm j.val i,
        ⟨simple_reflection_positive P b f hb j h.1 he, h.2⟩, P.reflectionPerm_self _ _⟩
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · rw [reflected_value]
      exact ⟨simple_value P b f hb j, neg_neg_of_pos hpos⟩
    · rw [P.reflectionPerm_self]
      have hne : a ≠ j.val := by
        rintro rfl
        exact not_lt_of_gt hpos ha.2
      exact ⟨simple_reflection_positive P b f hb j ha.1 hne, ha.2⟩

include hb in
private lemma rightInversions_card_mul (w : P.weylGroup) (j : b.support)
    (hpos : 0 < f (P.root (P.weylGroupToPerm w j.val))) :
    (rightInversions P f (w * weylGroup.ofIdx P j.val)).ncard =
      (rightInversions P f w).ncard + 1 := by
  rw [rightInversions_mul P b f hb w j hpos]
  have hn : j.val ∉ P.reflectionPerm j.val '' rightInversions P f w := by
    rintro ⟨a, ha, he⟩
    apply_fun P.reflectionPerm j.val at he
    rw [P.reflectionPerm_self] at he
    have hpa := ha.1
    rw [he, root_reflectionPerm, reflection_apply_self, map_neg] at hpa
    exact not_lt_of_gt (simple_value P b f hb j) (neg_pos.mp hpa)
  rw [Set.ncard_insert_of_notMem hn, Set.ncard_image_of_injective _ (P.reflectionPerm _).injective]

include hf hb in
private lemma shortest_word_card (l : List b.support)
    (hmin : ∀ k, wordProduct P b k = wordProduct P b l → l.length ≤ k.length) :
    l.length = (rightInversions P f (wordProduct P b l)).ncard := by
  induction l using List.reverseRecOn with
  | nil =>
    have h : rightInversions P f (1 : P.weylGroup) = ∅ := by
      ext i
      simp only [rightInversions, map_one, Equiv.Perm.one_apply, mem_ofPred_eq, mem_empty_iff_false,
        iff_false]
      exact fun he ↦ not_lt_of_gt he.1 he.2
    simp [h]
  | append_singleton l j ih =>
    have hl : ∀ k, wordProduct P b k = wordProduct P b l → l.length ≤ k.length := by
      intro k hk
      simpa using hmin (k ++ [j]) (by simp [hk])
    have hp : 0 < f (P.root (P.weylGroupToPerm (wordProduct P b l) j.val)) := by
      rcases lt_or_gt_of_ne (hf (P.weylGroupToPerm (wordProduct P b l) j.val)) with hn | hp
      · obtain ⟨k, hk, hkl⟩ := delete_of_signChange P b f hf hb l (simple_value P b f hb j) hn
        have hm := hmin k (by simpa using hk)
        simp only [List.length_append, List.length_singleton] at hm
        omega
      · exact hp
    simp only [List.length_append, List.length_singleton, word_append, word_cons, word_nil, mul_one,
      rightInversions_card_mul P b f hb _ j hp, ih hl]

include hf hb in
private lemma length_eq_inversions
    (hgen : Subgroup.closure (Set.range (fun j : b.support ↦ weylGroup.ofIdx P j.val)) = ⊤)
    (w : P.weylGroup) : wordLength P b w = (inversions P f w).ncard := by
  rw [← length_inverse P b w]
  obtain ⟨l, hw, hlen, hmin⟩ := exists_shortest_word P b hgen w⁻¹
  rw [← hlen]
  change l.length = (rightInversions P f w⁻¹).ncard
  rw [← hw]
  exact shortest_word_card P b f hf hb l fun k hk ↦ hmin k (hk.trans hw)

end WordLength

section Geometry

open scoped nonZeroDivisors

private abbrev rationalize : X →ₗ[ℤ] (ℚ ⊗[ℤ] X) := TensorProduct.mk ℤ ℚ X 1

private lemma rationalValues {J V : Type*} [AddCommGroup V] [Module ℚ V] {v : J → V}
    (hv : LinearIndependent ℚ v) (c : J → ℚ) :
    ∃ g : V →ₗ[ℚ] ℚ, ∀ j, g (v j) = c j := by
  let B := Module.Basis.span hv
  obtain ⟨g, hg⟩ := (B.constr ℚ c).exists_extend
  refine ⟨g, fun j ↦ ?_⟩
  have hj := DFunLike.congr_fun hg (B j)
  simpa only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coe_span_apply,
    Module.Basis.constr_basis, B] using hj

private lemma independent_rational {J : Type*} {v : J → X} (hv : LinearIndependent ℤ v) :
    LinearIndependent ℚ (rationalize ∘ v) :=
  hv.of_isLocalizedModule ℚ ℤ⁰ (TensorProduct.mk ℤ ℚ X 1)

private lemma rationalSpan_iff (b : P.Base) (I : Set Idx) (hI : I ⊆ b.support) (i : Idx) :
    rationalize (P.root i) ∈ span ℚ ((rationalize ∘ P.root) '' I) ↔
      P.root i ∈ span ℤ (P.root '' I) := by
  classical
  constructor
  · intro hi
    obtain ⟨c, _, _, hc⟩ := b.exists_root_eq_sum_int i
    have hz (j : b.support) (hj : j.val ∉ I) : c j.val = 0 := by
      obtain ⟨g, hg⟩ := rationalValues
        (independent_rational (v := fun j : b.support ↦ P.root j.val) b.linearIndepOn_root)
        (Pi.single (M := fun _ : b.support ↦ ℚ) j 1)
      have hker : span ℚ ((rationalize ∘ P.root) '' I) ≤ LinearMap.ker g := by
        refine span_le.mpr ?_
        rintro - ⟨l, hl, rfl⟩
        change g (rationalize (P.root l)) = 0
        have hne : (⟨l, hI hl⟩ : b.support) ≠ j := fun h ↦ hj (congrArg Subtype.val h ▸ hl)
        simpa [Pi.single_apply, hne] using hg ⟨l, hI hl⟩
      have hg' (l : b.support) : g (rationalize (P.root l.val)) = Pi.single (M := fun _ : b.support ↦ ℚ) j 1 l := hg l
      have hs : g (rationalize (P.root i)) = (c j.val : ℚ) := by
        rw [hc, ← Finset.sum_finset_coe, map_sum, map_sum]
        simp only [map_zsmul, hg']
        simp [Pi.single_apply, smul_ite, zsmul_eq_mul]
      exact_mod_cast hs.symm.trans (show g (rationalize (P.root i)) = 0 from hker hi)
    rw [hc, ← Finset.sum_finset_coe]
    refine sum_mem fun j _ ↦ ?_
    by_cases hj : j.val ∈ I
    · exact smul_mem _ _ (subset_span (mem_image_of_mem _ hj))
    · simp [hz j hj]
  · intro hi
    refine Submodule.span_induction (p := fun x _ ↦ rationalize x ∈
      span ℚ ((rationalize ∘ P.root) '' I)) ?_ ?_ ?_ ?_ hi
    · rintro - ⟨j, hj, rfl⟩
      exact subset_span (mem_image_of_mem (rationalize ∘ P.root) hj)
    · simp
    · intro x y _ _ hx hy
      simpa only [map_add] using add_mem hx hy
    · intro a x _ hx
      rw [map_smul, ← algebraMap_smul ℚ]
      exact smul_mem _ _ hx

private lemma exists_integralValues [Module.Free ℤ X] [Module.Finite ℤ X] {J : Type*}
    {v : J → X} (hv : LinearIndependent ℤ v) (c : J → ℤ) :
    ∃ (g : X →ₗ[ℤ] ℤ) (m : ℤ), 0 < m ∧ ∀ j, g (v j) = m * c j := by
  obtain ⟨g, hg⟩ := rationalValues (independent_rational hv) (fun j ↦ (c j : ℚ))
  let B := Module.Free.chooseBasis ℤ X
  let gQ : X →ₗ[ℤ] ℚ := (g.restrictScalars ℤ).comp rationalize
  have : Finite (Module.Free.ChooseBasisIndex ℤ X) := Module.Finite.finite_basis B
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite ℤ⁰ (fun j ↦ gQ (B j))
  choose coeff hcoeff using hd
  let gZ := B.constr ℤ coeff
  let castZ : ℤ →ₗ[ℤ] ℚ := Algebra.linearMap ℤ ℚ
  have he : castZ.comp gZ = (d.val : ℤ) • gQ := by
    apply B.ext
    intro j
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, Module.Basis.constr_basis,
      Algebra.linearMap_apply, gZ, castZ] using hcoeff j
  have hd' : (d : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp d.property
  refine ⟨d.val • gZ, d.val * d.val, mul_self_pos.mpr hd', fun j ↦ ?_⟩
  have hj := DFunLike.congr_fun he (v j)
  change ((gZ (v j) : ℤ) : ℚ) = (d : ℤ) • g (rationalize (v j)) at hj
  rw [show g (rationalize (v j)) = (c j : ℚ) from hg j] at hj
  have H : (gZ (v j) : ℚ) = ((d : ℤ) : ℚ) * (c j : ℚ) := by
    simpa only [zsmul_eq_mul] using hj
  simp only [LinearMap.smul_apply, smul_eq_mul, mul_assoc]
  congr 1
  exact_mod_cast H

private lemma realFunctional_apply (f : X →ₗ[ℤ] ℤ) (x : X) :
    realFunctional f x = (f x : ℝ) := rfl

private lemma positive_coefficients (b : P.Base) {i : Idx} (hi : b.IsPos i) :
    ∃ c : b.support → ℤ, (∀ j, 0 ≤ c j) ∧
      (∃ j, 0 < c j) ∧ ∑ j, c j • P.root j.val = P.root i := by
  obtain ⟨d, -, hd, he⟩ := b.exists_root_eq_sum_int i
  have hp : 0 < d := by
    refine hd.resolve_right fun hn ↦ ?_
    rw [b.isPos_iff, b.height_eq_sum he] at hi
    exact not_lt_of_ge (Finset.sum_nonpos (fun j _ ↦ hn.le j)) hi
  refine ⟨fun j ↦ d j.val, fun j ↦ hp.le j.val, ?_, ?_⟩
  · by_contra! h
    have hz (j : b.support) : d j.val = 0 := le_antisymm (h j) (hp.le j.val)
    apply P.ne_zero i
    rw [he, ← Finset.sum_finset_coe]
    simp [hz]
  · exact (Finset.sum_finset_coe (fun j ↦ d j • P.root j) b.support).trans he.symm

private lemma chamber_description (f : X →ₗ[ℤ] ℤ) (b : P.Base)
    (hb : ∀ i, b.IsPos i ↔ i ∈ positive P f) :
    chamber P f = {x | ∀ i ∈ b.support, 0 < x (P.root i)} := by
  ext x
  constructor
  · exact fun hx i hi ↦ hx i ((hb i).mp (b.isPos_of_mem_support hi))
  · intro hx i hi
    obtain ⟨c, hc, ⟨j, hj⟩, he⟩ := positive_coefficients P b ((hb i).mpr hi)
    rw [← he, map_sum]
    apply Finset.sum_pos'
    · intro l _
      rw [map_smul, zsmul_eq_mul]
      exact mul_nonneg (by exact_mod_cast hc l) (le_of_lt (hx _ l.property))
    · refine ⟨j, Finset.mem_univ _, ?_⟩
      rw [map_smul, zsmul_eq_mul]
      exact mul_pos (by exact_mod_cast hj) (hx _ j.property)

private lemma closedChamber_description (f : X →ₗ[ℤ] ℤ) (b : P.Base)
    (hb : ∀ i, b.IsPos i ↔ i ∈ positive P f) :
    closedChamber P f = {x | ∀ i ∈ b.support, 0 ≤ x (P.root i)} := by
  ext x
  constructor
  · exact fun hx i hi ↦ hx i ((hb i).mp (b.isPos_of_mem_support hi))
  · intro hx i hi
    obtain ⟨c, hc, -, he⟩ := positive_coefficients P b ((hb i).mpr hi)
    rw [← he, map_sum]
    refine Finset.sum_nonneg fun j _ ↦ ?_
    rw [map_smul, zsmul_eq_mul]
    exact mul_nonneg (by exact_mod_cast hc j) (hx _ j.property)

private lemma integral_wall [Module.Free ℤ X] [Module.Finite ℤ X] [P.IsReduced]
    (f : X →ₗ[ℤ] ℤ) (b : P.Base) (hb : ∀ i, b.IsPos i ↔ i ∈ positive P f)
    (i : Idx) (h : i ∈ b.support) :
    ∃ g : X →ₗ[ℤ] ℤ, realFunctional g ∈ wallInterior P f i := by
  classical
  have hi := (hb i).mp (b.isPos_of_mem_support h)
  let j : b.support := ⟨i, h⟩
  obtain ⟨g, m, hm, hg⟩ := exists_integralValues
    (v := fun l : b.support ↦ P.root l.val) b.linearIndepOn_root (fun l ↦ if l = j then 0 else 1)
  have hgj : g (P.root i) = 0 := by simpa [j] using hg j
  refine ⟨g, ⟨by simp [realFunctional_apply, hgj], fun a ha hai ↦ ?_⟩⟩
  obtain ⟨c, hc, -, hs⟩ := positive_coefficients P b ((hb a).mpr ha)
  have hnonzero : ∃ l : b.support, l ≠ j ∧ 0 < c l := by
    by_contra! hnone
    have hc' : c = Pi.single j (c j) := by
      funext l
      by_cases hl : l = j
      · subst l; simp
      · simp [hl, le_antisymm (hnone l hl) (hc l)]
    rw [hc'] at hs
    have he : c j • P.root i = P.root a := by simpa [j, Pi.single_apply] using hs
    have hn : ¬ LinearIndependent ℤ ![P.root a, P.root i] := by
      rw [LinearIndependent.pair_iff]
      push Not
      refine ⟨1, -c j, ?_, by simp⟩
      simp [← he]
    rcases IsReduced.eq_or_eq_neg a i hn with he' | he'
    · exact hai (P.root.injective he')
    · have H : f (P.root a) = -f (P.root i) := by rw [he', map_neg]
      exact (not_lt_of_gt (show 0 < f (P.root a) from ha))
        (H ▸ neg_neg_of_pos (show 0 < f (P.root i) from hi))
  obtain ⟨l, hlj, hl⟩ := hnonzero
  rw [realFunctional_apply, Int.cast_pos, ← hs, map_sum]
  apply Finset.sum_pos'
  · intro r _
    rw [map_smul, smul_eq_mul, hg]
    exact mul_nonneg (hc r) (mul_nonneg hm.le (by split <;> simp))
  · refine ⟨l, Finset.mem_univ _, ?_⟩
    rw [map_smul, smul_eq_mul, hg, ite_eq_right hlj, mul_one]
    exact mul_pos hl hm

private lemma walls_description [Module.Free ℤ X] [Module.Finite ℤ X] [P.IsReduced]
    (f : X →ₗ[ℤ] ℤ) (b : P.Base) (hb : ∀ i, b.IsPos i ↔ i ∈ positive P f)
    (i : Idx) (hi : i ∈ positive P f) :
    i ∈ b.support ↔ (wallInterior P f i).Nonempty := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨g, hg⟩ := integral_wall P f b hb i h
    exact ⟨realFunctional g, hg⟩
  · rintro ⟨x, hx⟩
    by_contra h
    have hp : x ∈ chamber P f := by
      rw [chamber_description P f b hb]
      exact fun j hj ↦ hx.2 j ((hb j).mp (b.isPos_of_mem_support hj)) (fun e ↦ h (e ▸ hj))
    exact (ne_of_gt (hp i hi)) hx.1

end Geometry

section Separation

variable [P.IsReduced] (f : X →ₗ[ℤ] ℤ)

private lemma different_hyperplanes {i j : Idx}
    (hi : 0 < f (P.root i)) (hj : 0 < f (P.root j)) (hne : i ≠ j) :
    hyperplane P i ≠ hyperplane P j := by
  have hp : P.root i ≠ -P.root j := by
    intro he
    have H : f (P.root i) = -f (P.root j) := by rw [he, map_neg]
    omega
  have hli := independent_rational (IsReduced.linearIndependent P hne hp)
  obtain ⟨g, hg⟩ := rationalValues hli ![(0 : ℚ), 1]
  let q : X →ₗ[ℤ] ℚ := (g.restrictScalars ℤ).comp rationalize
  let x : X →ₗ[ℤ] ℝ := ((Rat.castHom ℝ).toAddMonoidHom.toIntLinearMap).comp q
  have hi' : g (rationalize (P.root i)) = 0 := hg 0
  have hj' : g (rationalize (P.root j)) = 1 := hg 1
  intro he
  have hxi : x ∈ hyperplane P i := by
    change ((g (rationalize (P.root i)) : ℚ) : ℝ) = 0
    simp [hi']
  have hxj := he ▸ hxi
  change ((g (rationalize (P.root j)) : ℚ) : ℝ) = 0 at hxj
  simp [hj'] at hxj

private lemma separating_count (w : P.weylGroup) :
    (separatingHyperplanes P (realFunctional f)
      ((realFunctional f).comp (w⁻¹).val.weightEquiv.toLinearMap)).ncard =
      (inversions P f w).ncard := by
  symm
  have heval (i : Idx) :
      ((realFunctional f).comp (w⁻¹).val.weightEquiv.toLinearMap) (P.root i) =
        (f (P.root (P.weylGroupToPerm w⁻¹ i)) : ℝ) := by
    change realFunctional f ((w⁻¹).val.weightEquiv (P.root i)) = _
    rw [realFunctional_apply]
    congr 1
    exact congrArg f (Hom.root_weightMap_apply P P i (w⁻¹).val.toHom)
  apply Set.ncard_congr (fun i _ ↦ hyperplane P i)
  · intro i hi
    refine ⟨i, rfl, ?_⟩
    rw [realFunctional_apply, heval]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hi.1) (by exact_mod_cast hi.2)
  · intro i j hi hj he
    by_contra hne
    exact different_hyperplanes P f hi.1 hj.1 hne he
  · rintro H ⟨i, rfl, hi⟩
    rw [realFunctional_apply, heval, mul_neg_iff] at hi
    rcases hi with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
    · exact ⟨i, ⟨by exact_mod_cast hpos, by exact_mod_cast hneg⟩, rfl⟩
    · refine ⟨P.reflectionPerm i i, ⟨?_, ?_⟩, ?_⟩
      · rw [root_reflectionPerm, reflection_apply_self, map_neg, neg_pos]
        exact_mod_cast hneg
      · change f (P.root (P.weylGroupToPerm w⁻¹ (P.reflectionPerm i i))) < 0
        rw [reflected_value, neg_neg_iff_pos]
        exact_mod_cast hpos
      · ext x
        change x (P.root (P.reflectionPerm i i)) = 0 ↔ x (P.root i) = 0
        rw [root_reflectionPerm, reflection_apply_self, map_neg, neg_eq_zero]

omit [P.IsReduced] in
private lemma inversion_set (w : P.weylGroup) :
    inversions P f w = positive P f ∩ (P.weylGroupToPerm w '' {i | f (P.root i) < 0}) := by
  ext i
  have he : P.weylGroupToPerm w⁻¹ = (P.weylGroupToPerm w).symm :=
    map_inv P.weylGroupToPerm w
  constructor
  · intro hi
    exact ⟨hi.1, P.weylGroupToPerm w⁻¹ i, hi.2, by rw [he, Equiv.apply_symm_apply]⟩
  · rintro ⟨hi, j, hj, rfl⟩
    refine ⟨hi, ?_⟩
    change f (P.root (P.weylGroupToPerm w⁻¹ (P.weylGroupToPerm w j))) < 0
    rwa [he, Equiv.symm_apply_apply]

end Separation

/-- Every regular positive system in a finite reduced integral root pairing
selects a base, with the simple-reflection length and wall formulas. -/
theorem baseFor [Finite Idx] [Module.Free ℤ X] [Module.Finite ℤ X]
    [P.IsReduced] (f : X →ₗ[ℤ] ℤ) (hf : ∀ i, f (P.root i) ≠ 0) :
    ∃ b : P.Base, IsBaseFor P f b := by
  let b := chosenBase P f hf
  have hs : b.support = simpleIndices P f := chosenBase_support P f hf
  have hp : ∀ i, b.IsPos i ↔ i ∈ positive P f := chosenBase_positive P f hf
  have hgen : Subgroup.closure (Set.range (fun i : b.support ↦ weylGroup.ofIdx P i.val)) = ⊤ :=
    chosenBase_generates P f hf
  refine ⟨b, ⟨?_, hp, independent_rational b.linearIndepOn_root, ?_, rationalSpan_iff P b,
    chamber_description P f b hp, closedChamber_description P f b hp, walls_description P f b hp,
    integral_wall P f b hp, ?_, hgen, inversion_set P f, length_eq_inversions P b f hf hp hgen, separating_count P f⟩⟩
  · intro i
    rw [hs]
    exact mem_simpleIndices P f i
  · intro i
    obtain ⟨c, hc, hsign, he⟩ := b.exists_root_eq_sum_int i
    exact ⟨c, hc, hsign.elim (fun h ↦ Or.inl h.le) (fun h ↦ Or.inr h.le), he⟩
  · intro i
    rw [hs]
    obtain ⟨w, j, _, he⟩ := simple_orbit P f hf i
    exact ⟨w, j, he⟩

/-- Conditional form using the full datum and scheme Weyl group identification. -/
theorem simpleRoots_conditional :
    Specs.DatumAndWeyl.Statement.{u} → Specs.SimpleRoots.Statement.{u} := by
  intro h k _ G hG T hT hmax
  obtain ⟨hcomm, D, ⟨e⟩⟩ := h G hG T hT hmax
  let := hcomm
  refine ⟨hcomm, D, e, fun cochar hregular ↦ ?_⟩
  let := D.finiteRoots
  let := D.freeCharacters
  let := D.finiteCharacters
  let := D.reduced
  have hregular' : ∀ i, evaluate D cochar (D.rootDatum.root i) ≠ 0 := by
    intro i
    change D.rootDatum.toLinearMap (D.rootDatum.root i) (Additive.ofMul cochar) ≠ 0
    rw [D.root_eq, D.pairing_eq]
    exact hregular i
  obtain ⟨b, hb⟩ := baseFor D.rootDatum (evaluate D cochar) hregular'
  refine ⟨b, hb, ?_, ?_⟩
  · intro i hi
    obtain ⟨g, hg⟩ := hb.integralWall i hi
    let c := D.rootDatum.toLinearMap.flip.toPerfPair.symm g
    refine ⟨Additive.toMul c, ?_⟩
    have he : evaluate D (Additive.toMul c) = g := by
      change D.rootDatum.toLinearMap.flip.toPerfPair c = g
      exact D.rootDatum.toLinearMap.flip.toPerfPair.apply_symm_apply g
    rwa [he]
  · intro w
    have htransport : evaluate D (cochar ≫ (e.image.conjugation (e.labelEquiv w)).hom) =
        (evaluate D cochar).comp (w⁻¹).val.weightEquiv.toLinearMap := by
      ext x
      change D.rootDatum.toLinearMap x
          (Additive.ofMul (cochar ≫ (e.image.conjugation (e.labelEquiv w)).hom)) =
        D.rootDatum.toLinearMap ((w⁻¹).val.weightEquiv x) (Additive.ofMul cochar)
      have he : (w⁻¹).val.coweightEquiv = w.val.coweightEquiv.symm :=
        RootPairing.Equiv.coweightEquiv_inv w.val
      rw [← e.cocharacterAction w cochar, ← he]
      exact ((w⁻¹).val.toLinearMap_weightEquiv x (Additive.ofMul cochar)).symm
    rw [htransport]
    exact (hb.length_eq w).trans (hb.separating_eq w).symm

end
end LinearAlgebraicGroups.RootData.SimpleRoots

universe v8_closure_4ffeee2a328e1bed_u0
theorem _root_.«LinearAlgebraicGroups».«RootData».«SimpleRoots».«simpleRoots» : _root_.«LinearAlgebraicGroups».«Specs».«SimpleRoots».«Statement».{v8_closure_4ffeee2a328e1bed_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«SimpleRoots».«simpleRoots_conditional».{v8_closure_4ffeee2a328e1bed_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«DatumAndWeyl».«datumAndWeyl».{v8_closure_4ffeee2a328e1bed_u0})
