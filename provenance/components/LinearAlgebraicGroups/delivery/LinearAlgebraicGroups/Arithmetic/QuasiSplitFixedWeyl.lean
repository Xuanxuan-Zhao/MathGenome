import Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
import LinearAlgebraicGroups.RootData.SimpleRoots
import LinearAlgebraicGroups.Relative.RelativeWeylScheme
import LinearAlgebraicGroups.Reductive.RadicalBaseChange
import LinearAlgebraicGroups.Classification.CentralIsogenies
import Batteries.Tactic.OpenPrivate

open Set RootPairing
open LinearAlgebraicGroups.Specs SimpleRoots
open LinearAlgebraicGroups.Specs.Arithmetic.QuasiSplitFixedWeyl

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

open private reflection_inverse reflected_value rightInversions rightInversions_card_mul
  length_inverse exists_shortest_word linearCombination_injective positive_coefficients from LinearAlgebraicGroups.RootData.SimpleRoots

universe u v w z

noncomputable section

variable {Idx : Type u} {X : Type v} {Y : Type w} [Finite Idx]
  [AddCommGroup X] [AddCommGroup Y] (P : RootPairing Idx ℤ X Y) [P.IsReduced]
  (f : X →ₗ[ℤ] ℤ) (hf : ∀ i, f (P.root i) ≠ 0) (b : P.Base)
  (hb : IsBaseFor P f b)

omit [Finite Idx] [P.IsReduced] in
include hb in
private theorem length_eq_rightInversions (a : P.weylGroup) :
    wordLength P b a = (rightInversions P f a).ncard := by
  rw [← length_inverse P b a, hb.length_eq]
  simp only [inversions, rightInversions, inv_inv]

include hb in
private theorem length_mul_of_pos (a : P.weylGroup) (j : b.support)
    (hj : 0 < f (P.root (P.weylGroupToPerm a j))) :
    wordLength P b (a * weylGroup.ofIdx P j) = wordLength P b a + 1 := by
  simp only [length_eq_rightInversions P f b hb]
  exact rightInversions_card_mul P b f hb.positive_iff a j hj

include hb in
private theorem length_mul_of_neg (a : P.weylGroup) (j : b.support)
    (hj : f (P.root (P.weylGroupToPerm a j)) < 0) :
    wordLength P b a = wordLength P b (a * weylGroup.ofIdx P j) + 1 := by
  have hpos : 0 < f (P.root (P.weylGroupToPerm (a * weylGroup.ofIdx P j) j)) := by
    rw [map_mul, Equiv.Perm.mul_apply]
    change 0 < f (P.root (P.weylGroupToPerm a (P.reflectionPerm j j)))
    rw [reflected_value]
    exact neg_pos.mpr hj
  have h := length_mul_of_pos P f b hb _ j hpos
  have hs : weylGroup.ofIdx P j.val * weylGroup.ofIdx P j.val = 1 :=
    mul_eq_one_iff_inv_eq.mpr (reflection_inverse P j)
  simpa only [mul_assoc, hs, mul_one] using h

omit [Finite Idx] [P.IsReduced] in
include hb in
private theorem eq_one_of_wordLength_zero {a : P.weylGroup} (h : wordLength P b a = 0) :
    a = 1 := by
  obtain ⟨l, hprod, hlen, -⟩ := exists_shortest_word P b hb.generates a
  have hnil := List.length_eq_zero_iff.mp (hlen.trans h)
  subst l
  exact hprod.symm

omit [Finite Idx] [P.IsReduced] in
private theorem supportedWord (I : Set Idx) (hI : I ⊆ b.support) (a : P.weylGroup)
    (ha : a ∈ parabolicWeyl P I) :
    ∃ l : List b.support, (∀ j ∈ l, (j : Idx) ∈ I) ∧ wordProduct P b l = a := by
  have hs (i : Idx) : (weylGroup.ofIdx P i)⁻¹ = weylGroup.ofIdx P i :=
    reflection_inverse P i
  have ha' : a ∈ Submonoid.closure (weylGroup.ofIdx P '' I) := by
    change a ∈ (parabolicWeyl P I).toSubmonoid at ha
    rwa [parabolicWeyl, Subgroup.closure_toSubmonoid,
      show (weylGroup.ofIdx P '' I)⁻¹ = weylGroup.ofIdx P '' I by
        ext x
        change x⁻¹ ∈ weylGroup.ofIdx P '' I ↔ x ∈ weylGroup.ofIdx P '' I
        constructor
        · rintro ⟨i, hi, he⟩
          exact ⟨i, hi, by rw [← inv_inv x, ← he, hs]⟩
        · rintro ⟨i, hi, rfl⟩
          exact ⟨i, hi, (hs i).symm⟩, union_self] at ha
  clear ha
  induction ha' using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    exact ⟨[⟨j, hI hj⟩], by simp [hj], by simp [wordProduct]⟩
  | one => exact ⟨[], by simp, rfl⟩
  | mul a c _ _ ha hc =>
    obtain ⟨l, hl, rfl⟩ := ha
    obtain ⟨r, hr, rfl⟩ := hc
    refine ⟨l ++ r, ?_, by simp [wordProduct]⟩
    intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact hl j hj
    · exact hr j hj


omit [Finite Idx] [P.IsReduced] in
private theorem supportedCoefficients {I : Set Idx} (hI : I ⊆ b.support) {i : Idx}
    (hi : b.IsPos i) (hspan : P.root i ∈ Submodule.span ℤ (P.root '' I)) :
    ∃ c : b.support → ℤ, (∀ j, 0 ≤ c j) ∧ (∃ j, 0 < c j) ∧
      (∀ j, j.val ∉ I → c j = 0) ∧ ∑ j, c j • P.root j.val = P.root i := by
  classical
  obtain ⟨c, hc, hcpos, he⟩ := positive_coefficients P b hi
  obtain ⟨J, hJ, d, hd⟩ := (Submodule.mem_span_image_iff_exists_fun (R := ℤ) (v := P.root)).mp hspan
  let d' (j : Idx) := if h : j ∈ J then d ⟨j, h⟩ else 0
  have hJb : J ⊆ b.support := fun _ hj ↦ hI (hJ hj)
  have hd' : ∑ j : b.support, d' j.val • P.root j.val = P.root i := by
    calc
      _ = ∑ j ∈ b.support, d' j • P.root j :=
        Finset.sum_coe_sort b.support (fun j ↦ d' j • P.root j)
      _ = ∑ j ∈ J, d' j • P.root j :=
        (Finset.sum_subset hJb (fun j _ hj ↦ by simp [d', hj])).symm
      _ = P.root i := by
        rw [← Finset.sum_coe_sort, ← hd]
        exact Finset.sum_congr rfl fun j _ ↦ by simp [d', j.property]
  have hcd := linearCombination_injective P b.linearIndepOn_root (he.trans hd'.symm)
  refine ⟨c, hc, hcpos, ?_, he⟩
  intro j hj
  rw [show c j = d' j.val from congrFun hcd j]
  exact dite_eq_right (fun he ↦ hj (hJ he))

omit [Finite Idx] [P.IsReduced] in
private theorem positive_of_simple_images (g : X →ₗ[ℤ] ℤ) {I : Set Idx}
    (hI : I ⊆ b.support) {i : Idx} (hi : b.IsPos i)
    (hspan : P.root i ∈ Submodule.span ℤ (P.root '' I))
    (hg : ∀ j ∈ I, 0 < g (P.root j)) : 0 < g (P.root i) := by
  classical
  obtain ⟨c, hc, ⟨j, hj⟩, hz, he⟩ := supportedCoefficients P b hI hi hspan
  have hji : j.val ∈ I := by
    by_contra hn
    exact hj.ne' (hz j hn)
  rw [← he]
  simp only [map_sum, map_smul, zsmul_eq_mul]
  refine Finset.sum_pos' (fun l _ ↦ ?_) ⟨j, Finset.mem_univ j, ?_⟩
  · by_cases hl : l.val ∈ I
    · exact mul_nonneg (hc l) (hg l.val hl).le
    · simp [hz l hl]
  · exact mul_pos hj (hg j.val hji)

omit [Finite Idx] [P.IsReduced] in
include hb in
private theorem sign_of_simple_images (w : P.weylGroup) {I : Set Idx}
    (hI : I ⊆ b.support) {i : Idx} (hi : 0 < f (P.root i))
    (hspan : P.root i ∈ Submodule.span ℤ (P.root '' I)) (ε : ℤ)
    (hw : ∀ j ∈ I, 0 < ε * f (P.root (P.weylGroupToPerm w j))) :
    0 < ε * f (P.root (P.weylGroupToPerm w i)) := by
  let g := ε • (f.comp w.val.weightEquiv.toLinearMap)
  have he (j : Idx) : g (P.root j) = ε * f (P.root (P.weylGroupToPerm w j)) := by
    rw [← P.weylGroup_apply_root]
    rfl
  rw [← he]
  apply positive_of_simple_images P b g hI ((hb.positive_iff i).mpr hi) hspan
  intro j hj
  rw [he]
  exact hw j hj

omit [Finite Idx] [P.IsReduced] in
private theorem parabolic_span_preserved {I : Set Idx} (w : P.weylGroup)
    (hw : w ∈ parabolicWeyl P I) :
    ∀ x ∈ Submodule.span ℤ (P.root '' I),
      w • x ∈ Submodule.span ℤ (P.root '' I) := by
  suffices h : ∀ x ∈ Submodule.span ℤ (P.root '' I),
      w • x ∈ Submodule.span ℤ (P.root '' I) ∧ w⁻¹ • x ∈ Submodule.span ℤ (P.root '' I) by
    exact fun x hx ↦ (h x hx).1
  induction hw using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    intro x hx
    rw [reflection_inverse]
    suffices h : weylGroup.ofIdx P j • x ∈ Submodule.span ℤ (P.root '' I) from ⟨h, h⟩
    change P.reflection j x ∈ _
    rw [reflection_apply]
    exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _
      (Submodule.subset_span (mem_image_of_mem _ hj)))
  | one => simp
  | mul a c _ _ ha hc =>
    intro x hx
    rw [mul_inv_rev, mul_smul, mul_smul]
    exact ⟨(ha _ (hc _ hx).1).1, (hc _ (ha _ hx).2).2⟩
  | inv a _ ha =>
    intro x hx
    rw [inv_inv]
    exact (ha x hx).symm

include hf hb in
private theorem length_add_of_descents {w : P.weylGroup} {I : Set Idx} (hI : I ⊆ b.support)
    (hw : ∀ j ∈ I, f (P.root (P.weylGroupToPerm w j)) < 0) {a : P.weylGroup}
    (ha : a ∈ parabolicWeyl P I) :
    wordLength P b (w * a) + wordLength P b a = wordLength P b w := by
  classical
  obtain ⟨l, hl, rfl⟩ := supportedWord P b I hI a ha
  clear ha
  induction l using List.reverseRecOn with
  | nil =>
    have hone : wordLength P b 1 = 0 := by
      rw [length_eq_rightInversions P f b hb]
      have hempty : rightInversions P f 1 = ∅ := by
        ext i
        simp only [rightInversions, mem_ofPred_eq, map_one, Equiv.Perm.one_apply,
          notMem_empty, iff_false]
        exact fun h ↦ (not_lt_of_gt h.1) h.2
      simp [hempty]
    simp [wordProduct, hone]
  | append_singleton l j ih =>
    have hj : j.val ∈ I := hl j (by simp)
    have hl' : ∀ k ∈ l, (k : Idx) ∈ I := fun k hk ↦ hl k (by simp [hk])
    have hmem : wordProduct P b l ∈ parabolicWeyl P I := by
      unfold wordProduct
      apply Subgroup.list_prod_mem
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      exact Subgroup.subset_closure ⟨k.val, hl' k hk, rfl⟩
    let v := wordProduct P b l
    have hspan : P.root (P.weylGroupToPerm v j) ∈ Submodule.span ℤ (P.root '' I) := by
      rw [← P.weylGroup_apply_root]
      exact parabolic_span_preserved P v hmem _ (Submodule.subset_span (mem_image_of_mem _ hj))
    have hdiff (i : Idx) : f (P.root (P.reflectionPerm i i)) = -f (P.root i) := by
      rw [root_reflectionPerm, reflection_apply_self, map_neg]
    have hflip : (0 < f (P.root (P.weylGroupToPerm v j)) →
        f (P.root (P.weylGroupToPerm (w * v) j)) < 0) := by
      intro hp
      have h := sign_of_simple_images P f b hb w hI hp hspan (-1) (by simpa using hw)
      simpa only [map_mul, Equiv.Perm.mul_apply, neg_one_mul, neg_pos] using h
    have hflip' : (f (P.root (P.weylGroupToPerm v j)) < 0 →
        0 < f (P.root (P.weylGroupToPerm (w * v) j))) := by
      intro hn
      let i := P.weylGroupToPerm v j
      have hnegspan : P.root (P.reflectionPerm i i) ∈ Submodule.span ℤ (P.root '' I) := by
        rw [root_reflectionPerm, reflection_apply_self]
        exact Submodule.neg_mem _ hspan
      have hp : 0 < f (P.root (P.reflectionPerm i i)) := by rw [hdiff]; exact neg_pos.mpr hn
      have h := sign_of_simple_images P f b hb w hI hp hnegspan (-1) (by simpa using hw)
      rw [neg_one_mul, reflected_value, neg_neg] at h
      simpa only [i, map_mul, Equiv.Perm.mul_apply] using h
    have ih' : wordLength P b (w * v) + wordLength P b v = wordLength P b w := ih hl'
    rw [show wordProduct P b (l ++ [j]) = v * weylGroup.ofIdx P j from by simp [v, wordProduct]]
    rw [← mul_assoc]
    rcases lt_or_gt_of_ne (hf (P.weylGroupToPerm v j)) with hn | hp
    · have h₁ := length_mul_of_neg P f b hb v j hn
      have h₂ := length_mul_of_pos P f b hb (w * v) j (hflip' hn)
      omega
    · have h₁ := length_mul_of_pos P f b hb v j hp
      have h₂ := length_mul_of_neg P f b hb (w * v) j (hflip hp)
      omega


include hf hb in
private theorem longest_descents {I : Set Idx} (hI : I ⊆ b.support) {a : P.weylGroup}
    (ha : IsLongest P b I a) :
    ∀ j ∈ I, f (P.root (P.weylGroupToPerm a j)) < 0 := by
  intro j hj
  rcases lt_or_gt_of_ne (hf (P.weylGroupToPerm a j)) with hn | hp
  · exact hn
  · have hmem : weylGroup.ofIdx P j ∈ parabolicWeyl P I :=
      Subgroup.subset_closure (mem_image_of_mem _ hj)
    have hmax := ha.2 _ (mul_mem ha.1 hmem)
    have hlen := length_mul_of_pos P f b hb a ⟨j, hI hj⟩ hp
    change wordLength P b (a * weylGroup.ofIdx P j) = wordLength P b a + 1 at hlen
    omega

include hf hb in
private theorem longest_unique {I : Set Idx} (hI : I ⊆ b.support) {a c : P.weylGroup}
    (ha : IsLongest P b I a) (hc : IsLongest P b I c) : c = a := by
  have hlen : wordLength P b c = wordLength P b a :=
    le_antisymm (ha.2 _ hc.1) (hc.2 _ ha.1)
  have hca := length_add_of_descents P f hf b hb hI (longest_descents P f hf b hb hI hc) ha.1
  have haa := length_add_of_descents P f hf b hb hI (longest_descents P f hf b hb hI ha) ha.1
  have h₁ : c * a = 1 := eq_one_of_wordLength_zero P f b hb (by omega)
  have h₂ : a * a = 1 := eq_one_of_wordLength_zero P f b hb (by omega)
  exact mul_right_cancel (h₁.trans h₂.symm)

omit [P.IsReduced] in
include hb in
private theorem exists_longest (I : Set Idx) : ∃ a, IsLongest P b I a := by
  classical
  let L := wordLength P b '' (parabolicWeyl P I : Set P.weylGroup)
  have hL : L.Finite := (Set.finite_Iic (Nat.card Idx)).subset (by
    rintro n ⟨a, _, rfl⟩
    rw [Set.mem_Iic, length_eq_rightInversions P f b hb]
    simpa using Set.ncard_le_ncard (Set.subset_univ (rightInversions P f a)))
  have hne : hL.toFinset.Nonempty := ⟨wordLength P b 1, hL.mem_toFinset.mpr ⟨1, one_mem _, rfl⟩⟩
  obtain ⟨n, hn, hmax⟩ := hL.toFinset.exists_max_image id hne
  obtain ⟨a, ha, rfl⟩ := hL.mem_toFinset.mp hn
  exact ⟨a, ha, fun x hx ↦ hmax _ (hL.mem_toFinset.mpr ⟨x, hx, rfl⟩)⟩

theorem longestElements : LongestElements.{u,v,w} := by
  intro Idx X Y _ _ _ P _ f hf b hb I hI
  obtain ⟨a, ha⟩ := exists_longest P f b hb I
  exact ⟨a, ha, fun c hc ↦ longest_unique P f hf b hb hI ha hc⟩

omit [Finite Idx] [P.IsReduced] in
include hf hb in
private theorem exists_simple_descent {a : P.weylGroup} (ha : a ≠ 1) :
    ∃ j ∈ b.support, f (P.root (P.weylGroupToPerm a j)) < 0 := by
  by_contra! hn
  have hp (i : Idx) (hi : 0 < f (P.root i)) :
      0 < f (P.root (P.weylGroupToPerm a i)) := by
    have h := sign_of_simple_images P f b hb a (subset_refl (b.support : Set Idx)) hi
      (b.root_mem_span_int i) 1 (fun j hj ↦ by
        rw [one_mul]
        exact lt_of_le_of_ne (hn j hj) (Ne.symm (hf _)))
    simpa only [one_mul] using h
  have he : rightInversions P f a = ∅ := by
    ext i
    simp only [rightInversions, mem_ofPred_eq, notMem_empty, iff_false]
    exact fun h ↦ (not_lt_of_gt (hp i h.1)) h.2
  exact ha (eq_one_of_wordLength_zero P f b hb (by rw [length_eq_rightInversions P f b hb, he]; simp))


omit [Finite Idx] [P.IsReduced] in
private theorem reflection_conjugation (d : P.Aut) (i : Idx) :
    RootPairing.Equiv.reflection P (d.indexEquiv i) =
      d * RootPairing.Equiv.reflection P i * d⁻¹ := by
  apply RootPairing.Equiv.weightHom_injective P
  ext x
  simp only [map_mul, map_inv, LinearEquiv.mul_apply]
  change P.reflection (d.indexEquiv i) x = d.weightEquiv (P.reflection i (d.weightEquiv.symm x))
  rw [d.weightEquiv_reflection, LinearEquiv.apply_symm_apply]

omit [Finite Idx] [P.IsReduced] in
private theorem conjugation_mem (d : P.Aut) {a : P.Aut} (ha : a ∈ P.weylGroup) :
    d * a * d⁻¹ ∈ P.weylGroup := by
  induction ha using RootPairing.weylGroup.induction with
  | mem i =>
    rw [← reflection_conjugation P d i]
    exact P.reflection_mem_weylGroup _
  | one => simp
  | mul a c _ _ ha hc =>
    convert P.weylGroup.mul_mem ha hc using 1
    group

omit [Finite Idx] [P.IsReduced] in
private def conjugation (d : P.Aut) : MulAut P.weylGroup where
  toFun a := ⟨d * a.val * d⁻¹, conjugation_mem P d a.property⟩
  invFun a := ⟨d⁻¹ * a.val * d⁻¹⁻¹, conjugation_mem P d⁻¹ a.property⟩
  left_inv a := by
    apply Subtype.ext
    change d⁻¹ * (d * a.val * d⁻¹) * d⁻¹⁻¹ = a.val
    rw [inv_inv]
    exact (MulAut.conj d).symm_apply_apply a.val
  right_inv a := by
    apply Subtype.ext
    change d * (d⁻¹ * a.val * d⁻¹⁻¹) * d⁻¹ = a.val
    rw [inv_inv]
    exact (MulAut.conj d).apply_symm_apply a.val
  map_mul' a c := Subtype.ext ((MulAut.conj d).map_mul a.val c.val)

omit [Finite Idx] [P.IsReduced] in
private theorem conjugation_reflection (d : P.Aut) (j : Idx) :
    conjugation P d (weylGroup.ofIdx P j) = weylGroup.ofIdx P (d.indexEquiv j) :=
  Subtype.ext (reflection_conjugation P d j).symm

omit [Finite Idx] [P.IsReduced] in
private theorem index_inv (d : P.Aut) (j : Idx) :
    (d⁻¹).indexEquiv (d.indexEquiv j) = j := by
  change (RootPairing.Equiv.indexHom P d⁻¹ * RootPairing.Equiv.indexHom P d) j = (1 : Equiv.Perm Idx) j
  rw [← map_mul, inv_mul_cancel, map_one]

omit [Finite Idx] [P.IsReduced] in
private theorem conjugation_symm (d : P.Aut) : (conjugation P d).symm = conjugation P d⁻¹ := by
  apply MulEquiv.ext
  intro a
  rfl

omit [Finite Idx] [P.IsReduced] in
include hb in
private theorem length_conjugation_le (d : P.Aut)
    (hd : ∀ j ∈ b.support, d.indexEquiv j ∈ b.support) (a : P.weylGroup) :
    wordLength P b (conjugation P d a) ≤ wordLength P b a := by
  obtain ⟨l, hl, hlen, -⟩ := exists_shortest_word P b hb.generates a
  let g (j : b.support) : b.support := ⟨d.indexEquiv j, hd j j.property⟩
  have he (l : List b.support) : wordProduct P b (l.map g) = conjugation P d (wordProduct P b l) := by
    induction l with
    | nil => simp [wordProduct]
    | cons j l ih =>
      simp only [List.map_cons, wordProduct, List.prod_cons, map_mul] at ih ⊢
      rw [ih, conjugation_reflection]
  rw [← hlen]
  exact csInf_le' ⟨l.map g, List.length_map g, (he l).trans (congrArg (conjugation P d) hl)⟩

omit [Finite Idx] [P.IsReduced] in
include hb in
private theorem length_conjugation (d : P.Aut)
    (hd : ∀ j, d.indexEquiv j ∈ b.support ↔ j ∈ b.support) (a : P.weylGroup) :
    wordLength P b (conjugation P d a) = wordLength P b a := by
  apply le_antisymm (length_conjugation_le P f b hb d (fun j hj ↦ (hd j).mpr hj) a)
  have h := length_conjugation_le P f b hb d⁻¹ (fun j hj ↦
    (hd _).mp (by simpa only [inv_inv] using (index_inv P d⁻¹ j).symm ▸ hj)) (conjugation P d a)
  rwa [← conjugation_symm, MulEquiv.symm_apply_apply] at h

omit [Finite Idx] [P.IsReduced] in
private theorem parabolic_conjugation (d : P.Aut) (I : Set Idx)
    (hI : ∀ j ∈ I, d.indexEquiv j ∈ I) {a : P.weylGroup} (ha : a ∈ parabolicWeyl P I) :
    conjugation P d a ∈ parabolicWeyl P I := by
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    rw [conjugation_reflection]
    exact Subgroup.subset_closure (mem_image_of_mem _ (hI j hj))
  | one => simp
  | mul a c _ _ ha hc => rw [map_mul]; exact mul_mem ha hc
  | inv a _ ha => rw [map_inv]; exact inv_mem ha

omit [Finite Idx] [P.IsReduced] in
private theorem index_mul (d e : P.Aut) (j : Idx) :
    (d * e).indexEquiv j = d.indexEquiv (e.indexEquiv j) := by
  change RootPairing.Equiv.indexHom P (d * e) j =
    RootPairing.Equiv.indexHom P d (RootPairing.Equiv.indexHom P e j)
  rw [map_mul, Equiv.Perm.mul_apply]

variable {Γ : Type z} [Group Γ] (ρ : Γ →* P.Aut)

omit [Finite Idx] [P.IsReduced] in
private theorem orbit_mem (j : Idx) : j ∈ rootOrbit P ρ j :=
  ⟨1, by change (ρ 1).indexEquiv j = j; rw [map_one]; rfl⟩

omit [Finite Idx] [P.IsReduced] in
private theorem orbit_stable (j : Idx) (γ : Γ) :
    ∀ i ∈ rootOrbit P ρ j, (ρ γ).indexEquiv i ∈ rootOrbit P ρ j := by
  rintro i ⟨δ, rfl⟩
  exact ⟨γ * δ, by change (ρ (γ * δ)).indexEquiv j = _; rw [map_mul, index_mul]⟩

include hf hb in
private theorem longest_orbit_fixed
    (hρ : ∀ γ i, (ρ γ).indexEquiv i ∈ b.support ↔ i ∈ b.support)
    {j : Idx} (hj : j ∈ b.support) {a : P.weylGroup}
    (ha : IsLongest P b (rootOrbit P ρ j) a) : a ∈ fixedWeyl P ρ := by
  have hI : rootOrbit P ρ j ⊆ b.support := by
    rintro i ⟨γ, rfl⟩
    exact (hρ γ j).mpr hj
  intro γ
  let d := ρ γ
  have hlong : IsLongest P b (rootOrbit P ρ j) (conjugation P d a) := by
    refine ⟨parabolic_conjugation P d _ (orbit_stable P ρ j γ) ha.1, ?_⟩
    intro x hx
    have hs : ∀ i ∈ rootOrbit P ρ j, (d⁻¹).indexEquiv i ∈ rootOrbit P ρ j := by
      simpa only [d, map_inv] using orbit_stable P ρ j γ⁻¹
    have hx' := parabolic_conjugation P d⁻¹ _ hs hx
    have h := ha.2 _ hx'
    rw [length_conjugation P f b hb d⁻¹ (by simpa only [d, map_inv] using hρ γ⁻¹)] at h
    simpa only [length_conjugation P f b hb d (hρ γ)] using h
  have hEq := congrArg Subtype.val (longest_unique P f hf b hb hI ha hlong)
  change d * a.val = a.val * d
  have h := congrArg (· * d) hEq
  change (d * a.val * d⁻¹) * d = a.val * d at h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h


omit [Finite Idx] [P.IsReduced] in
include hb in
private theorem positive_under_based (d : P.Aut)
    (hd : ∀ j ∈ b.support, d.indexEquiv j ∈ b.support)
    {i : Idx} (hi : 0 < f (P.root i)) : 0 < f (P.root (d.indexEquiv i)) := by
  let g := f.comp d.weightEquiv.toLinearMap
  have he (j : Idx) : g (P.root j) = f (P.root (d.indexEquiv j)) := by
    rw [RootPairing.Equiv.root_indexEquiv_eq_smul]
    rfl
  rw [← he]
  refine positive_of_simple_images P b g (subset_refl (b.support : Set Idx))
    ((hb.positive_iff i).mpr hi) (b.root_mem_span_int i) ?_
  intro j hj
  rw [he]
  exact (hb.positive_iff _).mp (b.isPos_of_mem_support (hd j hj))

omit [Finite Idx] [P.IsReduced] in
include hf hb in
private theorem negative_under_based (d : P.Aut)
    (hd : ∀ j, d.indexEquiv j ∈ b.support ↔ j ∈ b.support)
    {i : Idx} (hi : f (P.root i) < 0) : f (P.root (d.indexEquiv i)) < 0 := by
  rcases lt_or_gt_of_ne (hf (d.indexEquiv i)) with hn | hp
  · exact hn
  · have hdinv (j : Idx) (hj : j ∈ b.support) : (d⁻¹).indexEquiv j ∈ b.support := by
      apply (hd _).mp
      simpa only [inv_inv] using (index_inv P d⁻¹ j).symm ▸ hj
    have h := positive_under_based P f b hb d⁻¹ hdinv hp
    rw [index_inv] at h
    exact ((not_lt_of_gt h) hi).elim

omit [Finite Idx] [P.IsReduced] in
include hf hb in
private theorem fixed_orbit_descents
    (hρ : ∀ γ i, (ρ γ).indexEquiv i ∈ b.support ↔ i ∈ b.support)
    {a : P.weylGroup} (ha : a ∈ fixedWeyl P ρ) {j : Idx}
    (hj : f (P.root (P.weylGroupToPerm a j)) < 0) :
    ∀ i ∈ rootOrbit P ρ j, f (P.root (P.weylGroupToPerm a i)) < 0 := by
  rintro i ⟨γ, rfl⟩
  have hc : (ρ γ) * a.val = a.val * (ρ γ) := ha γ
  have he := congrArg (fun v : P.Aut ↦ v.indexEquiv j) hc
  simp only [index_mul] at he
  change (ρ γ).indexEquiv (P.weylGroupToPerm a j) =
    P.weylGroupToPerm a ((ρ γ).indexEquiv j) at he
  rw [← he]
  exact negative_under_based P f hf b hb (ρ γ) (hρ γ) hj

theorem orbitGeneration : OrbitGeneration.{u,v,w,z} := by
  intro Idx X Y Γ _ _ _ _ P _ f hf b hb ρ hρ
  let C := Subgroup.closure {a | ∃ i ∈ b.support, IsLongest P b (rootOrbit P ρ i) a}
  have hC : C ≤ fixedWeyl P ρ :=
    (Subgroup.closure_le _).mpr (fun a ⟨i, hi, ha⟩ ↦ longest_orbit_fixed P f hf b hb ρ hρ hi ha)
  apply le_antisymm hC
  intro w
  induction w using (measure (wordLength P b)).wf.induction with
  | h w ih =>
    intro hw
    by_cases h : w = 1
    · subst w
      exact one_mem C
    obtain ⟨j, hj, hdescent⟩ := exists_simple_descent P f hf b hb h
    let I := rootOrbit P ρ j
    have hI : I ⊆ b.support := by
      rintro i ⟨γ, rfl⟩
      exact (hρ γ j).mpr hj
    obtain ⟨a, ha⟩ := exists_longest P f b hb I
    have haC : a ∈ C := Subgroup.subset_closure ⟨j, hj, ha⟩
    have hlen := length_add_of_descents P f hf b hb hI
      (fixed_orbit_descents P f hf b hb ρ hρ hw hdescent) ha.1
    have hne : wordLength P b a ≠ 0 := by
      intro hzero
      have hneg := longest_descents P f hf b hb hI ha j (orbit_mem P ρ j)
      rw [eq_one_of_wordLength_zero P f b hb hzero, map_one, Equiv.Perm.one_apply] at hneg
      exact (not_lt_of_gt ((hb.positive_iff j).mp (b.isPos_of_mem_support hj))) hneg
    have hlt : (measure (wordLength P b)).rel (w * a) w := by
      change wordLength P b (w * a) < wordLength P b w
      omega
    have hwa := ih (w * a) hlt ((fixedWeyl P ρ).mul_mem hw (hC haC))
    simpa using C.mul_mem hwa (C.inv_mem haC)

end
end LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

open AlgebraicGeometry CategoryTheory
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open private kBorel_smooth_connected from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private extendSubgroup subgroup_extend subgroup_descend
  from LinearAlgebraicGroups.RootData.BorelNormalizer

theorem borelIsMinimalParabolic : BorelIsMinimalParabolic.{u} := by
  intro F _ G hG B hB
  let K := AlgebraicClosure F
  have hBk : Specs.GeometricBorelConjugacy.IsBorel (extendSubgroup K B) := hB.choose_spec
  have hs : Smooth B.group.X.hom := (kBorel_smooth_connected G B hB).1
  refine ⟨⟨hG, hs, (extendSubgroup K B).isClosedImmersion,
    extendSubgroup K B, hBk, ⟨𝟙 _, Category.id_comp _⟩⟩, ?_⟩
  intro P hP hPB
  obtain ⟨_, A, hA, hAP⟩ := hP.2.2
  have hPB' := subgroup_extend K hPB
  obtain ⟨f, hf⟩ := hAP
  obtain ⟨g, hg⟩ := hPB'
  have hAB : IsSubgroupOf A (extendSubgroup K B) :=
    ⟨f ≫ g, by rw [Category.assoc, hg, hf]⟩
  obtain ⟨r, hr⟩ := hA.2 _ hBk.1 hAB
  exact subgroup_descend K ⟨r ≫ f, by rw [Category.assoc, hf, hr]⟩

open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

set_option linter.style.haveILetI false
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive IsTorus IsMaximalTorus IsSplitTorus identitySubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open private maximalSplitTorusAbove from LinearAlgebraicGroups.Relative.RelativeWeylScheme
open private splitTorusUpperBound splitTorusImage from LinearAlgebraicGroups.Relative.MaximalSplitTori
open private trivial_isSplitTorus isTorus_of_split from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private torus_baseChange_algClosure from LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private torus_commutative from LinearAlgebraicGroups.Reductive.TorusFreeUnipotent
open private subgroupOf_trans factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers

theorem largestSplitSubtorusExists : LargestSplitSubtorusExists.{u} := by
  intro F _ T hT
  obtain ⟨S, hS, _⟩ := maximalSplitTorusAbove T (identitySubgroup T) trivial_isSplitTorus
  refine ⟨S, hS.1, fun A hA ↦ ?_⟩
  letI := torus_commutative T hT
  obtain ⟨H, hH, hSH, hAH⟩ := splitTorusUpperBound T S A hS.1 hA (fun X a b ↦ by
    letI : CommMonoid (X ⟶ T.val.X) := Hom.commMonoid
    exact Commute.all _ _)
  exact subgroupOf_trans hAH (hS.2 H hH hSH)

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F}

set_option backward.isDefEq.respectTransparency false in
private theorem torusSectionsCentralize {T : ClosedSubgroup G.val} (hT : IsTorus T.group)
    {A : GroupScheme F} (i : A ⟶ T.group) {Y : SchemeOver F} (g : Y ⟶ T.group.X) :
    Centralizes (i ≫ T.inclusion) (g ≫ T.inclusion.hom.hom) := by
  apply (centralizes_iff _ _).mpr
  intro X x a
  letI : IsCommMonObj T.group.X := torus_commutative (closedSubgroupAlgebraicGroup T) hT
  letI : CommMonoid (X ⟶ T.group.X) := Hom.commMonoid
  have hc := (Commute.all (x ≫ g) (a ≫ i.hom.hom)).map
    (IsMonHom.monoidHom T.inclusion.hom.hom X)
  change Commute ((x ≫ g) ≫ T.inclusion.hom.hom)
    ((a ≫ i.hom.hom) ≫ T.inclusion.hom.hom) at hc
  change Commute (x ≫ g ≫ T.inclusion.hom.hom) (a ≫ i.hom.hom ≫ T.inclusion.hom.hom)
  simpa only [Category.assoc] using hc

open private restrictSubgroup compose_restrict local_maximal_of_ambient
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private isKBorel_iff_of_isAlgClosed geometricMaximal_of_maximal split_of_maximal
  from LinearAlgebraicGroups.RootData.BorelNormalizer
open private reductive_geometricGroup centralizer_of_regular pairing_inv centralizer_of_cast
  from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private multiplicativeBaseChange multiplicativeBaseChange_unit extendCocharacter
  limitParabolic_signs_of_same limitParabolic_transport from LinearAlgebraicGroups.Relative.RationalCocharacter
open private limits_subgroups_extend same_subgroup_trans same_subgroup_symm
  from LinearAlgebraicGroups.RootData.RankOneFlag

open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (absoluteRoots pairing)
open Specs.BorelsAndChambers (IsRegular)
open Specs.GeometricRadicals (GeometricGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition existsLimitDecomposition)

set_option backward.isDefEq.respectTransparency false in
private theorem maximalInBorel {B T : ClosedSubgroup G.val}
    (hTm : IsGeometricallyMaximal T) (hT : IsTorus T.group)
    (i : T.group ⟶ B.group) (hi : i ≫ B.inclusion = T.inclusion) :
    IsMaximalTorus (restrictSubgroup T B i hi) := by
  refine local_maximal_of_ambient B _ ?_
  rw [compose_restrict T B i hi]
  refine ⟨hT, fun R hR hTR ↦ subgroup_descend (AlgebraicClosure F)
    (hTm.choose_spec.2 _ ?_ (subgroup_extend (AlgebraicClosure F) hTR))⟩
  exact torus_baseChange_algClosure (closedSubgroupAlgebraicGroup R) hR

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem borelDefiningCocharacter :
    ∀ {F : Type u} [Field F] (G : AffineAlgebraicGroup F), IsReductive G →
      ∀ (B T : ClosedSubgroup G.val), IsKBorel B → IsTorus T.group →
        IsGeometricallyMaximal T → IsSubgroupOf T B →
        ∃ (c : Cocharacter T.group) (D : LimitDecomposition (c ≫ T.inclusion)),
          SameSubgroup B D.parabolic ∧
            RepresentsSubgroup T (fun _ g ↦ Centralizes (c ≫ T.inclusion) g) := by
  intro F _ G hG B T hB hT hTm ⟨i, hi⟩
  let K := AlgebraicClosure F
  let H := GeometricGroup G
  let Tk := extendSubgroup K T
  let Bk := extendSubgroup K B
  have hPk := borelIsMinimalParabolic G hG B hB
  obtain ⟨c, D₀, hBD₀, _, _⟩ :=
    LinearAlgebraicGroups.Relative.RationalCocharacter.rationalParabolicThroughTorus G B hPk.1
      (restrictSubgroup T B i hi) (maximalInBorel hTm hT i hi)
  have hC : c ≫ (subgroupOfSubgroup B (restrictSubgroup T B i hi)).inclusion =
      (show Cocharacter T.group from c) ≫ T.inclusion := by
    change c ≫ (i ≫ B.inclusion) = c ≫ T.inclusion
    rw [hi]
  let D : LimitDecomposition ((show Cocharacter T.group from c) ≫ T.inclusion) := hC ▸ D₀
  have hBD : SameSubgroup B D.parabolic := by
    change SameSubgroup B (hC ▸ D₀ :
      LimitDecomposition ((show Cocharacter T.group from c) ≫ T.inclusion)).parabolic
    rw [limitParabolic_transport hC D₀]
    exact hBD₀
  let C : Cocharacter T.group := c
  let Ck : Cocharacter Tk.group := extendCocharacter K C
  have he : extendCocharacter K (C ≫ T.inclusion) = Ck ≫ Tk.inclusion := by
    change (multiplicativeBaseChange F K).hom ≫ (groupBaseChange F K).map (C ≫ T.inclusion) =
      ((multiplicativeBaseChange F K).hom ≫ (groupBaseChange F K).map C) ≫
        (groupBaseChange F K).map T.inclusion
    rw [Functor.map_comp, Category.assoc]
  obtain ⟨E₀⟩ := existsLimitDecomposition H (extendCocharacter K (C ≫ T.inclusion))
  let E : LimitDecomposition (Ck ≫ Tk.inclusion) := he ▸ E₀
  have hE : SameSubgroup E.parabolic Bk ∧ SameSubgroup E.centralizer (extendSubgroup K D.centralizer) := by
    have hbase := limits_subgroups_extend G D (multiplicativeBaseChange F K)
      (multiplicativeBaseChange_unit K) E₀
    have h : E.parabolic = E₀.parabolic ∧ E.centralizer = E₀.centralizer := by
      exact ⟨limitParabolic_transport he E₀, centralizer_of_cast he E₀⟩
    rw [h.1, h.2]
    exact ⟨same_subgroup_trans hbase.1 ⟨subgroup_extend K hBD.2, subgroup_extend K hBD.1⟩, hbase.2.2⟩
  have hH : IsReductive H := reductive_geometricGroup G hG
  have hTk : IsMaximalTorus Tk := hTm.choose_spec
  have hTs : IsSplitTorus Tk.group := split_of_maximal (A := H) hTk
  have hTkm : IsGeometricallyMaximal Tk := geometricMaximal_of_maximal H Tk hTk
  have hBk : IsKBorel Bk := (isKBorel_iff_of_isAlgClosed H Bk).mpr hB.choose_spec
  have hTkBk : IsSubgroupOf Tk Bk := subgroup_extend K ⟨i, hi⟩
  obtain ⟨a, A, ha, hBA, _⟩ :=
    (LinearAlgebraicGroups.RootData.BorelsAndChambers.borelsThroughT H hH Tk hTs hTkm).1 Bk hBk hTkBk
  have hsign := limitParabolic_signs_of_same H Tk Ck a E A (same_subgroup_trans hE.1 hBA)
  obtain ⟨comm, R, _⟩ := LinearAlgebraicGroups.RootData.DatumAndWeyl.datumAndWeyl H hH Tk hTs hTkm
  letI := comm
  have hr : IsRegular Tk Ck := by
    intro α hz
    let i := R.rootDatum.reflectionPerm α α
    have hi : i.val = α.val⁻¹ := by
      have h := R.rootDatum.root_reflectionPerm α α
      rw [reflection_apply_self, R.root_eq, R.root_eq] at h
      exact Additive.ofMul.injective h
    have hα := (hsign α).mp (le_of_eq hz.symm)
    have hβ : 0 ≤ pairing Tk.group i.val Ck := by rw [hi, pairing_inv _ hTs, hz, neg_zero]
    have hβ' := (hsign i).mp hβ
    rw [hi, pairing_inv _ hTs] at hβ'
    exact ha α (by omega)
  have hcentral := centralizer_of_regular H hH Tk hTs hTkm Ck hr E
  have hsame : SameSubgroup D.centralizer T := by
    have h := same_subgroup_trans (same_subgroup_symm hE.2) hcentral
    exact ⟨subgroup_descend K h.1, subgroup_descend K h.2⟩
  refine ⟨C, D, hBD, fun Y g ↦ ?_⟩
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := (D.centralizer_points Y g).mp hg
    obtain ⟨f, hf⟩ := hsame.1
    have hf' : f.hom.hom ≫ T.inclusion.hom.hom = D.centralizer.inclusion.hom.hom :=
      (Grp.forget _).congr_map hf
    exact ⟨a ≫ f.hom.hom, by rw [Category.assoc, hf', ha]⟩
  · rintro ⟨g, rfl⟩
    exact torusSectionsCentralize hT C g

theorem borelTorusCentralizer : BorelTorusCentralizer.{u} := by
  intro F _ G hG B T hB hT hTm hTB
  obtain ⟨c, _, _, h⟩ := borelDefiningCocharacter G hG B T hB hT hTm hTB
  exact ⟨c, h⟩


open Specs.DiagonalizableGroups (diagonalGroup groupAlgebra IntegerCharacters)
open private multiplicative_group_iso from LinearAlgebraicGroups.Relative.LeviConjugacy

set_option backward.isDefEq.respectTransparency false in
theorem quasiSplitCentralizer : QuasiSplitCentralizer.{u} := by
  intro F _ G hG B T hB hT hTm hTB
  let T₀ := closedSubgroupAlgebraicGroup T
  obtain ⟨S, hS⟩ := largestSplitSubtorusExists T₀ hT
  obtain ⟨c, hc⟩ := borelTorusCentralizer G hG B T hB hT hTm hTB
  let e : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
  letI : Group.FG IntegerCharacters.{u} := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  let M := diagonalGroup F IntegerCharacters.{u}
  have hM : IsSplitTorus M.val := ⟨1, multiplicative_group_iso⟩
  obtain ⟨I, p, hI, hp⟩ := splitTorusImage M T₀ hM c
  obtain ⟨j, hj⟩ := hS.2 I hI
  have hfactor : (p ≫ j) ≫ S.inclusion = c := by rw [Category.assoc, hj, hp.1]
  let S₀ := subgroupOfSubgroup T S
  have hcentral : RepresentsSubgroup T (fun _ g ↦ Centralizes S₀.inclusion g) := by
    intro Y g
    constructor
    · intro hg
      apply (hc Y g).mp
      have h : (p ≫ j) ≫ S₀.inclusion = c ≫ T.inclusion := by
        change (p ≫ j) ≫ S.inclusion ≫ T.inclusion = _
        rw [← Category.assoc, hfactor]
      rw [← h]
      apply (centralizes_iff _ _).mpr
      intro X f a
      exact (centralizes_iff _ _).mp hg X f (a ≫ (p ≫ j).hom.hom)
    · rintro ⟨g, rfl⟩
      exact torusSectionsCentralize hT S.inclusion g
  refine ⟨S, hS, ⟨hS.1, ?_⟩, hcentral, borelIsMinimalParabolic G hG B hB,
    subgroupOf_trans ⟨S.inclusion, rfl⟩ hTB⟩
  intro A hA hSA
  obtain ⟨v, hv⟩ := hSA
  have hcomm : Centralizes S₀.inclusion A.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro X a s
    have hA' : IsTorus A.group := isTorus_of_split hA
    letI : IsCommMonObj A.group.X := torus_commutative (closedSubgroupAlgebraicGroup A) hA'
    letI : CommMonoid (X ⟶ A.group.X) := Hom.commMonoid
    have h := (Commute.all a (s ≫ v.hom.hom)).map
      (IsMonHom.monoidHom A.inclusion.hom.hom X)
    have hv' : v.hom.hom ≫ A.inclusion.hom.hom = S₀.inclusion.hom.hom :=
      (Grp.forget _).congr_map hv
    change Commute (a ≫ A.inclusion.hom.hom)
      ((s ≫ v.hom.hom) ≫ A.inclusion.hom.hom) at h
    simpa only [Category.assoc, hv'] using h
  obtain ⟨q, hq⟩ := (hcentral _ _).mp hcomm
  obtain ⟨a, ha⟩ := factor_group_through_subgroup T A.inclusion q hq
  let A' := restrictSubgroup A T a ha
  obtain ⟨m, hm⟩ := hS.2 A' hA
  refine ⟨m, ?_⟩
  change m ≫ S.inclusion ≫ T.inclusion = _
  rw [← Category.assoc, hm]
  exact ha


open private torus_coordinates from LinearAlgebraicGroups.Reductive.SubtorusCentralizer
open private finiteGaloisSplitsTorus from LinearAlgebraicGroups.Relative.RationalDensity
open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups

theorem finiteGaloisTorusSplitting : FiniteGaloisTorusSplitting.{u} := by
  intro F _ T hT
  obtain ⟨A, ⟨t⟩, hA⟩ := torus_coordinates T hT
  obtain ⟨K, _, _, _, _, r, ⟨e⟩⟩ := finiteGaloisSplitsTorus hA
  obtain ⟨s⟩ := LinearAlgebraicGroups.CharacterDescent.standardSplitTorus (k := K) r
  let j := (AlgebraicGeometry.hopfSpec (CommRingCat.of K)).mapIso e.symm.op ≪≫
    extendedGroupIso K A ≪≫ (groupBaseChange F K).mapIso t
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, r, ⟨j.symm ≪≫ s⟩⟩

open private normalizes_iff_sections normalizes_inv
  from LinearAlgebraicGroups.RootData.BorelNormalizer

theorem normalizesCentralizer : NormalizesCentralizer.{u} := by
  intro F _ G S C hC Y g hg
  have forward (g : Y ⟶ G.X) (hg : Normalizes S.inclusion g) (X : SchemeOver F)
      (x : X ⟶ Y) (c : X ⟶ C.group.X) :
      Specs.SchemeDerivedGroup.FactorsThrough C
        ((x ≫ g) * (c ≫ C.inclusion.hom.hom) * (x ≫ g)⁻¹) := by
    apply (hC _ _).mp
    apply (centralizes_iff _ _).mpr
    intro Z z s
    let a := (z ≫ x) ≫ g
    let v := (z ≫ c) ≫ C.inclusion.hom.hom
    let b := s ≫ S.inclusion.hom.hom
    obtain ⟨t, ht⟩ := ((normalizes_iff_sections S g).mp hg Z (z ≫ x) s).2
    change t ≫ S.inclusion.hom.hom = a⁻¹ * b * a at ht
    have hct := (hC X (c ≫ C.inclusion.hom.hom)).mpr ⟨c, rfl⟩
    have h := (centralizes_iff _ _).mp hct Z z t
    have h' : Commute v (a⁻¹ * b * a) := by
      rw [← ht]
      simpa only [v, Category.assoc] using h
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
    change Commute (a * v * a⁻¹) b
    have he := (h'.map (MulAut.conj a)).eq
    simp only [MulAut.conj_apply] at he
    have hab : a * (a⁻¹ * b * a) * a⁻¹ = b := by group
    rw [hab] at he
    exact he
  apply (normalizes_iff_sections C g).mpr
  intro X x c
  refine ⟨forward g hg X x c, ?_⟩
  change ∃ d : X ⟶ C.group.X, d ≫ C.inclusion.hom.hom =
    (x ≫ g)⁻¹ * (c ≫ C.inclusion.hom.hom) * (x ≫ g)
  obtain ⟨d, hd⟩ := forward g⁻¹ (normalizes_inv S hg) X x c
  change d ≫ C.inclusion.hom.hom = (x ≫ g⁻¹) * (c ≫ C.inclusion.hom.hom) * (x ≫ g⁻¹)⁻¹ at hd
  exact ⟨d, by simpa only [GrpObj.comp_inv, inv_inv] using hd⟩


open Specs.Relative.RelativeWeylScheme (rationalProjection)
open Specs.SchemeDerivedGroup (FactorsThrough)
open private factor_of_baseChange from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private rationalSectionsEquiv from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private scalarExtendedPoint_natural from LinearAlgebraicGroups.RootData.RankOneFlag

set_option backward.isDefEq.respectTransparency false in
private theorem projectionOneIff {N C : ClosedSubgroup G.val} {H : GroupScheme F}
    {p : N.group ⟶ H} {i : C.group ⟶ N.group}
    {hi : IsClosedImmersion i.hom.hom.left}
    (hc : i ≫ N.inclusion = C.inclusion) (hk : IsSchemeKernel p ⟨_, i, hi⟩)
    (n : 𝟙_ (SchemeOver F) ⟶ N.group.X) :
    n ≫ p.hom.hom = 1 ↔ FactorsThrough C (n ≫ N.inclusion.hom.hom) := by
  letI := N.isClosedImmersion
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  have hi' : i.hom.hom ≫ N.inclusion.hom.hom = C.inclusion.hom.hom :=
    (Grp.forget _).congr_map hc
  rw [← schemeKernel_sections hk n]
  change (∃ c : 𝟙_ (SchemeOver F) ⟶ C.group.X, c ≫ i.hom.hom = n) ↔
    ∃ c : 𝟙_ (SchemeOver F) ⟶ C.group.X, c ≫ C.inclusion.hom.hom = n ≫ N.inclusion.hom.hom
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Category.assoc, hi']⟩
  · rintro ⟨c, he⟩
    exact ⟨c, (cancel_mono N.inclusion.hom.hom).mp (by rw [Category.assoc, hi', he])⟩

variable {K : Type u} [Field K] [Algebra F K]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarPointHom (H : GroupScheme F) :
    (𝟙_ (SchemeOver F) ⟶ H.X) →*
      (𝟙_ (SchemeOver K) ⟶ ((groupBaseChange F K).obj H).X) where
  toFun := scalarExtendedRationalPoint K
  map_one' := by
    letI : MonObj ((baseChange F K).obj H.X) := inferInstanceAs
      (MonObj ((groupBaseChange F K).obj H).X)
    change Functor.LaxMonoidal.ε (baseChange F K) ≫ (baseChange F K).map (1 : _ ⟶ H.X) = 1
    rw [Functor.map_one, MonObj.comp_one]
  map_mul' n m := by
    letI : MonObj ((baseChange F K).obj H.X) := inferInstanceAs
      (MonObj ((groupBaseChange F K).obj H).X)
    change Functor.LaxMonoidal.ε (baseChange F K) ≫ (baseChange F K).map (n * m) =
      (Functor.LaxMonoidal.ε (baseChange F K) ≫ (baseChange F K).map n) *
        (Functor.LaxMonoidal.ε (baseChange F K) ≫ (baseChange F K).map m)
    rw [Functor.map_mul, MonObj.comp_mul]

set_option backward.isDefEq.respectTransparency false in
private theorem factorsThroughScalarPointIff (T : ClosedSubgroup G.val)
    (g : 𝟙_ (SchemeOver F) ⟶ G.val.X) :
    FactorsThrough (extendSubgroup K T) (scalarExtendedRationalPoint K g) ↔ FactorsThrough T g := by
  let F' := baseChange F K
  let e := Functor.Monoidal.εIso F'
  constructor
  · rintro ⟨c, hc⟩
    change c ≫ F'.map T.inclusion.hom.hom = scalarExtendedRationalPoint K g at hc
    letI := T.isClosedImmersion
    have hc' : (e.inv ≫ c) ≫ F'.map T.inclusion.hom.hom = F'.map g := by
      rw [Category.assoc, hc]
      change e.inv ≫ e.hom ≫ F'.map g = F'.map g
      rw [Iso.inv_hom_id_assoc]
    exact factor_of_baseChange K g T.inclusion.hom.hom (e.inv ≫ c) hc'
  · rintro ⟨c, rfl⟩
    exact ⟨scalarExtendedRationalPoint K c, scalarExtendedPoint_natural K c _ |>.symm⟩

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem relativeWeylEmbedding : RelativeWeylEmbedding.{u} := by
  intro F K _ _ _ G hG S P T hS hP hSP hC Q hTK
  dsimp only
  intro comm D A
  letI := comm
  let E := groupBaseChange F K
  let NK := extendSubgroup K Q.normalizer
  let TK := extendSubgroup K T
  let SK := extendSubgroup K S
  obtain ⟨_, hN⟩ := LinearAlgebraicGroups.normalizerSchemeBaseChange F K S.inclusion Q.normalizer
    S.isClosedImmersion Q.normalizerProperty
  obtain ⟨_, hC'⟩ := LinearAlgebraicGroups.centralizerSchemeBaseChange F K S.inclusion T hC
  have hN' : Normalizes SK.inclusion NK.inclusion.hom.hom := (hN _ _).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hT' : Normalizes TK.inclusion NK.inclusion.hom.hom :=
    normalizesCentralizer SK TK hC' _ _ hN'
  obtain ⟨i, hi⟩ := (A.representsNormalizer _ _).mp hT'
  obtain ⟨j, hj⟩ := factor_group_through_subgroup A.normalizer NK.inclusion i hi
  obtain ⟨rel, hrel⟩ := rationalSectionsEquiv Q.splitImage.constantGroup
  obtain ⟨abs, habs⟩ := rationalSectionsEquiv A.image.constantGroup
  let t := (IsMonHom.monoidHom j.hom.hom (𝟙_ (SchemeOver K))).comp (scalarPointHom Q.normalizer.group)
  let q := rel.symm.toMonoidHom.comp (rationalProjection Q)
  let p := A.labelEquiv.symm.toMonoidHom.comp
    (abs.symm.toMonoidHom.comp
      ((IsMonHom.monoidHom A.quotient.hom.hom (𝟙_ (SchemeOver K))).comp t))
  obtain ⟨_, _, _, _, hsurj, _, _⟩ :=
    LinearAlgebraicGroups.Relative.RelativeWeylScheme.relativeWeylAction G hG S P hS hP hSP Q
  have hq : Function.Surjective q := by
    intro w
    obtain ⟨n, hn⟩ := hsurj w
    exact ⟨n, rel.symm_apply_eq.mpr (hn.trans (hrel w).symm)⟩
  have ht (n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X) :
      t n ≫ A.normalizer.inclusion.hom.hom =
        scalarExtendedRationalPoint K (n ≫ Q.normalizer.inclusion.hom.hom) := by
    change (scalarExtendedRationalPoint K n ≫ j.hom.hom) ≫ A.normalizer.inclusion.hom.hom = _
    rw [Category.assoc, show j.hom.hom ≫ A.normalizer.inclusion.hom.hom = NK.inclusion.hom.hom from
      (Grp.forget _).congr_map hj]
    exact (scalarExtendedPoint_natural K n _).symm
  have hsame : ∀ (X : SchemeOver F) (g : X ⟶ G.val.X),
      FactorsThrough Q.centralizer g ↔ FactorsThrough T g :=
    fun X g ↦ (Q.centralizerProperty X g).symm.trans (hC X g)
  have hker : q.ker = p.ker := by
    ext n
    change rel.symm (rationalProjection Q n) = 1 ↔
      A.labelEquiv.symm (abs.symm (t n ≫ A.quotient.hom.hom)) = 1
    simp only [MulEquiv.map_eq_one_iff]
    change n ≫ Q.projection.hom.hom = 1 ↔ t n ≫ A.quotient.hom.hom = 1
    rw [projectionOneIff Q.inclusionProperty Q.quotientProperty.1,
      projectionOneIff A.inclusion_eq A.isQuotient.1, ht, factorsThroughScalarPointIff]
    exact hsame _ _
  let eq := QuotientGroup.liftEquiv q.ker hq rfl
  let dest := QuotientGroup.lift q.ker p hker.le
  let embed := dest.comp eq.symm.toMonoidHom
  have hinj : Function.Injective dest := (QuotientGroup.injective_lift_iff _ _ _).mpr hker
  refine ⟨embed, hinj.comp eq.symm.injective, ?_⟩
  intro n w hn
  have he : eq (QuotientGroup.mk n) = w := rel.symm_apply_eq.mpr (hn.trans (hrel w).symm)
  have hp : embed w = p n := by
    change dest (eq.symm w) = p n
    rw [← he, eq.symm_apply_apply]
    rfl
  refine ⟨t n, ht n, ?_⟩
  rw [hp]
  change _ = A.image.constantGroup.sectionPoint (A.labelEquiv
    (A.labelEquiv.symm (abs.symm (t n ≫ A.quotient.hom.hom))))
  rw [A.labelEquiv.apply_symm_apply, ← habs, abs.apply_symm_apply]

open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.AbstractPairing (Datum)
open Specs.DatumAndWeyl (Identification)
open private regular_of_centralizer subgroupRoots_of_regular lieImage_eq_of_same
  from LinearAlgebraicGroups.RootData.BorelsAndChambers

set_option backward.isDefEq.respectTransparency false in
private theorem sameSubgroupOfCentralizer {A H : GroupScheme F} (c : A ⟶ H)
    {T U : ClosedSubgroup H}
    (hT : RepresentsSubgroup T (fun _ g ↦ Centralizes c g))
    (hU : RepresentsSubgroup U (fun _ g ↦ Centralizes c g)) :
    SameSubgroup T U := by
  constructor
  · obtain ⟨j, hj⟩ := (hU _ _).mp ((hT _ _).mpr ⟨𝟙 _, Category.id_comp _⟩)
    exact factor_group_through_subgroup U T.inclusion j hj
  · obtain ⟨j, hj⟩ := (hT _ _).mp ((hU _ _).mpr ⟨𝟙 _, Category.id_comp _⟩)
    exact factor_group_through_subgroup T U.inclusion j hj

set_option backward.isDefEq.respectTransparency false in
private theorem torusMaximalOfCentralizer (G : AffineAlgebraicGroup F)
    {H : GroupScheme F} (T : ClosedSubgroup G.val) (hT : IsTorus T.group)
    (c : H ⟶ T.group)
    (hC : RepresentsSubgroup T (fun _ g ↦ Centralizes (c ≫ T.inclusion) g)) :
    IsMaximalTorus T := by
  refine ⟨hT, ?_⟩
  intro A hA ⟨j, hj⟩
  have hh := torusSectionsCentralize (T := A) hA (c ≫ j) (𝟙 A.group.X)
  rw [Category.assoc, hj, Category.id_comp] at hh
  obtain ⟨m, hm⟩ := (hC _ _).mp hh
  exact factor_group_through_subgroup T A.inclusion m hm

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem regularAtSplittingField (G : AffineAlgebraicGroup F) (hG : IsReductive G)
    (T B : ClosedSubgroup G.val)
    (c : Cocharacter T.group) (L : LimitDecomposition (c ≫ T.inclusion))
    (hB : SameSubgroup B L.parabolic)
    (hC : RepresentsSubgroup T (fun _ g ↦ Centralizes (c ≫ T.inclusion) g))
    (hSplit : IsSplitTorus ((groupBaseChange F K).obj T.group)) :
    let G' := baseChangedAlgebraicGroup K G
    let T' : ClosedSubgroup G'.val := extendSubgroup K T
    let B' : ClosedSubgroup G'.val := extendSubgroup K B
    let c' : Cocharacter T'.group := extendCocharacter K c
    IsGeometricallyMaximal T' ∧ IsRegular T' c' ∧
      BorelsAndChambers.positiveRoots T' c' = BorelsAndChambers.subgroupRoots T' B' := by
  dsimp only
  let G' := baseChangedAlgebraicGroup K G
  let T' : ClosedSubgroup G'.val := extendSubgroup K T
  let B' : ClosedSubgroup G'.val := extendSubgroup K B
  let c' : Cocharacter T'.group := extendCocharacter K c
  let H := AlgebraicClosure K
  have hG' : IsReductive G' :=
    (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  have hT' : IsTorus T'.group := isTorus_of_split hSplit
  have hC' : RepresentsSubgroup T' (fun _ g ↦
      Centralizes ((groupBaseChange F K).map (c ≫ T.inclusion)) g) :=
    (LinearAlgebraicGroups.centralizerSchemeBaseChange F K (c ≫ T.inclusion) T hC).choose_spec
  let T'' := extendSubgroup H T'
  have hC'' : RepresentsSubgroup T'' (fun _ g ↦
      Centralizes ((groupBaseChange K H).map ((groupBaseChange F K).map (c ≫ T.inclusion))) g) :=
    (LinearAlgebraicGroups.centralizerSchemeBaseChange K H _ T' hC').choose_spec
  let c'' := (groupBaseChange K H).map ((groupBaseChange F K).map c)
  have hcc : (groupBaseChange K H).map ((groupBaseChange F K).map (c ≫ T.inclusion)) =
      c'' ≫ T''.inclusion := by
    change (groupBaseChange K H).map ((groupBaseChange F K).map (c ≫ T.inclusion)) =
      (groupBaseChange K H).map ((groupBaseChange F K).map c) ≫
        (groupBaseChange K H).map ((groupBaseChange F K).map T.inclusion)
    rw [(groupBaseChange F K).map_comp, (groupBaseChange K H).map_comp]
  rw [hcc] at hC''
  have hT'' : IsTorus T''.group :=
    torus_baseChange_algClosure (closedSubgroupAlgebraicGroup (G := G') T') hT'
  have hTm : IsGeometricallyMaximal T' := ⟨T''.isClosedImmersion,
    torusMaximalOfCentralizer (GeometricGroup G') T'' hT'' c'' hC''⟩
  have he : extendCocharacter K (c ≫ T.inclusion) = c' ≫ T'.inclusion := by
    change (multiplicativeBaseChange F K).hom ≫ (groupBaseChange F K).map (c ≫ T.inclusion) =
      ((multiplicativeBaseChange F K).hom ≫ (groupBaseChange F K).map c) ≫
        (groupBaseChange F K).map T.inclusion
    rw [Functor.map_comp, Category.assoc]
  obtain ⟨L₀⟩ := existsLimitDecomposition G' (extendCocharacter K (c ≫ T.inclusion))
  let L' : LimitDecomposition (c' ≫ T'.inclusion) := he ▸ L₀
  have hLimit := limits_subgroups_extend G L (multiplicativeBaseChange F K)
    (multiplicativeBaseChange_unit K) L₀
  have hB' : SameSubgroup L'.parabolic B' := by
    change SameSubgroup (he ▸ L₀ : LimitDecomposition (c' ≫ T'.inclusion)).parabolic B'
    rw [limitParabolic_transport he L₀]
    exact same_subgroup_trans hLimit.1 ⟨subgroup_extend K hB.2, subgroup_extend K hB.1⟩
  have hL : SameSubgroup L.centralizer T :=
    sameSubgroupOfCentralizer _ L.centralizer_points hC
  have hL' : SameSubgroup L'.centralizer T' := by
    change SameSubgroup (he ▸ L₀ : LimitDecomposition (c' ≫ T'.inclusion)).centralizer T'
    rw [centralizer_of_cast he L₀]
    exact same_subgroup_trans hLimit.2.2 ⟨subgroup_extend K hL.1, subgroup_extend K hL.2⟩
  have hreg : IsRegular T' c' :=
    regular_of_centralizer G' hG' T' hSplit hTm c' L' hL'
  refine ⟨hTm, hreg, ?_⟩
  rw [show BorelsAndChambers.subgroupRoots T' B' = BorelsAndChambers.subgroupRoots T' L'.parabolic by
    unfold BorelsAndChambers.subgroupRoots
    rw [lieImage_eq_of_same hB']]
  exact (subgroupRoots_of_regular G' T' c' hreg L').symm

end LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj CategoryTheory.Obj
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.Arithmetic.QuasiSplitFixedWeyl
open LinearAlgebraicGroups.Specs.CharacterDescent (Character Cocharacter)
open LinearAlgebraicGroups.Specs.CharacterPairing (pairing powerMorphism characterValue)
open LinearAlgebraicGroups.CocharacterDynamics (unitPoint)

universe u
namespace LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
variable {F K : Type u} [Field F] [Field K] [Algebra F K]

open private isCommMonObj_of_groupIso from LinearAlgebraicGroups.Affine.HopfAlgebras
open private twist twistGroups twistGroupBaseChangeIso from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private twistedBaseChange twistedBaseChange_inv twistedBaseChange_hom_fst
  twistedBaseChange_hom_snd twistMorphism twistMorphism_one twistMorphism_twistMorphism
  multiplicativeBaseChange multiplicativeBaseChange_unit
  from LinearAlgebraicGroups.Relative.RationalCocharacter

private abbrev scalarMorphism (σ : Gal(K/F)) {A B : GroupScheme F}
    (f : (groupBaseChange F K).obj A ⟶ (groupBaseChange F K).obj B) :=
  twistMorphism σ⁻¹ f

private theorem scalarMorphism_comp (σ : Gal(K/F)) {A B C : GroupScheme F}
    (f : (groupBaseChange F K).obj A ⟶ (groupBaseChange F K).obj B)
    (g : (groupBaseChange F K).obj B ⟶ (groupBaseChange F K).obj C) :
    scalarMorphism σ (f ≫ g) = scalarMorphism σ f ≫ scalarMorphism σ g := by
  simp only [twistMorphism, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

private theorem scalarMorphism_id (σ : Gal(K/F)) (A : GroupScheme F) :
    scalarMorphism σ (𝟙 ((groupBaseChange F K).obj A)) = 𝟙 _ := by
  change (twistedBaseChange σ⁻¹ A).inv ≫
    (twistGroups σ⁻¹).map (𝟙 ((groupBaseChange F K).obj A)) ≫
      (twistedBaseChange σ⁻¹ A).hom = _
  erw [(twistGroups σ⁻¹).map_id, Category.id_comp]
  exact (twistedBaseChange σ⁻¹ A).inv_hom_id

private theorem scalarMorphism_baseChange (σ : Gal(K/F)) {A B : GroupScheme F} (f : A ⟶ B) :
    scalarMorphism σ ((groupBaseChange F K).map f) = (groupBaseChange F K).map f := by
  let d := twistGroupBaseChangeIso σ⁻¹
  have h := d.hom.naturality f
  change (twistGroups σ⁻¹).map ((groupBaseChange F K).map f) ≫ (d.app B).hom =
    (d.app A).hom ≫ (groupBaseChange F K).map f at h
  change (d.app A).inv ≫ (twistGroups σ⁻¹).map ((groupBaseChange F K).map f) ≫
    (d.app B).hom = _
  rw [h, Iso.inv_hom_id_assoc]

private theorem scalarMorphism_mul (σ : Gal(K/F)) {A B : GroupScheme F}
    [IsCommMonObj ((groupBaseChange F K).obj B).X]
    (f g : (groupBaseChange F K).obj A ⟶ (groupBaseChange F K).obj B) :
    scalarMorphism σ (f * g) = scalarMorphism σ f * scalarMorphism σ g := by
  apply Grp.hom_ext
  let d := (twistedBaseChange σ⁻¹ A).inv.hom.hom
  let e := (twistedBaseChange σ⁻¹ B).hom.hom.hom
  change d ≫ (twist σ⁻¹).map (f.hom.hom * g.hom.hom) ≫ e =
    (d ≫ (twist σ⁻¹).map f.hom.hom ≫ e) * (d ≫ (twist σ⁻¹).map g.hom.hom ≫ e)
  rw [Functor.map_mul, MonObj.mul_comp, MonObj.comp_mul]

private theorem scalarMorphism_one (σ : Gal(K/F)) {A B : GroupScheme F}
    [IsCommMonObj ((groupBaseChange F K).obj B).X] :
    scalarMorphism σ (1 : (groupBaseChange F K).obj A ⟶ (groupBaseChange F K).obj B) = 1 := by
  apply Grp.hom_ext
  let d := (twistedBaseChange σ⁻¹ A).inv.hom.hom
  let e := (twistedBaseChange σ⁻¹ B).hom.hom.hom
  change d ≫ (twist σ⁻¹).map 1 ≫ e = 1
  rw [Functor.map_one, MonObj.one_comp, MonObj.comp_one]

private theorem scalarMorphism_identity {A B : GroupScheme F}
    (f : (groupBaseChange F K).obj A ⟶ (groupBaseChange F K).obj B) :
    scalarMorphism (1 : Gal(K/F)) f = f := by
  simp only [scalarMorphism, inv_one, twistMorphism_one]

private theorem scalarMorphism_action (σ τ : Gal(K/F)) {A B : GroupScheme F}
    (f : (groupBaseChange F K).obj A ⟶ (groupBaseChange F K).obj B) :
    scalarMorphism σ (scalarMorphism τ f) = scalarMorphism (σ * τ) f := by
  simp only [scalarMorphism, twistMorphism_twistMorphism, mul_inv_rev]

private theorem twistedBaseChange_left (σ : Gal(K/F)) (A : GroupScheme F) :
    (twistedBaseChange σ A).hom.hom.hom.left = scalarTransport σ A.X := by
  apply pullback.hom_ext
  · rw [twistedBaseChange_hom_fst]
    exact (pullback.lift_fst ..).symm
  · rw [twistedBaseChange_hom_snd]
    exact (pullback.lift_snd ..).symm

private theorem scalarMorphism_left (σ : Gal(K/F)) {A B : GroupScheme F}
    (f : (groupBaseChange F K).obj A ⟶ (groupBaseChange F K).obj B) :
    (scalarMorphism σ f).hom.hom.left =
      scalarTransport σ A.X ≫ f.hom.hom.left ≫ scalarTransport σ⁻¹ B.X := by
  change (twistedBaseChange σ⁻¹ A).inv.hom.hom.left ≫ f.hom.hom.left ≫
    (twistedBaseChange σ⁻¹ B).hom.hom.hom.left = _
  rw [twistedBaseChange_inv, inv_inv, twistedBaseChange_left, twistedBaseChange_left]

local notation "M" => multiplicativeGroup F
local notation "E" => multiplicativeBaseChange F K

private def scalarCharacter (σ : Gal(K/F)) {T : GroupScheme F}
    (χ : Character ((groupBaseChange F K).obj T)) :
    Character ((groupBaseChange F K).obj T) :=
  scalarMorphism σ (χ ≫ (E).hom) ≫ (E).inv

private def scalarCocharacter (σ : Gal(K/F)) {T : GroupScheme F}
    (c : Cocharacter ((groupBaseChange F K).obj T)) :
    Cocharacter ((groupBaseChange F K).obj T) :=
  (E).hom ≫ scalarMorphism σ ((E).inv ≫ c)

private theorem scalarCharacter_comparison (σ : Gal(K/F)) {T : GroupScheme F}
    (χ : Character ((groupBaseChange F K).obj T)) :
    scalarCharacter σ χ ≫ (E).hom = scalarMorphism σ (χ ≫ (E).hom) := by
  simp only [scalarCharacter, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem scalarCocharacter_comparison (σ : Gal(K/F)) {T : GroupScheme F}
    (c : Cocharacter ((groupBaseChange F K).obj T)) :
    (E).inv ≫ scalarCocharacter σ c = scalarMorphism σ ((E).inv ≫ c) := by
  simp only [scalarCocharacter, Iso.inv_hom_id_assoc]

private theorem scalarCharacter_mul (σ : Gal(K/F)) {T : GroupScheme F}
    (χ ψ : Character ((groupBaseChange F K).obj T)) :
    scalarCharacter σ (χ * ψ) = scalarCharacter σ χ * scalarCharacter σ ψ := by
  letI : IsCommMonObj ((groupBaseChange F K).obj M).X :=
    (isCommMonObj_of_groupIso E inferInstance)
  have mul_comp {X Y Z : GroupScheme K} [IsCommMonObj Y.X] [IsCommMonObj Z.X]
      (a b : X ⟶ Y) (c : Y ⟶ Z) : (a * b) ≫ c = (a ≫ c) * (b ≫ c) := by
    apply Grp.hom_ext
    exact MonObj.mul_comp _ _ _
  simp only [scalarCharacter, mul_comp, scalarMorphism_mul]

private theorem scalarCharacter_one (σ : Gal(K/F)) {T : GroupScheme F} :
    scalarCharacter σ (1 : Character ((groupBaseChange F K).obj T)) = 1 := by
  letI : IsCommMonObj ((groupBaseChange F K).obj M).X :=
    (isCommMonObj_of_groupIso E inferInstance)
  have one_comp {X Y Z : GroupScheme K} [IsCommMonObj Y.X] [IsCommMonObj Z.X]
      (c : Y ⟶ Z) : (1 : X ⟶ Y) ≫ c = 1 := by
    apply Grp.hom_ext
    exact MonObj.one_comp _
  simp only [scalarCharacter, one_comp, scalarMorphism_one]

private theorem scalarCharacter_identity {T : GroupScheme F}
    (χ : Character ((groupBaseChange F K).obj T)) :
    scalarCharacter (1 : Gal(K/F)) χ = χ := by
  simp only [scalarCharacter, scalarMorphism_identity, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem scalarCharacter_action (σ τ : Gal(K/F)) {T : GroupScheme F}
    (χ : Character ((groupBaseChange F K).obj T)) :
    scalarCharacter σ (scalarCharacter τ χ) = scalarCharacter (σ * τ) χ := by
  simp only [scalarCharacter, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    scalarMorphism_action]

private def scalarCharacterEquiv (σ : Gal(K/F)) (T : GroupScheme F) :
    MulAut (Character ((groupBaseChange F K).obj T)) where
  toFun := scalarCharacter σ
  invFun := scalarCharacter σ⁻¹
  left_inv χ := by rw [scalarCharacter_action, inv_mul_cancel, scalarCharacter_identity]
  right_inv χ := by rw [scalarCharacter_action, mul_inv_cancel, scalarCharacter_identity]
  map_mul' := scalarCharacter_mul σ

private theorem scalarCocharacter_baseChange (σ : Gal(K/F)) {T : GroupScheme F}
    (c : Cocharacter T) :
    scalarCocharacter σ ((E).hom ≫ (groupBaseChange F K).map c) =
      (E).hom ≫ (groupBaseChange F K).map c := by
  simp only [scalarCocharacter, Iso.inv_hom_id_assoc, scalarMorphism_baseChange]


section SemilinearPoints

open Specs.AdjointRepresentation (dualMap constants scale)
open private unitEquiv unitEquiv_unitPoint from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private mapPoints_comp from LinearAlgebraicGroups.RootData.CharacterPairing
open private integerExponent from LinearAlgebraicGroups.RootData.CharacterPairing
open scoped MonoidAlgebra

private structure SemilinearTestMap (σ : Gal(K/F)) (R U : TestAlgebra K) where
  hom : R →+* U
  commutes (k : K) : hom (algebraMap K R k) = algebraMap K U (σ k)

private def SemilinearTestMap.restrict {σ : Gal(K/F)} {R U : TestAlgebra K}
    (a : SemilinearTestMap σ R U) :
    (restrictTestAlgebra F K).obj R ⟶ (restrictTestAlgebra F K).obj U :=
  ConcreteCategory.ofHom (C := CommAlgCat F)
    ({ toRingHom := a.hom
       commutes' := fun k ↦ by
         change a.hom (algebraMap K R (algebraMap F K k)) = algebraMap K U (algebraMap F K k)
         rw [a.commutes, σ.commutes] } :
      (restrictTestAlgebra F K).obj R →ₐ[F] (restrictTestAlgebra F K).obj U)

private def SemilinearTestMap.dual {σ : Gal(K/F)} {R U : TestAlgebra K}
    (a : SemilinearTestMap σ R U) :
    SemilinearTestMap σ (CommAlgCat.of K (DualNumber R)) (CommAlgCat.of K (DualNumber U)) where
  hom := InfinitesimalCommutator.mapCoefficients a.hom
  commutes t := TrivSqZeroExt.ext (a.commutes t) (map_zero a.hom)

private def semilinearSource (σ : Gal(K/F)) (U : TestAlgebra K) : TestAlgebra K :=
  letI : Algebra K U := ((algebraMap K U).comp σ.toRingHom).toAlgebra
  CommAlgCat.of K U

private def semilinearSourceMap (σ : Gal(K/F)) (U : TestAlgebra K) :
    SemilinearTestMap σ (semilinearSource σ U) U :=
  ⟨RingHom.id U, fun _ ↦ rfl⟩

private def semilinearFieldMap (σ : Gal(K/F)) :
    SemilinearTestMap σ (CommAlgCat.of K K) (CommAlgCat.of K K) :=
  ⟨σ.toRingHom, fun _ ↦ rfl⟩

private def semilinearPoint (A : GroupScheme F) {σ : Gal(K/F)} {R U : TestAlgebra K}
    (a : SemilinearTestMap σ R U) :
    Points ((groupBaseChange F K).obj A).X R →* Points ((groupBaseChange F K).obj A).X U :=
  let e := baseChangePointGroupEquiv K A
  (e U).symm.toMonoidHom.comp
    ((((groupPointsFunctor F).obj A).map a.restrict).hom.comp (e R).toMonoidHom)

private theorem semilinearPoint_apply (A : GroupScheme F) {σ : Gal(K/F)} {R U : TestAlgebra K}
    (a : SemilinearTestMap σ R U) (p : Points ((groupBaseChange F K).obj A).X R) :
    baseChangePoint F K A.X U (semilinearPoint A a p) =
      mapPoints a.restrict (baseChangePoint F K A.X R p) :=
  (baseChangePointGroupEquiv K A U).apply_symm_apply _

private theorem semilinearPoint_bijective (A : GroupScheme F) {σ : Gal(K/F)}
    {R U : TestAlgebra K} (a : SemilinearTestMap σ R U)
    (ha : Function.Bijective a.hom) : Function.Bijective (semilinearPoint A a) :=
  haveI : IsIso a.restrict := (ConcreteCategory.isIso_iff_bijective _).mpr ha
  (baseChangePointGroupEquiv K A U).symm.bijective.comp
    (((ConcreteCategory.isIso_iff_bijective (((groupPointsFunctor F).obj A).map a.restrict)).mp
      inferInstance).comp (baseChangePointGroupEquiv K A R).bijective)

private theorem scalarMap_comp (σ τ : Gal(K/F)) :
    scalarMap (σ * τ) = scalarMap σ ≫ scalarMap τ := by
  change Spec.map (CommRingCat.ofHom (σ * τ).toRingHom) =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom)
  rw [← Spec.map_comp]
  rfl

private theorem scalarMap_one :
    scalarMap (1 : Gal(K/F)) = 𝟙 _ := Scheme.Spec.map_id _

private theorem semilinearPoint_left (A : GroupScheme F) {σ : Gal(K/F)}
    {R U : TestAlgebra K} (a : SemilinearTestMap σ R U)
    (p : Points ((groupBaseChange F K).obj A).X R) :
    (semilinearPoint A a p).left =
      Spec.map (CommRingCat.ofHom a.hom) ≫ p.left ≫ scalarTransport σ⁻¹ A.X := by
  let p' : Points ((baseChange F K).obj A.X) R := p
  let q' : Points ((baseChange F K).obj A.X) U := semilinearPoint A a p
  change q'.left = Spec.map (CommRingCat.ofHom a.hom) ≫ p'.left ≫ scalarTransport σ⁻¹ A.X
  apply pullback.hom_ext
  · have h := congrArg (fun f : Points A.X ((restrictTestAlgebra F K).obj U) ↦ f.left)
      (semilinearPoint_apply A a p)
    change q'.left ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom a.hom) ≫ (p'.left ≫ pullback.fst _ _) at h
    rw [h]
    simp only [scalarTransport, Category.assoc, pullback.lift_fst]
  · let S := (testSpec K).obj (op R)
    let V := (testSpec K).obj (op U)
    have hc : Spec.map (CommRingCat.ofHom a.hom) ≫ S.hom = V.hom ≫ scalarMap σ := by
      change Spec.map (CommRingCat.ofHom a.hom) ≫ Spec.map (CommRingCat.ofHom (algebraMap K R)) =
        Spec.map (CommRingCat.ofHom (algebraMap K U)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext a.commutes)
    have hp : p'.left ≫ pullback.snd A.X.hom (fieldSpecMap F K) = S.hom := Over.w p'
    rw [show q'.left ≫ pullback.snd A.X.hom (fieldSpecMap F K) = V.hom from Over.w q']
    rw [Category.assoc, Category.assoc, show scalarTransport σ⁻¹ A.X ≫
      pullback.snd A.X.hom (fieldSpecMap F K) =
        pullback.snd A.X.hom (fieldSpecMap F K) ≫ scalarMap σ⁻¹ from pullback.lift_snd ..]
    rw [← Category.assoc p'.left, hp, ← Category.assoc, hc, Category.assoc, ← scalarMap_comp,
      mul_inv_cancel, scalarMap_one, Category.comp_id]

private theorem scalarTransport_cancel (σ : Gal(K/F)) (A : GroupScheme F) :
    scalarTransport σ⁻¹ A.X ≫ scalarTransport σ A.X = 𝟙 _ := by
  rw [← twistedBaseChange_left, ← twistedBaseChange_inv, ← twistedBaseChange_left]
  exact ((Grp.forget (SchemeOver K) ⋙ Over.forget _).mapIso (twistedBaseChange σ A)).inv_hom_id

private theorem semilinearPoint_natural (σ : Gal(K/F)) {A B : GroupScheme F}
    {R U : TestAlgebra K} (a : SemilinearTestMap σ R U)
    (f : (groupBaseChange F K).obj A ⟶ (groupBaseChange F K).obj B)
    (p : Points ((groupBaseChange F K).obj A).X R) :
    semilinearPoint B a (p ≫ f.hom.hom) =
      semilinearPoint A a p ≫ (scalarMorphism σ f).hom.hom := by
  apply Over.OverMorphism.ext
  change (semilinearPoint B a (p ≫ f.hom.hom)).left =
    (semilinearPoint A a p).left ≫ (scalarMorphism σ f).hom.hom.left
  simp only [semilinearPoint_left, scalarMorphism_left, Over.comp_left, Category.assoc,
    ← Category.assoc (scalarTransport σ⁻¹ A.X), scalarTransport_cancel, Category.id_comp]

private theorem semilinearPoint_map {σ : Gal(K/F)} (A : GroupScheme F) {R S U V : TestAlgebra K}
    (a : SemilinearTestMap σ R U) (b : SemilinearTestMap σ S V)
    (f : R ⟶ S) (g : U ⟶ V) (h : b.hom.comp f.hom.toRingHom = g.hom.toRingHom.comp a.hom)
    (p : Points ((groupBaseChange F K).obj A).X R) :
    semilinearPoint A b (mapPoints f p) = mapPoints g (semilinearPoint A a p) := by
  apply (baseChangePoints F K A.X V).injective
  rw [semilinearPoint_apply, baseChangePointsNaturality, baseChangePointsNaturality,
    semilinearPoint_apply, ← mapPoints_comp, ← mapPoints_comp]
  congr 1
  exact CommAlgCat.hom_ext (AlgHom.toRingHom_injective h)

private theorem semilinearPoint_unit {σ : Gal(K/F)} {R U : TestAlgebra K}
    (a : SemilinearTestMap σ R U) (s : Rˣ) :
    semilinearPoint M a (unitPoint R s ≫ (E).hom.hom.hom) =
      unitPoint U (Units.map a.hom.toMonoidHom s) ≫ (E).hom.hom.hom := by
  apply (baseChangePoints F K (M).X U).injective
  have h (V : TestAlgebra K) (t : Vˣ) :
      baseChangePoint F K (M).X V (unitPoint V t ≫ (E).hom.hom.hom) =
        unitPoint ((restrictTestAlgebra F K).obj V) t := multiplicativeBaseChange_unit K V t
  rw [semilinearPoint_apply, h, h]
  exact LinearAlgebraicGroups.CocharacterDynamics.mapPoints_unitPoint a.restrict s

private theorem scalarCharacter_value {σ : Gal(K/F)} {T : GroupScheme F} {R U : TestAlgebra K}
    (a : SemilinearTestMap σ R U) (χ : Character ((groupBaseChange F K).obj T))
    (p : Points ((groupBaseChange F K).obj T).X R) :
    characterValue (scalarCharacter σ χ) U (semilinearPoint T a p) =
      a.hom (characterValue χ R p) := by
  let s := unitEquiv R (p ≫ χ.hom.hom)
  have hs : p ≫ χ.hom.hom = unitPoint R s :=
    (unitEquiv R).injective (unitEquiv_unitPoint R s).symm
  have h := semilinearPoint_natural σ a (χ ≫ (E).hom) p
  rw [← scalarCharacter_comparison σ χ] at h
  simp only [Grp.comp_hom_hom] at h
  have h' : semilinearPoint (M) a ((p ≫ χ.hom.hom) ≫ (E).hom.hom.hom) =
    (semilinearPoint T a p ≫ (scalarCharacter σ χ).hom.hom) ≫ (E).hom.hom.hom := by
    simpa only [Category.assoc] using h
  rw [hs, semilinearPoint_unit] at h'
  have hu : semilinearPoint T a p ≫ (scalarCharacter σ χ).hom.hom =
      unitPoint U (Units.map a.hom.toMonoidHom s) :=
    (Iso.cancel_iso_hom_right _ _ ((Grp.forget _).mapIso E)).mp h'.symm
  have value {V : TestAlgebra K} {B : GroupScheme K} (x : Character B) (q : Points B.X V)
      (v : Vˣ) (hv : q ≫ x.hom.hom = unitPoint V v) : characterValue x V q = (v : V) := by
    let A := CommAlgCat.of K (MonoidAlgebra K Specs.DiagonalizableGroups.IntegerCharacters.{u})
    let w : A ⟶ V := CommAlgCat.ofHom (CocharacterDynamics.unitCoordinates V v)
    let F := algSpec.fullyFaithful (R := CommRingCat.of K)
    have hw : (F.preimage ((testSpec K).map w.op)).unop = w :=
      congrArg Quiver.Hom.unop (F.preimage_map w.op)
    unfold characterValue
    dsimp only
    rw [hv]
    change (F.preimage ((testSpec K).map w.op)).unop.hom (MonoidAlgebra.single
      Specs.DiagonalizableGroups.integerGenerator 1) = v.val
    rw [hw]
    change CocharacterDynamics.unitCoordinates V v (MonoidAlgebra.single
      Specs.DiagonalizableGroups.integerGenerator 1) = v.val
    simp only [CocharacterDynamics.unitCoordinates, MonoidAlgebra.lift_single, one_smul]
    change (↑(v ^ (1 : ℤ)) : V) = ↑v
    rw [zpow_one]
  rw [value _ _ _ hu, value _ _ _ hs]
  rfl

end SemilinearPoints

section ScalarRoots

open Specs.AdjointRepresentation (dualMap constants scale reduction)
open Specs.CharacterPairing (absoluteRoots adjointWeightVectors)
open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open scoped MonoidAlgebra
open private integerExponent integerExponent_zpow from LinearAlgebraicGroups.RootData.CharacterPairing

private theorem scalarCocharacter_point {σ : Gal(K/F)} {T : GroupScheme F} {R U : TestAlgebra K}
    (a : SemilinearTestMap σ R U) (c : Cocharacter ((groupBaseChange F K).obj T))
    (s : Rˣ) :
    semilinearPoint T a (cocharacterPoint c R s) =
      cocharacterPoint (scalarCocharacter σ c) U (Units.map a.hom.toMonoidHom s) := by
  have h := semilinearPoint_natural σ a ((E).inv ≫ c)
    (unitPoint R s ≫ (E).hom.hom.hom)
  rw [semilinearPoint_unit, ← scalarCocharacter_comparison σ c] at h
  change semilinearPoint T a ((unitPoint R s ≫ (E).hom.hom.hom) ≫
      (E).inv.hom.hom ≫ c.hom.hom) =
    (unitPoint U (Units.map a.hom.toMonoidHom s) ≫ (E).hom.hom.hom) ≫
      (E).inv.hom.hom ≫ (scalarCocharacter σ c).hom.hom at h
  have he {X : SchemeOver K} (f : (multiplicativeGroup K).X ⟶ X) :
      (E).hom.hom.hom ≫ (E).inv.hom.hom ≫ f = f :=
    ((Grp.forget (SchemeOver K)).mapIso (E)).hom_inv_id_assoc f
  change semilinearPoint T a (unitPoint R s ≫ c.hom.hom) =
    unitPoint U (Units.map a.hom.toMonoidHom s) ≫ (scalarCocharacter σ c).hom.hom
  simpa only [Category.assoc, he] using h

private theorem scalarPairing (σ : Gal(K/F)) {T : GroupScheme F}
    (χ : Character ((groupBaseChange F K).obj T))
    (c : Cocharacter ((groupBaseChange F K).obj T)) :
    pairing _ (scalarCharacter σ χ) (scalarCocharacter σ c) = pairing _ χ c := by
  let R := CommAlgCat.of K (MonoidAlgebra K IntegerCharacters.{u})
  let a := semilinearSourceMap σ R
  let s : (semilinearSource σ R)ˣ :=
    (MonoidAlgebra.of K IntegerCharacters).toHomUnits integerGenerator
  have h := scalarCharacter_value a χ (cocharacterPoint c (semilinearSource σ R) s)
  rw [scalarCocharacter_point,
    (LinearAlgebraicGroups.RootData.CharacterPairing.characterPairingComposition _ _ _).2,
    (LinearAlgebraicGroups.RootData.CharacterPairing.characterPairingComposition _ _ _).2] at h
  let m := pairing ((groupBaseChange F K).obj T) (scalarCharacter σ χ) (scalarCocharacter σ c)
  let n := pairing ((groupBaseChange F K).obj T) χ c
  have hv (j : ℤ) :
      (s ^ j).val =
        MonoidAlgebra.of K IntegerCharacters (integerGenerator ^ j) :=
    congrArg Units.val (map_zpow (MonoidAlgebra.of K IntegerCharacters).toHomUnits integerGenerator j).symm
  change (s ^ m).val =
    (s ^ n).val at h
  rw [hv m, hv n] at h
  have h' := MonoidAlgebra.of_injective h
  exact (integerExponent_zpow.{u} m).symm.trans ((congrArg integerExponent.{u} h').trans (integerExponent_zpow.{u} n))

private def scalarLie (A : GroupScheme F) (σ : Gal(K/F))
    (v : Lie K ((groupBaseChange F K).obj A)) : Lie K ((groupBaseChange F K).obj A) := by
  let a := semilinearFieldMap σ
  let R := CommAlgCat.of K K
  refine Additive.ofMul ⟨semilinearPoint A a.dual v.toMul.val, ?_⟩
  change mapPoints (reduction R) (semilinearPoint A a.dual v.toMul.val) = 1
  rw [← semilinearPoint_map A a.dual a (reduction R) (reduction R) rfl]
  have hv : mapPoints (reduction R) v.toMul.val = 1 := v.toMul.property
  rw [hv, map_one]

private theorem scalarLie_ne_zero (A : GroupScheme F) (σ : Gal(K/F))
    {v : Lie K ((groupBaseChange F K).obj A)} (hv : v ≠ 0) : scalarLie A σ v ≠ 0 := by
  intro h
  apply hv
  apply Subtype.ext
  let a := (semilinearFieldMap σ).dual
  have hinj : Function.Bijective a.hom := by
    constructor
    · intro v w e
      apply TrivSqZeroExt.ext
      · exact σ.injective (congrArg TrivSqZeroExt.fst e)
      · exact σ.injective (congrArg TrivSqZeroExt.snd e)
    · intro v
      exact ⟨(σ.symm v.fst, σ.symm v.snd), TrivSqZeroExt.ext (σ.apply_symm_apply _)
        (σ.apply_symm_apply _)⟩
  apply (semilinearPoint_bijective A a hinj).injective
  change semilinearPoint A a v.toMul.val = semilinearPoint A a 1
  rw [map_one]
  exact congrArg (fun v : Lie K ((groupBaseChange F K).obj A) ↦ v.toMul.val) h

private theorem scalarWeightVector {A : GroupScheme F} (T : ClosedSubgroup A)
    (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
    (σ : Gal(K/F)) (χ : Character ((groupBaseChange F K).obj T.group))
    (v : Lie K ((groupBaseChange F K).obj A))
    (hv : v ∈ adjointWeightVectors (GeometricRadicals.baseChangedSubgroup K T hT) χ) :
    scalarLie A σ v ∈
      adjointWeightVectors (GeometricRadicals.baseChangedSubgroup K T hT) (scalarCharacter σ χ) := by
  let TK := GeometricRadicals.baseChangedSubgroup K T hT
  let i := (groupBaseChange F K).map T.inclusion
  intro U u
  let R := semilinearSource σ U
  let a := semilinearSourceMap σ U
  obtain ⟨t, ht⟩ := (semilinearPoint_bijective T.group a Function.bijective_id).surjective u
  let R₀ := CommAlgCat.of K K
  let b := semilinearFieldMap σ
  let f : R₀ ⟶ R := ConcreteCategory.ofHom (C := CommAlgCat K) (X := R₀) (Y := R)
    (@Algebra.ofId K R _ _ R.algebra)
  let g : R₀ ⟶ U := ConcreteCategory.ofHom (C := CommAlgCat K) (X := R₀) (Y := U)
    (@Algebra.ofId K U _ _ U.algebra)
  let p := mapPoints (dualMap f) v.toMul.val
  let z := mapPoints (constants R) (t ≫ i.hom.hom)
  have h := hv R t
  change z * p * z⁻¹ = mapPoints (scale R (characterValue χ R t)) p at h
  have hp : semilinearPoint A a.dual p =
      mapPoints (dualMap g) (scalarLie A σ v).toMul.val := by
    apply semilinearPoint_map A b.dual a.dual (dualMap f) (dualMap g) _ v.toMul.val
    apply RingHom.ext
    intro v
    exact TrivSqZeroExt.ext (a.commutes v.fst) (a.commutes v.snd)
  have hz : semilinearPoint A a.dual z = mapPoints (constants U) (u ≫ i.hom.hom) := by
    have hcomm : a.dual.hom.comp (constants R).hom.toRingHom =
        (constants U).hom.toRingHom.comp a.hom := by
      apply RingHom.ext
      intro v
      exact TrivSqZeroExt.ext rfl (map_zero a.hom)
    change semilinearPoint A a.dual (mapPoints (constants R) (t ≫ i.hom.hom)) = _
    rw [semilinearPoint_map A a a.dual (constants R) (constants U) hcomm,
      semilinearPoint_natural σ a i t]
    rw [show scalarMorphism σ i = i from scalarMorphism_baseChange σ T.inclusion, ht]
  have hχ : characterValue (scalarCharacter σ χ) U u = a.hom (characterValue χ R t) := by
    rw [← ht]
    exact scalarCharacter_value a χ t
  have hs : a.dual.hom.comp (scale R (characterValue χ R t)).hom.toRingHom =
      (scale U (characterValue (scalarCharacter σ χ) U u)).hom.toRingHom.comp a.dual.hom := by
    apply RingHom.ext
    intro v
    apply TrivSqZeroExt.ext
    · rfl
    · change a.hom (characterValue χ R t * v.snd) =
        characterValue (scalarCharacter σ χ) U u * a.hom v.snd
      rw [map_mul, hχ]
  have e := congrArg (semilinearPoint A a.dual) h
  rw [map_mul, map_mul, map_inv, hp, hz,
    semilinearPoint_map A a.dual a.dual _ _ hs p, hp] at e
  exact e

private theorem scalarRoot {A : GroupScheme F} (T : ClosedSubgroup A)
    (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
    (σ : Gal(K/F)) (χ : Character ((groupBaseChange F K).obj T.group))
    (hχ : χ ∈ absoluteRoots (GeometricRadicals.baseChangedSubgroup K T hT)) :
    scalarCharacter σ χ ∈ absoluteRoots (GeometricRadicals.baseChangedSubgroup K T hT) := by
  obtain ⟨hne, v, hv, hv0⟩ := hχ
  refine ⟨?_, scalarLie A σ v, scalarWeightVector T hT σ χ v hv, scalarLie_ne_zero A σ hv0⟩
  intro h
  apply hne
  exact (scalarCharacterEquiv σ T.group).injective (h.trans (scalarCharacter_one σ).symm)

end ScalarRoots

section ScalarWeyl

open Specs.AbstractPairing (Datum)
open Specs.DatumAndWeyl (Identification)
open Specs.RankOneFlag (IsGeometricallyMaximal)
open Specs.GeometricRadicals (baseChangedSubgroup IsSplitTorus)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open private rationalSectionsEquiv labelConjugation inducedConjugation_unique
  from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private twistedSections twist_conjugation conjugationIso comp_conjugation conjugates_iff_iso twistBaseChangeIso
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private normalizes_of_conjugates_self from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private fibreTorsor splitFibrePoint from LinearAlgebraicGroups.Reductive.WeylScheme

private def scalarMorphismIso (σ : Gal(K/F)) {A B : GroupScheme F}
    (e : (groupBaseChange F K).obj A ≅ (groupBaseChange F K).obj B) :
    (groupBaseChange F K).obj A ≅ (groupBaseChange F K).obj B where
  hom := scalarMorphism σ e.hom
  inv := scalarMorphism σ e.inv
  hom_inv_id := by rw [← scalarMorphism_comp, Iso.hom_inv_id, scalarMorphism_id]
  inv_hom_id := by rw [← scalarMorphism_comp, Iso.inv_hom_id, scalarMorphism_id]

private abbrev scalarSection (σ : Gal(K/F)) (A : GroupScheme F) := twistedSections σ⁻¹ A

private theorem scalarSection_conjugation (σ : Gal(K/F)) (A : GroupScheme F)
    (r : 𝟙_ (SchemeOver K) ⟶ ((groupBaseChange F K).obj A).X) :
    scalarMorphism σ (conjugationIso r).hom = (conjugationIso (scalarSection σ A r)).hom := by
  change (twistedBaseChange σ⁻¹ A).inv ≫
    (twistGroups σ⁻¹).map (conjugationIso r).hom ≫ (twistedBaseChange σ⁻¹ A).hom = _
  rw [twist_conjugation, Iso.inv_hom_id_assoc]

private theorem scalarSection_baseChange (σ : Gal(K/F)) (A : GroupScheme F)
    (r : 𝟙_ (SchemeOver F) ⟶ A.X) :
    scalarSection σ A (scalarExtendedRationalPoint K r) = scalarExtendedRationalPoint K r := by
  let B := baseChange F K
  let f := twist σ⁻¹
  let e := twistBaseChangeIso σ⁻¹
  let a := Functor.Monoidal.εIso B
  let b := Functor.Monoidal.εIso f
  have hnat := e.hom.naturality r
  change f.map (B.map r) ≫ (e.app A.X).hom = (e.app (𝟙_ (SchemeOver F))).hom ≫ B.map r at hnat
  change b.hom ≫ f.map (a.hom ≫ B.map r) ≫ (e.app A.X).hom = a.hom ≫ B.map r
  rw [Functor.map_comp, Category.assoc, hnat]
  have he : b.hom ≫ f.map a.hom ≫ (e.app (𝟙_ (SchemeOver F))).hom = a.hom := by
    apply (Iso.cancel_iso_inv_right _ _ a).mp
    exact (isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _
  simpa only [Category.assoc] using congrArg (· ≫ B.map r) he

variable {G : AffineAlgebraicGroup F} {T : ClosedSubgroup G.val}
  {hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left}

variable [IsCommMonObj (baseChangedSubgroup K T hT).group.X] {D : Datum (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT)}
variable (A : Identification D)

private theorem absoluteLabelLifts (hSplit : IsSplitTorus (baseChangedSubgroup K T hT).group)
    (w : D.rootDatum.weylGroup) :
    ∃ n : 𝟙_ (SchemeOver K) ⟶ A.normalizer.group.X,
      n ≫ A.quotient.hom.hom = A.image.constantGroup.sectionPoint (A.labelEquiv w) := by
  let N := closedSubgroupAlgebraicGroup A.normalizer
  let T' : ClosedSubgroup N.val := ⟨(baseChangedSubgroup K T hT).group, A.torusInclusion, A.torusClosed⟩
  let x := A.image.constantGroup.sectionPoint (A.labelEquiv w)
  exact splitFibrePoint T' hSplit A.quotient x (fibreTorsor T' A.quotient A.isQuotient x)

private theorem scalarRepresentative (σ : Gal(K/F)) {w : D.rootDatum.weylGroup}
    {r : 𝟙_ (SchemeOver K) ⟶ A.normalizer.group.X}
    (hr : r ≫ A.quotient.hom.hom = A.image.constantGroup.sectionPoint (A.labelEquiv w)) :
    ∃ (v : D.rootDatum.weylGroup) (s : 𝟙_ (SchemeOver K) ⟶ A.normalizer.group.X),
      s ≫ A.normalizer.inclusion.hom.hom =
        scalarSection σ G.val (r ≫ A.normalizer.inclusion.hom.hom) ∧
      s ≫ A.quotient.hom.hom = A.image.constantGroup.sectionPoint (A.labelEquiv v) ∧
        A.image.conjugation (A.labelEquiv v) =
          scalarMorphismIso σ (A.image.conjugation (A.labelEquiv w)) := by
  let g := r ≫ A.normalizer.inclusion.hom.hom
  let k := scalarSection σ G.val g
  let e := A.image.conjugation (A.labelEquiv w)
  have hrT := labelConjugation A.image (A.labelEquiv w) r hr
  have h : e.hom ≫ (baseChangedSubgroup K T hT).inclusion = (baseChangedSubgroup K T hT).inclusion ≫ (conjugationIso g).hom :=
    Grp.hom_ext _ _ (hrT.trans (comp_conjugation
      g (baseChangedSubgroup K T hT).inclusion.hom.hom).symm)
  have h' : (scalarMorphismIso σ e).hom ≫ (baseChangedSubgroup K T hT).inclusion =
      (baseChangedSubgroup K T hT).inclusion ≫ (conjugationIso k).hom := by
    have hh := congrArg (scalarMorphism σ) h
    rw [scalarMorphism_comp, scalarMorphism_comp, scalarSection_conjugation] at hh
    change scalarMorphism σ e.hom ≫ scalarMorphism σ ((groupBaseChange F K).map T.inclusion) =
      scalarMorphism σ ((groupBaseChange F K).map T.inclusion) ≫ (conjugationIso k).hom at hh
    rw [scalarMorphism_baseChange] at hh
    exact hh
  have hC : Specs.GeometricBorelConjugacy.ConjugatesSubgroups k (baseChangedSubgroup K T hT) (baseChangedSubgroup K T hT) :=
    (conjugates_iff_iso k (baseChangedSubgroup K T hT) (baseChangedSubgroup K T hT)).mpr ⟨scalarMorphismIso σ e, h'⟩
  obtain ⟨s, hs⟩ := (A.representsNormalizer _ k).mp (normalizes_of_conjugates_self (baseChangedSubgroup K T hT) hC)
  change s ≫ A.normalizer.inclusion.hom.hom = k at hs
  obtain ⟨q, hq⟩ := rationalSectionsEquiv A.image.constantGroup
  let v := A.labelEquiv.symm (q.symm (s ≫ A.quotient.hom.hom))
  have hvs : s ≫ A.quotient.hom.hom = A.image.constantGroup.sectionPoint (A.labelEquiv v) := by
    rw [show A.labelEquiv v = q.symm (s ≫ A.quotient.hom.hom) from A.labelEquiv.apply_symm_apply _,
      ← hq, q.apply_symm_apply]
  refine ⟨v, s, hs, hvs, ?_⟩
  apply inducedConjugation_unique (labelConjugation A.image _ s hvs)
  rw [hs]
  exact (congrArg (fun f ↦ f.hom.hom) h').trans
    (comp_conjugation k (baseChangedSubgroup K T hT).inclusion.hom.hom)

private theorem scalarWeightOfConjugation (σ : Gal(K/F)) (w v : D.rootDatum.weylGroup)
    (he : A.image.conjugation (A.labelEquiv v) =
      scalarMorphismIso σ (A.image.conjugation (A.labelEquiv w)))
    (χ : Character (baseChangedSubgroup K T hT).group) :
    v.val.weightEquiv (Additive.ofMul (scalarCharacter σ χ)) =
      Additive.ofMul (scalarCharacter σ (Additive.toMul (w.val.weightEquiv (Additive.ofMul χ)))) := by
  rw [A.characterAction, A.characterAction, A.image.characterAction, A.image.characterAction, he]
  congr 1
  change scalarMorphism σ (A.image.conjugation (A.labelEquiv w)).inv ≫ scalarCharacter σ χ =
    scalarCharacter σ ((A.image.conjugation (A.labelEquiv w)).inv ≫ χ)
  simp only [scalarCharacter, scalarMorphism_comp, Category.assoc]

private theorem scalarWeyl_transport (hSplit : IsSplitTorus (baseChangedSubgroup K T hT).group)
    (σ : Gal(K/F)) (w : D.rootDatum.weylGroup) :
    ∃ v : D.rootDatum.weylGroup,
      A.image.conjugation (A.labelEquiv v) =
        scalarMorphismIso σ (A.image.conjugation (A.labelEquiv w)) ∧
      ∀ χ : Character (baseChangedSubgroup K T hT).group,
        v.val.weightEquiv (Additive.ofMul (scalarCharacter σ χ)) =
          Additive.ofMul (scalarCharacter σ (Additive.toMul (w.val.weightEquiv (Additive.ofMul χ)))) := by
  obtain ⟨r, hr⟩ := absoluteLabelLifts A hSplit w
  obtain ⟨v, s, _, _, he⟩ := scalarRepresentative A σ hr
  exact ⟨v, he, scalarWeightOfConjugation A σ w v he⟩

end ScalarWeyl

section BasedScalarDatum

open RootPairing
open Specs.AbstractPairing (Datum Root)
open Specs.DatumAndWeyl (Identification)
open Specs.GeometricRadicals (baseChangedSubgroup IsSplitTorus)
open Specs.Unipotent (baseChangedAlgebraicGroup)

/-- Two reflections with the same root line have the same coefficient form
when both belong to a finite Weyl group. Their product acts as a shear. -/
private theorem finiteWeylReflections_sameCoefficient
    {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Module.IsTorsionFree ℤ X]
    (P : RootPairing I ℤ X Y) [Finite P.weylGroup]
    (r s : P.weylGroup) {z : X} (hz : z ≠ 0) (a b : X →ₗ[ℤ] ℤ)
    (ha : a z = 2) (hb : b z = 2)
    (hr : ∀ x, r.val.weightEquiv x = x - a x • z)
    (hs : ∀ x, s.val.weightEquiv x = x - b x • z) :
    a = b := by
  let w := r * s
  let c := b - a
  have hc : c z = 0 := by simp [c, ha, hb]
  have hw (x : X) : w.val.weightEquiv x = x + c x • z := by
    change (r.val * s.val).weightEquiv x = _
    rw [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.weightEquiv_comp_toLin, LinearEquiv.trans_apply, hs, hr]
    have he : a (x - b x • z) = a x - 2 * b x := by
      simp [ha, mul_comm]
    rw [he]
    simp only [c, LinearMap.sub_apply, two_mul, sub_smul, add_smul]
    abel
  have hp (n : ℕ) (x : X) : (w ^ n).val.weightEquiv x = x + ((n : ℤ) * c x) • z := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      change (w.val * (w ^ n).val).weightEquiv x = _
      rw [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.weightEquiv_comp_toLin, LinearEquiv.trans_apply, ih, hw]
      have hcx : c (x + ((n : ℤ) * c x) • z) = c x := by simp [hc]
      rw [hcx, Nat.cast_succ, add_mul, one_mul, add_smul, add_assoc]
  obtain ⟨n, hn, hnw⟩ := (isOfFinOrder_of_finite w).exists_pow_eq_one
  apply LinearMap.ext
  intro x
  have h := hp n x
  rw [hnw] at h
  change x = x + ((n : ℤ) * c x) • z at h
  have h' : ((n : ℤ) * c x) • z = 0 := by
    apply add_left_cancel (a := x)
    rw [← h, add_zero]
  have hc' : c x = 0 := (mul_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hz)).resolve_left
    (by exact_mod_cast hn.ne')
  exact (sub_eq_zero.mp hc').symm

variable {G : AffineAlgebraicGroup F} {T : ClosedSubgroup G.val}
  {hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left}
  [IsCommMonObj (baseChangedSubgroup K T hT).group.X]
  {D : Datum (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT)}

private def scalarRootEquiv (σ : Gal(K/F)) : Equiv.Perm (Root (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT)) where
  toFun i := ⟨scalarCharacter σ i.val, scalarRoot T hT σ i.val i.property⟩
  invFun i := ⟨scalarCharacter σ⁻¹ i.val, scalarRoot T hT σ⁻¹ i.val i.property⟩
  left_inv i := Subtype.ext ((scalarCharacterEquiv σ T.group).left_inv i.val)
  right_inv i := Subtype.ext ((scalarCharacterEquiv σ T.group).right_inv i.val)

private abbrev scalarWeightEquiv (T : GroupScheme F) (σ : Gal(K/F)) :=
  (scalarCharacterEquiv σ T).toAdditive.toIntLinearEquiv

private theorem scalarWeight_root (σ : Gal(K/F)) (i : Root (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT)) :
    scalarWeightEquiv T.group σ (D.rootDatum.root i) =
      D.rootDatum.root (scalarRootEquiv σ i) := by
  rw [D.root_eq, D.root_eq]
  rfl

private theorem scalarWeight_coroot (A : Identification D) (hSplit : IsSplitTorus
    (baseChangedSubgroup K T hT).group) (σ : Gal(K/F)) (i : Root (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT))
    (x : Additive (Character (baseChangedSubgroup K T hT).group)) :
    D.rootDatum.coroot' (scalarRootEquiv σ i) (scalarWeightEquiv T.group σ x) =
      D.rootDatum.coroot' i x := by
  let P := D.rootDatum
  let L : Additive (Character (baseChangedSubgroup K T hT).group) ≃ₗ[ℤ]
      Additive (Character (baseChangedSubgroup K T hT).group) :=
    scalarWeightEquiv T.group σ
  let j : Root (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT) := scalarRootEquiv σ i
  let s := weylGroup.ofIdx P j
  let r := weylGroup.ofIdx P i
  letI := A.image.finite
  letI : Finite P.weylGroup := Finite.of_injective _ A.labelEquiv.injective
  letI := D.freeCharacters
  have hroot : L (P.root i) = P.root j := scalarWeight_root (D := D) σ i
  obtain ⟨v, _, hv⟩ := scalarWeyl_transport A hSplit σ r
  let a := (P.coroot' i).comp L.symm.toLinearMap
  have ha : a (P.root j) = 2 := by
    change P.coroot' i (L.symm (P.root j)) = 2
    rw [← hroot, L.symm_apply_apply, P.coroot_root_two]
  have href (y : Additive (Character (baseChangedSubgroup K T hT).group)) :
      v.val.weightEquiv y = y - a y • P.root j := by
    have he : v.val.weightEquiv (L (L.symm y)) = L (P.reflection i (L.symm y)) :=
      hv (L.symm y).toMul
    rw [P.reflection_apply] at he
    have hsub : L (L.symm y - P.coroot' i (L.symm y) • P.root i) =
        L (L.symm y) - L (P.coroot' i (L.symm y) • P.root i) := by
      exact L.toLinearMap.map_sub (L.symm y) (P.coroot' i (L.symm y) • P.root i)
    have hsmul : L (P.coroot' i (L.symm y) • P.root i) =
        P.coroot' i (L.symm y) • L (P.root i) := L.map_smul _ _
    rw [hsub, hsmul, L.apply_symm_apply, hroot] at he
    exact he
  have hs (y : Additive (Character (baseChangedSubgroup K T hT).group)) :
      s.val.weightEquiv y = y - P.coroot' j y • P.root j := P.reflection_apply j y
  have hb : P.coroot' j (P.root j) = 2 := P.coroot_root_two j
  have hf := finiteWeylReflections_sameCoefficient P v s (P.ne_zero j) a (P.coroot' j)
    ha hb href hs
  change (P.coroot' j) (L x) = _
  rw [← hf]
  change P.coroot' i (L.symm (L x)) = _
  rw [L.symm_apply_apply]

private def scalarDatumAut (A : Identification D)
    (hSplit : IsSplitTorus (baseChangedSubgroup K T hT).group) (σ : Gal(K/F)) : D.rootDatum.Aut := by
  let P := D.rootDatum
  let a := scalarWeightEquiv T.group σ
  let b := P.flip.toPerfPair.trans (a.dualMap.trans P.flip.toPerfPair.symm)
  have hb (y) : P.flip.toPerfPair (b y) = a.dualMap (P.flip.toPerfPair y) :=
    P.flip.toPerfPair.apply_symm_apply _
  refine {
    weightMap := a.toLinearMap
    coweightMap := b.toLinearMap
    indexEquiv := scalarRootEquiv σ
    weight_coweight_transpose := ?_
    root_weightMap := funext (scalarWeight_root (D := D) σ)
    coroot_coweightMap := ?_
    bijective_weightMap := a.bijective
    bijective_coweightMap := b.bijective }
  · ext y x
    change (a.dualMap (P.flip.toPerfPair y)) x = (P.flip.toPerfPair (b y)) x
    rw [hb]
    rfl
  · funext j
    let i := (scalarRootEquiv (T := T) (hT := hT) σ).symm j
    have hj : scalarRootEquiv σ i = j := (scalarRootEquiv σ).apply_symm_apply j
    apply P.flip.toPerfPair.injective
    change P.flip.toPerfPair (b (P.coroot j)) = P.flip.toPerfPair (P.coroot i)
    rw [hb]
    ext x
    change P.coroot' j (a x) = P.coroot' i x
    rw [← hj]
    exact scalarWeight_coroot A hSplit σ i x

private def scalarDatumAction (A : Identification D)
    (hSplit : IsSplitTorus (baseChangedSubgroup K T hT).group) :
    Gal(K/F) →* D.rootDatum.Aut where
  toFun := scalarDatumAut A hSplit
  map_one' := by
    apply RootPairing.Equiv.weightHom_injective D.rootDatum
    apply LinearEquiv.ext
    intro x
    change Additive.ofMul (scalarCharacter 1 (Additive.toMul x)) = x
    rw [scalarCharacter_identity]
    rfl
  map_mul' σ τ := by
    apply RootPairing.Equiv.weightHom_injective D.rootDatum
    apply LinearEquiv.ext
    intro x
    change (scalarDatumAut A hSplit (σ * τ)).weightEquiv x =
      (scalarDatumAut A hSplit σ * scalarDatumAut A hSplit τ).weightEquiv x
    rw [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.weightEquiv_comp_toLin]
    change Additive.ofMul (scalarCharacter (σ * τ) (Additive.toMul x)) =
      Additive.ofMul (scalarCharacter σ (scalarCharacter τ (Additive.toMul x)))
    rw [scalarCharacter_action]

private theorem scalarDatum_coweight (A : Identification D)
    (hSplit : IsSplitTorus (baseChangedSubgroup K T hT).group) (σ : Gal(K/F))
    (c : Cocharacter (baseChangedSubgroup K T hT).group) :
    (scalarDatumAction A hSplit σ).coweightEquiv.symm (Additive.ofMul c) =
      Additive.ofMul (scalarCocharacter σ c) := by
  let e := scalarDatumAction A hSplit σ
  apply e.coweightEquiv.injective
  rw [e.coweightEquiv.apply_symm_apply]
  apply D.rootDatum.flip.toPerfPair.injective
  ext x
  change D.rootDatum.toLinearMap x (Additive.ofMul c) =
    D.rootDatum.toLinearMap x (e.coweightEquiv (Additive.ofMul (scalarCocharacter σ c)))
  rw [← e.toLinearMap_weightEquiv]
  change D.rootDatum.toLinearMap x (Additive.ofMul c) =
    D.rootDatum.toLinearMap (Additive.ofMul (scalarCharacter σ x.toMul))
      (Additive.ofMul (scalarCocharacter σ c))
  rw [D.pairing_eq]
  exact (D.pairing_eq x.toMul c).trans (scalarPairing σ x.toMul c).symm

private theorem scalarDatum_isScalarAction (A : Identification D)
    (hSplit : IsSplitTorus (baseChangedSubgroup K T hT).group) :
    IsScalarAction T hT (inferInstance) D (E) (scalarDatumAction A hSplit) := by
  constructor
  · intro σ χ
    change (scalarCharacter σ χ ≫ (E).hom).hom.hom.left = _
    rw [scalarCharacter_comparison, scalarMorphism_left]
  · intro σ c
    rw [scalarDatum_coweight]
    change ((E).inv ≫ scalarCocharacter σ c).hom.hom.left = _
    rw [scalarCocharacter_comparison, scalarMorphism_left]

end BasedScalarDatum

section FixedComparison

open RootPairing
open Specs.AbstractPairing (Datum)
open Specs.DatumAndWeyl (Identification)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (baseChangedSubgroup IsReductive IsSplitTorus)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.RankOneFlag (SameSubgroup)
open Specs.SchemeDerivedGroup (FactorsThrough IsSubgroupOf)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open Specs.Relative.RelativeWeylScheme (QuotientData rationalProjection)
open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private descendInvariantGroupMorphism from LinearAlgebraicGroups.Relative.RationalCocharacter
open private extendSubgroup subgroup_extend from LinearAlgebraicGroups.RootData.BorelNormalizer
open private baseChange_map_injective constant_sections_after_scalar_extension
  scalarExtendedPoint_natural from LinearAlgebraicGroups.RootData.RankOneFlag
open private pushSubgroup from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private baseChangeMapIsPullback from LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private mono_over from LinearAlgebraicGroups.Affine.Stabilizers
open private baseChangeKernelSquare from LinearAlgebraicGroups.Affine.Components
open private rationalSectionsEquiv labelConjugation inducedConjugation_unique
  from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private conjugationIso comp_conjugation conjugates_iff_iso
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private normalizes_of_conjugates_self from LinearAlgebraicGroups.Reductive.MaximalToriConjugate

open private factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

private theorem groupBaseChange_injective {X Y : GroupScheme F} :
    Function.Injective ((groupBaseChange F K).map (X := X) (Y := Y)) := by
  intro f g h
  apply Grp.hom_ext
  exact baseChange_map_injective K ((Grp.forget (SchemeOver K)).congr_map h)

private theorem scalarMorphism_descends [IsGalois F K]
    (X Y : AffineAlgebraicGroup F)
    (f : (groupBaseChange F K).obj X.val ⟶ (groupBaseChange F K).obj Y.val)
    (hf : ∀ σ, scalarMorphism σ f = f) :
    ∃ g : X.val ⟶ Y.val, (groupBaseChange F K).map g = f := by
  obtain ⟨A, _, ⟨a⟩⟩ := groupPresentation X
  obtain ⟨B, _, ⟨b⟩⟩ := groupPresentation Y
  let extScalars := groupBaseChange F K
  let f' := extScalars.map a.hom ≫ f ≫ extScalars.map b.inv
  have hh (σ : Gal(K/F)) : twistMorphism σ f' = f' := by
    have h : scalarMorphism σ⁻¹ f' = f' := by
      dsimp only [f']
      rw [scalarMorphism_comp, scalarMorphism_comp,
        show scalarMorphism σ⁻¹ (extScalars.map a.hom) = extScalars.map a.hom from
          scalarMorphism_baseChange σ⁻¹ a.hom,
        show scalarMorphism σ⁻¹ (extScalars.map b.inv) = extScalars.map b.inv from
          scalarMorphism_baseChange σ⁻¹ b.inv,
        hf]
    simpa only [scalarMorphism, inv_inv] using h
  obtain ⟨g, hg⟩ := descendInvariantGroupMorphism B A f' hh
  refine ⟨a.inv ≫ g ≫ b.hom, ?_⟩
  change extScalars.map (a.inv ≫ g ≫ b.hom) = f
  change extScalars.map g = extScalars.map a.hom ≫ f ≫ extScalars.map b.inv at hg
  rw [extScalars.map_comp, extScalars.map_comp, hg]
  simpa only [Category.assoc] using calc
    extScalars.map a.inv ≫ (extScalars.map a.hom ≫ f) ≫
        extScalars.map b.inv ≫ extScalars.map b.hom =
        extScalars.map a.inv ≫ extScalars.map a.hom ≫ f := by
      rw [show extScalars.map b.inv ≫ extScalars.map b.hom = 𝟙 _ from
        (extScalars.mapIso b).inv_hom_id, Category.comp_id]
    _ = f := (extScalars.mapIso a).inv_hom_id_assoc f

private theorem scalarIso_descends [IsGalois F K] (T : AffineAlgebraicGroup F)
    (e : (groupBaseChange F K).obj T.val ≅ (groupBaseChange F K).obj T.val)
    (he : ∀ σ, scalarMorphismIso σ e = e) :
    ∃ t : T.val ≅ T.val, (groupBaseChange F K).map t.hom = e.hom := by
  obtain ⟨f, hf⟩ := scalarMorphism_descends T T e.hom (fun σ ↦ congrArg Iso.hom (he σ))
  obtain ⟨g, hg⟩ := scalarMorphism_descends T T e.inv (fun σ ↦ congrArg Iso.inv (he σ))
  have hh : f ≫ g = 𝟙 _ := groupBaseChange_injective (K := K) (by
    rw [Functor.map_comp, hf, hg, e.hom_inv_id]
    exact ((groupBaseChange F K).map_id _).symm)
  have hi : g ≫ f = 𝟙 _ := groupBaseChange_injective (K := K) (by
    rw [Functor.map_comp, hf, hg, e.inv_hom_id]
    exact ((groupBaseChange F K).map_id _).symm)
  exact ⟨⟨f, g, hh, hi⟩, hf⟩

private theorem largestSplitSubtorus_preserved {T : GroupScheme F} (S : ClosedSubgroup T)
    (hS : IsLargestSplitSubtorus S) (t : T ≅ T) :
    ∃ a : S.group ≅ S.group, a.hom ≫ S.inclusion = S.inclusion ≫ t.hom := by
  obtain ⟨f, hf⟩ := hS.2 (pushSubgroup t S) hS.1
  obtain ⟨g, hg⟩ := hS.2 (pushSubgroup t.symm S) hS.1
  change f ≫ S.inclusion = S.inclusion ≫ t.hom at hf
  change g ≫ S.inclusion = S.inclusion ≫ t.inv at hg
  letI : IsClosedImmersion S.inclusion.hom.hom.left := S.isClosedImmersion
  letI : Mono S.inclusion := (Grp.forget _).mono_of_mono_map
    (f := S.inclusion) (mono_over S.inclusion.hom.hom S.isClosedImmersion)
  have hi : f ≫ g = 𝟙 _ := (cancel_mono S.inclusion).mp (by
    rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc, t.hom_inv_id, Category.comp_id,
      Category.id_comp])
  have hj : g ≫ f = 𝟙 _ := (cancel_mono S.inclusion).mp (by
    rw [Category.assoc, hf, ← Category.assoc, hg, Category.assoc, t.inv_hom_id, Category.comp_id,
      Category.id_comp])
  exact ⟨⟨f, g, hi, hj⟩, hf⟩

variable {G : AffineAlgebraicGroup F} {T : ClosedSubgroup G.val}
  {hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left}
  [IsCommMonObj (baseChangedSubgroup K T hT).group.X]
  {D : Datum (G := baseChangedAlgebraicGroup K G) (baseChangedSubgroup K T hT)}
  (A : Identification D) (hSplit : IsSplitTorus (baseChangedSubgroup K T hT).group)

private theorem scalarWeyl_eq_iff (σ : Gal(K/F)) (w v : D.rootDatum.weylGroup)
    (he : A.image.conjugation (A.labelEquiv v) =
      scalarMorphismIso σ (A.image.conjugation (A.labelEquiv w))) :
    v = w ↔ Commute (scalarDatumAction A hSplit σ) w.val := by
  let L := scalarWeightEquiv T.group σ
  let d := scalarDatumAction A hSplit σ
  have h (x : Additive (Character (baseChangedSubgroup K T hT).group)) :
      v.val.weightEquiv (L x) = L (w.val.weightEquiv x) :=
    scalarWeightOfConjugation A σ w v he x.toMul
  constructor
  · intro hEq
    subst v
    apply RootPairing.Equiv.weightHom_injective D.rootDatum
    apply LinearEquiv.ext
    intro x
    change L (w.val.weightEquiv x) = w.val.weightEquiv (L x)
    exact (h x).symm
  · intro hw
    apply Subtype.ext
    apply RootPairing.Equiv.weightHom_injective D.rootDatum
    apply LinearEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := L.surjective y
    have hw' (x : Additive (Character (baseChangedSubgroup K T hT).group)) :
        L (w.val.weightEquiv x) = w.val.weightEquiv (L x) :=
      congrArg (fun p : D.rootDatum.Aut ↦ p.weightEquiv x) hw.eq
    exact (h x).trans (hw' x)

private theorem rationalAbsoluteLabel_fixed (w : D.rootDatum.weylGroup)
    (r : 𝟙_ (SchemeOver K) ⟶ A.normalizer.group.X)
    (hr : r ≫ A.quotient.hom.hom = A.image.constantGroup.sectionPoint (A.labelEquiv w))
    (n : 𝟙_ (SchemeOver F) ⟶ G.val.X)
    (hn : r ≫ A.normalizer.inclusion.hom.hom = scalarExtendedRationalPoint K n) :
    w ∈ fixedWeyl D.rootDatum (scalarDatumAction A hSplit) := by
  intro σ
  obtain ⟨v, s, hs, hv, he⟩ := scalarRepresentative A σ hr
  rw [hn, scalarSection_baseChange, ← hn] at hs
  letI := A.normalizer.isClosedImmersion
  letI : Mono A.normalizer.inclusion.hom.hom := Over.mono_of_mono_left _
  have hsr : s = r := (cancel_mono A.normalizer.inclusion.hom.hom).mp hs
  obtain ⟨q, hq⟩ := rationalSectionsEquiv A.image.constantGroup
  have hvw : v = w := by
    apply A.labelEquiv.injective
    apply q.injective
    rw [hq, hq, ← hv, hsr, hr]
  exact (scalarWeyl_eq_iff A hSplit σ w v he).mp hvw

set_option maxHeartbeats 1000000 in
private theorem fixedAbsoluteLabel_normalizes [IsGalois F K]
    (S : ClosedSubgroup T.group) (hS : IsLargestSplitSubtorus S)
    (w : D.rootDatum.weylGroup)
    (hw : w ∈ fixedWeyl D.rootDatum (scalarDatumAction A hSplit))
    (r : 𝟙_ (SchemeOver K) ⟶ A.normalizer.group.X)
    (hr : r ≫ A.quotient.hom.hom = A.image.constantGroup.sectionPoint (A.labelEquiv w)) :
    Normalizes ((groupBaseChange F K).map (subgroupOfSubgroup T S).inclusion)
      (r ≫ A.normalizer.inclusion.hom.hom) := by
  let e := A.image.conjugation (A.labelEquiv w)
  have he (σ : Gal(K/F)) : scalarMorphismIso σ e = e := by
    obtain ⟨v, hv, _⟩ := scalarWeyl_transport A hSplit σ w
    have heq : v = w := (scalarWeyl_eq_iff A hSplit σ w v hv).mpr (hw σ)
    subst v
    exact hv.symm
  obtain ⟨t, ht⟩ := scalarIso_descends (closedSubgroupAlgebraicGroup T) e he
  obtain ⟨s, hs⟩ := largestSplitSubtorus_preserved S hS t
  let j := groupBaseChange F K
  let p := r ≫ A.normalizer.inclusion.hom.hom
  let SK := extendSubgroup K (subgroupOfSubgroup T S)
  let TK := baseChangedSubgroup K T hT
  have hg : e.hom ≫ TK.inclusion = TK.inclusion ≫ (conjugationIso p).hom :=
    Grp.hom_ext _ _ ((labelConjugation A.image (A.labelEquiv w) r hr).trans
      (comp_conjugation p TK.inclusion.hom.hom).symm)
  change e.hom ≫ j.map T.inclusion = j.map T.inclusion ≫ (conjugationIso p).hom at hg
  have hSK : (j.mapIso s).hom ≫ SK.inclusion = SK.inclusion ≫ (conjugationIso p).hom := by
    change j.map s.hom ≫ j.map (S.inclusion ≫ T.inclusion) =
      j.map (S.inclusion ≫ T.inclusion) ≫ (conjugationIso p).hom
    simp only [j.map_comp, ← Category.assoc]
    rw [← j.map_comp, hs, j.map_comp, Category.assoc, ht, hg, Category.assoc]
  exact normalizes_of_conjugates_self SK ((conjugates_iff_iso p SK SK).mpr ⟨j.mapIso s, hSK⟩)

set_option maxHeartbeats 1000000 in
private theorem compareWithRationalRepresentative
    {S : ClosedSubgroup G.val} (Q : QuotientData S)
    (hC : SameSubgroup Q.centralizer T)
    (r : 𝟙_ (SchemeOver K) ⟶ A.normalizer.group.X)
    (hr : Normalizes ((groupBaseChange F K).map S.inclusion)
      (r ≫ A.normalizer.inclusion.hom.hom))
    (hLift : ∀ w, ∃ n, rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w) :
    ∃ (w : Q.splitImage.labels) (n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X),
      rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w ∧
      ∀ t : 𝟙_ (SchemeOver K) ⟶ A.normalizer.group.X,
        t ≫ A.normalizer.inclusion.hom.hom =
          scalarExtendedRationalPoint K (n ≫ Q.normalizer.inclusion.hom.hom) →
        t ≫ A.quotient.hom.hom = r ≫ A.quotient.hom.hom := by
  let extScalars := groupBaseChange F K
  let NK := extendSubgroup K Q.normalizer
  let CK := extendSubgroup K Q.centralizer
  let TK := baseChangedSubgroup K T hT
  let p := extScalars.map Q.projection
  obtain ⟨_, hNK⟩ := LinearAlgebraicGroups.normalizerSchemeBaseChange F K S.inclusion
    Q.normalizer S.isClosedImmersion Q.normalizerProperty
  have hNK' : RepresentsSubgroup NK (fun _ g ↦ Normalizes (extScalars.map S.inclusion) g) := hNK
  obtain ⟨s, hs⟩ := (hNK' _ _).mp hr
  change s ≫ NK.inclusion.hom.hom = r ≫ A.normalizer.inclusion.hom.hom at hs
  obtain ⟨w, hw⟩ := constant_sections_after_scalar_extension Q.splitImage.constantGroup K
    (s ≫ p.hom.hom)
  obtain ⟨n, hn⟩ := hLift w
  refine ⟨w, n, hn, ?_⟩
  intro t ht
  let nK : 𝟙_ (SchemeOver K) ⟶ NK.group.X := scalarExtendedRationalPoint K n
  have hnK : nK ≫ p.hom.hom = s ≫ p.hom.hom := by
    have he := scalarExtendedPoint_natural K n Q.projection.hom.hom
    change scalarExtendedRationalPoint K (rationalProjection Q n) = nK ≫ p.hom.hom at he
    rw [← he, hn, hw]
  have hdelta : (nK⁻¹ * s) ≫ p.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hnK, inv_mul_cancel]
  have hclosed : IsClosedImmersion (extScalars.map Q.inclusion).hom.hom.left :=
    MorphismProperty.of_isPullback (baseChangeMapIsPullback K Q.inclusion.hom.hom).flip Q.inclusionClosed
  have hker : IsSchemeKernel p ⟨CK.group, extScalars.map Q.inclusion, hclosed⟩ :=
    baseChangeKernelSquare Q.projection Q.inclusion Q.quotientProperty.1
  have hincl : extScalars.map Q.inclusion ≫ NK.inclusion = CK.inclusion := by
    change extScalars.map Q.inclusion ≫ extScalars.map Q.normalizer.inclusion = extScalars.map Q.centralizer.inclusion
    rw [← extScalars.map_comp, Q.inclusionProperty]
  obtain ⟨d, hd⟩ := (projectionOneIff (G := baseChangedAlgebraicGroup K G) hincl hker _).mp hdelta
  obtain ⟨j, hj⟩ := subgroup_extend K hC.1
  change j ≫ TK.inclusion = CK.inclusion at hj
  have hj' := (Grp.forget _).congr_map hj
  have hs₀ : nK ≫ NK.inclusion.hom.hom = t ≫ A.normalizer.inclusion.hom.hom := by
    rw [ht]
    exact (scalarExtendedPoint_natural K n Q.normalizer.inclusion.hom.hom).symm
  have hdelta' : (t⁻¹ * r) ≫ A.quotient.hom.hom = 1 := by
    apply (projectionOneIff A.inclusion_eq A.isQuotient.1 _).mpr
    refine ⟨d ≫ j.hom.hom, ?_⟩
    change (d ≫ j.hom.hom) ≫ TK.inclusion.hom.hom =
      (t⁻¹ * r) ≫ A.normalizer.inclusion.hom.hom
    change j.hom.hom ≫ TK.inclusion.hom.hom = CK.inclusion.hom.hom at hj'
    change d ≫ CK.inclusion.hom.hom = (nK⁻¹ * s) ≫ NK.inclusion.hom.hom at hd
    rw [Category.assoc, hj', hd, MonObj.mul_comp, GrpObj.inv_comp, hs₀, hs,
      MonObj.mul_comp, GrpObj.inv_comp]
  rw [MonObj.mul_comp, GrpObj.inv_comp, inv_mul_eq_one] at hdelta'
  exact hdelta'

set_option maxHeartbeats 1200000 in
private theorem relativeFixedComparison [IsGalois F K] (hG : IsReductive G)
    (S : ClosedSubgroup T.group) (hS : IsLargestSplitSubtorus S) (B : ClosedSubgroup G.val)
    (hMax : IsMaximalSplitTorus (subgroupOfSubgroup T S))
    (hB : IsMinimalParabolic G B) (hSB : IsSubgroupOf (subgroupOfSubgroup T S) B)
    (hC : RepresentsSubgroup T (fun _ g ↦ Centralizes (subgroupOfSubgroup T S).inclusion g))
    (Q : QuotientData (subgroupOfSubgroup T S)) :
    ∃ e : Q.splitImage.labels ≃* fixedWeyl D.rootDatum (scalarDatumAction A hSplit),
      SameSubgroup Q.centralizer T ∧
      (∀ w, ∃ n, rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w) ∧
      (∀ (n : 𝟙_ (SchemeOver F) ⟶ Q.normalizer.group.X) (w : Q.splitImage.labels),
        rationalProjection Q n = Q.splitImage.constantGroup.sectionPoint w →
        ∃ r : 𝟙_ (SchemeOver K) ⟶ A.normalizer.group.X,
          r ≫ A.normalizer.inclusion.hom.hom =
            scalarExtendedRationalPoint K (n ≫ Q.normalizer.inclusion.hom.hom) ∧
          r ≫ A.quotient.hom.hom = A.image.constantGroup.sectionPoint (A.labelEquiv (e w).val)) := by
  let S₀ := subgroupOfSubgroup T S
  have hsame : SameSubgroup Q.centralizer T :=
    sameSubgroupOfCentralizer S₀.inclusion Q.centralizerProperty hC
  obtain ⟨_, _, _, _, hLift, _, _⟩ :=
    LinearAlgebraicGroups.Relative.RelativeWeylScheme.relativeWeylAction G hG S₀ B hMax hB hSB Q
  obtain ⟨map, hInj, hRep⟩ := relativeWeylEmbedding G hG S₀ B T hMax hB hSB hC Q hT
    inferInstance D A
  have hfixed (w) : map w ∈ fixedWeyl D.rootDatum (scalarDatumAction A hSplit) := by
    obtain ⟨n, hn⟩ := hLift w
    obtain ⟨r, hr, hlabel⟩ := hRep n w hn
    exact rationalAbsoluteLabel_fixed A hSplit (map w) r hlabel _ hr
  let h := map.codRestrict (fixedWeyl D.rootDatum (scalarDatumAction A hSplit)) hfixed
  refine ⟨MulEquiv.ofBijective h ⟨fun _ _ eq ↦ hInj (congrArg Subtype.val eq), ?_⟩,
    hsame, hLift, hRep⟩
  intro x
  obtain ⟨r, hr⟩ := absoluteLabelLifts A hSplit x.val
  have hrS := fixedAbsoluteLabel_normalizes A hSplit S hS x.val x.property r hr
  obtain ⟨w, n, hn, ht⟩ := compareWithRationalRepresentative A Q hsame r hrS hLift
  obtain ⟨t, htG, htLabel⟩ := hRep n w hn
  refine ⟨w, Subtype.ext ?_⟩
  obtain ⟨q, hq⟩ := rationalSectionsEquiv A.image.constantGroup
  apply A.labelEquiv.injective
  apply q.injective
  change q (A.labelEquiv (map w)) = q (A.labelEquiv x.val)
  exact (hq _).trans (htLabel.symm.trans ((ht t htG).trans (hr.trans (hq _).symm)))

end FixedComparison

section Assemble

open RootPairing
open Specs.AbstractPairing (Datum)
open Specs.DatumAndWeyl (Identification)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup IsKBorel)
open Specs.GeometricRadicals (IsReductive IsSplitTorus baseChangedSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open Specs.UnipotentRadicalIntersection (IsSchemeIntersection)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open private extendCocharacter from LinearAlgebraicGroups.Relative.RationalCocharacter
open private extendSubgroup from LinearAlgebraicGroups.RootData.BorelNormalizer
open private factor_group_through_subgroup
  from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies

private theorem baseSupport_preserved_of_evaluation
    {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (P : RootPairing I ℤ X Y)
    (f : X →ₗ[ℤ] ℤ) (b : P.Base) (hb : SimpleRoots.IsBaseFor P f b)
    (d : P.Aut) (hf : ∀ i, f (P.root (d.indexEquiv i)) = f (P.root i)) (i : I) :
    d.indexEquiv i ∈ b.support ↔ i ∈ b.support := by
  have rootMap (j : I) : d.weightEquiv (P.root j) = P.root (d.indexEquiv j) :=
    Hom.root_weightMap_apply P P j d.toHom
  have pos (j : I) : d.indexEquiv j ∈ SimpleRoots.positive P f ↔ j ∈ SimpleRoots.positive P f := by
    change (0 < f (P.root (d.indexEquiv j))) ↔ 0 < f (P.root j)
    rw [hf]
  rw [hb.simple_iff, hb.simple_iff, pos]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · intro h j hj l hl eq
    apply h (d.indexEquiv j) ((pos j).mpr hj) (d.indexEquiv l) ((pos l).mpr hl)
    have he := congrArg d.weightEquiv eq
    simpa only [map_add, rootMap] using he
  · intro h j hj l hl eq
    obtain ⟨j, rfl⟩ := d.indexEquiv.surjective j
    obtain ⟨l, rfl⟩ := d.indexEquiv.surjective l
    apply h j ((pos j).mp hj) l ((pos l).mp hl)
    apply d.weightEquiv.injective
    simpa only [map_add, rootMap] using eq

private theorem generation_pulledBack {A B : Type*} [Group A] [Group B]
    (H : Subgroup B) (e : A ≃* H) {s : Set B} (hs : Subgroup.closure s = H) :
    Subgroup.closure {x | (e x).val ∈ s} = ⊤ := by
  let f := H.subtype.comp e.toMonoidHom
  let t : Set A := {x | (e x).val ∈ s}
  have hi : Function.Injective f := Subtype.val_injective.comp e.injective
  have hft : f '' t = s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      have hyH := Subgroup.subset_closure hy
      rw [hs] at hyH
      obtain ⟨x, hx⟩ := e.surjective ⟨y, hyH⟩
      refine ⟨x, ?_, congrArg Subtype.val hx⟩
      change (e x).val ∈ s
      rw [hx]
      exact hy
  have hmap : (Subgroup.closure t).map f = H := by
    rw [MonoidHom.map_closure, hft, hs]
  apply top_unique
  intro x _
  have hx : f x ∈ (Subgroup.closure t).map f := hmap.symm ▸ (e x).property
  obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp hx
  exact hi he ▸ hy

set_option maxHeartbeats 2200000 in
theorem quasiSplitFixedWeyl : Specs.Arithmetic.QuasiSplitFixedWeyl.Statement.{u} := by
  intro F _ G hSemi _ Bpos Bneg T hBpos hBneg hT hTm hInter
  have hG := reductive_of_semisimple G hSemi
  have hTB : IsSubgroupOf T Bpos := by
    have ht : T.inclusion.hom.hom ∈ SubgroupSections T T.group.X := by
      change ∃ x : T.group.X ⟶ T.group.X, x ≫ T.inclusion.hom.hom = T.inclusion.hom.hom
      exact ⟨𝟙 _, Category.id_comp _⟩
    have h := (hInter T.group.X T.inclusion.hom.hom).mp ht Bpos (by simp)
    change ∃ z : T.group.X ⟶ Bpos.group.X,
      z ≫ Bpos.inclusion.hom.hom = T.inclusion.hom.hom at h
    obtain ⟨z, hz⟩ := h
    exact factor_group_through_subgroup Bpos T.inclusion z hz
  obtain ⟨S, hS, hMax, hC, hP, hSP⟩ := quasiSplitCentralizer G hG Bpos T hBpos hT hTm hTB
  let S₀ := subgroupOfSubgroup T S
  obtain ⟨c, L, hL, hCL⟩ := borelDefiningCocharacter G hG Bpos T hBpos hT hTm hTB
  obtain ⟨K, hK, hAlg, hFin, hGal, hSplit⟩ :=
    finiteGaloisTorusSplitting (closedSubgroupAlgebraicGroup T) hT
  letI := hK
  letI := hAlg
  letI := hFin
  letI := hGal
  let GK := baseChangedAlgebraicGroup K G
  let TK : ClosedSubgroup GK.val := extendSubgroup K T
  let BK : ClosedSubgroup GK.val := extendSubgroup K Bpos
  let cK : Cocharacter TK.group := extendCocharacter K c
  let t := multiplicativeBaseChange F K
  obtain ⟨hTKmax, hRegular, hPositive⟩ :=
    regularAtSplittingField (K := K) G hG T Bpos c L hL hCL hSplit
  have hGK : IsReductive GK :=
    (Reductive.RadicalBaseChange.reductiveFieldExtension (K := K) G hG.1 hG.2.1).mpr hG
  obtain ⟨comm, D, A, hBases⟩ :=
    LinearAlgebraicGroups.RootData.SimpleRoots.simpleRoots GK hGK TK hSplit hTKmax
  letI := comm
  obtain ⟨b, hBase, _, _⟩ := hBases cK hRegular
  letI := D.finiteRoots
  letI := D.reduced
  let ρ : Gal(K/F) →* D.rootDatum.Aut :=
    scalarDatumAction (G := G) (T := T) (hT := TK.isClosedImmersion) A hSplit
  let P := D.rootDatum
  let f := SimpleRoots.evaluate (G := GK) (T := TK) D cK
  have hEval (i : Specs.AbstractPairing.Root (G := GK) TK) :
      f (P.root i) = Specs.CharacterPairing.pairing TK.group i.val cK := by
    change P.toLinearMap (P.root i) (Additive.ofMul cK) = _
    rw [D.root_eq, D.pairing_eq]
  have hReg (i : Specs.AbstractPairing.Root (G := GK) TK) : f (P.root i) ≠ 0 := by
    rw [hEval]
    exact hRegular i
  have hPos : SimpleRoots.positive P f = BorelsAndChambers.subgroupRoots TK BK := by
    change BorelsAndChambers.positiveRoots TK cK = BorelsAndChambers.subgroupRoots TK BK at hPositive
    rw [← hPositive]
    ext i
    change (0 < f (P.root i)) ↔ 0 < Specs.CharacterPairing.pairing TK.group i.val cK
    rw [hEval]
  have hInv (σ : Gal(K/F)) (i : Specs.AbstractPairing.Root (G := GK) TK) :
      f (P.root ((ρ σ).indexEquiv i)) = f (P.root i) := by
    change f (P.root (scalarRootEquiv (G := G) (T := T) (hT := TK.isClosedImmersion) σ i)) =
      f (P.root i)
    erw [D.root_eq, D.root_eq]
    change P.toLinearMap (Additive.ofMul (scalarCharacter σ (T := T.group) i.val)) (Additive.ofMul cK) =
      P.toLinearMap (Additive.ofMul i.val) (Additive.ofMul cK)
    erw [D.pairing_eq, D.pairing_eq]
    have he := scalarPairing σ (T := T.group) i.val cK
    rw [show scalarCocharacter σ (T := T.group) cK = cK from
      scalarCocharacter_baseChange σ c] at he
    exact he
  have hBaseStable (σ : Gal(K/F)) (i : Specs.AbstractPairing.Root (G := GK) TK) :
      (ρ σ).indexEquiv i ∈ b.support ↔ i ∈ b.support :=
    baseSupport_preserved_of_evaluation P f b hBase (ρ σ) (hInv σ) i
  obtain ⟨Q, _⟩ := LinearAlgebraicGroups.Relative.RelativeWeylScheme.finiteConstantQuotient G hG S₀ hMax
  obtain ⟨e, hEq, hLifts, hProj⟩ := relativeFixedComparison (G := G) (T := T) (hT := TK.isClosedImmersion) A hSplit hG S hS Bpos hMax hP hSP hC Q
  let longest : Set P.weylGroup := {a | ∃ i ∈ b.support, IsLongest P b (rootOrbit P ρ i) a}
  have hGen : Subgroup.closure longest = fixedWeyl P ρ :=
    orbitGeneration P f hReg b hBase ρ hBaseStable
  have hGenRel : Subgroup.closure {w : Q.splitImage.labels | (e w).val ∈ longest} = ⊤ :=
    generation_pulledBack (fixedWeyl P ρ) e (s := longest) hGen
  have ht : IsUnitComparison t := fun R s ↦ multiplicativeBaseChange_unit K R s
  have hρ : IsScalarAction (G := G) T TK.isClosedImmersion comm D t ρ :=
    scalarDatum_isScalarAction (G := G) (T := T) (hT := TK.isClosedImmersion) A hSplit
  refine ⟨S, hS, hMax, hC, hP, hSP, K, hK, hAlg, hFin, hGal,
    TK.isClosedImmersion, BK.isClosedImmersion, hSplit, comm, D, A, cK, b, ρ, t,
    ht, hρ, hReg, hBase, hPos, hBaseStable, Q, e, hEq, hLifts, hProj, hGenRel⟩

end Assemble

end
end LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
