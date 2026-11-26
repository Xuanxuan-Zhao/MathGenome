import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.GallerySubwords
import Mathlib.Data.List.Induction

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SimpleRoots
namespace LinearAlgebraicGroups.Flag.GallerySubwords

open LinearAlgebraicGroups.Specs
open Specs.GallerySubwords (HasGallerySubwords)
open SimpleRoots (IsBaseFor hyperplane inversions wordLength wordProduct)

section RootPairing

variable {Idx X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootPairing Idx ℤ X Y) (b : P.Base)

local notation "act" => P.weylGroupToPerm
local notation "refl" => RootPairing.weylGroup.ofIdx P
local notation "opp" => (fun i : Idx ↦ P.reflectionPerm i i)

private theorem product_append (l r : List b.support) :
    wordProduct P b (l ++ r) = wordProduct P b l * wordProduct P b r := by
  simp [wordProduct]

private theorem product_snoc (l : List b.support) (s : b.support) :
    wordProduct P b (l ++ [s]) = wordProduct P b l * refl s.val := by
  simp [wordProduct]

private theorem product_cons (l : List b.support) (s : b.support) :
    wordProduct P b (s :: l) = refl s.val * wordProduct P b l := by
  simp [wordProduct]

private theorem reflection_inv (i : Idx) : (refl i)⁻¹ = refl i := by
  apply Subtype.ext
  exact RootPairing.Equiv.reflection_inv P i

private theorem reflection_mul_self (i : Idx) : refl i * refl i = 1 := by
  simpa only [reflection_inv] using inv_mul_cancel (refl i)

private theorem act_mul (v w : P.weylGroup) (i : Idx) :
    act (v * w) i = act v (act w i) := by
  rw [map_mul, Equiv.Perm.mul_apply]

private theorem act_inv_apply (w : P.weylGroup) (i : Idx) :
    act w⁻¹ (act w i) = i := by
  rw [← act_mul, inv_mul_cancel, map_one, Equiv.Perm.one_apply]

private theorem act_apply_inv (w : P.weylGroup) (i : Idx) :
    act w (act w⁻¹ i) = i := by
  rw [← act_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]

private theorem act_opp (w : P.weylGroup) (i : Idx) :
    act w (opp i) = opp (act w i) := by
  apply P.root.injective
  rw [← P.weylGroup_apply_root, P.root_reflectionPerm, P.reflection_apply_self, smul_neg,
    P.weylGroup_apply_root, P.root_reflectionPerm, P.reflection_apply_self]

private theorem hyperplane_opp (i : Idx) : hyperplane P (opp i) = hyperplane P i := by
  ext x
  simp only [hyperplane, Set.mem_ofPred_eq, P.root_reflectionPerm, P.reflection_apply_self,
    map_neg, neg_eq_zero]

private theorem reflection_opp (i : Idx) : refl (opp i) = refl i := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective P
  ext x
  change P.reflection (opp i) x = P.reflection i x
  have hroot : P.root (opp i) = -P.root i := by
    rw [P.root_reflectionPerm, P.reflection_apply_self]
  have hcoroot : P.coroot (opp i) = -P.coroot i := by
    rw [P.coroot_reflectionPerm, P.coreflection_apply_self]
  simp only [P.reflection_apply, RootPairing.coroot', LinearMap.flip_apply]
  rw [hroot, hcoroot, map_neg, neg_smul, smul_neg, neg_neg]

private theorem reflection_mul (w : P.weylGroup) (i : Idx) :
    refl (act w i) * w = w * refl i := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective P
  ext x
  exact (w.val.weightEquiv_reflection i x).symm

private theorem pulled_root_snoc (l : List b.support) (s : b.support) (j : Idx) :
    act (wordProduct P b (l ++ [s]))⁻¹ j =
      P.reflectionPerm s.val (act (wordProduct P b l)⁻¹ j) := by
  rw [product_snoc, mul_inv_rev, reflection_inv, act_mul]
  rfl

private theorem pos_opp (i : Idx) : b.IsPos (opp i) ↔ ¬ b.IsPos i :=
  RootPairing.Base.IsPos.neg_iff_not b i

variable [Finite Idx] [P.IsReduced]

-- A simple reflection changes signs only at the two roots normal to its wall.
private theorem pos_reflection_iff (s : b.support) {j : Idx}
    (hj : j ≠ s.val) (hopp : j ≠ opp s.val) :
    b.IsPos (P.reflectionPerm s.val j) ↔ b.IsPos j := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.reflectionPerm s.property hj⟩
  have hne : P.reflectionPerm s.val j ≠ s.val := by
    intro he
    apply hopp
    simpa only [P.reflectionPerm_self] using congrArg (P.reflectionPerm s.val) he
  simpa only [P.reflectionPerm_self] using h.reflectionPerm s.property hne

-- Compare the sign of a fixed root after pulling it back by successive prefixes.
private theorem crossed_wall (l : List b.support) (j : Idx)
    (h : ¬ (b.IsPos (act (wordProduct P b l)⁻¹ j) ↔ b.IsPos j)) :
    ∃ (pre post : List b.support) (i : b.support),
      l = pre ++ i :: post ∧
        (j = act (wordProduct P b pre) i.val ∨ j = opp (act (wordProduct P b pre) i.val)) := by
  induction l using List.reverseRecOn with
  | nil =>
    exact (h (by simp [wordProduct])).elim
  | append_singleton l s ih =>
    by_cases hl : b.IsPos (act (wordProduct P b l)⁻¹ j) ↔ b.IsPos j
    · have hs {k : Idx} (he : act (wordProduct P b l)⁻¹ j = k) :
          j = act (wordProduct P b l) k :=
        (act_apply_inv P (wordProduct P b l) j).symm.trans
          (congrArg (act (wordProduct P b l)) he)
      refine ⟨l, [], s, rfl, ?_⟩
      by_cases he : act (wordProduct P b l)⁻¹ j = s.val
      · exact Or.inl (hs he)
      by_cases he' : act (wordProduct P b l)⁻¹ j = opp s.val
      · exact Or.inr ((hs he').trans (act_opp P _ _))
      exact (h (by
        rw [pulled_root_snoc]
        exact (pos_reflection_iff P b s he he').trans hl)).elim
    · obtain ⟨pre, post, i, hsplit, hroot⟩ := ih hl
      exact ⟨pre, post ++ [s], i, by rw [hsplit, List.append_assoc, List.cons_append], hroot⟩

private theorem exchange_of_negative (l : List b.support) (s : b.support)
    (h : ¬ b.IsPos (act (wordProduct P b l) s.val)) :
    ∃ (pre post : List b.support) (i : b.support),
      l = pre ++ i :: post ∧
      hyperplane P (act (wordProduct P b pre) i.val) =
        hyperplane P (act (wordProduct P b l) s.val) ∧
      wordProduct P b (pre ++ post) = wordProduct P b (l ++ [s]) := by
  let j := act (wordProduct P b l) s.val
  have hj : ¬ (b.IsPos (act (wordProduct P b l)⁻¹ j) ↔ b.IsPos j) := by
    intro he
    apply h
    apply he.mp
    rw [show act (wordProduct P b l)⁻¹ j = s.val from act_inv_apply P _ _]
    exact b.isPos_of_mem_support s.property
  obtain ⟨pre, post, i, hsplit, hroot⟩ := crossed_wall P b l j hj
  have hwall : hyperplane P (act (wordProduct P b pre) i.val) = hyperplane P j := by
    rcases hroot with he | he
    · rw [he]
    · rw [he, hyperplane_opp]
  have hreflect : refl (act (wordProduct P b pre) i.val) = refl j := by
    rcases hroot with he | he
    · rw [he]
    · rw [he, reflection_opp]
  refine ⟨pre, post, i, hsplit, hwall, ?_⟩
  calc
    wordProduct P b (pre ++ post) =
        refl (act (wordProduct P b pre) i.val) * wordProduct P b l := by
      rw [hsplit, product_append, product_append, product_cons, ← mul_assoc,
        reflection_mul, mul_assoc, ← mul_assoc (refl i.val), reflection_mul_self, one_mul]
    _ = wordProduct P b (l ++ [s]) := by
      rw [hreflect, product_snoc]
      exact reflection_mul P _ _

variable {f : X →ₗ[ℤ] ℤ}

omit [Finite Idx] [P.IsReduced] in
private theorem mem_inversions (hb : IsBaseFor P f b) (hreg : ∀ i, f (P.root i) ≠ 0)
    (w : P.weylGroup) (j : Idx) :
    j ∈ inversions P f w ↔ b.IsPos j ∧ ¬ b.IsPos (act w⁻¹ j) := by
  rw [hb.positive_iff, hb.positive_iff]
  change (0 < f (P.root j) ∧ f (P.root (act w⁻¹ j)) < 0) ↔
    (0 < f (P.root j) ∧ ¬ 0 < f (P.root (act w⁻¹ j)))
  have := hreg (act w⁻¹ j)
  omega

private theorem length_lt_of_positive (hb : IsBaseFor P f b)
    (hreg : ∀ i, f (P.root i) ≠ 0) (l : List b.support) (s : b.support)
    (h : b.IsPos (act (wordProduct P b l) s.val)) :
    wordLength P b (wordProduct P b l) < wordLength P b (wordProduct P b (l ++ [s])) := by
  let w := wordProduct P b l
  let a := act w s.val
  have hpre : act w⁻¹ a = s.val := act_inv_apply P w s.val
  have hpost : act (wordProduct P b (l ++ [s]))⁻¹ a = opp s.val := by
    rw [pulled_root_snoc, hpre]
  have hs : b.IsPos s.val := b.isPos_of_mem_support s.property
  rw [hb.length_eq, hb.length_eq]
  apply Set.ncard_lt_ncard (ht := Set.toFinite _)
  apply Set.ssubset_iff_exists.mpr
  constructor
  · intro j hj
    rw [mem_inversions P b hb hreg] at hj ⊢
    refine ⟨hj.1, ?_⟩
    rw [pulled_root_snoc]
    have hne : act w⁻¹ j ≠ s.val := fun he ↦ hj.2 (he ▸ hs)
    have hne' : act w⁻¹ j ≠ opp s.val := by
      intro he
      have hjopp : j = opp a := by
        rw [← act_apply_inv P w j, he, act_opp]
      exact (pos_opp P b a).mp (hjopp ▸ hj.1) h
    exact fun hp ↦ hj.2 ((pos_reflection_iff P b s hne hne').mp hp)
  · refine ⟨a, ?_, ?_⟩
    · rw [mem_inversions P b hb hreg, hpost]
      exact ⟨h, fun hp ↦ (pos_opp P b _).mp hp hs⟩
    · rw [mem_inversions P b hb hreg, hpre]
      exact fun ha ↦ ha.2 hs

omit [Finite Idx] [P.IsReduced] in
private theorem length_le_word (l : List b.support) :
    wordLength P b (wordProduct P b l) ≤ l.length :=
  Nat.sInf_le ⟨l, rfl, rfl⟩

private theorem reduced_subword (hb : IsBaseFor P f b) (hreg : ∀ i, f (P.root i) ≠ 0)
    (l : List b.support) :
    ∃ r : List b.support, r.Sublist l ∧ Specs.GallerySubwords.IsReduced P b r ∧
      wordProduct P b r = wordProduct P b l := by
  induction l using List.reverseRecOn with
  | nil =>
    exact ⟨[], List.Sublist.refl _, Nat.eq_zero_of_le_zero (length_le_word P b []), rfl⟩
  | append_singleton l s ih =>
    obtain ⟨r, hr, hred, hprod⟩ := ih
    have hprod' : wordProduct P b (r ++ [s]) = wordProduct P b (l ++ [s]) := by
      rw [product_snoc, product_snoc, hprod]
    by_cases h : b.IsPos (act (wordProduct P b r) s.val)
    · have hlt := length_lt_of_positive P b hb hreg r s h
      have hle := length_le_word P b (r ++ [s])
      change wordLength P b (wordProduct P b r) = r.length at hred
      rw [hred] at hlt
      refine ⟨r ++ [s], hr.append (List.Sublist.refl _), ?_, hprod'⟩
      unfold Specs.GallerySubwords.IsReduced
      simp only [List.length_append, List.length_singleton] at hle ⊢
      omega
    · obtain ⟨pre, post, i, hsplit, _, hdel⟩ := exchange_of_negative P b r s h
      have hsub : (pre ++ post).Sublist r := by
        rw [hsplit, List.append_sublist_append_left]
        exact (List.Sublist.refl post).cons i
      have hshort : ∃ q : List b.support,
          q.length = wordLength P b (wordProduct P b (r ++ [s])) ∧
            wordProduct P b q = wordProduct P b (r ++ [s]) :=
        Nat.sInf_mem (s := {n | ∃ q : List b.support,
          q.length = n ∧ wordProduct P b q = wordProduct P b (r ++ [s])})
          ⟨(pre ++ post).length, pre ++ post, rfl, hdel⟩
      obtain ⟨q, hq, hqprod⟩ := hshort
      have hcancel : wordProduct P b (q ++ [s]) = wordProduct P b r := by
        rw [product_snoc, hqprod, product_snoc, mul_assoc, reflection_mul_self, mul_one]
      have hmin := length_le_word P b (q ++ [s])
      rw [hcancel, show wordLength P b (wordProduct P b r) = r.length from hred,
        List.length_append, List.length_singleton, hq, ← hdel] at hmin
      have hle := length_le_word P b (pre ++ post)
      have hlen : r.length = (pre ++ post).length + 1 := by
        rw [hsplit]
        simp only [List.length_append, List.length_cons]
        omega
      refine ⟨pre ++ post, (hsub.trans hr).trans (List.sublist_append_left _ _), ?_,
        hdel.trans hprod'⟩
      unfold Specs.GallerySubwords.IsReduced
      omega

private theorem hasGallerySubwords (hb : IsBaseFor P f b) (hreg : ∀ i, f (P.root i) ≠ 0) :
    HasGallerySubwords P b where
  rightExchange l s _ hs :=
    exchange_of_negative P b l s (fun h ↦ (length_lt_of_positive P b hb hreg l s h).not_gt hs)
  reducedSubword := reduced_subword P b hb hreg
  subword_iff l v := by
    constructor
    · rintro ⟨r, hr, hprod⟩
      obtain ⟨q, hqr, hqred, hqprod⟩ := reduced_subword P b hb hreg r
      exact ⟨q, hqr.trans hr, hqred, hqprod.trans hprod⟩
    · rintro ⟨r, hr, _, hprod⟩
      exact ⟨r, hr, hprod⟩

end RootPairing

/-- Exchange and reduced-subword reduction conditional on the simple-root theorem. -/
theorem gallerySubwords_conditional.{u} (hSimpleRoots : Specs.SimpleRoots.Statement.{u}) :
    Specs.GallerySubwords.Statement.{u} := by
  intro k _ G hG T hT hmax
  obtain ⟨hcomm, D, e, hbase⟩ := hSimpleRoots G hG T hT hmax
  let := hcomm
  let := D.finiteRoots
  let := D.reduced
  refine ⟨hcomm, D, e, ?_⟩
  intro cochar hregular
  obtain ⟨b, hb, _, _⟩ := hbase cochar hregular
  refine ⟨b, hb, hasGallerySubwords D.rootDatum b hb ?_⟩
  intro i
  change D.rootDatum.toLinearMap (D.rootDatum.root i) (Additive.ofMul cochar) ≠ 0
  rw [D.root_eq, D.pairing_eq]
  exact hregular i

end LinearAlgebraicGroups.Flag.GallerySubwords

universe v8_closure_6018436d4525dd4c_u0
theorem _root_.«LinearAlgebraicGroups».«Flag».«GallerySubwords».«gallerySubwords» : _root_.«LinearAlgebraicGroups».«Specs».«GallerySubwords».«Statement».{v8_closure_6018436d4525dd4c_u0} :=
  @_root_.«LinearAlgebraicGroups».«Flag».«GallerySubwords».«gallerySubwords_conditional».{v8_closure_6018436d4525dd4c_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«SimpleRoots».«simpleRoots».{v8_closure_6018436d4525dd4c_u0})
