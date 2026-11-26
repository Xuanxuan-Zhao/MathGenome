import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.ParabolicCosetLength
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SimpleParabolicProduct
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SimpleRoots
import Batteries.Tactic.OpenPrivate
import Mathlib.GroupTheory.DoubleCoset

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.BruhatCells
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.StandardParabolicLevi
open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj Pointwise

universe u v w z

namespace LinearAlgebraicGroups.Flag.ParabolicCosetLength

open LinearAlgebraicGroups.Specs
open Specs.ParabolicCosetLength
open Specs.SimpleRoots
open RootPairing

set_option backward.isDefEq.respectTransparency false

open private exists_integralValues positive_coefficients reflection_conjugate
  reflection_cancel perm_mul perm_reflection reflected_value rightInversions rightInversions_card_mul
  shortest_word_card exists_shortest_word root_reflection_sum
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SimpleRoots

noncomputable section

section Length

variable {Idx X Y : Type*} [Finite Idx] [AddCommGroup X] [AddCommGroup Y]
  [Module.Free ℤ X] [Module.Finite ℤ X]
  (P : RootDatum Idx X Y) [P.IsReduced] (b : P.Base)

omit [Module.Free ℤ X] [Module.Finite ℤ X] in
private lemma base_generates :
    Subgroup.closure (Set.range fun j : b.support ↦ weylGroup.ofIdx P j.val) = ⊤ := by
  let H := Subgroup.closure (Set.range fun j : b.support ↦ weylGroup.ofIdx P j.val)
  have hsimple (i : Idx) (hi : i ∈ b.support) : weylGroup.ofIdx P i ∈ H :=
    Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
  have hall (i : Idx) : weylGroup.ofIdx P i ∈ H := by
    apply b.induction_reflect i (p := fun j ↦ weylGroup.ofIdx P j ∈ H)
    · intro j hj
      rw [← perm_reflection, reflection_conjugate]
      exact H.mul_mem (H.mul_mem hj hj) (H.inv_mem hj)
    · exact hsimple
    · intro j a hj ha
      rw [← perm_reflection, reflection_conjugate]
      exact H.mul_mem (H.mul_mem (hsimple a ha) hj) (H.inv_mem (hsimple a ha))
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨g, hg⟩ := x
  induction hg using weylGroup.induction with
  | mem i => exact hall i
  | one => exact H.one_mem
  | mul a c ha hc ia ic => exact H.mul_mem ia ic

omit [Finite Idx] [P.IsReduced] in
private lemma height_functional :
    ∃ (f : X →ₗ[ℤ] ℤ), (∀ i, f (P.root i) ≠ 0) ∧
      ∀ i, b.IsPos i ↔ i ∈ positive P f := by
  obtain ⟨f, d, hd, hf⟩ :=
    exists_integralValues (v := fun j : b.support ↦ P.root j.val) b.linearIndepOn_root (fun _ ↦ 1)
  have h (i : Idx) : f (P.root i) = d * b.height i := by
    obtain ⟨c, _, _, hc⟩ := b.exists_root_eq_sum_int i
    calc
      f (P.root i) = ∑ j ∈ b.support, c j * d := by
        rw [hc, map_sum]
        exact Finset.sum_congr rfl fun j hj ↦ by
          simp only [map_zsmul, hf ⟨j, hj⟩, mul_one, zsmul_eq_mul, Int.cast_id]
      _ = d * b.height i := by
        rw [b.height_eq_sum hc, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  refine ⟨f, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [h]; exact mul_ne_zero hd.ne' (b.height_ne_zero i)
  · change 0 < b.height i ↔ 0 < f (P.root i)
    rw [h, mul_pos_iff_of_pos_left hd]

private def subsystem (I : Set Idx) : Set Idx :=
  {i | P.root i ∈ Submodule.span ℤ (P.root '' I)}

omit [Finite Idx] [P.IsReduced] in
/-- A functional on the chamber face detects the subsystem and the sign of every root outside it. -/
private lemma face_functional (I : Set Idx) (hI : I ⊆ b.support) :
    ∃ g : X →ₗ[ℤ] ℤ,
      (∀ i, i ∈ subsystem P I ↔ g (P.root i) = 0) ∧
      (∀ i, i ∉ subsystem P I → (b.IsPos i ↔ 0 < g (P.root i))) ∧
      (∀ i : b.support, i.val ∉ I → 0 < g (P.root i.val)) := by
  classical
  obtain ⟨g, d, hd, hg⟩ := exists_integralValues
    (v := fun j : b.support ↦ P.root j.val) b.linearIndepOn_root
    (fun j ↦ if j.val ∈ I then 0 else 1)
  have hval (j : b.support) : g (P.root j.val) = if j.val ∈ I then 0 else d := by
    rw [hg j]; split <;> simp
  have hzero (i : Idx) (hi : i ∈ subsystem P I) : g (P.root i) = 0 := by
    have hle : Submodule.span ℤ (P.root '' I) ≤ LinearMap.ker g :=
      Submodule.span_le.mpr fun _ ⟨j, hj, he⟩ ↦ by
        change _ ∈ g.ker
        rw [← he, LinearMap.mem_ker, hval ⟨j, hI hj⟩, ite_eq_left hj]
    exact hle hi
  have hpositive (i : Idx) (hi : b.IsPos i) :
      0 ≤ g (P.root i) ∧ (g (P.root i) = 0 → i ∈ subsystem P I) := by
    obtain ⟨c, hc, _, he⟩ := positive_coefficients P b hi
    have hs : g (P.root i) = ∑ j : b.support, c j * g (P.root j.val) := by
      rw [← he, map_sum]
      simp only [map_zsmul, zsmul_eq_mul, Int.cast_id]
    have hnonneg (j : b.support) : 0 ≤ c j * g (P.root j.val) :=
      mul_nonneg (hc j) (by rw [hval]; split <;> omega)
    refine ⟨hs ▸ Finset.sum_nonneg (fun j _ ↦ hnonneg j), fun h ↦ ?_⟩
    change P.root i ∈ Submodule.span ℤ (P.root '' I)
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    by_cases hj : j.val ∈ I
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j.val, hj, rfl⟩)
    · have hterm := Finset.single_le_sum (fun a _ ↦ hnonneg a) (Finset.mem_univ j)
      rw [← hs, h, hval j, ite_eq_right hj] at hterm
      have hz : c j = 0 := by
        by_contra hn
        exact (not_lt_of_ge hterm) (mul_pos (lt_of_le_of_ne (hc j) (Ne.symm hn)) hd)
      simp [hz]
  let := P.indexNeg
  have hneg (i : Idx) : (-i) ∈ subsystem P I ↔ i ∈ subsystem P I := by
    change P.root (P.reflectionPerm i i) ∈ Submodule.span ℤ (P.root '' I) ↔ _
    rw [root_reflectionPerm, reflection_apply_self]
    exact Submodule.neg_mem_iff _
  refine ⟨g, fun i ↦ ⟨hzero i, fun h ↦ ?_⟩, fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · rcases RootPairing.Base.IsPos.or_neg b i with hp | hn
    · exact (hpositive i hp).2 h
    · apply (hneg i).mp ((hpositive (-i) hn).2 ?_)
      change g (P.root (P.reflectionPerm i i)) = 0
      rw [root_reflectionPerm, reflection_apply_self, map_neg, h, neg_zero]
  · rcases RootPairing.Base.IsPos.or_neg b i with hp | hn
    · exact iff_of_true hp (lt_of_le_of_ne (hpositive i hp).1
        (Ne.symm fun h ↦ hi ((hpositive i hp).2 h)))
    · have hle := (hpositive (-i) hn).1
      change 0 ≤ g (P.root (P.reflectionPerm i i)) at hle
      rw [root_reflectionPerm, reflection_apply_self, map_neg] at hle
      exact iff_of_false ((RootPairing.Base.IsPos.neg_iff_not b i).mp hn) (by omega)
  · rw [hval i, ite_eq_right hi]
    exact hd

omit [Finite Idx] [Module.Free ℤ X] [Module.Finite ℤ X] [P.IsReduced] in
private lemma parabolic_fixes_functional (I : Set Idx) (g : X →ₗ[ℤ] ℤ)
    (hg : ∀ i ∈ I, g (P.root i) = 0) {x : P.weylGroup}
    (hx : x ∈ Subgroup.closure (weylGroup.ofIdx P '' I)) (i : Idx) :
    g (P.root (P.weylGroupToPerm x i)) = g (P.root i) := by
  induction hx using Subgroup.closure_induction generalizing i with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    rw [perm_reflection, root_reflection_sum, map_sub, map_zsmul, hg j hj, smul_zero, sub_zero]
  | one => simp
  | mul x y _ _ h₁ h₂ => rw [perm_mul, h₁, h₂]
  | inv x _ h =>
    have he := (P.weylGroupToPerm x).apply_symm_apply i
    rw [map_inv] at ⊢
    exact (h _).symm.trans (congrArg (fun j ↦ g (P.root j)) he)

omit [Finite Idx] [Module.Free ℤ X] [Module.Finite ℤ X] [P.IsReduced] in
private lemma maps_positive_subsystem (I : Set Idx)
    (f : X →ₗ[ℤ] ℤ) (hf : ∀ i, f (P.root i) ≠ 0)
    (hfb : ∀ i, b.IsPos i ↔ i ∈ positive P f)
    (g : X →ₗ[ℤ] ℤ) (hg : ∀ i, i ∈ subsystem P I ↔ g (P.root i) = 0)
    (hval : ∀ i : b.support, i.val ∉ I → 0 < g (P.root i.val))
    (hzero : ∀ i ∈ I, g (P.root i) = 0) (m : P.weylGroup)
    (hm : ∀ i ∈ I, b.IsPos (P.weylGroupToPerm m i)) :
    ∀ i, b.IsPos i → i ∈ subsystem P I → b.IsPos (P.weylGroupToPerm m i) := by
  classical
  intro i hi hsub
  obtain ⟨c, hc, _, he⟩ := positive_coefficients P b hi
  have hsum : (∑ j : b.support, c j * g (P.root j.val)) = 0 := by
    rw [← (hg i).mp hsub, ← he, map_sum]
    simp only [map_zsmul, zsmul_eq_mul, Int.cast_id]
  have hz (j : b.support) (hj : j.val ∉ I) : c j = 0 := by
    have hle := Finset.single_le_sum
      (f := fun a : b.support ↦ c a * g (P.root a.val))
      (fun a _ ↦ mul_nonneg (hc a) (by
        by_cases ha : a.val ∈ I
        · rw [hzero _ ha]
        · exact (hval a ha).le)) (Finset.mem_univ j)
    rw [hsum] at hle
    by_contra h
    exact (not_lt_of_ge hle) (mul_pos (lt_of_le_of_ne (hc j) (Ne.symm h)) (hval j hj))
  have hsumroot : P.root (P.weylGroupToPerm m i) =
      ∑ j : b.support, c j • P.root (P.weylGroupToPerm m j.val) := by
    rw [← P.weylGroup_apply_root, ← he, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [smul_comm, P.weylGroup_apply_root]
  have hmval : 0 ≤ f (P.root (P.weylGroupToPerm m i)) := by
    rw [hsumroot, map_sum]
    refine Finset.sum_nonneg fun j _ ↦ ?_
    rw [map_zsmul, zsmul_eq_mul, Int.cast_id]
    by_cases hj : j.val ∈ I
    · exact mul_nonneg (hc j) ((hfb _).mp (hm _ hj) : 0 < f _).le
    · rw [hz j hj, zero_mul]
  exact (hfb _).mpr (lt_of_le_of_ne hmval (Ne.symm (hf _)))

omit [Module.Free ℤ X] [Module.Finite ℤ X] in
private lemma length_eq_rightInversions
    (f : X →ₗ[ℤ] ℤ) (hf : ∀ i, f (P.root i) ≠ 0)
    (hb : ∀ i, b.IsPos i ↔ i ∈ positive P f) (m : P.weylGroup) :
    wordLength P b m = (rightInversions P f m).ncard := by
  obtain ⟨l, hl, hlen, hmin⟩ := exists_shortest_word P b (base_generates P b) m
  rw [← hlen, ← hl]
  exact shortest_word_card P b f hf hb l fun k hk ↦ hmin k (hk.trans hl)

omit [Module.Free ℤ X] [Module.Finite ℤ X] in
private lemma length_add_of_maps_positive (I : Set Idx)
    (f : X →ₗ[ℤ] ℤ) (hf : ∀ i, f (P.root i) ≠ 0)
    (hb : ∀ i, b.IsPos i ↔ i ∈ positive P f)
    (g : X →ₗ[ℤ] ℤ) (hg : ∀ i, i ∈ subsystem P I ↔ g (P.root i) = 0)
    (hout : ∀ i, i ∉ subsystem P I → (b.IsPos i ↔ 0 < g (P.root i)))
    (m : P.weylGroup) (hm : ∀ i, b.IsPos i → i ∈ subsystem P I →
      b.IsPos (P.weylGroupToPerm m i))
    (x : P.weylGroup) (hx : x ∈ Subgroup.closure (weylGroup.ofIdx P '' I)) :
    wordLength P b (m * x) = wordLength P b m + wordLength P b x := by
  classical
  let p := P.weylGroupToPerm x
  have hfixed (i : Idx) : g (P.root (p i)) = g (P.root i) :=
    parabolic_fixes_functional P I g (fun j hj ↦ (hg j).mp (Submodule.subset_span ⟨j, hj, rfl⟩)) hx i
  have hsub (i : Idx) : p i ∈ subsystem P I ↔ i ∈ subsystem P I := by
    rw [hg, hg, hfixed]
  have hpos (i : Idx) (hi : i ∉ subsystem P I) :
      0 < f (P.root (p i)) ↔ 0 < f (P.root i) := by
    change p i ∈ positive P f ↔ i ∈ positive P f
    rw [← hb, ← hb, hout _ (fun h ↦ hi ((hsub _).mp h)), hout _ hi, hfixed]
  have hsign (i : Idx) (hi : i ∈ subsystem P I) :
      f (P.root (P.weylGroupToPerm m i)) < 0 ↔ f (P.root i) < 0 := by
    rcases lt_or_gt_of_ne (hf i) with hn | hp
    · let j := P.reflectionPerm i i
      have hjg : g (P.root j) = 0 := by
        rw [show j = P.reflectionPerm i i from rfl, root_reflectionPerm,
          reflection_apply_self, map_neg, (hg _).mp hi, neg_zero]
      have hjf : j ∈ positive P f := by
        change 0 < f (P.root (P.reflectionPerm i i))
        rw [root_reflectionPerm, reflection_apply_self, map_neg]
        omega
      have h := (hb _).mp (hm j ((hb _).mpr hjf) ((hg _).mpr hjg))
      change 0 < f (P.root (P.weylGroupToPerm m (P.reflectionPerm i i))) at h
      rw [reflected_value] at h
      exact iff_of_true (by omega) hn
    · have h : 0 < f (P.root (P.weylGroupToPerm m i)) :=
        (hb _).mp (hm i ((hb _).mpr hp) hi)
      exact iff_of_false (not_lt_of_gt h) (not_lt_of_gt hp)
  let R := rightInversions P f
  have hinside {i : Idx} (hi : i ∈ R x) : i ∈ subsystem P I := by
    by_contra hn
    exact not_lt_of_gt ((hpos i hn).mpr hi.1) hi.2
  have houtside {i : Idx} (hi : i ∈ R m) : i ∉ subsystem P I := by
    intro h
    exact not_lt_of_gt hi.1 ((hsign i h).mp hi.2)
  have hpre (i : Idx) : i ∈ p.symm '' R m ↔ p i ∈ R m := by
    constructor
    · rintro ⟨j, hj, rfl⟩
      simpa using hj
    · intro hi
      exact ⟨p i, hi, p.symm_apply_apply i⟩
  have hdis : Disjoint (p.symm '' R m) (R x) :=
    Set.disjoint_left.mpr fun i hi hj ↦
      houtside ((hpre i).mp hi) ((hsub i).mpr (hinside hj))
  -- Inside the subsystem the sign change comes from x. Outside it, x permutes positive roots.
  have hsplit : R (m * x) = (p.symm '' R m) ∪ R x := by
    ext i
    rw [Set.mem_union, hpre]
    change (0 < f (P.root i) ∧ f (P.root (P.weylGroupToPerm (m * x) i)) < 0) ↔
      p i ∈ R m ∨ i ∈ R x
    rw [perm_mul]
    by_cases hi : i ∈ subsystem P I
    · rw [or_iff_right (fun h ↦ houtside h ((hsub i).mpr hi))]
      change (0 < f (P.root i) ∧ f (P.root (P.weylGroupToPerm m (p i))) < 0) ↔
        (0 < f (P.root i) ∧ f (P.root (p i)) < 0)
      rw [hsign _ ((hsub i).mpr hi)]
    · rw [or_iff_left (fun h ↦ hi (hinside h))]
      change (_ ∧ _) ↔ (0 < f (P.root (p i)) ∧ _)
      rw [hpos i hi]
  simp only [length_eq_rightInversions P b f hf hb]
  change (R (m * x)).ncard = (R m).ncard + (R x).ncard
  rw [hsplit, Set.ncard_union_eq hdis, Set.ncard_image_of_injective _ p.symm.injective]

private theorem cosetLength : LengthStatement.{v, w, z} := by
  classical
  intro Idx X Y _ _ _ _ _ _ _ P _ _ b I hI
  dsimp only
  let H := Subgroup.closure (weylGroup.ofIdx P '' I)
  let len := wordLength P b
  let pos (m : P.weylGroup) : Prop := ∀ i, b.IsPos i → i ∈ subsystem P I →
    b.IsPos (P.weylGroupToPerm m i)
  obtain ⟨f, hf, hb⟩ := height_functional P b
  obtain ⟨g, hg, hout, hval⟩ := face_functional P b I hI
  have hzero (i : Idx) (hi : i ∈ I) : g (P.root i) = 0 :=
    (hg i).mp (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hadd (m : P.weylGroup) (hm : pos m) (x : H) :
      len (m * x.val) = len m + len x.val :=
    length_add_of_maps_positive P b I f hf hb g hg hout m hm x.val x.property
  have hlenzero (x : P.weylGroup) (hx : len x = 0) : x = 1 := by
    obtain ⟨l, hl, hlen, _⟩ := exists_shortest_word P b (base_generates P b) x
    change wordLength P b x = 0 at hx
    rw [hx, List.length_eq_zero_iff] at hlen
    subst l
    exact hl.symm
  intro y
  have hshort (m : P.weylGroup) (hm : IsShortestInCoset len H y m) : pos m := by
    apply maps_positive_subsystem P b I f hf hb g hg hval hzero m
    intro i hi
    by_contra h
    let s := weylGroup.ofIdx P i
    have hs : s ∈ H := Subgroup.subset_closure ⟨i, hi, rfl⟩
    have hn : f (P.root (P.weylGroupToPerm m i)) < 0 := by
      have hnot : ¬ 0 < f (P.root (P.weylGroupToPerm m i)) := fun hp ↦ h ((hb _).mpr hp)
      exact lt_of_le_of_ne (le_of_not_gt hnot) (hf _)
    have hp : 0 < f (P.root (P.weylGroupToPerm (m * s) i)) := by
      rw [perm_mul, perm_reflection, reflected_value]
      omega
    have hlen : len m = len (m * s) + 1 := by
      simp only [len, length_eq_rightInversions P b f hf hb]
      simpa only [s, mul_assoc, reflection_cancel, mul_one] using
        rightInversions_card_mul P b f hb (m * s) ⟨i, hI hi⟩ hp
    have hmin := hm.2 ⟨(y⁻¹ * m) * s, H.mul_mem hm.1 hs⟩
    have he : y * ((y⁻¹ * m) * s) = m * s := by group
    change len m ≤ len (y * ((y⁻¹ * m) * s)) at hmin
    rw [he, hlen] at hmin
    omega
  have hleast (m : P.weylGroup) (hm : y⁻¹ * m ∈ H) (hp : pos m) :
      IsShortestInCoset len H y m := by
    refine ⟨hm, fun x ↦ ?_⟩
    let t : H := ⟨(y⁻¹ * m)⁻¹ * x.val, H.mul_mem (H.inv_mem hm) x.property⟩
    have he : m * t.val = y * x.val := by dsimp [t]; group
    rw [← he, hadd m hp t]
    omega
  let L : Set ℕ := Set.range fun x : H ↦ len (y * x.val)
  obtain ⟨x, hx⟩ := csInf_mem
    (show L.Nonempty from ⟨_, ⟨1, rfl⟩⟩)
  let m := y * x.val
  have hm : IsShortestInCoset len H y m := by
    refine ⟨?_, fun t ↦ ?_⟩
    · simp [m]
    · change len (y * x.val) ≤ len (y * t.val)
      change len (y * x.val) = sInf L at hx
      rw [hx]
      exact csInf_le' (show len (y * t.val) ∈ L from ⟨t, rfl⟩)
  refine ⟨⟨m, hm, ?_⟩, ?_, fun a ha ↦ hadd a (hshort a ha)⟩
  · intro a ha
    let t : H := ⟨(y⁻¹ * m)⁻¹ * (y⁻¹ * a), H.mul_mem (H.inv_mem hm.1) ha.1⟩
    have he : m * t.val = a := by dsimp [t]; group
    have he' : y * (y⁻¹ * m) = m := by group
    have hle := ha.2 ⟨y⁻¹ * m, hm.1⟩
    change len a ≤ len (y * (y⁻¹ * m)) at hle
    rw [he', ← he, hadd m (hshort m hm) t] at hle
    have ht : t.val = 1 := hlenzero _ (by omega)
    rw [← he, ht, mul_one]
  · intro a
    exact ⟨fun ha ↦ ⟨ha.1, fun _ hi ↦ hshort a ha _ hi.1 hi.2⟩,
      fun ha ↦ hleast a ha.1 (fun i hp hs ↦ ha.2 (show i ∈ _ from ⟨hp, hs⟩))⟩

end Length

section Saturation

open CategoryTheory.Limits
open Opposite
open Specs.AbstractPairing (Datum Root)
open Specs.BorelsAndChambers (positiveRoots subgroupRoots)
open Specs.BruhatOrbitParametrization (Cell IsRepresentative)
open Specs.DatumAndWeyl (Identification)
open Specs.SimpleParabolicProduct (doubleCoset)
open Specs.StandardParabolicLevi (parabolicWeylGroup)

open private mem_sections_of_subgroupOf representative_product
  some_representative_label representative_conjugates_torus closed_factor_of_range evaluate_root
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SimpleParabolicProduct
open private exists_field_point from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.DiagonalizableFixedLocus

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {T B : ClosedSubgroup G.val} [IsCommMonObj T.group.X]

private def weightAction (D : Datum T) :=
  (RootPairing.Equiv.weightHom D.rootDatum).domRestrict D.rootDatum.weylGroup

private lemma weightAction_injective (D : Datum T) : Function.Injective (weightAction D) :=
  fun _ _ h ↦ Subtype.ext (RootPairing.Equiv.weightHom_injective D.rootDatum h)

private lemma transferRepresentative {D E : Datum T} (W : Identification D) (V : Identification E)
    {x : D.rootDatum.weylGroup} {n : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X}
    (hn : IsRepresentative W x n) :
    ∃ y : E.rootDatum.weylGroup, ∃ q, IsRepresentative V y q ∧
      q ≫ V.normalizer.inclusion.hom.hom = n ≫ W.normalizer.inclusion.hom.hom ∧
      weightAction E y = weightAction D x := by
  obtain ⟨q, hq⟩ := (V.representsNormalizer _ _).mp
    ((W.representsNormalizer _ _).mpr ⟨n, rfl⟩)
  obtain ⟨y, hy⟩ := some_representative_label V q
  refine ⟨y, q, hy, hq, ?_⟩
  have hc := representative_conjugates_torus V hy
  rw [hq, ← representative_conjugates_torus W hn] at hc
  have hmono : Mono T.inclusion.hom.hom := by
    let := T.isClosedImmersion
    exact Over.mono_of_mono_left _
  have he : V.image.conjugation (V.labelEquiv y) = W.image.conjugation (W.labelEquiv x) := by
    apply Iso.ext
    apply Grp.hom_ext
    exact (cancel_mono T.inclusion.hom.hom).mp hc
  apply LinearEquiv.ext
  intro a
  change y.val.weightEquiv (Additive.ofMul (Additive.toMul a)) =
    x.val.weightEquiv (Additive.ofMul (Additive.toMul a))
  rw [V.characterAction, W.characterAction, V.image.characterAction, W.image.characterAction, he]

/-- Two identifications label the same rational normalizer points through the same action on characters. -/
private lemma reindexRepresentatives {D E : Datum T} (W : Identification D) (V : Identification E)
    (n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X))
    (hn : ∀ x, IsRepresentative W x (n x)) (hV : ∀ y, ∃ q, IsRepresentative V y q) :
    ∃ (e : D.rootDatum.weylGroup ≃* E.rootDatum.weylGroup)
      (q : E.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ V.normalizer.group.X)),
      (∀ y, IsRepresentative V y (q y)) ∧
      (∀ x, q (e x) ≫ V.normalizer.inclusion.hom.hom = n x ≫ W.normalizer.inclusion.hom.hom) ∧
      (∀ x i, E.rootDatum.weylGroupToPerm (e x) i = D.rootDatum.weylGroupToPerm x i) := by
  classical
  choose l q hq heq hweight using fun x ↦ transferRepresentative W V (hn x)
  have hl_inj : Function.Injective l := fun x y h ↦
    weightAction_injective D ((hweight x).symm.trans ((congrArg (weightAction E) h).trans (hweight y)))
  have hl_surj : Function.Surjective l := by
    intro y
    obtain ⟨n', hn'⟩ := hV y
    obtain ⟨x, _, _, _, hw⟩ := transferRepresentative V W hn'
    exact ⟨x, weightAction_injective E ((hweight x).trans hw)⟩
  let e : D.rootDatum.weylGroup ≃* E.rootDatum.weylGroup :=
    { Equiv.ofBijective l ⟨hl_inj, hl_surj⟩ with
      map_mul' := fun x y ↦ weightAction_injective E (by
        change weightAction E (l (x * y)) = weightAction E (l x * l y)
        rw [hweight, map_mul, map_mul, hweight, hweight]) }
  refine ⟨e, fun y ↦ q (e.symm y), fun y ↦ ?_, fun x ↦ ?_, fun x i ↦ ?_⟩
  · simpa only [show l (e.symm y) = e (e.symm y) from rfl, e.apply_symm_apply] using hq (e.symm y)
  · simpa only [e.symm_apply_apply] using heq x
  · apply Subtype.ext
    apply Additive.ofMul.injective
    rw [← E.root_eq, ← D.root_eq, ← E.rootDatum.weylGroup_apply_root, ← D.rootDatum.weylGroup_apply_root]
    change weightAction E (l x) (E.rootDatum.root i) = weightAction D x (D.rootDatum.root i)
    rw [hweight, E.root_eq, D.root_eq]

private lemma reindexSimpleReflection {D E : Datum T} {b : D.rootDatum.Base} {b' : E.rootDatum.Base}
    (hpos : ∀ i, b.IsPos i ↔ b'.IsPos i)
    (e : D.rootDatum.weylGroup ≃* E.rootDatum.weylGroup)
    (he : ∀ x i, E.rootDatum.weylGroupToPerm (e x) i = D.rootDatum.weylGroupToPerm x i)
    {i : Root T} (hi : i ∈ b.support) :
    e (weylGroup.ofIdx D.rootDatum i) = weylGroup.ofIdx E.rootDatum i := by
  classical
  let := D.finiteRoots
  let := D.reduced
  let := E.reduced
  let := E.freeCharacters
  let := E.finiteCharacters
  let s := weylGroup.ofIdx D.rootDatum i
  obtain ⟨f, hf, hfb⟩ := height_functional E.rootDatum b'
  have hsimple (i : Root T) (j : Root T) (hj : j ∈ b.support) :
      i ∈ rightInversions E.rootDatum f (e (weylGroup.ofIdx D.rootDatum j)) ↔ i = j := by
    change (i ∈ positive E.rootDatum f ∧
      f (E.rootDatum.root (E.rootDatum.weylGroupToPerm (e (weylGroup.ofIdx D.rootDatum j)) i)) < 0) ↔ _
    rw [he, perm_reflection, ← hfb, ← hpos]
    constructor
    · rintro ⟨hp, hn⟩
      by_contra hne
      have h := (hfb _).mp ((hpos _).mp (hp.reflectionPerm hj hne))
      exact not_lt_of_gt h hn
    · rintro rfl
      refine ⟨b.isPos_of_mem_support hj, ?_⟩
      have hr : E.rootDatum.root (D.rootDatum.reflectionPerm i i) = - E.rootDatum.root i := by
        rw [E.root_eq, E.root_eq, ← D.root_eq, ← D.root_eq, root_reflectionPerm, reflection_apply_self]
      rw [hr, map_neg, neg_lt_zero]
      exact (hfb _).mp ((hpos _).mp (b.isPos_of_mem_support hj))
  have hR : rightInversions E.rootDatum f (e s) = {i} := Set.ext fun j ↦ hsimple j i hi
  have hlen : wordLength E.rootDatum b' (e s) = 1 := by
    rw [length_eq_rightInversions E.rootDatum b' f hf hfb, hR, Set.ncard_singleton]
  obtain ⟨l, hl, hll, _⟩ := exists_shortest_word E.rootDatum b' (base_generates E.rootDatum b') (e s)
  obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp (hll.trans hlen)
  have hls : weylGroup.ofIdx E.rootDatum j.val = e s := by simpa [wordProduct] using hl
  have hji : i = j.val := by
    have hmem : i ∈ rightInversions E.rootDatum f (weylGroup.ofIdx E.rootDatum j.val) := by
      rw [hls, hR]; rfl
    by_contra hne
    have hp := (hfb _).mpr hmem.1
    have hpos' := (hfb _).mp (hp.reflectionPerm j.property hne)
    exact not_lt_of_gt hpos' hmem.2
  change e s = weylGroup.ofIdx E.rootDatum i
  rw [← hls, hji]

private lemma geometricPointAt (X : SchemeOver k) (x : X.left) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : IsAlgClosed K)
      (p : Over.mk (fieldSpecMap k K) ⟶ X), p.left (IsLocalRing.closedPoint K) = x := by
  obtain ⟨L, _, _, r, hr⟩ := exists_field_point X x
  let K := AlgebraicClosure L
  let φ := (algebraMap L K).comp (algebraMap k L)
  let : Algebra k K := φ.toAlgebra
  let e : Over.mk (fieldSpecMap k K) ⟶ (testSpec k).obj (op (CommAlgCat.of k L)) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap L K))) (by
      exact (Spec.map_comp (CommRingCat.ofHom (algebraMap k L))
        (CommRingCat.ofHom (algebraMap L K))).symm)
  refine ⟨K, inferInstance, inferInstance, inferInstance, e ≫ r, ?_⟩
  change r.left (e.left (IsLocalRing.closedPoint K)) = x
  rw [Subsingleton.elim (α := PrimeSpectrum L) (e.left (IsLocalRing.closedPoint K))
    (IsLocalRing.closedPoint L), hr]

private lemma fieldPoint_factors_immersion {K : Type u} [Field K] [Algebra k K]
    {X Z : SchemeOver k} (p : Over.mk (fieldSpecMap k K) ⟶ X) (f : Z ⟶ X)
    (hf : IsImmersion f.left) :
    p.left (IsLocalRing.closedPoint K) ∈ Set.range f.left ↔ ∃ q, q ≫ f = p := by
  let := hf
  constructor
  · intro hp
    let Y := Over.mk (fieldSpecMap k K)
    let U := f.left.coborderRange
    let Zu := Over.mk (U.ι ≫ X.hom)
    let j : Zu ⟶ X := Over.homMk U.ι rfl
    let f' : Z ⟶ Zu := Over.homMk f.left.liftCoborder (by
      change _ ≫ U.ι ≫ X.hom = Z.hom
      rw [← Category.assoc, Scheme.Hom.liftCoborder_ι, Over.w f])
    have hfj : f' ≫ j = f := by
      apply Over.OverMorphism.ext
      exact Scheme.Hom.liftCoborder_ι f.left
    have hpu : Set.range p.left ⊆ Set.range U.ι := by
      rintro _ ⟨x, rfl⟩
      rw [Subsingleton.elim (α := PrimeSpectrum K) x (IsLocalRing.closedPoint K)]
      obtain ⟨z, hz⟩ := hp
      exact ⟨f'.left z, (show (f' ≫ j).left z = _ from (congrArg (fun a : Z ⟶ X ↦ a.left z) hfj).trans hz)⟩
    let r : Y.left ⟶ Zu.left := IsOpenImmersion.lift U.ι p.left hpu
    have hr : r ≫ U.ι = p.left := IsOpenImmersion.lift_fac _ _ _
    let p' : Y ⟶ Zu := Over.homMk r (by
      change r ≫ U.ι ≫ X.hom = Y.hom
      rw [← Category.assoc, hr, Over.w p])
    have hpp : p' ≫ j = p := by
      apply Over.OverMorphism.ext
      exact hr
    have hrange : Set.range p'.left ⊆ Set.range f'.left := by
      rintro _ ⟨x, rfl⟩
      rw [Subsingleton.elim (α := PrimeSpectrum K) x (IsLocalRing.closedPoint K)]
      obtain ⟨z, hz⟩ := hp
      refine ⟨z, U.ι.isOpenEmbedding.injective ?_⟩
      change (f' ≫ j).left z = (p' ≫ j).left (IsLocalRing.closedPoint K)
      rw [hfj, hpp, hz]
    have : IsReduced Y.left := by
      change IsReduced (Spec (CommRingCat.of K))
      infer_instance
    have hf' : IsClosedImmersion f'.left := by
      change IsClosedImmersion f.left.liftCoborder
      infer_instance
    obtain ⟨q, hq⟩ := closed_factor_of_range p' f' hf' hrange
    exact ⟨q, by rw [← hfj, ← Category.assoc, hq, hpp]⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q.left (IsLocalRing.closedPoint K), rfl⟩

private lemma mem_doubleCoset_iff {Y : SchemeOver k}
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X} {p : Y ⟶ G.val.X} :
    p ∈ doubleCoset B Y n ↔
      ∃ b₁ ∈ SubgroupSections B Y, ∃ b₂ ∈ SubgroupSections B Y,
        b₁ * (toUnit Y ≫ n) * b₂ = p := by
  change p ∈ DoubleCoset.doubleCoset (toUnit Y ≫ n)
    (SubgroupSections B Y : Set (Y ⟶ G.val.X)) (SubgroupSections B Y : Set (Y ⟶ G.val.X)) ↔ _
  simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe, eq_comm]

omit [IsCommMonObj T.group.X] in
private lemma cell_sections_iff {Q : Specs.QuotientEmbedding.Presentation B} {a : ModObj G.val.X Q.scheme}
    {n : 𝟙_ (SchemeOver k) ⟶ G.val.X} {A : ClosedSubgroup G.val}
    (C : Cell (T := T) Q a n A) {Y : SchemeOver k} (p : Y ⟶ G.val.X) :
    p ∈ doubleCoset B Y n ↔ ∃ q : Y ⟶ C.doubleOrbit, q ≫ C.doubleOrbitInclusion = p := by
  rw [C.doubleOrbitSections, mem_doubleCoset_iff]
  constructor
  · rintro ⟨_, ⟨b₁, rfl⟩, _, ⟨b₂, rfl⟩, h⟩
    exact ⟨b₁, b₂, h⟩
  · rintro ⟨b₁, b₂, h⟩
    exact ⟨_, ⟨b₁, rfl⟩, _, ⟨b₂, rfl⟩, h⟩

private lemma saturate_doubleCosets {W M J : Type*} [Group W] [Group M]
    (B H : Subgroup M) (s : J → W) (P : J → Subgroup M) (r : W → M)
    (hBH : B ≤ H)
    (hr : ∀ x y, ∃ t ∈ B, r x * r y = r (x * y) * t)
    (hrep : ∀ y ∈ Subgroup.closure (Set.range s), r y ∈ H)
    (hP : ∀ j, r (s j) ∈ P j)
    (hcover : (H : Set M) ⊆ ⋃ y : Subgroup.closure (Set.range s), (B : Set M) * {r y.val} * (B : Set M))
    (hstep : ∀ j x, ((B : Set M) * {r x} * (B : Set M)) * (P j : Set M) =
      ((B : Set M) * {r x} * (B : Set M)) ∪ ((B : Set M) * {r (x * s j)} * (B : Set M)))
    (w : W) :
    ((B : Set M) * {r w} * (B : Set M)) * (H : Set M) =
      ⋃ y : Subgroup.closure (Set.range s), (B : Set M) * {r (w * y.val)} * (B : Set M) := by
  let L := Subgroup.closure (Set.range s)
  let C (x : W) := (B : Set M) * {r x} * (B : Set M)
  let U := ⋃ y : L, C (w * y.val)
  have hC {x : W} {a : M} : a ∈ C x ↔ ∃ b ∈ B, ∃ c ∈ B, b * r x * c = a := by
    change a ∈ DoubleCoset.doubleCoset (r x) (B : Set M) (B : Set M) ↔ _
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe, eq_comm]
  have hU {a : M} : a ∈ U ↔ ∃ y : L, a ∈ C (w * y.val) := Set.mem_iUnion
  let stable (p : M) : Prop := ∀ a ∈ U, a * p ∈ U
  -- Multiplication by these elements and their inverses preserves the union.
  let S : Subgroup M :=
    { carrier := {p | stable p ∧ stable p⁻¹}
      one_mem' := ⟨by simp [stable], by simp [stable]⟩
      mul_mem' := by
        rintro p q ⟨hp, hp'⟩ ⟨hq, hq'⟩
        exact ⟨fun a ha ↦ by simpa only [mul_assoc] using hq (a * p) (hp a ha),
          fun a ha ↦ by simpa only [mul_inv_rev, mul_assoc] using hp' (a * q⁻¹) (hq' a ha)⟩
      inv_mem' := by
        rintro p ⟨hp, hp'⟩
        exact ⟨hp', by simpa only [inv_inv]⟩ }
  have hright {p : M} (hp : p ∈ B) : stable p := by
    intro a ha
    obtain ⟨y, hy⟩ := hU.mp ha
    obtain ⟨b, hb, c, hc, rfl⟩ := hC.mp hy
    exact hU.mpr ⟨y, hC.mpr ⟨b, hb, c * p, B.mul_mem hc hp, (mul_assoc _ _ _).symm⟩⟩
  have hBS : B ≤ S := fun p hp ↦ ⟨hright hp, hright (B.inv_mem hp)⟩
  have hPS (j : J) : P j ≤ S := by
    have hstable (p : M) (hp : p ∈ P j) : stable p := by
      intro a ha
      obtain ⟨y, hy⟩ := hU.mp ha
      have hz : a * p ∈ C (w * y.val) * (P j : Set M) := Set.mul_mem_mul hy hp
      rw [hstep j] at hz
      rcases hz with h | h
      · exact hU.mpr ⟨y, h⟩
      · let z : L := ⟨y.val * s j, L.mul_mem y.property (Subgroup.subset_closure ⟨j, rfl⟩)⟩
        have hz : w * y.val * s j = w * z.val := mul_assoc _ _ _
        rw [hz] at h
        exact hU.mpr ⟨z, h⟩
    exact fun p hp ↦ ⟨hstable p hp, hstable _ ((P j).inv_mem hp)⟩
  have h1 : r 1 ∈ B := by
    obtain ⟨t, ht, he⟩ := hr 1 1
    rw [one_mul] at he
    exact (mul_left_cancel he).symm ▸ ht
  have hrS (y : W) (hy : y ∈ L) : r y ∈ S := by
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact hPS j (hP j)
    | one => exact hBS h1
    | mul x y _ _ hx hy =>
      obtain ⟨t, ht, he⟩ := hr x y
      have he' : r (x * y) = (r x * r y) * t⁻¹ := by rw [he, mul_inv_cancel_right]
      rw [he']
      exact S.mul_mem (S.mul_mem hx hy) (S.inv_mem (hBS ht))
    | inv x _ hx =>
      obtain ⟨t, ht, he⟩ := hr x⁻¹ x
      rw [inv_mul_cancel] at he
      have he' : r x⁻¹ = r 1 * t * (r x)⁻¹ := by rw [← he, mul_inv_cancel_right]
      rw [he']
      exact S.mul_mem (S.mul_mem (hBS h1) (hBS ht)) (S.inv_mem hx)
  change C w * (H : Set M) = U
  apply le_antisymm
  · intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp ha
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp (hcover hy)
    obtain ⟨b, hb, c, hc, rfl⟩ := hC.mp hv
    have hs := S.mul_mem (S.mul_mem (hBS hb) (hrS v.val v.property)) (hBS hc)
    have hu : x ∈ U := hU.mpr ⟨1, by simpa using hx⟩
    exact hs.1 x hu
  · intro a ha
    obtain ⟨v, hv⟩ := hU.mp ha
    obtain ⟨b, hb, c, hc, rfl⟩ := hC.mp hv
    obtain ⟨t, ht, he⟩ := hr w v.val
    refine Set.mem_mul.mpr ⟨b * r w, hC.mpr ⟨b, hb, 1, B.one_mem, mul_one _⟩,
      r v.val * t⁻¹ * c,
      H.mul_mem (H.mul_mem (hrep _ v.property) (H.inv_mem (hBH ht))) (hBH hc), ?_⟩
    calc
      b * r w * (r v.val * t⁻¹ * c) = b * (r w * r v.val) * t⁻¹ * c := by group
      _ = b * r (w * v.val) * c := by rw [he]; group

private lemma geometric_to_range {X Z : SchemeOver k} {J : Type*} {Y : J → SchemeOver k}
    (f : Z ⟶ X) (g : ∀ j, Y j ⟶ X)
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
      let S := Over.mk (fieldSpecMap k K)
      ∀ p : S ⟶ X, (∃ a, a ≫ f = p) ↔ ∃ j, ∃ b, b ≫ g j = p) :
    Set.range f.left = ⋃ j, Set.range (g j).left := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨K, _, _, _, p, hp⟩ := geometricPointAt Z z
    obtain ⟨j, q, hq⟩ := (h K (p ≫ f)).mp ⟨p, rfl⟩
    exact Set.mem_iUnion.mpr ⟨j, q.left (IsLocalRing.closedPoint K), by
      change (q ≫ g j).left (IsLocalRing.closedPoint K) = _
      rw [hq]
      exact congrArg f.left hp⟩
  · intro hx
    obtain ⟨j, y, rfl⟩ := Set.mem_iUnion.mp hx
    obtain ⟨K, _, _, _, p, hp⟩ := geometricPointAt (Y j) y
    obtain ⟨q, hq⟩ := (h K (p ≫ g j)).mpr ⟨j, p, rfl⟩
    exact ⟨q.left (IsLocalRing.closedPoint K), by
      change (q ≫ f).left (IsLocalRing.closedPoint K) = _
      rw [hq]
      exact congrArg (g j).left hp⟩

set_option maxHeartbeats 1400000 in
private theorem cosetSaturation (hparabolic : Specs.StandardParabolicLevi.Statement.{u}) :
    SaturationStatement.{u} := by
  classical
  intro k _ G hG T B hT hTm hB hTB
  obtain ⟨hcomm, D, W, U, c, b, hc, hpos, hb, hpar⟩ := hparabolic G hG T B hT hTm hB hTB
  let := hcomm
  obtain ⟨_, E, V, _, c', b', _, hpos', hb', hrep', hrank⟩ :=
    LinearAlgebraicGroups.Flag.SimpleParabolicProduct.simpleParabolicProduct G hG T B hT hTm hB hTB
  have hpositive (i : Root T) : b.IsPos i ↔ i ∈ subgroupRoots T B := by
    rw [← hpos, hb.positive_iff]
    change (0 < evaluate D c (D.rootDatum.root i)) ↔ _
    rw [evaluate_root]
    rfl
  have hpositive' (i : Root T) : b'.IsPos i ↔ i ∈ subgroupRoots T B := by
    rw [← hpos', hb'.positive_iff]
    change (0 < evaluate E c' (E.rootDatum.root i)) ↔ _
    rw [evaluate_root]
    rfl
  have hsimple (i : Root T) (hi : i ∈ b.support) : i ∈ b'.support := by
    apply (hb'.simple_iff i).mpr
    obtain ⟨hp, hnd⟩ := (hb.simple_iff i).mp hi
    refine ⟨(hb'.positive_iff _).mp ((hpositive' _).mpr ((hpositive _).mp ((hb.positive_iff _).mpr hp))), ?_⟩
    intro j hj l hl he
    have hmap (x : Root T) (hx : x ∈ positive E.rootDatum (evaluate E c')) :
        x ∈ positive D.rootDatum (evaluate D c) :=
      (hb.positive_iff _).mp ((hpositive _).mpr ((hpositive' _).mp ((hb'.positive_iff _).mpr hx)))
    apply hnd j (hmap _ hj) l (hmap _ hl)
    simpa only [D.root_eq, E.root_eq] using he
  refine ⟨hcomm, D, W, U, c, b, hc, hpos, hb, ?_⟩
  intro I hI
  obtain ⟨P, hrep, hpres, hcells⟩ := hpar I hI
  refine ⟨P, hrep, hpres, ?_⟩
  intro Q n hn
  dsimp only
  obtain ⟨a, A, cells, ha, hP, hcover⟩ := hcells Q n hn
  let g := fun x ↦ n x ≫ W.normalizer.inclusion.hom.hom
  let H := P.limitGroups.parabolic
  let L := parabolicWeylGroup D I
  let s := fun i : I ↦ weylGroup.ofIdx D.rootDatum i.val
  have hL : Subgroup.closure (Set.range s) = L := by
    unfold L parabolicWeylGroup
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  obtain ⟨e, q, hq, hpoints, hperm⟩ := reindexRepresentatives W V n hn hrep'
  have hlabel (i : I) : e (s i) = weylGroup.ofIdx E.rootDatum i.val :=
    reindexSimpleReflection (fun j ↦ (hpositive j).trans (hpositive' j).symm) e hperm (hI i.property)
  have hgeo (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K] :
      let Y := Over.mk (fieldSpecMap k K)
      ∀ x, doubleCoset B Y (g x) * (SubgroupSections H Y : Set (Y ⟶ G.val.X)) =
        ⋃ y : L, doubleCoset B Y (g (x * y.val)) := by
    let Y := Over.mk (fieldSpecMap k K)
    let r := fun x ↦ toUnit Y ≫ g x
    let C := fun x ↦ doubleCoset B Y (g x)
    let BS := SubgroupSections B Y
    let HS := SubgroupSections H Y
    have hstep (i : I) : ∃ S : Subgroup (Y ⟶ G.val.X),
        r (s i) ∈ S ∧ ∀ x, C x * (S : Set (Y ⟶ G.val.X)) = C x ∪ C (x * s i) := by
      obtain ⟨wall, Ps, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrule⟩ :=
        hrank i.val (hsimple _ (hI i.property))
      obtain ⟨hPs, _, _, hsteps⟩ := hrule q hq K
      let S := SubgroupSections Ps.parabolic Y
      refine ⟨S, ?_, fun x ↦ ?_⟩
      · have hm : r (s i) ∈ C (s i) := mem_doubleCoset_iff.mpr
          ⟨1, BS.one_mem, 1, BS.one_mem, by simp [r]⟩
        have hPs' : (S : Set (Y ⟶ G.val.X)) = (BS : Set (Y ⟶ G.val.X)) ∪ C (s i) := by
          simpa only [← hlabel i, hpoints] using hPs
        change r (s i) ∈ (S : Set (Y ⟶ G.val.X))
        rw [hPs']
        exact Or.inr hm
      · simpa only [← hlabel i, ← e.map_mul, hpoints] using (hsteps (e x)).1
    choose S hS hsteps using hstep
    have hgeom_cover : (HS : Set (Y ⟶ G.val.X)) ⊆ ⋃ y : L, C y.val := by
      intro p hp
      obtain ⟨p', rfl⟩ := hp
      have h := congrArg (fun S : Set G.val.X.left ↦
          (p' ≫ H.inclusion.hom.hom).left (IsLocalRing.closedPoint K) ∈ S) hcover
      have hmem := h.mpr ⟨p'.left (IsLocalRing.closedPoint K), rfl⟩
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hmem
      exact Set.mem_iUnion.mpr ⟨y, (cell_sections_iff (cells y.val) _).mpr
        ((fieldPoint_factors_immersion _ _ (cells y.val).doubleOrbitImmersion).mp hy)⟩
    change ∀ x, C x * (HS : Set (Y ⟶ G.val.X)) = ⋃ y : L, C (x * y.val)
    intro x
    rw [← hL]
    apply saturate_doubleCosets BS HS s S r (mem_sections_of_subgroupOf P.containsBorel)
    · intro a b
      obtain ⟨t, ht, he⟩ := representative_product W n hn Y a b
      exact ⟨t, mem_sections_of_subgroupOf hTB ht, by simpa only [r, g] using he⟩
    · intro y hy
      rw [hL] at hy
      obtain ⟨p, hp⟩ := (hP y).mpr hy
      change p ≫ H.inclusion.hom.hom = g y at hp
      refine ⟨toUnit Y ≫ p, ?_⟩
      change (toUnit Y ≫ p) ≫ H.inclusion.hom.hom = toUnit Y ≫ g y
      rw [Category.assoc, hp]
    · exact hS
    · change (HS : Set (Y ⟶ G.val.X)) ⊆ ⋃ y : Subgroup.closure (Set.range s), C y.val
      rw [hL]
      exact hgeom_cover
    · exact hsteps
  refine ⟨a, A, cells, ha, hgeo, ?_⟩
  intro x
  apply geometric_to_range _ (fun y : L ↦ (cells (x * y.val)).doubleOrbitInclusion)
  intro K _ _ _
  dsimp only
  intro p
  let Y := Over.mk (fieldSpecMap k K)
  let F := (fst (cells x).doubleOrbit H.group.X ≫ (cells x).doubleOrbitInclusion) *
      (snd (cells x).doubleOrbit H.group.X ≫ H.inclusion.hom.hom)
  have hF : (∃ t : Y ⟶ _, t ≫ F = p) ↔
      p ∈ doubleCoset B Y (g x) * (SubgroupSections H Y : Set (Y ⟶ G.val.X)) := by
    constructor
    · rintro ⟨t, rfl⟩
      rw [MonObj.comp_mul]
      exact Set.mul_mem_mul ((cell_sections_iff (cells x) _).mpr ⟨t ≫ fst _ _, rfl⟩)
        ⟨t ≫ snd _ _, rfl⟩
    · intro hp
      obtain ⟨l, hl, r, hr, rfl⟩ := Set.mem_mul.mp hp
      obtain ⟨t, ht⟩ := (cell_sections_iff (cells x) l).mp hl
      obtain ⟨q, hq⟩ := hr
      change q ≫ H.inclusion.hom.hom = r at hq
      refine ⟨lift t q, ?_⟩
      dsimp only [F]
      rw [MonObj.comp_mul]
      have hf₁ : lift t q ≫ fst (cells x).doubleOrbit H.group.X ≫
          (cells x).doubleOrbitInclusion = l :=
        (lift_fst_assoc t q _).trans ht
      have hf₂ : lift t q ≫ snd (cells x).doubleOrbit H.group.X ≫ H.inclusion.hom.hom = r :=
        (lift_snd_assoc t q _).trans hq
      rw [hf₁, hf₂]
  rw [hF, hgeo K x, Set.mem_iUnion]
  exact exists_congr fun y ↦ cell_sections_iff (cells (x * y.val)) p

end Saturation

/-- Conditional parabolic coset length and saturation for the ordered Bruhat and Levi interfaces. -/
theorem parabolicCosetLength_conditional.{field, index, weight, coweight}
    (_bruhat : Specs.BruhatCells.Statement.{field})
    (parabolic : Specs.StandardParabolicLevi.Statement.{field}) :
    Specs.ParabolicCosetLength.Statement.{field, index, weight, coweight} :=
  ⟨cosetSaturation parabolic, cosetLength⟩

end

end LinearAlgebraicGroups.Flag.ParabolicCosetLength

universe v8_closure_a5a14f128dd22d95_u0 v8_closure_a5a14f128dd22d95_u1 v8_closure_a5a14f128dd22d95_u2 v8_closure_a5a14f128dd22d95_u3
theorem _root_.«LinearAlgebraicGroups».«Flag».«ParabolicCosetLength».«parabolicCosetLength» : _root_.«LinearAlgebraicGroups».«Specs».«ParabolicCosetLength».«Statement».{v8_closure_a5a14f128dd22d95_u0, v8_closure_a5a14f128dd22d95_u1, v8_closure_a5a14f128dd22d95_u2, v8_closure_a5a14f128dd22d95_u3} :=
  @_root_.«LinearAlgebraicGroups».«Flag».«ParabolicCosetLength».«parabolicCosetLength_conditional».{v8_closure_a5a14f128dd22d95_u0, v8_closure_a5a14f128dd22d95_u1, v8_closure_a5a14f128dd22d95_u2, v8_closure_a5a14f128dd22d95_u3} (@_root_.«LinearAlgebraicGroups».«Flag».«BruhatCells».«bruhatCells».{v8_closure_a5a14f128dd22d95_u0}) (@_root_.«LinearAlgebraicGroups».«Flag».«StandardParabolicLevi».«standardParabolicLevi».{v8_closure_a5a14f128dd22d95_u0})
