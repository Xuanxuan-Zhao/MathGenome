import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems
import LinearAlgebraicGroups.Arithmetic.AffineArrangementAlcoves
import LinearAlgebraicGroups.Arithmetic.CoxeterPresentationFromDeletion
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import LinearAlgebraicGroups.RootData.EuclideanComparison
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Interval.Finset.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems

universe u v w z

open Specs.ExceptionalAffineRootSystems
open scoped Matrix BigOperators TensorProduct

private theorem wall_threshold_iff {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] (a : K) (n : ℤ) :
    threshold a ≤ n ↔ 0 < a + (n : K) := by
  rw [threshold, ← Int.lt_iff_add_one_le, Int.floor_lt]
  constructor <;> intro h <;> linarith only [h]

private theorem separating_iff {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] (a b : K)
    (hb : b ∉ Set.range (Int.cast : ℤ → K)) (n : ℤ) :
    n ∈ separatingLevels a b ↔ 0 < a + (n : K) ∧ b + (n : K) < 0 := by
  have hne : b + (n : K) ≠ 0 := by
    intro h
    apply hb
    exact ⟨-n, by push_cast; linarith only [h]⟩
  have hn : n < threshold b ↔ b + (n : K) < 0 := by
    rw [← not_le, wall_threshold_iff, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩
  rw [separatingLevels, Finset.mem_Ico, wall_threshold_iff, hn]

theorem thresholdCount : ThresholdCount := by
  intro K _ _ _ _ a b ha hb
  refine ⟨wall_threshold_iff a, separating_iff a b hb, Int.card_Ico _ _, ?_⟩
  have hn (v : K) (hv : v ∉ Set.range (Int.cast : ℤ → K)) :
      threshold (-v) + threshold v = 1 := by
    simp only [threshold, neg_neg, Int.floor_neg, (Int.ceil_eq_floor_add_one_iff_notMem v).2 hv]
    omega
  have ha' := hn a ha
  have hb' := hn b hb
  omega

theorem oppositeWallCount : OppositeWallCount := by
  intro K _ _ _ _ a b ha hb
  have hneg (v : K) (hv : v ∉ Set.range (Int.cast : ℤ → K)) :
      -v ∉ Set.range (Int.cast : ℤ → K) := by
    rintro ⟨n, hn⟩
    apply hv
    exact ⟨-n, by push_cast; linarith only [hn]⟩
  have h₁ := thresholdCount a b ha hb
  have h₂ := thresholdCount (-a) (-b) (hneg a ha) (hneg b hb)
  have hmem (n : ℤ) :
      n ∈ Neg.neg '' (↑(separatingLevels (-a) (-b)) : Set ℤ) ↔
        a + (n : K) < 0 ∧ 0 < b + (n : K) := by
    rw [Set.mem_image]
    constructor
    · rintro ⟨m, hm, rfl⟩
      rw [Finset.mem_coe, h₂.2.1] at hm
      push_cast
      exact ⟨by linarith only [hm.1], by linarith only [hm.2]⟩
    · intro hn
      refine ⟨-n, ?_, neg_neg n⟩
      rw [Finset.mem_coe, h₂.2.1]
      push_cast
      exact ⟨by linarith only [hn.1], by linarith only [hn.2]⟩
  refine ⟨?_, ?_, ?_⟩
  · ext n
    simp only [Set.mem_ofPred_eq, Set.mem_union, Finset.mem_coe, h₁.2.1, hmem]
  · refine Set.disjoint_left.2 ?_
    intro n hn hn'
    rw [Finset.mem_coe, h₁.2.1] at hn
    rw [hmem] at hn'
    exact (not_lt_of_gt hn.1) hn'.1
  · rw [h₁.2.2.1, h₂.2.2.1, h₁.2.2.2]
    omega

theorem separatingWallSum : SeparatingWallSum := by
  intro ι K _ _ _ _ _ x y hx hy
  apply Finset.sum_congr rfl
  intro i _
  have h := (thresholdCount (x i) (y i) (hx i) (hy i)).2.2.2
  rw [h]
  omega

theorem normalizeWall : NormalizeWall.{u} := by
  intro K _ _ _ a d hd n
  have hd' : (0 : K) < (d : K) := by exact_mod_cast hd
  have hm : (d : K) * (a + (n : K) / d) = (d : K) * a + n := by
    rw [mul_add, mul_div_cancel₀ _ hd'.ne']
  rw [← hm, mul_eq_zero, or_iff_right hd'.ne', mul_pos_iff_of_pos_left hd']
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem affineThresholdCount : AffineThresholdCount.{u,v,w} := by
  classical
  intro K V ι _ _ _ _ _ _ _ D x y _ hy
  let f (i : ι) := separatingLevels (D.root i x) (D.root i y)
  let F := (Finset.univ.sigma f).map (Equiv.sigmaEquivProd ι ℤ).toEmbedding
  have hF : D.orientedSeparators x y = (F : Set (ι × ℤ)) := by
    ext ⟨i, n⟩
    rw [Finset.mem_coe, Finset.mem_map_equiv]
    change (0 < D.root i x + (n : K) ∧ D.root i y + (n : K) < 0) ↔ ⟨i, n⟩ ∈ Finset.univ.sigma f
    simpa only [Finset.mem_sigma, Finset.mem_univ, true_and] using
      (separating_iff (D.root i x) (D.root i y) (hy i) n).symm
  rw [hF]
  refine ⟨F.finite_toSet, ?_⟩
  rw [Set.ncard_coe_finset, Finset.card_map, Finset.card_sigma]
  exact Finset.sum_congr rfl fun i _ => Int.card_Ico _ _

section SignedWalls

variable {W S A : Type*} [Group W] [MulAction W A] {s : S → W}
    (H : SignedWallAction (A := A) s)

@[simp] private theorem wallWord_nil : wallWord s [] = 1 := rfl

@[simp] private theorem wallWord_cons (i : S) (l : List S) :
    wallWord s (i :: l) = s i * wallWord s l := rfl

@[simp] private theorem wallWord_single (i : S) : wallWord s [i] = s i := by simp

private theorem wallWord_append (l k : List S) :
    wallWord s (l ++ k) = wallWord s l * wallWord s k := by
  simp only [wallWord, List.map_append, List.prod_append]

private def inversionWalls (w : W) : Set A :=
  {a | H.positive a ∧ ¬ H.positive (w • a)}

include H in
private theorem simpleWall_mul_self (i : S) : s i * s i = 1 := by
  rw [← H.simple_reflect i, H.reflection_sq]

include H in
private theorem wallAction_simple_invol (i : S) (a : A) : s i • (s i • a) = a := by
  rw [← mul_smul, simpleWall_mul_self H i, one_smul]

private theorem removeCrossing (l : List S) {a : A} (ha : H.positive a)
    (hn : ¬ H.positive (wallWord s l • a)) :
    ∃ (p q : List S) (i : S), l = p ++ i :: q ∧
      wallWord s (p ++ q) = wallWord s l * H.reflect a := by
  induction l with
  | nil => simp at hn; exact False.elim (hn ha)
  | cons i l ih =>
    by_cases hp : H.positive (wallWord s l • a)
    · have he : wallWord s l • a = H.simple i := by
        by_contra h
        exact hn (by simpa only [wallWord_cons, mul_smul] using H.simple_preserves i hp h)
      have hc := H.conjugate_reflect (wallWord s l) a
      rw [he, H.simple_reflect] at hc
      refine ⟨[], l, i, rfl, ?_⟩
      let u := wallWord s l
      rw [wallWord_cons, hc]
      change u = (u * H.reflect a * u⁻¹) * u * H.reflect a
      rw [mul_assoc (u * H.reflect a) u⁻¹ u, inv_mul_cancel, mul_one, mul_assoc,
        H.reflection_sq, mul_one]
    · obtain ⟨p, q, j, hpq, he⟩ := ih hp
      refine ⟨i :: p, q, j, congrArg (List.cons i) hpq, ?_⟩
      change s i * wallWord s (p ++ q) = (s i * wallWord s l) * H.reflect a
      rw [he, mul_assoc]

private theorem inversion_subset (w : W) (i : S) :
    inversionWalls H (w * s i) ⊆
      insert (H.simple i) ((fun a => s i • a) '' inversionWalls H w) := by
  intro a ha
  by_cases he : a = H.simple i
  · exact Or.inl he
  · exact Or.inr ⟨s i • a,
      ⟨H.simple_preserves i ha.1 he, by simpa only [mul_smul] using ha.2⟩,
      wallAction_simple_invol H i a⟩

private theorem inversion_word_bounds (l : List S) :
    (inversionWalls H (wallWord s l)).Finite ∧
      (inversionWalls H (wallWord s l)).ncard ≤ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [inversionWalls]
  | append_singleton l i ih =>
    rw [wallWord_append, wallWord_single, List.length_append, List.length_singleton]
    let f : A → A := fun a => s i • a
    have hfin := (ih.1.image f).insert (H.simple i)
    have hinj : Function.Injective f := fun a b h => by
      simpa only [f, wallAction_simple_invol H] using congrArg f h
    refine ⟨hfin.subset (inversion_subset H _ i), ?_⟩
    calc
      _ ≤ (insert (H.simple i) (f '' inversionWalls H (wallWord s l))).ncard :=
        Set.ncard_le_ncard (inversion_subset H _ i) hfin
      _ ≤ (f '' inversionWalls H (wallWord s l)).ncard + 1 := Set.ncard_insert_le _ _
      _ ≤ l.length + 1 := by rw [Set.ncard_image_of_injective _ hinj]; exact Nat.add_le_add_right ih.2 1

private theorem inversion_ascend (w : W) (i : S) (hp : H.positive (w • H.simple i))
    (hf : (inversionWalls H w).Finite) :
    (inversionWalls H (w * s i)).ncard = (inversionWalls H w).ncard + 1 := by
  have he : inversionWalls H (w * s i) =
      insert (H.simple i) ((fun a => s i • a) '' inversionWalls H w) := by
    apply Set.Subset.antisymm (inversion_subset H w i)
    rintro a (rfl | ⟨b, hb, rfl⟩)
    · refine ⟨H.simple_positive i, ?_⟩
      rw [mul_smul, H.simple_opposite, H.smul_opposite, H.opposite_positive]
      exact fun h => h hp
    · have hb' : b ≠ H.simple i := fun h => hb.2 (h.symm ▸ hp)
      exact ⟨H.simple_preserves i hb.1 hb', by
        simpa only [mul_smul, wallAction_simple_invol H] using hb.2⟩
  have hnot : H.simple i ∉ (fun a => s i • a) '' inversionWalls H w := by
    rintro ⟨a, ha, he⟩
    have he' : a = H.opposite (H.simple i) := by
      have hi := congrArg (fun x => s i • x) he
      rwa [wallAction_simple_invol H, H.simple_opposite] at hi
    exact (H.opposite_positive _).mp (he' ▸ ha.1) (H.simple_positive i)
  rw [he, Set.ncard_insert_of_notMem hnot (hf.image _), Set.ncard_image_of_injective]
  intro a b hab
  simpa only [wallAction_simple_invol H] using congrArg (fun c => s i • c) hab

private theorem shortestWord_inversionCount (l : List S)
    (hmin : ∀ k : List S, wallWord s k = wallWord s l → l.length ≤ k.length) :
    (inversionWalls H (wallWord s l)).ncard = l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [inversionWalls]
  | append_singleton l i ih =>
    have hp : H.positive (wallWord s l • H.simple i) := by
      by_contra hn
      obtain ⟨p, q, j, h, he⟩ := removeCrossing H l (H.simple_positive i) hn
      have hlen := congrArg List.length h
      have hm := hmin (p ++ q) (by simpa only [H.simple_reflect, wallWord_append,
        wallWord_single] using he)
      simp only [List.length_append, List.length_cons] at hlen hm
      omega
    have hl : ∀ k : List S, wallWord s k = wallWord s l → l.length ≤ k.length := by
      intro k hk
      have h := hmin (k ++ [i]) (by simp only [wallWord_append, hk])
      simpa using h
    simp only [wallWord_append, wallWord_single, List.length_append, List.length_singleton,
      inversion_ascend H _ _ hp (inversion_word_bounds H l).1, ih hl]

private theorem inversion_finite {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    (H : SignedWallAction (A := A) cs.simple) (w : W) : (inversionWalls H w).Finite := by
  obtain ⟨l, rfl⟩ := cs.wordProd_surjective w
  exact (inversion_word_bounds H l).1

private theorem inverseWalls_length {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    (H : SignedWallAction (A := A) cs.simple) (w : W) : (inversionWalls H w).ncard = cs.length w := by
  obtain ⟨l, hl, rfl⟩ := cs.exists_isReduced w
  change (inversionWalls H (wallWord cs.simple l)).ncard = cs.length (cs.wordProd l)
  rw [hl.eq, shortestWord_inversionCount H l]
  intro k hk
  change cs.wordProd k = cs.wordProd l at hk
  simpa only [hk, hl.eq] using cs.length_wordProd_le k

theorem wallSignsAndLength : WallSignsAndLength.{u,v,w} := by
  intro W S A _ _ M cs H
  refine ⟨fun w => ⟨inversion_finite cs H w⁻¹,
    (inverseWalls_length cs H w⁻¹).trans (cs.length_inv w)⟩, ?_⟩
  intro w i
  refine ⟨?_, ?_⟩
  · intro hp
    simpa only [inverseWalls_length cs H] using inversion_ascend H w i hp (inversion_finite cs H w)
  · intro hn
    have hp : H.positive ((w * cs.simple i) • H.simple i) := by
      rw [mul_smul, H.simple_opposite, H.smul_opposite, H.opposite_positive]
      exact hn
    have h := inversion_ascend H (w * cs.simple i) i hp (inversion_finite cs H _)
    rw [mul_assoc, cs.simple_mul_simple_self, mul_one, inverseWalls_length cs H,
      inverseWalls_length cs H] at h
    exact h.symm

include H in
private theorem wallWord_reverse (l : List S) : wallWord s l.reverse = (wallWord s l)⁻¹ := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hi : (s i)⁻¹ = s i := (eq_inv_of_mul_eq_one_right (simpleWall_mul_self H i)).symm
    simp [List.reverse_cons, wallWord_append, mul_inv_rev, ih, hi]

theorem signedWallDeletion : SignedWallDeletion.{u,v,w} := by
  classical
  intro W S A _ _ s H
  refine ⟨?_, ?_⟩
  · intro l
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton l i ih =>
      rintro ⟨k, hk, hlen⟩
      by_cases hmin : ∀ v : List S, wallWord s v = wallWord s l → l.length ≤ v.length
      · have hn : ¬ H.positive (wallWord s l • H.simple i) := by
          intro hp
          have h := inversion_ascend H (wallWord s l) i hp (inversion_word_bounds H l).1
          rw [shortestWord_inversionCount H l hmin] at h
          have hb := (inversion_word_bounds H k).2
          rw [hk, wallWord_append, wallWord_single, h] at hb
          exact not_lt_of_ge hb (by simpa only [List.length_append, List.length_singleton] using hlen)
        obtain ⟨p, m, j, h, he⟩ := removeCrossing H l (H.simple_positive i) hn
        refine ⟨p, m, [], j, i, by rw [h]; simp, ?_⟩
        simpa only [List.append_nil, H.simple_reflect, wallWord_append, wallWord_single] using he
      · push Not at hmin
        obtain ⟨p, m, q, j, j', h, he⟩ := ih hmin
        refine ⟨p, m, q ++ [i], j, j', ?_, ?_⟩
        · rw [h]; simp [List.append_assoc]
        · simp only [← List.append_assoc, wallWord_append, wallWord_single, he]
  · intro x hx hzero
    have hex : ∃ n : ℕ, ∃ l : List S, l.length = n ∧ wallWord s l = x⁻¹ := by
      obtain ⟨l, rfl⟩ := hx
      exact ⟨l.reverse.length, l.reverse, rfl, wallWord_reverse H l⟩
    obtain ⟨l, hl, hx'⟩ := Nat.find_spec hex
    have hmin (k : List S) (hk : wallWord s k = wallWord s l) : l.length ≤ k.length :=
      hl.trans_le (Nat.find_min' hex ⟨k, rfl, hk.trans hx'⟩)
    have h := (shortestWord_inversionCount H l hmin).symm
    rw [hx'] at h
    change l.length = (separatingWalls H x).ncard at h
    rw [hzero, Set.ncard_empty] at h
    rw [List.length_eq_zero_iff.mp h, wallWord_nil] at hx'
    simpa using hx'.symm

end SignedWalls

section AffineGroups

open ApartmentRoots

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (D : ApartmentRoots K V ι)

private theorem corootLattice_le_coweightLattice : D.corootLattice ≤ D.coweightLattice := by
  rw [corootLattice, AddSubgroup.closure_le]
  rintro _ ⟨j, rfl⟩ i
  exact D.integral i j

private theorem linearReflection_congr (i : ι) {x : V} (hx : x ∈ D.coweightLattice) :
    D.linearReflection i x - x ∈ D.corootLattice := by
  obtain ⟨n, hn⟩ := hx i
  change Module.reflection (D.diagonal i) x - x ∈ D.corootLattice
  rw [Module.reflection_apply, hn, Int.cast_smul_eq_zsmul, sub_sub_cancel_left]
  exact D.corootLattice.neg_mem (D.corootLattice.zsmul_mem
    (AddSubgroup.subset_closure (Set.mem_range_self i)) n)

private theorem linearWeyl_congr {w : V ≃ₗ[K] V} (hw : w ∈ D.linearWeylGroup) :
    ∀ x ∈ D.coweightLattice, w x - x ∈ D.corootLattice ∧ w⁻¹ x - x ∈ D.corootLattice := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    intro x hx
    have h := linearReflection_congr D i hx
    exact ⟨h, h⟩
  | one =>
    intro x hx
    simp
  | mul w v hw hv ihw ihv =>
    have step (f g : V ≃ₗ[K] V) (x : V) (hx : x ∈ D.coweightLattice)
        (hfx : ∀ y ∈ D.coweightLattice, f y - y ∈ D.corootLattice)
        (hgx : g x - x ∈ D.corootLattice) :
        f (g x) - x ∈ D.corootLattice := by
      have h' : g x ∈ D.coweightLattice := by
        simpa using D.coweightLattice.add_mem (corootLattice_le_coweightLattice D hgx) hx
      simpa only [sub_add_sub_cancel] using D.corootLattice.add_mem (hfx _ h') hgx
    intro x hx
    exact ⟨step w v x hx (fun y hy => (ihw y hy).1) (ihv x hx).1,
      step v⁻¹ w⁻¹ x hx (fun y hy => (ihv y hy).2) (ihw x hx).2⟩
  | inv w hw ih =>
    intro x hx
    simpa only [inv_inv] using (ih x hx).symm

private theorem linearWeyl_stable {L : AddSubgroup V} (hQ : D.corootLattice ≤ L)
    (hP : L ≤ D.coweightLattice) {w : V ≃ₗ[K] V} (hw : w ∈ D.linearWeylGroup)
    {x : V} (hx : x ∈ L) : w x ∈ L := by
  simpa using L.add_mem (hQ (linearWeyl_congr D hw x (hP hx)).1) hx

private theorem affine_value (g : V ≃ᵃ[K] V) (x : V) : g x = g.linear x + g 0 := by
  simpa using g.map_vadd (0 : V) x

private def affineWithLattice (L : AddSubgroup V) (hQ : D.corootLattice ≤ L)
    (hP : L ≤ D.coweightLattice) : Subgroup (V ≃ᵃ[K] V) where
  carrier := {g | g 0 ∈ L ∧ g.linear ∈ D.linearWeylGroup}
  one_mem' := ⟨L.zero_mem, D.linearWeylGroup.one_mem⟩
  mul_mem' := by
    rintro g h ⟨hg, hgl⟩ ⟨hh, hhl⟩
    have hh' : (g * h) 0 = g.linear (h 0) + g 0 := affine_value g (h 0)
    exact ⟨hh'.symm ▸ L.add_mem (linearWeyl_stable D hQ hP hgl hh) hg,
      D.linearWeylGroup.mul_mem hgl hhl⟩
  inv_mem' := by
    rintro g ⟨hg, hgl⟩
    have hil : (g⁻¹).linear ∈ D.linearWeylGroup := D.linearWeylGroup.inv_mem hgl
    have hi : (g⁻¹) (g 0) = (0 : V) := g.symm_apply_apply _
    rw [affine_value] at hi
    exact ⟨eq_neg_of_add_eq_zero_right hi ▸ L.neg_mem (linearWeyl_stable D hQ hP hil hg), hil⟩

private def linearAffineHom : (V ≃ₗ[K] V) →* (V ≃ᵃ[K] V) where
  toFun := LinearEquiv.toAffineEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem linear_mem_of_generators (A : Subgroup (V ≃ᵃ[K] V))
    (hA : ∀ i, (D.linearReflection i).toAffineEquiv ∈ A)
    {w : V ≃ₗ[K] V} (hw : w ∈ D.linearWeylGroup) : w.toAffineEquiv ∈ A := by
  have hle : D.linearWeylGroup ≤ A.comap linearAffineHom := by
    rw [linearWeylGroup, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hA i
  exact hle hw

private theorem translation_mul_linear (g : V ≃ᵃ[K] V) :
    AffineEquiv.constVAdd K V (g 0) * g.linear.toAffineEquiv = g := by
  ext x
  rw [affine_value g x]
  change g 0 + g.linear x = _
  exact add_comm _ _

private theorem wall_mem (i : ι) (n : ℤ) : D.wallReflection i n ∈ D.affineWeylGroup :=
  Subgroup.subset_closure (Set.mem_range_self (i, n))

private theorem linear_mem_affine (i : ι) :
    (D.linearReflection i).toAffineEquiv ∈ D.affineWeylGroup := by
  have h := wall_mem D i 0
  change AffineEquiv.constVAdd K V ((-(0 : ℤ)) • D.coroot i) *
    (D.linearReflection i).toAffineEquiv ∈ D.affineWeylGroup at h
  rwa [neg_zero, zero_zsmul, AffineEquiv.constVAdd_zero,
    ← AffineEquiv.one_def, one_mul] at h

private theorem translation_mem_affine {x : V} (hx : x ∈ D.corootLattice) :
    AffineEquiv.constVAdd K V x ∈ D.affineWeylGroup := by
  induction hx using AddSubgroup.closure_induction with
  | mem t ht =>
    obtain ⟨i, rfl⟩ := ht
    have h := D.affineWeylGroup.mul_mem (wall_mem D i (-1))
      (D.affineWeylGroup.inv_mem (linear_mem_affine D i))
    simpa [AffineArrangement.Datum.reflection, mul_assoc] using h
  | zero =>
    rw [AffineEquiv.constVAdd_zero, ← AffineEquiv.one_def]
    exact D.affineWeylGroup.one_mem
  | add x y hx hy ihx ihy =>
    rw [AffineEquiv.constVAdd_add, ← AffineEquiv.mul_def]
    exact D.affineWeylGroup.mul_mem ihx ihy
  | neg x hx ih =>
    simpa only [AffineEquiv.inv_def, AffineEquiv.constVAdd_symm] using
      D.affineWeylGroup.inv_mem ih

private theorem affine_mem_iff (g : V ≃ᵃ[K] V) :
    g ∈ D.affineWeylGroup ↔ g 0 ∈ D.corootLattice ∧ g.linear ∈ D.linearWeylGroup := by
  constructor
  · have hle : D.affineWeylGroup ≤ affineWithLattice D D.corootLattice le_rfl
        (corootLattice_le_coweightLattice D) := by
      change Subgroup.closure (Set.range D.reflection) ≤ _
      rw [Subgroup.closure_le]
      rintro _ ⟨⟨i, n⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [AffineArrangement.Datum.reflection] using D.corootLattice.zsmul_mem
          (AddSubgroup.subset_closure (Set.mem_range_self i)) (-n)
      · change (1 : V ≃ₗ[K] V) * D.linearReflection i ∈ D.linearWeylGroup
        rw [one_mul]
        exact Subgroup.subset_closure (Set.mem_range_self i)
    intro hg
    exact hle hg
  · rintro ⟨ht, hl⟩
    rw [← translation_mul_linear g]
    exact D.affineWeylGroup.mul_mem (translation_mem_affine D ht)
      (linear_mem_of_generators D _ (linear_mem_affine D) hl)

private theorem extended_mem_iff (g : V ≃ᵃ[K] V) :
    g ∈ D.extendedAffineWeylGroup ↔ g 0 ∈ D.coweightLattice ∧ g.linear ∈ D.linearWeylGroup := by
  have ht {t : V} (ht : t ∈ D.coweightLattice) :
      AffineEquiv.constVAdd K V t ∈ D.extendedAffineWeylGroup :=
    Subgroup.subset_closure (Or.inr ⟨t, ht, rfl⟩)
  have hl (i : ι) : (D.linearReflection i).toAffineEquiv ∈ D.extendedAffineWeylGroup :=
    Subgroup.subset_closure (Or.inl (Set.mem_range_self i))
  constructor
  · have hle : D.extendedAffineWeylGroup ≤
        affineWithLattice D D.coweightLattice (corootLattice_le_coweightLattice D) le_rfl := by
      change Subgroup.closure
        (Set.range (fun i => (D.linearReflection i).toAffineEquiv) ∪
          AffineEquiv.constVAdd K V '' (D.coweightLattice : Set V)) ≤ _
      rw [Subgroup.closure_le]
      rintro _ (⟨i, rfl⟩ | ⟨t, ht, rfl⟩)
      · exact ⟨by simp, Subgroup.subset_closure (Set.mem_range_self i)⟩
      · exact ⟨by simpa using ht, D.linearWeylGroup.one_mem⟩
    intro hg
    exact hle hg
  · rintro ⟨hg, hgl⟩
    rw [← translation_mul_linear g]
    exact D.extendedAffineWeylGroup.mul_mem (ht hg) (linear_mem_of_generators D _ hl hgl)

theorem affineGroupNormalForms : AffineGroupNormalForms.{u,v,w} := by
  intro K V ι _ _ _ D
  refine ⟨?_, affine_mem_iff D, extended_mem_iff D⟩
  exact fun i n x => AffineArrangement.reflectionFormula D (i, n) x

theorem extendedTranslationQuotient : ExtendedTranslationQuotient.{u,v,w} := by
  intro K V ι _ _ _ D Q
  let t (g : D.extendedAffineWeylGroup) : D.coweightLattice :=
    ⟨g.val 0, ((extended_mem_iff D g.val).mp g.property).1⟩
  let q := QuotientAddGroup.mk' Q
  let f : D.extendedAffineWeylGroup →* Multiplicative (D.coweightLattice ⧸ Q) :=
    { toFun := fun g => Multiplicative.ofAdd (q (t g))
      map_one' := by change Multiplicative.ofAdd (q 0) = 1; rw [map_zero]; rfl
      map_mul' := by
        intro g h
        have hdiff : t (g * h) - (t g + t h) ∈ Q := by
          change g.val (h.val 0) - (g.val 0 + h.val 0) ∈ D.corootLattice
          rw [affine_value g.val (h.val 0)]
          have he : g.val.linear (h.val 0) + g.val 0 - (g.val 0 + h.val 0) =
              g.val.linear (h.val 0) - h.val 0 := by abel
          rw [he]
          exact (linearWeyl_congr D ((extended_mem_iff D _).mp g.property).2 _ (t h).property).1
        have he : q (t (g * h)) = q (t g + t h) := by
          apply sub_eq_zero.mp
          rw [← map_sub]
          exact (QuotientAddGroup.eq_zero_iff _).mpr hdiff
        change Multiplicative.ofAdd (q (t (g * h))) =
          Multiplicative.ofAdd (q (t g) + q (t h))
        rw [he, map_add] }
  refine ⟨f, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective Q z.toAdd
    have hh : AffineEquiv.constVAdd K V x.val ∈ D.extendedAffineWeylGroup :=
      (extended_mem_iff D _).mpr ⟨by simpa only [AffineEquiv.constVAdd_apply, vadd_eq_add, add_zero] using x.property,
        D.linearWeylGroup.one_mem⟩
    refine ⟨⟨_, hh⟩, ?_⟩
    have ht : t ⟨AffineEquiv.constVAdd K V x.val, hh⟩ = x := by
      apply Subtype.ext
      simp [t]
    change Multiplicative.ofAdd (q (t ⟨_, hh⟩)) = z
    rw [ht, hx]
    rfl
  · intro g x hx
    have : t g = x := Subtype.ext hx
    change Multiplicative.ofAdd (q (t g)) = _
    rw [this]
  · intro g
    change ((t g : D.coweightLattice) : D.coweightLattice ⧸ Q) = 0 ↔
      g.val ∈ D.affineWeylGroup
    rw [QuotientAddGroup.eq_zero_iff, affine_mem_iff]
    exact and_iff_left ((extended_mem_iff D _).mp g.property).2 |>.symm

theorem alcoveStabilizerQuotient : AlcoveStabilizerQuotient.{u,v,w} := by
  intro K V ι _ _ _ D C hc Q
  obtain ⟨f, hf, _, hker⟩ := extendedTranslationQuotient D
  have hle : D.affineWeylGroup ≤ D.extendedAffineWeylGroup := by
    intro g hg
    obtain ⟨hg, hl⟩ := (affine_mem_iff D g).mp hg
    exact (extended_mem_iff D g).mpr ⟨corootLattice_le_coweightLattice D hg, hl⟩
  let inc := Subgroup.inclusion hle
  let st := alcoveStabilizer D C
  let φ : st →* Multiplicative (D.coweightLattice ⧸ Q) := f.comp st.subtype
  refine ⟨MulEquiv.ofBijective φ ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have hw := (hker g.val).mp hg
    have hC : g.val.val '' C = C := g.property
    have hu := (hc (1 : D.extendedAffineWeylGroup)).unique (y₁ := ⟨g.val.val, hw⟩) (y₂ := 1)
    have he : (⟨g.val.val, hw⟩ : D.affineWeylGroup) = 1 := hu (by simpa using hC) (by simp)
    have hv : (g.val.val : V ≃ᵃ[K] V) = 1 :=
      congrArg (fun w : D.affineWeylGroup => w.val) he
    exact Subtype.ext (Subtype.ext hv)
  · intro y
    obtain ⟨g, rfl⟩ := hf y
    obtain ⟨w, hw, _⟩ := hc g
    let h := (inc w)⁻¹ * g
    have hh : h ∈ st := by
      change ((w.val⁻¹ * g.val : V ≃ᵃ[K] V) : V → V) '' C = C
      rw [AffineEquiv.coe_mul, Set.image_comp, ← hw, Set.image_image]
      simp [AffineEquiv.inv_def]
    refine ⟨⟨h, hh⟩, ?_⟩
    change f ((inc w)⁻¹ * g) = f g
    rw [map_mul, map_inv, (hker (inc w)).mpr w.property, inv_one, one_mul]

end AffineGroups

section Transport

variable {K V V' ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (D : ApartmentRoots K V ι) (f : V ≃ₗ[K] V')

private theorem transported_root (i : ι) (x : V) : (D.transport f).root i (f x) = D.root i x :=
  congrArg (D.root i) (f.symm_apply_apply x)

private theorem transported_linearReflection (i : ι) (x : V) :
    (D.transport f).linearReflection i (f x) = f (D.linearReflection i x) := by
  change f x - (D.transport f).root i (f x) • f (D.coroot i) = f (x - D.root i x • D.coroot i)
  rw [transported_root, map_sub, map_smul]

private theorem transported_reflectionClosed (hR : D.ReflectionClosed) :
    (D.transport f).ReflectionClosed := by
  intro i j
  obtain ⟨k, hroot, hcoroot⟩ := hR i j
  refine ⟨k, ?_, ?_⟩
  · ext x
    obtain ⟨y, rfl⟩ := f.surjective x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, transported_linearReflection, transported_root]
    exact LinearMap.congr_fun hroot y
  · exact (congrArg f hcoroot).trans (transported_linearReflection D f i (D.coroot j)).symm

private theorem transported_reducedDirections (hD : D.ReducedDirections) :
    (D.transport f).ReducedDirections := by
  have comp_injective : Function.Injective (fun α : V →ₗ[K] K => α.comp f.symm.toLinearMap) := by
    intro α β h
    ext x
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using
      LinearMap.congr_fun h (f x)
  refine ⟨fun i j hij => hD.1 (comp_injective hij), fun i j a h => ?_⟩
  have hre : D.root j = a • D.root i := comp_injective h
  exact (hD.2 i j a hre).imp_right (fun he => congrArg (fun α : V →ₗ[K] K => α.comp f.symm.toLinearMap) he)

private theorem transported_corootLattice :
    f '' (D.corootLattice : Set V) = ((D.transport f).corootLattice : Set V') := by
  change (D.corootLattice.map f.toLinearMap.toAddMonoidHom : Set V') = _
  simp only [ApartmentRoots.corootLattice, AddMonoidHom.map_closure, ← Set.range_comp]
  rfl

private theorem transported_coweightLattice :
    f '' (D.coweightLattice : Set V) = ((D.transport f).coweightLattice : Set V') := by
  ext x
  obtain ⟨y, rfl⟩ := f.surjective x
  rw [f.injective.mem_set_image]
  change (∀ i, ∃ n : ℤ, D.root i y = (n : K)) ↔
    ∀ i, ∃ n : ℤ, (D.transport f).root i (f y) = (n : K)
  simp only [transported_root]

end Transport

section AlcoveGeometry

open AffineArrangement

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [LinearOrder K] [IsStrictOrderedRing K] (D : ApartmentRoots K V ι)

private theorem regular_iff (p : V) : D.IsRegular p ↔ D.regular p := by
  constructor
  · intro hp a h
    exact hp a.1 ⟨-a.2, by change D.root a.1 p + (a.2 : K) = 0 at h; push_cast; linarith⟩
  · rintro hp i ⟨n, hn⟩
    exact hp (i, -n) (by change D.root i p + ((-n : ℤ) : K) = 0; simp [← hn])

@[instance_reducible] private noncomputable def ordinaryWallAction
    (hD : D.ReducedDirections) (hle : D.ordinary ≤ D.symmetries) :
    MulAction D.ordinary (Wall ι) :=
  letI := signedMulAction D hD
  MulAction.compHom _ (Subgroup.inclusion hle)

omit [IsStrictOrderedRing K] in
private theorem ordinaryClosure (p : V) (hgen : D.simpleGroup p = D.ordinary) :
    Subgroup.closure (Set.range (D.simpleAffineReflection p)) = ⊤ := by
  apply Subgroup.map_injective D.ordinary.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_top, D.ordinary.range_subtype]
  refine (congrArg Subgroup.closure ?_).trans hgen
  rw [← Set.range_comp]
  ext g
  change (∃ i : D.SimpleWall p, D.reflection i.val = g) ↔ g ∈ D.reflection '' {a | D.IsSimple p a}
  exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.property, hi⟩, fun ⟨a, ha, hg⟩ => ⟨⟨a, ha⟩, hg⟩⟩

private theorem simpleReflection_ne_one (p : V) (i : D.SimpleWall p) :
    D.simpleAffineReflection p i ≠ 1 := by
  intro h
  exact i.property.1.ne' ((reflection_fixed_iff D i.val p).mp
    (congrArg (fun g : D.affineWeylGroup => g.val p) h))

private noncomputable def ordinarySignedWalls (hR : D.ReflectionClosed) (hD : D.ReducedDirections)
    (hle : D.ordinary ≤ D.symmetries) (p : V) (hp : D.regular p) :
    letI := ordinaryWallAction D hD hle
    SignedWallAction (A := Wall ι) (D.simpleAffineReflection p) := by
  letI := ordinaryWallAction D hD hle
  let f := Subgroup.inclusion hle
  have htransport (w : D.ordinary) (a : Wall ι) : D.Transports w.val a (w • a) :=
    (f w).property.choose_spec a
  refine {
    positive := D.positive p
    opposite := D.opposite
    reflect := fun a => ⟨D.reflection a, Subgroup.subset_closure ⟨a, rfl⟩⟩
    simple := Subtype.val
    opposite_positive := opposite_positive D hR hD hp
    smul_opposite := fun w a => transports_unique D hD (htransport w _) ((htransport w a).opposite hR hD)
    simple_positive := fun i => i.property.1
    simple_opposite := fun i => transports_unique D hD (htransport (D.simpleAffineReflection p i) i.val)
      (reflection_transports_opposite D hR hD i.val)
    simple_preserves := fun i a ha hne => (simpleWallSigns D hR hD p i.val hp i.property).2 _ _
      (htransport (D.simpleAffineReflection p i) a) ha hne
    simple_reflect := fun _ => rfl
    conjugate_reflect := fun w a => Subtype.ext (htransport w a).conjugates
    reflection_sq := fun a => Subtype.ext (reflectionInvolution D a) }

private theorem castSignedWalls {W S A : Type*} [Group W] [MulAction W A] {s t : S → W}
    (e : t = s) (H : SignedWallAction (A := A) s) :
    let H' : SignedWallAction (A := A) t := e ▸ H
    H'.positive = H.positive ∧ H'.opposite = H.opposite ∧ H'.reflect = H.reflect ∧ H'.simple = H.simple := by
  subst t
  exact ⟨rfl, rfl, rfl, rfl⟩

private theorem separators_to_hyperplanes [Finite ι] [Archimedean K]
    (hR : D.ReflectionClosed) (hD : D.ReducedDirections) (p q : V) :
    D.separatingHyperplanes p q = D.wallHyperplane '' D.orientedSeparators p q ∧
      Set.InjOn D.wallHyperplane (D.orientedSeparators p q) := by
  have hopp (a : Wall ι) : D.wallHyperplane (D.opposite a) = D.wallHyperplane a :=
    ((wallGeometry D hR hD a).1 (D.opposite a) |>.2 (Or.inr rfl)).symm
  constructor
  · apply Set.Subset.antisymm
    · rintro _ ⟨a, h | h, rfl⟩
      · exact ⟨a, h, rfl⟩
      · refine ⟨D.opposite a, ?_, hopp a⟩
        change 0 < D.value (D.opposite a) p ∧ D.value (D.opposite a) q < 0
        simpa only [(opposite_value_coroot D hR hD a).1, neg_pos, Left.neg_neg_iff] using h
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨a, Or.inl ha, rfl⟩
  · intro a ha b hb he
    rcases (wallGeometry D hR hD a).1 b |>.1 he with h | h
    · exact h.symm
    · have hbp : 0 < D.value b p := hb.1
      rw [h, (opposite_value_coroot D hR hD a).1, neg_pos] at hbp
      exact (hbp.not_gt ha.1).elim

theorem affineApartmentGeometry : AffineApartmentGeometry.{u,v,w} := by
  classical
  intro K V ι _ _ _ _ _ _ _ _ D hR hD p hp
  have hp' := (regular_iff D p).mp hp
  obtain ⟨hle, hext⟩ := groupPreservation D hR hD
  obtain ⟨hgen, htrans⟩ := generationAndTransitivity D hR hD p hp'
  let action := ordinaryWallAction D hD hle
  let H := ordinarySignedWalls D hR hD hle p hp'
  have hdel := (signedWallDeletion H).1
  have hinj : Function.Injective (D.simpleAffineReflection p) := by
    intro a b h
    exact simple_reflection_injective D hR hD p (congrArg Subtype.val h)
  obtain ⟨M, hM, cs, hcs⟩ := coxeterPresentationFromDeletion (D.simpleAffineReflection p)
    hinj (simpleReflection_ne_one D p) (simpleWall_mul_self H) (ordinaryClosure D p hgen) hdel
  let hs : SignedWallAction (A := Wall ι) cs.simple := hcs ▸ H
  obtain ⟨hpos, hopp, href, hsimple⟩ := castSignedWalls hcs H
  change hs.positive = D.positive p at hpos
  change hs.opposite = D.opposite at hopp
  change hs.simple = Subtype.val at hsimple
  obtain ⟨hlen, hsign⟩ := wallSignsAndLength cs hs
  have heq (w : D.ordinary) (a : Wall ι) (x : V) :
      D.wallValue (w • a) x = D.wallValue a (w.val.symm x) :=
    signed_value D hD (Subgroup.inclusion hle w) a x
  have hsep (w : D.ordinary) : separatingWalls hs w = D.orientedSeparators p (w.val p) := by
    ext a
    change hs.positive a ∧ ¬ hs.positive (w⁻¹ • a) ↔
      0 < D.wallValue a p ∧ D.wallValue a (w.val p) < 0
    rw [hpos, show D.positive p (w⁻¹ • a) ↔ 0 < D.wallValue a (w.val p) by
      change 0 < D.wallValue (w⁻¹ • a) p ↔ _
      rw [heq]
      rfl]
    have hw := symmetry_reg D w.val (hle w.property) hp' a
    exact and_congr_right (fun _ => not_lt.trans ⟨fun h => lt_of_le_of_ne h hw, le_of_lt⟩)
  have hlength (w : D.ordinary) :
      (D.separatingHyperplanes p (w.val p)).Finite ∧
        cs.length w = (D.separatingHyperplanes p (w.val p)).ncard := by
    obtain ⟨he, hi⟩ := separators_to_hyperplanes D hR hD p (w.val p)
    obtain ⟨hf, hn⟩ := hlen w
    rw [hsep] at hf hn
    rw [he, hi.ncard_image]
    exact ⟨hf.image _, hn.symm⟩
  have hsign' (w : D.ordinary) (i : D.SimpleWall p) := hsign w i
  have hdata : AlcoveCoxeterData D p := {
    matrix := M
    coxeter := cs
    simple_eq := hcs
    matrix_eq := fun i j => by rw [hcs]; exact hM i j
    action := action
    walls := hs
    positive_eq := hpos
    opposite_eq := hopp
    reflection_eq := fun a => by rw [show hs.reflect = H.reflect from href]; rfl
    simple_wall := congrFun hsimple
    equation := heq
    right_ascent := fun w i => by
      obtain ⟨ha, hd⟩ := hsign' w i
      rw [hpos, hsimple] at ha hd
      exact ⟨fun hl => by by_contra hn; have := hd hn; omega, ha⟩
    right_descent := fun w i => by
      obtain ⟨ha, hd⟩ := hsign' w i
      rw [hpos, hsimple] at ha hd
      change cs.length (w * cs.simple i) < cs.length w ↔ D.value (w • i.val) p < 0
      constructor
      · intro hl
        have hn : ¬ D.positive p (w • i.val) := fun hp => by have := ha hp; omega
        exact lt_of_le_of_ne (le_of_not_gt hn) (hp' _)
      · intro hn
        have := hd (not_lt_of_ge hn.le)
        omega
    length_walls := hlength
    length_thresholds := fun w => by
      have h := (hlen w).2
      rw [hsep] at h
      have hw := symmetry_reg D w.val (hle w.property) hp'
      let := Fintype.ofFinite ι
      rw [finsum_eq_sum_of_fintype]
      exact h.symm.trans (affineThresholdCount D p (w.val p) hp ((regular_iff D _).mpr hw)).2 }
  have hfree (w : D.ordinary) (hw : w.val '' D.alcove p = D.alcove p) : w = 1 := by
    have hwp : w.val p ∈ D.alcove p := hw ▸ Set.mem_image_of_mem _ (fun _ h => h)
    have he : D.orientedSeparators p (w.val p) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro a ⟨ha, hn⟩
      exact hn.not_gt (hwp a ha)
    apply cs.length_eq_zero_iff.mp
    rw [← (hlen w).2, hsep, he, Set.ncard_empty]
  have hsim (q : V) (hq : D.IsRegular q) :
      ∃! w : D.ordinary, w.val '' D.alcove p = D.alcove q := by
    obtain ⟨g, hg, hgc⟩ := htrans q ((regular_iff D q).mp hq)
    refine ⟨⟨g, hg⟩, hgc, fun w hw => ?_⟩
    have he : (⟨g, hg⟩ : D.ordinary)⁻¹ * w = 1 := by
      apply hfree
      change ((g⁻¹ * w.val : V ≃ᵃ[K] V) : V → V) '' D.alcove p = D.alcove p
      rw [AffineEquiv.coe_mul, Set.image_comp, hw, ← hgc, Set.image_image]
      simp [AffineEquiv.inv_def]
    exact (inv_mul_eq_one.mp he).symm
  have hex (g : D.extendedAffineWeylGroup) :
      D.IsRegular (g.val p) ∧ g.val '' D.alcove p = D.alcove (g.val p) :=
    ⟨(regular_iff D _).mpr (symmetry_reg D g.val (hext g.property) hp'),
      symmetry_alcove D g.val (hext g.property) p⟩
  refine ⟨hp, hle, hext, ⟨hdata⟩, hsim, hex, ?_⟩
  apply alcoveStabilizerQuotient
  intro g
  rw [(hex g).2]
  exact hsim (g.val p) (hex g).1

theorem realAlcovesInCoordinates : RealAlcovesInCoordinates.{v,w} := by
  intro V ι _ _ D hR hD n f p hp
  let E := D.transport f
  have hvalue (a : Wall ι) (x : V) : E.value a (f x) = D.value a x :=
    congrArg (· + (a.2 : ℝ)) (transported_root D f a.1 x)
  have hregular : E.regular (f p) := fun a => hvalue a p ▸ (regular_iff D p).mp hp a
  have hs : {x | E.IsRegular x} = {x | E.regular x} := Set.ext (regular_iff E)
  change f '' D.alcove p = connectedComponentIn {x | E.IsRegular x} (f p)
  rw [hs, realComponents E (transported_reflectionClosed D f hR) (transported_reducedDirections D f hD) _ hregular]
  ext x
  obtain ⟨y, rfl⟩ := f.surjective x
  rw [f.injective.mem_set_image]
  constructor <;> intro hy a ha
  · change 0 < E.value a (f y)
    change 0 < E.value a (f p) at ha
    rw [hvalue] at ha ⊢
    exact hy a ha
  · have hp' : E.positive (f p) a := by
      change 0 < E.value a (f p)
      rwa [hvalue]
    have h := hy a hp'
    change 0 < E.value a (f y) at h
    rwa [hvalue] at h

private theorem small_alcove_signs [FloorRing K] (p : V) (P : ι → Prop)
    (h : ∀ i, (0 < D.root i p ↔ P i) ∧ 0 < |D.root i p| ∧ |D.root i p| < 1) :
    D.IsRegular p ∧ PinnedWallSigns D p P := by
  have hwall (i : ι) (n : ℤ) :
      D.value (i, n) p ≠ 0 ∧ (D.positive p (i, n) ↔ 0 < n ∨ (n = 0 ∧ P i)) := by
    obtain ⟨hpos, hnz, habs⟩ := h i
    obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
    change D.root i p + (n : K) ≠ 0 ∧ (0 < D.root i p + (n : K) ↔ _)
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · have hn' : (n : K) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      have hv : D.root i p + (n : K) < 0 := by linarith only [hhi, hn']
      exact ⟨hv.ne, iff_of_false (not_lt_of_ge hv.le) (by simp [hn.not_gt, hn.ne])⟩
    · simpa [hpos] using abs_pos.mp hnz
    · have hn' : (1 : K) ≤ (n : K) := by exact_mod_cast (show 1 ≤ n by omega)
      have hv : 0 < D.root i p + (n : K) := by linarith only [hlo, hn']
      exact ⟨hv.ne', iff_of_true hv (Or.inl hn)⟩
  refine ⟨(regular_iff D p).mpr (fun a => (hwall a.1 a.2).1), ⟨fun i n => (hwall i n).2, ?_, ?_, ?_⟩⟩
  · intro i hi
    have hu := (wall_threshold_iff (D.root i p) 0).2 ((hwall i 0).2.mpr (Or.inr ⟨rfl, hi⟩))
    have hl : ¬threshold (D.root i p) ≤ -1 := by
      intro ht
      have hneg := (hwall i (-1)).2.mp ((wall_threshold_iff _ (-1)).mp ht)
      omega
    omega
  · intro i hi
    have hu := (wall_threshold_iff (D.root i p) 1).2 ((hwall i 1).2.mpr (Or.inl Int.zero_lt_one))
    have hl : ¬threshold (D.root i p) ≤ 0 := by
      intro ht
      have hpos := (hwall i 0).2.mp ((wall_threshold_iff _ 0).mp ht)
      exact hi (by simpa using hpos)
    omega
  · rintro ⟨i, n⟩ ⟨hn, x, hx, hpanel⟩
    let t := threshold (D.root i p)
    change n = t
    have htn : t ≤ n := (wall_threshold_iff _ _).mpr hn
    by_contra hnt
    have ht : D.positive p (i, t) := (wall_threshold_iff _ _).mp le_rfl
    have hne : (i, t) ≠ (i, n) := fun h => hnt (congrArg Prod.snd h).symm
    have ht' := hpanel (i, t) ht hne
    change D.root i x + (n : K) = 0 at hx
    change 0 < D.root i x + (t : K) at ht'
    have hc : (t : K) ≤ (n : K) := by exact_mod_cast htn
    linarith only [hx, ht', hc]

end AlcoveGeometry

section SimpleCoordinates

private def extendRootMap {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum (ι := ι) X Y) (K : Type*) [Field K] :
    X →ₗ[ℤ] ((K ⊗[ℤ] Y) →ₗ[K] K) :=
  (((TensorProduct.AlgebraTensorModule.rid ℤ K K).toLinearMap.compRight ℤ).comp
    (LinearMap.baseChangeHom ℤ K Y ℤ)).comp P.toLinearMap

theorem splitReflectionClosed : SplitReflectionClosed.{u,v,w,z} := by
  intro ι X Y K _ _ _ P D i j
  refine ⟨?_, ?_⟩
  · apply LinearMap.ext
    intro x
    let f := (LinearMap.applyₗ x).restrictScalars ℤ ∘ₗ extendRootMap P K
    change f (P.root (P.reflectionPerm i j)) = D.root j (D.linearReflection i x)
    rw [P.root_reflectionPerm, P.reflection_apply_root, map_sub, map_zsmul]
    change D.root j x - P.pairing j i • D.root i x =
      D.root j (x - D.root i x • D.coroot i)
    rw [map_sub, map_smul, zsmul_eq_mul, smul_eq_mul]
    change D.root j x - (P.pairing j i : K) * D.root i x =
      D.root j x - D.root i x * RootData.extendFunctional K (P.root' j) (1 ⊗ₜ[ℤ] P.coroot i)
    rw [RootData.extendFunctional_one_tmul, RootPairing.root'_coroot_eq_pairing, mul_comm (D.root i x)]
  · let f := TensorProduct.mk ℤ K Y 1
    change f (P.coroot (P.reflectionPerm i j)) = f (P.coroot j) -
      RootData.extendFunctional K (P.root' i) (1 ⊗ₜ[ℤ] P.coroot j) • f (P.coroot i)
    rw [P.coroot_reflectionPerm, P.coreflection_apply_coroot, map_sub, map_zsmul,
      RootData.extendFunctional_one_tmul, RootPairing.root'_coroot_eq_pairing, Int.cast_smul_eq_zsmul]

theorem splitReducedDirections : SplitReducedDirections.{u,v,w,z} := by
  intro ι X Y K _ _ _ _ P _
  let D := ApartmentRoots.split P K
  let f := P.toLinearMap.toPerfPair
  have heval (i : ι) (y : Y) : D.root i (1 ⊗ₜ[ℤ] y) = (P.root' i y : K) :=
    RootData.extendFunctional_one_tmul K _ _
  change D.ReducedDirections
  refine ⟨?_, ?_⟩
  · intro i j h
    apply P.root.injective
    apply f.injective
    apply LinearMap.ext
    intro y
    apply Int.cast_injective (α := K)
    have h' := LinearMap.congr_fun h ((1 : K) ⊗ₜ[ℤ] y)
    rw [heval, heval] at h'
    exact h'
  · intro i j a h
    have ha (y : Y) : (P.root' j y : K) = a * (P.root' i y : K) := by
      have h' := LinearMap.congr_fun h ((1 : K) ⊗ₜ[ℤ] y)
      rwa [LinearMap.smul_apply, heval, heval, smul_eq_mul] at h'
    have hp : (P.pairing j i : K) = a * 2 := by simpa using ha (P.coroot i)
    have ht : (2 : ℤ) • P.root j + (-P.pairing j i) • P.root i = 0 := by
      apply f.injective
      apply LinearMap.ext
      intro y
      simp only [map_add, map_zsmul, map_zero, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.zero_apply, zsmul_eq_mul]
      apply Int.cast_injective (α := K)
      push_cast
      change (2 : K) * (P.root' j y : K) + -(P.pairing j i : K) * (P.root' i y : K) = 0
      rw [ha, hp]
      ring
    have hdep : ¬ LinearIndependent ℤ ![P.root j, P.root i] := by
      rw [LinearIndependent.pair_iff]
      intro H
      have hn := (H 2 (-P.pairing j i) ht).1
      norm_num at hn
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) j i hdep with hji | hji
    · exact Or.inl (P.root.injective hji.symm)
    · exact Or.inr (by
        change extendRootMap P K (P.root j) = -extendRootMap P K (P.root i)
        rw [hji, map_neg])

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum (ι := ι) X Y) (B : P.Base) {n : ℕ}
  (e : Fin n ≃ B.support) (C : Matrix (Fin n) (Fin n) ℤ)
  (hC : ∀ i j, C i j = P.pairing (e j) (e i))

include hC in
private theorem simpleCoordinates_reflect (r : Fin n → ℤ) (i : Fin n) :
    (∑ j, simpleReflection C i r j • P.root (e j)) =
      P.reflection (e i) (∑ j, r j • P.root (e j)) := by
  classical
  have hsum : (∑ j, ((C.mulVec r i) • (Pi.single i 1 : Fin n → ℤ)) j • P.root (e j)) =
      (C.mulVec r i) • P.root (e i) := by
    simp [Pi.smul_apply, Pi.single_apply, mul_ite, ite_smul]
  have hpair : P.coroot' (e i) (∑ j, r j • P.root (e j)) = C.mulVec r i := by
    simp [Matrix.mulVec, dotProduct, hC, mul_comm]
  rw [P.reflection_apply]
  change _ = _ - (P.coroot' (e i) _) • _
  rw [hpair]
  simp only [simpleReflection, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hsum]

include hC in
private theorem simpleCoordinates_mem [Finite ι] [P.IsReduced] (r : Fin n → ℤ) :
    IsRootCoordinate C r ↔ (∑ i, r i • P.root (e i)) ∈ Set.range P.root := by
  constructor
  · intro h
    induction h with
    | simple i =>
      exact ⟨e i, by simp [Pi.single_apply, ite_smul]⟩
    | @reflect r hr i ih =>
      obtain ⟨j, hj⟩ := ih
      exact ⟨P.reflectionPerm (e i) j, by
        rw [simpleCoordinates_reflect P B e C hC, ← hj, P.root_reflectionPerm]⟩
  · rintro ⟨j, hj⟩
    have hinj : Function.Injective (Fintype.linearCombination ℤ
        (fun i : Fin n => P.root (e i))) :=
      linearIndependent_iff_injective_fintypeLinearCombination.mp
        (B.linearIndepOn_root.comp e e.injective)
    suffices hex : ∀ j : ι, ∃ s : Fin n → ℤ, IsRootCoordinate C s ∧
        P.root j = ∑ i, s i • P.root (e i) by
      obtain ⟨s, hs, hs'⟩ := hex j
      have : r = s := hinj (by simpa only [Fintype.linearCombination_apply] using hj.symm.trans hs')
      rwa [this]
    have hstep (k : ι) (i : Fin n) (hk : ∃ s : Fin n → ℤ, IsRootCoordinate C s ∧
          P.root k = ∑ j, s j • P.root (e j)) :
        ∃ s : Fin n → ℤ, IsRootCoordinate C s ∧
          P.root (P.reflectionPerm (e i) k) = ∑ j, s j • P.root (e j) := by
      obtain ⟨s, hs, he⟩ := hk
      exact ⟨_, hs.reflect i, by rw [simpleCoordinates_reflect P B e C hC,
        P.root_reflectionPerm, he]⟩
    intro k
    let p : ι → Prop := fun l => ∃ s : Fin n → ℤ, IsRootCoordinate C s ∧
        P.root l = ∑ i, s i • P.root (e i)
    have hpos (l : ι) (hl : B.IsPos l) : p l := by
      refine hl.induction_on_reflect (p := p) ?_ ?_
      · intro l hl
        let i := e.symm ⟨l, hl⟩
        have hi : (e i : ι) = l := congrArg Subtype.val (e.apply_symm_apply ⟨l, hl⟩)
        exact ⟨Pi.single i 1, .simple i, by simp [Pi.single_apply, ite_smul, hi]⟩
      · intro l m hl hm
        let i := e.symm ⟨m, hm⟩
        have hi : (e i : ι) = m := congrArg Subtype.val (e.apply_symm_apply ⟨m, hm⟩)
        simpa only [hi] using hstep l i hl
    let := P.indexNeg
    rcases RootPairing.Base.IsPos.or_neg B k with hk | hk
    · exact hpos k hk
    · obtain ⟨s, hs, he⟩ := hpos (-k) hk
      have hneg : IsRootCoordinate C (-s) := by
        suffices ∀ t, IsRootCoordinate C t → IsRootCoordinate C (-t) from this s hs
        intro t ht
        induction ht with
        | simple i =>
          have hii : C i i = 2 := (hC i i).trans (P.pairing_same (e i))
          convert (IsRootCoordinate.simple (C := C) i).reflect i using 1
          ext j
          by_cases hij : j = i <;>
            simp [simpleReflection, Matrix.mulVec, dotProduct, Pi.single_apply, hii, hij]
        | @reflect t ht i ih =>
          convert ih.reflect i using 1
          ext j
          simp [simpleReflection, Matrix.mulVec_neg]
          ring
      exact ⟨-s, hneg, by simpa using congrArg Neg.neg he⟩

theorem simpleRootCoordinates : SimpleRootCoordinates.{u,v,w} := by
  intro ι X Y _ _ _ P _ B n e C hC r
  exact simpleCoordinates_mem P B e C hC r

theorem cocharacterLatticeCoordinates : CocharacterLatticeCoordinates.{u,v,w,z} := by
  classical
  intro ι X Y K _ _ _ _ P _ B n e C hC D φ
  let c (j : Fin n) : K ⊗[ℤ] Y := 1 ⊗ₜ[ℤ] P.coroot (e j)
  have hspan :
      (D.corootLattice : Set (K ⊗[ℤ] Y)) = Submodule.span ℤ (Set.range c) := by
    change ((AddSubgroup.closure (Set.range fun i : ι =>
      (1 : K) ⊗ₜ[ℤ] P.coroot i)) : Set (K ⊗[ℤ] Y)) = _
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    apply congrArg (fun A : Submodule ℤ (K ⊗[ℤ] Y) => (A : Set (K ⊗[ℤ] Y)))
    have hsimple : (fun j : Fin n => P.coroot (e j)) '' (Set.univ : Set (Fin n)) =
        P.coroot '' (B.support : Set ι) := by
      rw [Set.image_univ]
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e j, (e j).property, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        refine ⟨e.symm ⟨j, hj⟩, ?_⟩
        simp only [Equiv.apply_symm_apply]
    let lift : Y →ₗ[ℤ] (K ⊗[ℤ] Y) := TensorProduct.mk ℤ K Y 1
    have h := congrArg (Submodule.map lift) B.span_int_coroot_support
    rw [Submodule.map_span, Submodule.map_span, ← hsimple, Set.image_univ,
      ← Set.range_comp, ← Set.range_comp] at h
    exact h.symm
  have hmemQ (x : K ⊗[ℤ] Y) : x ∈ D.corootLattice ↔ ∃ t : Fin n → ℤ, x = ∑ j, t j • c j := by
    change x ∈ (D.corootLattice : Set (K ⊗[ℤ] Y)) ↔ _
    rw [hspan]
    simpa [eq_comm] using (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := c) (x := x))
  refine ⟨?_, hmemQ, ?_⟩
  · intro x
    constructor
    · intro hx
      choose t ht using fun i : Fin n => hx (e i)
      exact ⟨t, funext ht⟩
    · rintro ⟨t, ht⟩ k
      let ext : (Y →ₗ[ℤ] ℤ) →ₗ[ℤ] ((K ⊗[ℤ] Y) →ₗ[K] K) :=
        ((TensorProduct.AlgebraTensorModule.rid ℤ K K).toLinearMap.compRight ℤ).comp
          (LinearMap.baseChangeHom ℤ K Y ℤ)
      let f : X →ₗ[ℤ] K :=
        ((LinearMap.applyₗ x).restrictScalars ℤ).comp (ext.comp P.toLinearMap)
      have hs : P.root k ∈ Submodule.span ℤ (Set.range fun j : Fin n => P.root (e j)) := by
        convert B.root_mem_span_int k using 2
        ext y
        constructor
        · rintro ⟨j, rfl⟩
          exact ⟨e j, (e j).property, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          exact ⟨e.symm ⟨j, hj⟩, by simp only [Equiv.apply_symm_apply]⟩
      obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hs
      refine ⟨∑ i, m i * t i, ?_⟩
      change f (P.root k) = _
      rw [← hm, map_sum]
      simp only [map_zsmul, Int.cast_sum, Int.cast_mul]
      apply Finset.sum_congr rfl
      intro j _
      have h : f (P.root (e j)) = (t j : K) := congrFun ht j
      rw [h, zsmul_eq_mul]
  · ext y
    have hEval (t : Fin n → ℤ) : φ (∑ j, t j • c j) =
        fun i => (C.mulVec t i : K) := by
      funext i
      rw [map_sum, Finset.sum_apply]
      simp only [map_zsmul, Pi.smul_apply, Matrix.mulVec, dotProduct, Int.cast_sum,
        Int.cast_mul, hC]
      apply Finset.sum_congr rfl
      intro j _
      change t j • RootData.extendFunctional K (P.root' (e i))
        (1 ⊗ₜ[ℤ] P.coroot (e j)) = _
      rw [RootData.extendFunctional_one_tmul, RootPairing.root'_coroot_eq_pairing,
        zsmul_eq_mul, mul_comm]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, rfl⟩ := (hmemQ x).mp hx
      exact ⟨t, (hEval t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨_, (hmemQ _).mpr ⟨t, rfl⟩, hEval t⟩

theorem pairedRootCoordinates : PairedRootCoordinates.{u,v,w} := by
  classical
  intro ι X Y _ _ _ P _ B n e C hsym hC
  let toRoot (r : Fin n → ℤ) := ∑ j, r j • P.root (e j)
  let toCoroot (r : Fin n → ℤ) := ∑ j, r j • P.coroot (e j)
  have hC' (i j) : C i j = P.pairing (e j) (e i) :=
    (hsym.apply j i).trans (hC j i)
  have hpaired : ∀ r, IsRootCoordinate C r → ∃ i, P.root i = toRoot r ∧ P.coroot i = toCoroot r := by
    intro r hr
    induction hr with
    | simple j =>
      exact ⟨e j, by simp [toRoot], by simp [toCoroot]⟩
    | @reflect r hr j ih =>
      obtain ⟨i, hi, hci⟩ := ih
      refine ⟨P.reflectionPerm (e j) i, ?_, ?_⟩
      · rw [P.root_reflectionPerm, hi]
        exact (simpleCoordinates_reflect P B e C hC' r j).symm
      · have hc : P.root' (e j) (toCoroot r) = C.mulVec r j := by
          simp [toCoroot, Matrix.mulVec, dotProduct, hC, mul_comm]
        have hsum : (∑ k, ((C.mulVec r j) • (Pi.single j 1 : Fin n → ℤ)) k • P.coroot (e k)) =
            (C.mulVec r j) • P.coroot (e j) := by
          simp [Pi.smul_apply, Pi.single_apply, mul_ite, ite_smul]
        rw [P.coroot_reflectionPerm, P.coreflection_apply, hci, hc]
        simp only [toCoroot, simpleReflection, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hsum]
  let σ : {r // IsRootCoordinate C r} → ι := fun r => (hpaired r r.property).choose
  have hσ (r : {r // IsRootCoordinate C r}) :
      P.root (σ r) = toRoot r ∧ P.coroot (σ r) = toCoroot r := (hpaired r r.property).choose_spec
  have hinj : Function.Injective toRoot :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp
      (B.linearIndepOn_root.comp e e.injective)
  have hspan : Set.range (fun j : Fin n => P.root (e j)) = P.root '' (B.support : Set ι) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, (e j).property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨e.symm ⟨i, hi⟩, by simp⟩
  have hbij : Function.Bijective σ := by
    refine ⟨fun r s h => Subtype.ext (hinj ((hσ r).1.symm.trans ((congrArg P.root h).trans (hσ s).1))), ?_⟩
    intro i
    have h := B.root_mem_span_int i
    rw [← hspan] at h
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).mp h
    have hrc := (simpleCoordinates_mem P B e C hC' r).mpr ⟨i, hr.symm⟩
    exact ⟨⟨r, hrc⟩, P.root.injective ((hσ ⟨r, hrc⟩).1.trans hr)⟩
  let ρ := Equiv.ofBijective σ hbij
  refine ⟨ρ.symm, fun i => ?_⟩
  have h := hσ (ρ.symm i)
  change P.root (ρ (ρ.symm i)) = _ ∧ P.coroot (ρ (ρ.symm i)) = _ at h
  rwa [ρ.apply_symm_apply i] at h

theorem cocharacterApartmentCoordinates : CocharacterApartmentCoordinates.{u,v,w,z} := by
  classical
  intro ι X Y K _ _ _ _ _ _ _ _ _ P _ B n e hdim
  let φ := simpleRootValues P B e K
  let C := (RootData.integralCartan P B).transpose
  have hC (i j : B.support) : C i j = P.pairing i j := rfl
  have hdetQ := (RootData.rationalComplement P B).1
  have hdet : (RootData.integralCartan P B).det ≠ 0 := by
    rw [← RingHom.map_det] at hdetQ
    exact fun h => (isUnit_iff_ne_zero.mp hdetQ) (by simp [h])
  have hu : IsUnit (((Int.castRingHom K).mapMatrix C).det) := by
    rw [isUnit_iff_ne_zero, ← RingHom.map_det]
    change (↑((RootData.integralCartan P B).transpose.det) : K) ≠ 0
    rw [Matrix.det_transpose]
    simpa using hdet
  let A := (Int.castRingHom K).mapMatrix C
  let F := A.toLinearEquiv' (A.invertibleOfIsUnitDet hu)
  let p (i : B.support) : K ⊗[ℤ] Y := (1 : K) ⊗ₜ[ℤ] P.coroot i
  have hEval (c : B.support → K) (i : B.support) :
      φ (∑ j, c j • p j) (e.symm i) = F c i := by
    change _ = Matrix.toLin' A c i
    rw [map_sum, Finset.sum_apply, Matrix.toLin'_apply]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    change c j * RootData.extendFunctional K (P.root' (e (e.symm i))) (p j) = (C i j : K) * c j
    rw [e.apply_symm_apply, RootData.extendFunctional_one_tmul, hC]
    exact mul_comm _ _
  have hsurj : Function.Surjective φ := by
    intro t
    let c := F.symm (t ∘ e.symm)
    refine ⟨∑ j, c j • p j, ?_⟩
    funext i
    rw [← e.symm_apply_apply i, hEval]
    simp [c]
  have hdimK : Module.finrank K (K ⊗[ℤ] Y) = Module.finrank K (Fin n → K) := by
    simpa [Module.finrank_baseChange] using hdim
  exact ⟨LinearEquiv.ofBijective φ
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimK).mpr hsurj, hsurj⟩, rfl⟩

theorem rootValuesFromCoordinates : RootValuesFromCoordinates.{u,v,w,z} := by
  intro ι X Y K _ _ _ P B n e i r hr x
  let ext : (Y →ₗ[ℤ] ℤ) →ₗ[ℤ] ((K ⊗[ℤ] Y) →ₗ[K] K) :=
    ((TensorProduct.AlgebraTensorModule.rid ℤ K K).toLinearMap.compRight ℤ).comp
      (LinearMap.baseChangeHom ℤ K Y ℤ)
  let f : X →ₗ[ℤ] K :=
    ((LinearMap.applyₗ x).restrictScalars ℤ).comp (ext.comp P.toLinearMap)
  change f (P.root i) = _
  rw [hr, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (map_zsmul f _ _).trans (zsmul_eq_mul _ _)

private theorem sum_over_simple_roots {M : Type*} [AddCommMonoid M] (g : ι → M) :
    ∑ j : Fin n, g (e j) = ∑ j ∈ B.support, g j := by
  rw [B.support.sum_subtype (p := (· ∈ B.support)) (by simp)]
  exact Equiv.sum_comp e (fun j : B.support => g j)

theorem pinnedAlcovePoint : PinnedAlcovePoint.{u,v,w,z} := by
  classical
  intro ι X Y K _ _ _ _ _ _ _ _ _ _ P _ B n e hdim D
  obtain ⟨φ, hφ⟩ := cocharacterApartmentCoordinates (K := K) P B e hdim
  let := Fintype.ofFinite ι
  let m := (Finset.univ : Finset ι).sup fun i => (B.height i).natAbs
  let d : K := 2 * ((m : K) + 1)
  let c := d⁻¹
  have hd : 0 < d := by positivity
  have hc : 0 < c := inv_pos.mpr hd
  obtain ⟨x, hx⟩ := φ.surjective (fun _ => c)
  have hx' : simpleRootValues P B e K x = fun _ => c := by
    rw [← hφ]
    exact hx
  refine ⟨x, c, hc, congrFun hx', fun i => ?_⟩
  obtain ⟨r, _, _, hr⟩ := B.exists_root_eq_sum_int i
  have hr' : P.root i = ∑ j : Fin n, r (e j) • P.root (e j) :=
    hr.trans (sum_over_simple_roots P B e (fun j => r j • P.root j)).symm
  have heval : D.root i x = (B.height i : K) * c := by
    rw [rootValuesFromCoordinates P B e i _ hr', hx', B.height_eq_sum hr]
    simp only [Int.cast_sum, Finset.sum_mul]
    exact sum_over_simple_roots P B e (fun j => (r j : K) * c)
  rw [heval]
  have hbound : |(B.height i : K)| ≤ (m : K) := by
    have h : (B.height i).natAbs ≤ m := Finset.le_sup (f := fun i => (B.height i).natAbs) (Finset.mem_univ i)
    have h' : ((B.height i).natAbs : K) ≤ (m : K) := by exact_mod_cast h
    simpa using h'
  refine ⟨by rw [mul_pos_iff_of_pos_right hc, Int.cast_pos]; rfl, ?_, ?_⟩
  · exact abs_pos.mpr (mul_ne_zero (Int.cast_ne_zero.mpr (B.height_ne_zero i)) hc.ne')
  · rw [abs_mul, abs_of_pos hc]
    refine (mul_le_mul_of_nonneg_right hbound hc.le).trans_lt ?_
    change (m : K) * d⁻¹ < 1 / 2
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ hd).mpr
    unfold d
    linarith

theorem splitPinnedAlcoveGeometry : SplitPinnedAlcoveGeometry.{u,v,w,z} := by
  intro ι X Y K _ _ _ _ _ _ _ _ _ _ _ _ P _ B n e hr D
  obtain ⟨p, c, hc, hp, hroot⟩ := pinnedAlcovePoint (K := K) P B e hr
  obtain ⟨hreg, hs⟩ := small_alcove_signs D p B.IsPos (fun i =>
    ⟨(hroot i).1, (hroot i).2.1, (hroot i).2.2.trans (by norm_num)⟩)
  have hR : D.ReflectionClosed := fun i j =>
    ⟨P.reflectionPerm i j, splitReflectionClosed (K := K) P i j⟩
  exact ⟨p, c, hc, hp, hs, affineApartmentGeometry D hR (splitReducedDirections P) p hreg⟩

theorem splitIntegralCocharacterImages : SplitIntegralCocharacterImages.{u,v,w,z} := by
  classical
  intro ι X Y K _ _ _ _ _ _ _ _ _ P _ B D lift
  refine ⟨?_, ?_⟩
  · let f : Y →ₗ[ℤ] (K ⊗[ℤ] Y) := TensorProduct.mk ℤ K Y 1
    change (D.corootLattice : Set (K ⊗[ℤ] Y)) =
      (Submodule.map f (Submodule.span ℤ (Set.range P.coroot)) : Set (K ⊗[ℤ] Y))
    rw [Submodule.map_span, ← Set.range_comp]
    change (D.corootLattice : Set (K ⊗[ℤ] Y)) =
      ((Submodule.span ℤ (Set.range (f ∘ P.coroot))).toAddSubgroup : Set (K ⊗[ℤ] Y))
    rw [Submodule.span_int_eq_addSubgroupClosure]
    rfl
  · intro hX
    let := Fintype.ofFinite B.support
    let n := Fintype.card B.support
    let e : Fin n ≃ B.support := (Fintype.equivFin B.support).symm
    have hspan : Set.range (fun j : Fin n => P.root (e j)) = P.root '' (B.support : Set ι) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨_, (e j).property, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨e.symm ⟨i, hi⟩, by simp⟩
    let b : Module.Basis (Fin n) ℤ X := Module.Basis.mk
      (B.linearIndepOn_root.comp e e.injective) (by
        change ⊤ ≤ Submodule.span ℤ (Set.range (fun j : Fin n => P.root (e j)))
        rw [hspan, B.span_int_root_support, hX])
    have hb (i : Fin n) : b i = P.root (e i) := Module.Basis.mk_apply _ _ _
    have hdim : Module.finrank ℤ Y = n := by
      calc
        Module.finrank ℤ Y = Module.finrank ℤ (Module.Dual ℤ Y) :=
          (Module.Free.chooseBasis ℤ Y).toDualEquiv.finrank_eq
        _ = Module.finrank ℤ X := P.toLinearMap.toPerfPair.finrank_eq.symm
        _ = n := by simpa using Module.finrank_eq_card_basis b
    obtain ⟨φ, hφ⟩ := cocharacterApartmentCoordinates (K := K) P B e hdim
    ext x
    constructor
    · intro hx
      choose t ht using fun i : Fin n => hx (e i)
      let F := b.constr ℤ t
      let y := P.toLinearMap.flip.toPerfPair.symm F
      refine ⟨y, φ.injective ?_⟩
      change φ.toLinearMap (lift y) = φ.toLinearMap x
      rw [hφ]
      funext i
      change RootData.extendFunctional K (P.root' (e i)) (lift y) = D.root (e i) x
      rw [RootData.extendFunctional_one_tmul, ht i]
      congr 1
      change P.toLinearMap (P.root (e i)) y = t i
      rw [show P.toLinearMap (P.root (e i)) y = F (P.root (e i)) from
        P.toLinearMap.apply_toPerfPair_flip F _]
      rw [← hb, Module.Basis.constr_basis]
    · rintro ⟨y, rfl⟩ i
      exact ⟨P.root' i y, RootData.extendFunctional_one_tmul K _ y⟩

end SimpleCoordinates

section SplitBorel

open LinearAlgebraicGroups.Specs
open scoped CategoryTheory.MonObj
open private semisimple_iff_corootFullRank from LinearAlgebraicGroups.Classification.SimplyConnectedLattice

private theorem attachedCocharacterRank {F : Type*} [Field F] (P : Pinning.SplitBorelPair F)
    (A : Pinning.AttachedDatum P) (hP : GeometricRadicals.IsSemisimple P.G) :
    letI := A.comm
    ∀ {n : ℕ} (_e : Fin n ≃ A.base.support),
      Module.finrank ℤ (Additive (CharacterDescent.Cocharacter P.T.group)) = n := by
  let := A.comm
  intro n e
  let := A.datum.freeCocharacters
  let := A.datum.finiteCocharacters
  let := Fintype.ofEquiv (Fin n) e
  let R := A.datum.rootDatum
  have h := (semisimple_iff_corootFullRank P A).mp hP
  have hspan : Set.range (fun i : A.base.support => R.coroot i) = R.coroot '' ↑A.base.support := by
    ext x
    exact ⟨fun ⟨i, he⟩ => ⟨i, i.property, he⟩, fun ⟨i, hi, he⟩ => ⟨⟨i, hi⟩, he⟩⟩
  change Module.finrank ℤ (Submodule.span ℤ (Set.range R.coroot)) = _ at h
  rw [← A.base.span_int_coroot_support, ← hspan] at h
  have hlin : LinearIndependent ℤ (fun i : A.base.support => R.coroot i) := A.base.linearIndepOn_coroot
  exact h.symm.trans ((finrank_span_eq_card hlin).trans ((Fintype.card_congr e).symm.trans (Fintype.card_fin n)))

theorem splitBorelApartmentGeometry : SplitBorelApartmentGeometry.{u,v} := by
  intro F _ K _ _ _ _ _ P A hP D lift
  let := A.comm
  let := A.datum.finiteRoots
  let := A.datum.freeCharacters
  let := A.datum.finiteCharacters
  let := A.datum.freeCocharacters
  let := A.datum.finiteCocharacters
  let := A.datum.reduced
  obtain ⟨c, _, hc, _, hpos⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  let f := Specs.SimpleRoots.evaluate A.datum c
  have hf (i : Specs.AbstractPairing.Root P.T) : f (A.datum.rootDatum.root i) =
      Specs.CharacterPairing.pairing P.T.group i.val c := by
    change A.datum.rootDatum.toLinearMap (A.datum.rootDatum.root i) (Additive.ofMul c) = _
    rw [A.datum.root_eq, A.datum.pairing_eq]
  obtain ⟨b, hb⟩ := RootData.SimpleRoots.baseFor A.datum.rootDatum f (fun i => hf i ▸ hc i)
  have hpos' : Specs.SimpleRoots.positive A.datum.rootDatum f =
      Specs.BorelsAndChambers.subgroupRoots P.T P.B := by
    rw [hpos]
    ext i
    change 0 < f (A.datum.rootDatum.root i) ↔ 0 < Specs.CharacterPairing.pairing P.T.group i.val c
    rw [hf]
  have hbA : b = A.base := by
    have hinj : Function.Injective (fun d : A.datum.rootDatum.Base => d.support) := by
      intro b₁ b₂ h
      cases b₁
      cases b₂
      cases h
      rfl
    apply hinj
    apply Finset.ext
    intro i
    rw [hb.simple_iff, hpos', A.simple_iff]
    unfold Pinning.IsSimple
    simp only [A.datum.root_eq]
    rfl
  obtain ⟨hQ, hL⟩ := splitIntegralCocharacterImages (K := K) A.datum.rootDatum A.base
  refine ⟨fun i => ?_, fun e => splitPinnedAlcoveGeometry (K := K) A.datum.rootDatum A.base e
    (attachedCocharacterRank P A hP e), ?_, ?_⟩
  · rw [← hbA, hb.positive_iff, hpos']
  · intro hsc
    have h := (Classification.SimplyConnectedLattice.latticeCriterion P.G hP P.T P.split P.maximal A.datum).mp hsc
    rw [SimplyConnectedLattice.corootLatticeOf] at h
    rw [hQ, h, Submodule.top_coe, Set.image_univ]
  · intro ha
    apply hL
    apply Submodule.toAddSubgroup_injective
    have hrange : Set.range A.datum.rootDatum.root = Additive.toMul ⁻¹'
        Specs.CharacterPairing.absoluteRoots P.T := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        rw [A.datum.root_eq]
        exact i.property
      · intro hx
        exact ⟨⟨Additive.toMul x, hx⟩, A.datum.root_eq _⟩
    rw [Submodule.span_int_eq_addSubgroupClosure, hrange, ← Subgroup.toAddSubgroup_closure,
      ← SchemeCentre.rootLattice, ha]
    rfl

end SplitBorel

theorem exceptionalSplitGeometry : ExceptionalSplitGeometry.{u,v,w,z} := by
  intro ι X Y K _ _ _ _ _ _ _ _ _ _ _ _ P _ B n e hn hr hC D
  have hsym : (exceptionalCartan n).IsSymm := by
    rcases hn with rfl | rfl | rfl <;> decide
  exact ⟨pairedRootCoordinates P B e (exceptionalCartan n) hsym hC,
    splitPinnedAlcoveGeometry (K := K) P B e hr⟩

private theorem e6Partner_partner : ∀ i, e6Partner (e6Partner i) = i := by
  decide

private theorem e6Cartan_symmetric : e6Cartan.IsSymm := by decide

private theorem e6Diagram_apply (x : Fin 6 → ℤ) (i : Fin 6) :
    e6Diagram.mulVec x i = x (e6Partner i) := by
  fin_cases i <;> simp [e6Diagram, e6Partner, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem e6DiagramCoordinates : E6DiagramCoordinates.{u,v,w,z} := by
  intro ι X Y K _ _ _ _ P _ B e σ hσ hC φ
  have hpair (j : Fin 6) (y : Y) :
      P.root' (e j) (σ.coweightEquiv.symm y) = P.root' (e (e6Partner j)) y := by
    have h := σ.root'_coweightEquiv (e (e6Partner j) : ι) y
    rwa [hσ, e6Partner_partner j] at h
  refine ⟨?_, ?_⟩
  · intro x j
    have hmap : (RootData.extendFunctional K (P.root' (e j))).comp
          (diagramCocharacters σ).toLinearMap =
        RootData.extendFunctional K (P.root' (e (e6Partner j))) := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro a y
      change RootData.extendFunctional K (P.root' (e j))
          (diagramCocharacters σ (a ⊗ₜ[ℤ] y)) =
        RootData.extendFunctional K (P.root' (e (e6Partner j))) (a ⊗ₜ[ℤ] y)
      simp only [diagramCocharacters, LinearEquiv.baseChange_tmul]
      have ht (b : Y) : a ⊗ₜ[ℤ] b = a • ((1 : K) ⊗ₜ[ℤ] b) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [ht, map_smul, RootData.extendFunctional_one_tmul, hpair]
    exact LinearMap.congr_fun hmap x
  · obtain ⟨ρ, hρ⟩ := pairedRootCoordinates P B e e6Cartan e6Cartan_symmetric hC
    let F := Fintype.linearCombination ℤ (fun j : Fin 6 => P.root (e j))
    have hF : Function.Injective F := linearIndependent_iff_injective_fintypeLinearCombination.mp
      (B.linearIndepOn_root.comp e e.injective)
    refine ⟨ρ, (fun i => ⟨(hρ i).1, (hρ i).2, ?_⟩), ?_⟩
    · apply hF
      simp only [F, Fintype.linearCombination_apply, ← (hρ (σ.indexEquiv i)).1, e6Diagram_apply]
      have hroot (j : Fin 6) : σ.weightEquiv (P.root (e j)) = P.root (e (e6Partner j)) := by
        rw [RootPairing.Equiv.weightEquiv_apply, RootPairing.Hom.root_weightMap_apply, hσ]
      calc
        P.root (σ.indexEquiv i) = σ.weightEquiv (P.root i) :=
          (σ.toHom.root_weightMap_apply P P i).symm
        _ = ∑ j, (ρ i).val j • P.root (e (e6Partner j)) := by
          rw [(hρ i).1, map_sum]
          simp only [map_zsmul, hroot]
        _ = ∑ j, (ρ i).val (e6Partner j) • P.root (e j) := by
          let τ : Fin 6 ≃ Fin 6 := ⟨e6Partner, e6Partner, e6Partner_partner, e6Partner_partner⟩
          have h := Equiv.sum_comp τ (fun j => (ρ i).val (e6Partner j) • P.root (e j))
          change (∑ j, (ρ i).val (e6Partner (e6Partner j)) • P.root (e (e6Partner j))) = _ at h
          simpa only [e6Partner_partner] using h
    · intro i j
      apply hF
      have hC' (a b) : e6Cartan a b = P.pairing (e b) (e a) :=
        (e6Cartan_symmetric.apply b a).trans (hC b a)
      rw [show F (ρ (P.reflectionPerm (e j) i)).val = P.root (P.reflectionPerm (e j) i) from
        (hρ _).1.symm, P.root_reflectionPerm]
      have h := simpleCoordinates_reflect P B e e6Cartan hC' (ρ i).val j
      exact (congrArg (P.reflection (e j)) (hρ i).1).trans h.symm

private def threeTimesCartanInverse : Matrix (Fin 6) (Fin 6) ℤ :=
  !![4, 3, 5, 6, 4, 2;
     3, 6, 6, 9, 6, 3;
     5, 6, 10, 12, 8, 4;
     6, 9, 12, 18, 12, 6;
     4, 6, 8, 12, 10, 5;
     2, 3, 4, 6, 5, 4]

private def inverseOnOrbitSums : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 2, 3, 4, 3, 2;
     2, 4, 4, 6, 4, 2;
     3, 4, 6, 8, 6, 3;
     4, 6, 8, 12, 8, 4;
     3, 4, 6, 8, 6, 3;
     2, 2, 3, 4, 3, 2]

private theorem cartan_mul_projected_inverse :
    (1 + e6Diagram) * e6Cartan * (threeTimesCartanInverse - inverseOnOrbitSums) =
      1 + e6Diagram := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem e6ProjectedLattices : E6ProjectedLattices := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨e6Cartan.mulVec x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨(threeTimesCartanInverse - inverseOnOrbitSums).mulVec x, ?_⟩
    funext i
    simp only [e6Projection]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, cartan_mul_projected_inverse]

private def corootCorrection : Matrix (Fin 6) (Fin 6) ℤ :=
  !![0, 1, 3, 2, 0, 2;
     0, 2, 3, 3, 1, 2;
     0, 2, 5, 4, 1, 3;
     0, 3, 6, 6, 2, 4;
     0, 2, 4, 4, 2, 3;
     0, 1, 2, 2, 1, 2]

private def firstCoweight : Fin 6 → ℤ := ![1, 0, 0, 0, 0, 0]

private theorem cartan_mul_correction :
    e6Cartan * corootCorrection =
      1 - Matrix.vecMulVec firstCoweight ![1, 0, -1, 0, 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem cartan_mul_threeTimesInverse :
    e6Cartan * threeTimesCartanInverse = 3 • (1 : Matrix (Fin 6) (Fin 6) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem e6CoweightQuotient : E6CoweightClass := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    exact ⟨![z.val, 0, 0, 0, 0, 0], by simp [e6CoweightClass]⟩
  · intro x
    rw [e6CoweightClass, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y 0 - y 2 + y 4 - y 5, ?_⟩
      simp [e6Cartan, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      ring
    · rintro ⟨m, hm⟩
      refine ⟨corootCorrection.mulVec x +
        threeTimesCartanInverse.mulVec (m • firstCoweight), ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        cartan_mul_correction, cartan_mul_threeTimesInverse, Matrix.sub_mulVec,
        Matrix.vecMulVec_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
      have hdot : ![1, 0, -1, 0, 1, -1] ⬝ᵥ x = 3 * m := by
        calc
          _ = x 0 - x 2 + x 4 - x 5 := by
            simp [dotProduct, Fin.sum_univ_succ]
            ring
          _ = 3 * m := by simpa using hm
      rw [hdot]
      ext i
      simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul]
      ring
  · intro x
    simp only [e6CoweightClass]
    rw [← Int.cast_neg]
    congr 1
    simp [e6Diagram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring

private theorem f4CoordinateShapes (z : Fin 4 → ℤ)
    (hz : IsLongF4Doubled z ∨ IsShortF4Doubled z) :
    (∀ i, z i = 1 ∨ z i = -1) ∨
      ((∃ i, z i ≠ 0) ∧ (∃ i, z i = 0) ∧ ∀ i, z i = 0 ∨ z i = 2 ∨ z i = -2) := by
  have hcoord (i k : Fin 4) (b : Bool) :
      let v : Fin 4 → ℤ := Pi.single i (2 * unitSign b)
      v k = 0 ∨ v k = 2 ∨ v k = -2 := by
    dsimp
    by_cases h : k = i
    · subst k
      cases b <;> simp [unitSign]
    · exact Or.inl (Pi.single_eq_of_ne h _)
  have hbit (s : Bool) : 2 * unitSign s ≠ 0 := by cases s <;> decide
  rcases hz with ⟨i, j, s, t, hij, rfl⟩ | ⟨i, s, rfl⟩ | h
  · right
    have hex : ∀ i j : Fin 4, ∃ k, k ≠ i ∧ k ≠ j := by decide
    obtain ⟨k, hki, hkj⟩ := hex i j
    refine ⟨⟨i, ?_⟩, ⟨k, ?_⟩, ?_⟩
    · simpa [Pi.single_apply, hij, Ne.symm hij] using hbit s
    · simp [hki, hkj]
    · intro k
      by_cases h : k = i
      · subst k
        simpa [Pi.single_apply, hij, Ne.symm hij] using hcoord i i s
      · simpa [Pi.single_apply, h, Ne.symm h] using hcoord j k t
  · right
    have hex : ∀ i : Fin 4, ∃ k, k ≠ i := by decide
    obtain ⟨k, hki⟩ := hex i
    exact ⟨⟨i, by simpa using hbit s⟩, ⟨k, Pi.single_eq_of_ne hki _⟩, fun j => hcoord i j s⟩
  · exact Or.inl h

theorem f4Reduced : F4Reduced.{u} := by
  intro K _ _ z w hz hw ⟨a, ha⟩
  have hnonzero (u : Fin 4 → ℤ) (hu : IsLongF4Doubled u ∨ IsShortF4Doubled u) :
      ∃ i, u i ≠ 0 := by
    rcases f4CoordinateShapes u hu with h | h
    · exact ⟨0, by rcases h 0 with hz | hz <;> simp [hz]⟩
    · exact h.1
  obtain ⟨j, hj⟩ := hnonzero w hw
  have ha₀ : a ≠ 0 := by
    intro h
    have hj' : (w j : K) = 0 := by simpa [h] using ha j
    exact hj (by exact_mod_cast hj')
  have hz_iff (i : Fin 4) : w i = 0 ↔ z i = 0 := by
    have hw_iff : w i = 0 ↔ (w i : K) = 0 := (Int.cast_eq_zero).symm
    rw [hw_iff, ha i, mul_eq_zero, or_iff_right ha₀, Int.cast_eq_zero]
  have ratio (i : Fin 4) (m : ℤ) (hm : (m : K) ≠ 0)
      (hz : z i = m ∨ z i = -m) (hw : w i = m ∨ w i = -m) : a = 1 ∨ a = -1 := by
    have hzi : (z i : K) ≠ 0 := by rcases hz with h | h <;> simp [h, hm]
    rw [show a = (w i : K) / (z i : K) from (eq_div_iff hzi).2 (ha i).symm]
    rcases hz with h | h <;> rcases hw with h' | h' <;> simp [h, h', neg_div, div_neg, div_self hm]
  have hsign : a = 1 ∨ a = -1 := by
    rcases f4CoordinateShapes z hz with hz | hz <;> rcases f4CoordinateShapes w hw with hw | hw
    · exact ratio 0 1 (by norm_num) (hz 0) (hw 0)
    · obtain ⟨i, hi⟩ := hw.2.1
      have he := (hz_iff i).mp hi
      rcases hz i with h | h <;> simp [h] at he
    · obtain ⟨i, hi⟩ := hz.2.1
      have he := (hz_iff i).mpr hi
      rcases hw i with h | h <;> simp [h] at he
    · obtain ⟨i, hi⟩ := hz.1
      exact ratio i 2 (by norm_num) ((hz.2.2 i).resolve_left hi)
        ((hw.2.2 i).resolve_left fun h => hi ((hz_iff i).mp h))
  rcases hsign with h | h
  · left
    funext i
    have hi := ha i
    rw [h, one_mul] at hi
    exact_mod_cast hi
  · right
    funext i
    have hi := ha i
    rw [h, neg_one_mul, ← Int.cast_neg] at hi
    exact_mod_cast hi

section E6FiniteCalculation

/-- Root coordinates in the order obtained by applying the four orbit
reflections, starting with the six simple roots. -/
private def e6RootTable : Fin 72 → Fin 6 → ℤ :=
  ![![0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0],
    ![0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0],
    ![1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1],
    ![0, -1, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0],
    ![0, 0, 0, -1, 0, 0],
    ![0, 0, 1, 1, 1, 0],
    ![0, 0, 1, 1, 0, 0],
    ![0, 0, -1, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 1, 1],
    ![-1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, -1],
    ![0, -1, 0, -1, 0, 0],
    ![0, 1, 1, 1, 1, 0],
    ![0, 0, -1, -1, -1, 0],
    ![1, 0, 1, 1, 1, 1],
    ![0, 1, 1, 1, 0, 0],
    ![1, 0, 1, 1, 0, 0],
    ![0, 0, -1, -1, 0, 0],
    ![-1, 0, -1, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0],
    ![0, 0, 0, 1, 1, 1],
    ![0, 0, 0, -1, -1, 0],
    ![0, 0, 0, 0, -1, -1],
    ![0, -1, -1, -1, -1, 0],
    ![0, 1, 1, 2, 1, 0],
    ![1, 1, 1, 1, 1, 1],
    ![-1, 0, -1, -1, -1, -1],
    ![1, 1, 1, 1, 0, 0],
    ![1, 0, 1, 1, 1, 0],
    ![0, -1, -1, -1, 0, 0],
    ![-1, 0, -1, -1, 0, 0],
    ![0, 1, 0, 1, 1, 1],
    ![0, 0, 1, 1, 1, 1],
    ![0, -1, 0, -1, -1, 0],
    ![0, 0, 0, -1, -1, -1],
    ![0, -1, -1, -2, -1, 0],
    ![-1, -1, -1, -1, -1, -1],
    ![1, 1, 1, 2, 1, 1],
    ![1, 1, 1, 1, 1, 0],
    ![-1, -1, -1, -1, 0, 0],
    ![-1, 0, -1, -1, -1, 0],
    ![0, 1, 1, 1, 1, 1],
    ![0, -1, 0, -1, -1, -1],
    ![0, 0, -1, -1, -1, -1],
    ![-1, -1, -1, -2, -1, -1],
    ![1, 1, 2, 2, 2, 1],
    ![1, 1, 1, 2, 1, 0],
    ![-1, -1, -1, -1, -1, 0],
    ![0, 1, 1, 2, 1, 1],
    ![0, -1, -1, -1, -1, -1],
    ![-1, -1, -2, -2, -2, -1],
    ![1, 1, 2, 3, 2, 1],
    ![1, 1, 2, 2, 1, 0],
    ![-1, -1, -1, -2, -1, 0],
    ![0, 1, 1, 2, 2, 1],
    ![0, -1, -1, -2, -1, -1],
    ![-1, -1, -2, -3, -2, -1],
    ![1, 2, 2, 3, 2, 1],
    ![1, 1, 2, 2, 1, 1],
    ![-1, -1, -2, -2, -1, 0],
    ![1, 1, 1, 2, 2, 1],
    ![0, -1, -1, -2, -2, -1],
    ![-1, -2, -2, -3, -2, -1],
    ![-1, -1, -2, -2, -1, -1],
    ![-1, -1, -1, -2, -2, -1]]

private def reflectedIndex : Fin 6 → Fin 72 → Fin 72 :=
  ![![0, 1, 12, 3, 16, 5, 6, 7, 8, 35, 23, 25, 2, 13, 14, 15, 4, 17, 18, 45, 47, 39, 34, 10, 37, 11, 26, 27, 28, 29, 54, 53, 48, 50, 22, 9, 46, 24, 38, 21, 40, 41, 60, 56, 55, 19, 36, 20, 32, 49, 33, 62, 52, 31, 30, 44, 43, 57, 58, 59, 42, 67, 51, 63, 64, 65, 66, 61, 71, 69, 70, 68],
    ![6, 7, 2, 3, 4, 5, 0, 1, 18, 19, 22, 11, 12, 26, 14, 15, 16, 17, 8, 9, 30, 32, 10, 34, 36, 25, 13, 38, 40, 29, 20, 31, 21, 43, 23, 45, 24, 46, 27, 48, 28, 49, 42, 33, 44, 35, 37, 54, 39, 41, 56, 51, 52, 53, 47, 55, 50, 57, 64, 59, 60, 61, 62, 69, 58, 65, 66, 67, 68, 63, 70, 71],
    ![0, 10, 11, 3, 12, 5, 6, 22, 24, 13, 1, 2, 4, 9, 14, 15, 25, 17, 36, 26, 28, 21, 7, 23, 8, 16, 19, 39, 20, 29, 40, 31, 32, 33, 34, 35, 18, 37, 48, 27, 30, 50, 42, 43, 65, 45, 46, 47, 38, 56, 41, 70, 67, 59, 54, 55, 49, 71, 58, 53, 66, 61, 62, 63, 64, 44, 60, 52, 68, 69, 51, 57],
    ![7, 8, 10, 13, 4, 5, 18, 0, 1, 9, 2, 24, 23, 3, 28, 27, 16, 17, 6, 31, 20, 21, 22, 12, 11, 37, 26, 15, 14, 41, 42, 19, 44, 33, 34, 35, 36, 25, 38, 39, 40, 29, 30, 51, 32, 53, 46, 47, 55, 49, 50, 43, 58, 45, 60, 48, 62, 63, 52, 59, 54, 61, 56, 57, 64, 65, 66, 67, 68, 69, 70, 71],
    ![0, 13, 2, 14, 4, 15, 6, 26, 28, 10, 9, 11, 12, 1, 3, 5, 16, 29, 40, 22, 24, 21, 19, 35, 20, 25, 7, 27, 8, 17, 36, 31, 32, 33, 45, 23, 30, 47, 38, 39, 18, 41, 42, 43, 67, 34, 54, 37, 48, 49, 50, 71, 65, 53, 46, 61, 56, 70, 58, 59, 60, 55, 68, 63, 64, 52, 66, 44, 62, 69, 57, 51],
    ![0, 1, 2, 15, 4, 17, 6, 7, 8, 39, 10, 11, 12, 27, 29, 3, 16, 5, 18, 48, 50, 35, 22, 23, 24, 25, 38, 13, 41, 14, 56, 55, 45, 47, 34, 21, 36, 37, 26, 9, 49, 28, 62, 54, 53, 32, 46, 33, 19, 40, 20, 60, 52, 44, 43, 31, 30, 57, 58, 65, 51, 61, 42, 63, 64, 59, 70, 67, 68, 69, 66, 71]]

/-- A simple orbit, a word of orbit reflections, and the choice of the second
member in that simple orbit. -/
private def orbitWordTable : Fin 72 → Fin 4 × List (Fin 4) × Bool :=
  ![(0, [], false),
    (1, [], false),
    (2, [], false),
    (2, [], true),
    (3, [], false),
    (3, [], true),
    (0, [0], false),
    (0, [1], false),
    (1, [1], false),
    (1, [2], false),
    (2, [1], false),
    (2, [2], false),
    (2, [3], false),
    (2, [1], true),
    (2, [2], true),
    (2, [3], true),
    (3, [3], false),
    (3, [3], true),
    (0, [1, 0], false),
    (0, [2, 1], false),
    (1, [2, 1], false),
    (1, [3, 2], false),
    (2, [0, 1], false),
    (2, [3, 1], false),
    (2, [1, 2], false),
    (2, [3, 2], false),
    (2, [0, 1], true),
    (2, [3, 1], true),
    (2, [1, 2], true),
    (2, [3, 2], true),
    (0, [2, 1, 0], false),
    (0, [1, 2, 1], false),
    (0, [3, 2, 1], false),
    (1, [3, 2, 1], false),
    (2, [3, 0, 1], false),
    (2, [2, 3, 1], false),
    (2, [0, 1, 2], false),
    (2, [3, 1, 2], false),
    (2, [3, 0, 1], true),
    (2, [2, 3, 1], true),
    (2, [0, 1, 2], true),
    (2, [3, 1, 2], true),
    (0, [1, 2, 1, 0], false),
    (0, [3, 2, 1, 0], false),
    (0, [3, 1, 2, 1], false),
    (2, [2, 3, 0, 1], false),
    (2, [3, 0, 1, 2], false),
    (2, [2, 3, 1, 2], false),
    (2, [2, 3, 0, 1], true),
    (2, [3, 0, 1, 2], true),
    (2, [2, 3, 1, 2], true),
    (0, [3, 1, 2, 1, 0], false),
    (0, [2, 3, 1, 2, 1], false),
    (2, [1, 2, 3, 0, 1], false),
    (2, [2, 3, 0, 1, 2], false),
    (2, [1, 2, 3, 0, 1], true),
    (2, [2, 3, 0, 1, 2], true),
    (0, [2, 3, 1, 2, 1, 0], false),
    (0, [1, 2, 3, 1, 2, 1], false),
    (2, [2, 1, 2, 3, 0, 1], false),
    (2, [1, 2, 3, 0, 1, 2], false),
    (2, [2, 1, 2, 3, 0, 1], true),
    (2, [1, 2, 3, 0, 1, 2], true),
    (0, [1, 2, 3, 1, 2, 1, 0], false),
    (0, [0, 1, 2, 3, 1, 2, 1], false),
    (2, [3, 2, 1, 2, 3, 0, 1], false),
    (2, [2, 1, 2, 3, 0, 1, 2], false),
    (2, [3, 2, 1, 2, 3, 0, 1], true),
    (2, [2, 1, 2, 3, 0, 1, 2], true),
    (0, [0, 1, 2, 3, 1, 2, 1, 0], false),
    (2, [3, 2, 1, 2, 3, 0, 1, 2], false),
    (2, [3, 2, 1, 2, 3, 0, 1, 2], true)]

private theorem e6Table_contains_simple (i : Fin 6) :
    Pi.single i 1 ∈ Set.range e6RootTable := by
  fin_cases i
  · exact ⟨4, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨5, by decide⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem e6Table_reflection :
    ∀ (i : Fin 6) (k : Fin 72),
      simpleReflection e6Cartan i (e6RootTable k) = e6RootTable (reflectedIndex i k) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem e6Table_orbitWord :
    ∀ k : Fin 72,
      let (j, w, second) := orbitWordTable k
      let i := if second then orbitSecond j else orbitFirst j
      e6RootTable k = orbitWord w (Pi.single i 1) ∧
        (e6RootTable k = e6Diagram.mulVec (e6RootTable k) ↔ orbitFirst j = orbitSecond j) := by
  decide +kernel

private theorem orbitReflection_isRoot (j : Fin 4) {r : Fin 6 → ℤ}
    (hr : IsRootCoordinate e6Cartan r) : IsRootCoordinate e6Cartan (orbitReflection j r) := by
  unfold orbitReflection
  split
  · exact hr.reflect _
  · exact (hr.reflect _).reflect _

private theorem orbitWord_isRoot (w : List (Fin 4)) {r : Fin 6 → ℤ}
    (hr : IsRootCoordinate e6Cartan r) : IsRootCoordinate e6Cartan (orbitWord w r) := by
  induction w with
  | nil => exact hr
  | cons j w ih => exact orbitReflection_isRoot j ih

private theorem e6Table_iff (r : Fin 6 → ℤ) :
    IsRootCoordinate e6Cartan r ↔ r ∈ Set.range e6RootTable := by
  constructor
  · intro hr
    induction hr with
    | simple i => exact e6Table_contains_simple i
    | reflect h i ih =>
      obtain ⟨k, rfl⟩ := ih
      exact ⟨reflectedIndex i k, (e6Table_reflection i k).symm⟩
  · rintro ⟨k, rfl⟩
    have hk := e6Table_orbitWord k
    cases h : orbitWordTable k with
    | mk j ws =>
      rcases ws with ⟨w, b⟩
      rw [h] at hk
      rw [hk.1]
      exact orbitWord_isRoot _ (.simple _)

private theorem e6Table_folded :
    ∀ k : Fin 72,
      let r := e6RootTable k
      (r ≠ e6Diagram.mulVec r → dotProduct r (e6Cartan.mulVec (e6Diagram.mulVec r)) = 0) ∧
      (IsLongF4Doubled (foldedRoot r) ↔ r = e6Diagram.mulVec r) ∧
      (IsShortF4Doubled (foldedRoot r) ↔ r ≠ e6Diagram.mulVec r) := by
  decide +kernel

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
private theorem e6Table_fibres :
    ∀ k l : Fin 72, foldedRoot (e6RootTable k) = foldedRoot (e6RootTable l) ↔
      e6RootTable l = e6RootTable k ∨ e6RootTable l = e6Diagram.mulVec (e6RootTable k) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem e6Table_long :
    ∀ (i j : Fin 4) (s t : Bool), i ≠ j → ∃ k : Fin 72,
      foldedRoot (e6RootTable k) = Pi.single i (2 * unitSign s) + Pi.single j (2 * unitSign t) := by
  decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem e6Table_short :
    (∀ (i : Fin 4) (s : Bool), ∃ k : Fin 72,
      foldedRoot (e6RootTable k) = Pi.single i (2 * unitSign s)) ∧
    (∀ signs : Fin 4 → Bool, ∃ k : Fin 72, foldedRoot (e6RootTable k) = unitSign ∘ signs) := by
  decide +kernel

theorem e6Folding : E6Folding := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨k, rfl⟩ := (e6Table_iff r).mp hr
    have hk := e6Table_orbitWord k
    refine ⟨(e6Table_folded k).1, (e6Table_folded k).2.1, (e6Table_folded k).2.2, ?_⟩
    cases h : orbitWordTable k with
    | mk j ws =>
      rcases ws with ⟨w, b⟩
      rw [h] at hk
      refine ⟨j, w, ?_, hk.2⟩
      cases b
      · exact Or.inl hk.1
      · exact Or.inr hk.1
  · intro r s hr hs
    obtain ⟨k, rfl⟩ := (e6Table_iff r).mp hr
    obtain ⟨l, rfl⟩ := (e6Table_iff s).mp hs
    exact e6Table_fibres k l
  · intro z
    constructor
    · intro h
      suffices hk : ∃ k : Fin 72, foldedRoot (e6RootTable k) = z by
        obtain ⟨k, hk⟩ := hk
        exact ⟨e6RootTable k, (e6Table_iff _).mpr ⟨k, rfl⟩, hk⟩
      rcases h with ⟨i, j, s, t, hij, rfl⟩ | ⟨i, s, rfl⟩ | h
      · exact e6Table_long i j s t hij
      · exact e6Table_short.1 i s
      · let signs : Fin 4 → Bool := fun i => decide (z i = 1)
        have hs : unitSign ∘ signs = z := by
          funext i
          rcases h i with hi | hi <;> simp [signs, unitSign, hi]
        simpa only [hs] using e6Table_short.2 signs
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨k, rfl⟩ := (e6Table_iff r).mp hr
      by_cases h : e6RootTable k = e6Diagram.mulVec (e6RootTable k)
      · exact Or.inl ((e6Table_folded k).2.1.mpr h)
      · exact Or.inr ((e6Table_folded k).2.2.mpr h)

theorem e6BasedOrbitTransport : E6BasedOrbitTransport.{u,v,w} := by
  classical
  intro ι X Y _ _ _ P _ B e σ hσ hC
  obtain ⟨_, ρ, hρ, hreflect⟩ := e6DiagramCoordinates (K := ℚ) P B e σ hσ hC
  let coeff (i : ι) : Fin 6 → ℤ := (ρ i).val
  have hinj : Function.Injective coeff := fun i j h => ρ.injective (Subtype.ext h)
  let F := Fintype.linearCombination ℤ (fun j : Fin 6 => P.root (e j))
  have hF : Function.Injective F := linearIndependent_iff_injective_fintypeLinearCombination.mp
    (B.linearIndepOn_root.comp e e.injective)
  have hsimple (j : Fin 6) : coeff (e j) = Pi.single j 1 := by
    apply hF
    change (∑ k, coeff (e j) k • P.root (e k)) = ∑ k, (Pi.single j 1 : Fin 6 → ℤ) k • P.root (e k)
    rw [← (hρ (e j)).1]
    simp [Pi.single_apply, ite_smul]
  have horbit (j : Fin 4) (i : ι) : coeff (basedOrbitReflection P B e j i) = orbitReflection j (coeff i) := by
    by_cases h : orbitFirst j = orbitSecond j <;>
      simp only [basedOrbitReflection, orbitReflection, h, ite_true, ite_false, coeff, hreflect]
  have hword (word : List (Fin 4)) (i : ι) :
      coeff (word.foldr (basedOrbitReflection P B e) i) = orbitWord word (coeff i) := by
    induction word with
    | nil => rfl
    | cons j word ih =>
      simpa only [orbitWord, List.foldr_cons] using
        (horbit j (word.foldr (basedOrbitReflection P B e) i)).trans (congrArg (orbitReflection j) ih)
  refine ⟨fun j hj => (hC _ _).symm.trans (e6Folding.1 j hj), fun i => ?_⟩
  obtain ⟨j, word, hw, hf⟩ := (e6Folding.2.1 (coeff i) (ρ i).property).2.2.2
  have hfixed : σ.indexEquiv i = i ↔ coeff i = e6Diagram.mulVec (coeff i) := by
    rw [← show coeff (σ.indexEquiv i) = e6Diagram.mulVec (coeff i) from (hρ i).2.2, eq_comm]
    exact hinj.eq_iff.symm
  refine ⟨j, word, ?_, hfixed.trans hf⟩
  rcases hw with hw | hw
  · exact Or.inl (hinj (hw.trans (by rw [hword, hsimple])))
  · exact Or.inr (hinj (hw.trans (by rw [hword, hsimple])))

/-! The finite checks below use the 48 distinct folded directions. -/

private def foldedDirectionTable (i : Fin 48) : Fin 4 → ℤ :=
  #[![-2, -2, 0, 0],
    ![-2, 0, -2, 0],
    ![-2, 0, 0, -2],
    ![-2, 0, 0, 0],
    ![-2, 0, 0, 2],
    ![-2, 0, 2, 0],
    ![-2, 2, 0, 0],
    ![-1, -1, -1, -1],
    ![-1, -1, -1, 1],
    ![-1, -1, 1, -1],
    ![-1, -1, 1, 1],
    ![-1, 1, -1, -1],
    ![-1, 1, -1, 1],
    ![-1, 1, 1, -1],
    ![-1, 1, 1, 1],
    ![0, -2, -2, 0],
    ![0, -2, 0, -2],
    ![0, -2, 0, 0],
    ![0, -2, 0, 2],
    ![0, -2, 2, 0],
    ![0, 0, -2, -2],
    ![0, 0, -2, 0],
    ![0, 0, -2, 2],
    ![0, 0, 0, -2],
    ![0, 0, 0, 2],
    ![0, 0, 2, -2],
    ![0, 0, 2, 0],
    ![0, 0, 2, 2],
    ![0, 2, -2, 0],
    ![0, 2, 0, -2],
    ![0, 2, 0, 0],
    ![0, 2, 0, 2],
    ![0, 2, 2, 0],
    ![1, -1, -1, -1],
    ![1, -1, -1, 1],
    ![1, -1, 1, -1],
    ![1, -1, 1, 1],
    ![1, 1, -1, -1],
    ![1, 1, -1, 1],
    ![1, 1, 1, -1],
    ![1, 1, 1, 1],
    ![2, -2, 0, 0],
    ![2, 0, -2, 0],
    ![2, 0, 0, -2],
    ![2, 0, 0, 0],
    ![2, 0, 0, 2],
    ![2, 0, 2, 0],
    ![2, 2, 0, 0]][i.val]!

private def foldedTableIndex (i : Fin 72) : Fin 48 :=
  #[28, 25, 24, 24, 33, 33, 19, 29, 22, 27, 26, 23, 34, 26, 23, 34, 14, 14, 18, 31, 20, 41, 30, 35, 21, 13, 30, 35, 21, 13, 16, 32, 42, 6, 37, 36, 17, 12, 37, 36, 17, 12, 15, 5, 43, 38, 10, 11, 38, 10, 11, 4, 45, 39, 9, 39, 9, 2, 46, 40, 8, 40, 8, 1, 47, 44, 7, 44, 7, 0, 3, 3][i.val]!

private def foldedPairing (r s : Fin 4 → ℤ) : ℤ :=
  (normalizedFoldedNumerator r ⬝ᵥ s) / 4

private theorem foldedTable_mem : ∀ k, IsLongF4Doubled (foldedDirectionTable k) ∨
    IsShortF4Doubled (foldedDirectionTable k) := by
  decide +kernel

private theorem foldedTable_restriction : ∀ k,
    foldedDirectionTable (foldedTableIndex k) = foldedRoot (e6RootTable k) := by
  decide +kernel

private theorem foldedTable_surjective (r : FoldedRootDirection) :
    ∃ k, foldedDirectionTable k = r.val := by
  obtain ⟨s, hs, h⟩ := (e6Folding.2.2.2 r.val).mp r.property
  obtain ⟨k, rfl⟩ := (e6Table_iff s).mp hs
  exact ⟨foldedTableIndex k, (foldedTable_restriction k).trans h⟩

private theorem foldedTable_diagonal : ∀ k, let r := foldedDirectionTable k
    normalizedFoldedNumerator r ⬝ᵥ r = 8 := by
  decide +kernel

set_option maxHeartbeats 10000000 in
private theorem foldedTable_integral : ∀ k l,
    let r := foldedDirectionTable k
    let s := foldedDirectionTable l
    normalizedFoldedNumerator r ⬝ᵥ s = 4 * foldedPairing r s := by
  decide +kernel

private def foldedMultiplier (r : Fin 4 → ℤ) : ℤ :=
  if IsLongF4Doubled r then 1 else 2

private theorem foldedNumerator_smul (r : Fin 4 → ℤ) :
    normalizedFoldedNumerator r = foldedMultiplier r • r := by
  simp only [normalizedFoldedNumerator, foldedMultiplier]
  split_ifs <;> simp

private theorem foldedMultiplier_ne_zero (r : Fin 4 → ℤ) : foldedMultiplier r ≠ 0 := by
  unfold foldedMultiplier
  split_ifs <;> decide

private theorem foldedTable_norm : ∀ k, let r := foldedDirectionTable k
    r ⬝ᵥ r = if IsLongF4Doubled r then 8 else 4 := by
  decide +kernel

private theorem folded_norm (r : FoldedRootDirection) :
    r.val ⬝ᵥ r.val = if IsLongF4Doubled r.val then 8 else 4 := by
  obtain ⟨k, hk⟩ := foldedTable_surjective r
  simpa only [hk] using foldedTable_norm k

private theorem folded_integral (r s : FoldedRootDirection) :
    foldedMultiplier r.val * (r.val ⬝ᵥ s.val) = 4 * foldedPairing r.val s.val := by
  obtain ⟨k, hk⟩ := foldedTable_surjective r
  obtain ⟨l, hl⟩ := foldedTable_surjective s
  simpa only [hk, hl, foldedNumerator_smul, smul_dotProduct, smul_eq_mul] using
    foldedTable_integral k l

private theorem folded_reflect_coefficients (r s : FoldedRootDirection) :
    ∃ t : FoldedRootDirection, t.val = s.val - foldedPairing r.val s.val • r.val ∧
    normalizedFoldedNumerator t.val = normalizedFoldedNumerator s.val -
      foldedPairing s.val r.val • normalizedFoldedNumerator r.val := by
  let a := foldedPairing r.val s.val
  let b := foldedPairing s.val r.val
  let t := s.val - a • r.val
  let R := r.val ⬝ᵥ r.val
  let P := r.val ⬝ᵥ s.val
  let m := foldedMultiplier r.val
  let n := foldedMultiplier s.val
  have ha : m * P = 4 * a := folded_integral r s
  have hb : n * P = 4 * b := by
    change foldedMultiplier s.val * (r.val ⬝ᵥ s.val) = _
    rw [dotProduct_comm]
    exact folded_integral s r
  have hn : m * R = 8 := by
    simp only [m, R, folded_norm, foldedMultiplier]
    split_ifs <;> norm_num
  have hp : R * a = 2 * P := by
    apply mul_left_cancel₀ (foldedMultiplier_ne_zero r.val)
    change m * (R * a) = m * (2 * P)
    calc
      m * (R * a) = (m * R) * a := by ring
      _ = 2 * (m * P) := by rw [hn, ha]; ring
      _ = _ := by ring
  have htn : t ⬝ᵥ t = s.val ⬝ᵥ s.val := by
    simp only [t, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm s.val r.val]
    change s.val ⬝ᵥ s.val - a * P - a * (P - a * R) = _
    have hp' : a * R = 2 * P := (mul_comm _ _).trans hp
    rw [hp']
    ring
  have hbound (i : Fin 4) : -2 ≤ t i ∧ t i ≤ 2 := by
    have hle : t i * t i ≤ t ⬝ᵥ t := by
      exact Finset.single_le_sum (fun j _ => mul_self_nonneg (t j)) (Finset.mem_univ i)
    have h8 : t ⬝ᵥ t ≤ 8 := by rw [htn, folded_norm]; split_ifs <;> decide
    constructor
    · by_contra! h
      have hn : t i ≤ -3 := by omega
      nlinarith [sq_nonneg (t i + 3)]
    · by_contra! h
      have h3 : 3 ≤ t i := by omega
      nlinarith [sq_nonneg (t i - 3)]
  let q (i : Fin 4) : Fin 5 := ⟨(t i + 2).toNat, by have := hbound i; omega⟩
  have hq : (fun i : Fin 4 => (q i : ℤ) - 2) = t := by
    funext i
    have := hbound i
    change ((t i + 2).toNat : ℤ) - 2 = t i
    omega
  have hcheck : ∀ q : Fin 4 → Fin 5,
      let v : Fin 4 → ℤ := fun i => (q i : ℤ) - 2
      (v ⬝ᵥ v = 8 → IsLongF4Doubled v) ∧ (v ⬝ᵥ v = 4 → IsShortF4Doubled v ∧ ¬IsLongF4Doubled v) := by
    decide +kernel
  have hs := hcheck q
  rw [hq] at hs
  have ht : IsLongF4Doubled t ∨ IsShortF4Doubled t := by
    rw [folded_norm] at htn
    split_ifs at htn with hs' 
    · exact Or.inl (hs.1 htn)
    · exact Or.inr (hs.2 htn).1
  have hmult : foldedMultiplier t = n := by
    rw [folded_norm] at htn
    by_cases hs' : IsLongF4Doubled s.val
    · have h : IsLongF4Doubled t := hs.1 (by simpa only [ite_eq_left hs'] using htn)
      simp [foldedMultiplier, h, n, hs']
    · have h : ¬IsLongF4Doubled t := (hs.2 (by simpa only [ite_eq_right hs'] using htn)).2
      simp [foldedMultiplier, h, n, hs']
  refine ⟨⟨t, ht⟩, rfl, ?_⟩
  change normalizedFoldedNumerator t = _
  have hmul : n * a = b * m := by
    have hna : n * (m * P) = n * (4 * a) := congrArg (fun x : ℤ => n * x) ha
    have hmb : m * (n * P) = m * (4 * b) := congrArg (fun x : ℤ => m * x) hb
    nlinarith only [hna, hmb]
  simp only [foldedNumerator_smul, hmult, t, smul_sub, smul_smul]
  rw [hmul]

private theorem normalizedFoldedRoot_apply {K : Type*} [Field K]
    (r : FoldedRootDirection) (x : Fin 4 → K) :
    normalizedFoldedRoot K r x = ∑ j, ((normalizedFoldedNumerator r.val j : K) / 2) * x j := by
  simp [normalizedFoldedRoot, Finset.sum_apply, smul_eq_mul]

private theorem normalizedFolded_pairing {K : Type*} [Field K] [CharZero K]
    (r s : FoldedRootDirection) :
    normalizedFoldedRoot K r (normalizedFoldedCoroot K s) = (foldedPairing r s : K) := by
  obtain ⟨k, hk⟩ := foldedTable_surjective r
  obtain ⟨l, hl⟩ := foldedTable_surjective s
  have h := foldedTable_integral k l
  dsimp only at h
  rw [hk, hl] at h
  have h' := congrArg (Int.cast : ℤ → K) h
  change ((normalizedFoldedNumerator r.val ⬝ᵥ s.val : ℤ) : K) = _ at h'
  rw [normalizedFoldedRoot_apply]
  calc
    (∑ j, ((normalizedFoldedNumerator r.val j : K) / 2) * normalizedFoldedCoroot K s j) =
        ((normalizedFoldedNumerator r.val ⬝ᵥ s.val : ℤ) : K) / 4 := by
      simp only [normalizedFoldedCoroot, dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [h']; push_cast; ring

private theorem foldedPairing_diagonal (r : FoldedRootDirection) : foldedPairing r r = 2 := by
  obtain ⟨k, hk⟩ := foldedTable_surjective r
  have h := foldedTable_diagonal k
  dsimp only at h
  rw [hk] at h
  norm_num [foldedPairing, h]

theorem foldedApartmentRootSystem : FoldedApartmentRootSystem.{u} := by
  intro K _ _
  let D : ApartmentRoots K (Fin 4 → K) FoldedRootDirection :=
    { root := normalizedFoldedRoot K
      coroot := normalizedFoldedCoroot K
      diagonal := fun r => by rw [normalizedFolded_pairing, foldedPairing_diagonal]; norm_num
      integral := fun r s => ⟨foldedPairing r s, normalizedFolded_pairing r s⟩ }
  refine ⟨D, rfl, rfl, fun r s => ?_⟩
  obtain ⟨t, h⟩ := folded_reflect_coefficients r s
  have hcoroot (j : Fin 4) := congrFun h.1 j
  have hnumerator (j : Fin 4) := congrFun h.2 j
  refine ⟨t, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change normalizedFoldedRoot K t x = normalizedFoldedRoot K s (D.linearReflection r x)
    rw [show D.linearReflection r x = x - (D.root r x) • D.coroot r from rfl, map_sub, map_smul]
    change normalizedFoldedRoot K t x = normalizedFoldedRoot K s x -
      normalizedFoldedRoot K r x • normalizedFoldedRoot K s (normalizedFoldedCoroot K r)
    rw [normalizedFolded_pairing]
    simp only [normalizedFoldedRoot_apply, hnumerator, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Int.cast_sub, Int.cast_mul, sub_div, mul_div_assoc, sub_mul,
      Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  · funext j
    change (t.val j : K) / 2 =
      (s.val j : K) / 2 - normalizedFoldedRoot K r (normalizedFoldedCoroot K s) * ((r.val j : K) / 2)
    rw [normalizedFolded_pairing, hcoroot]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul]
    ring

private theorem e6Table_foldedNorm :
    ∀ k : Fin 72,
    let r := e6RootTable k
    foldedRoot r ⬝ᵥ foldedRoot r = if r = e6Diagram.mulVec r then 8 else 4 := by
  decide +kernel

theorem foldedApartmentCoordinates : FoldedApartmentCoordinates.{u} := by
  intro K _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    funext i
    fin_cases i <;>
      simp [foldedApartment, unfoldApartment, f4SimpleDoubled, Fin.sum_univ_succ] <;> ring
  · intro x hx₀ hx₂
    funext i
    fin_cases i <;>
      simp [foldedApartment, unfoldApartment, f4SimpleDoubled, Fin.sum_univ_succ,
        ← hx₀, ← hx₂] <;> ring
  · intro r v
    simp [foldedApartment, foldedRoot, restrictedRoot, f4SimpleDoubled, Matrix.vecMul,
      Fin.sum_univ_succ, dotProduct]
    ring
  · intro r i
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    fin_cases i <;>
      simp [foldedApartment, foldedRoot, restrictedRoot, f4SimpleDoubled, e6Cartan, e6Diagram,
        Matrix.vecMul, Fin.sum_univ_succ, dotProduct] <;> ring

theorem foldedNormalizedCoroots : FoldedNormalizedCoroots := by
  intro r hr
  have hn : foldedRoot r ⬝ᵥ foldedRoot r = if r = e6Diagram.mulVec r then 8 else 4 := by
    obtain ⟨k, rfl⟩ := (e6Table_iff r).mp hr
    exact e6Table_foldedNorm k
  let β : Fin 4 → ℚ := fun j => (foldedRoot r j : ℚ) / 2
  let d : ℚ := if r = e6Diagram.mulVec r then 1 else 2
  change ((d • β) ⬝ᵥ (d • β) ≠ 0) ∧ _
  have hβ : β ⬝ᵥ β = if r = e6Diagram.mulVec r then 2 else 1 := by
    have hnorm : (4 : ℚ) * (β ⬝ᵥ β) = (foldedRoot r ⬝ᵥ foldedRoot r : ℤ) := by
      simp only [β, dotProduct, Finset.mul_sum, Int.cast_sum, Int.cast_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hn] at hnorm
    split_ifs at hnorm ⊢ <;> norm_num at hnorm <;> linarith only [hnorm]
  have hd : d * (β ⬝ᵥ β) = 2 := by
    simp only [d, hβ]
    split_ifs <;> norm_num
  have hγ : (d • β) ⬝ᵥ (d • β) = 2 * d := by
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm d d,
      mul_assoc, hd, mul_comm]
  have hdne : d ≠ 0 := by unfold d; split_ifs <;> norm_num
  refine ⟨by rw [hγ]; exact mul_ne_zero (by norm_num) hdne, ?_⟩
  have hvec : (fun j => 2 * (d • β) j / ((d • β) ⬝ᵥ (d • β))) = β := by
    funext j
    rw [hγ, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_div_cancel_left₀ _ (mul_ne_zero
      (by norm_num) hdne)]
  rw [hvec]
  funext i
  exact foldedApartmentCoordinates.2.2.2 r i

set_option maxHeartbeats 1500000 in
theorem foldedLatticeComparison : FoldedLatticeComparison := by
  let a : (Fin 4 → ℚ) →+ (Fin 6 → ℚ) :=
    { toFun := foldedApartment
      map_zero' := by funext i; fin_cases i <;> simp [foldedApartment]
      map_add' := by
        intro v w
        funext i
        fin_cases i <;>
          simp [foldedApartment, f4SimpleDoubled, Fin.sum_univ_succ] <;> ring }
  let p : (Fin 6 → ℤ) →+ (Fin 6 → ℚ) :=
    { toFun := fun x => e6Projection (e6Cartan.mulVec x)
      map_zero' := by funext i; simp [e6Projection]
      map_add' := by
        intro x y
        funext i
        simp [e6Projection, Matrix.mulVec_add, add_div] }
  have ha (r : Fin 6 → ℤ) :
      a (fun j => (foldedRoot r j : ℚ) / 2) = p r := by
    funext i
    exact foldedApartmentCoordinates.2.2.2 _ _
  have hL : foldedCorootLattice.map a = p.range := by
    apply le_antisymm
    · rw [foldedCorootLattice, AddMonoidHom.map_closure, AddSubgroup.closure_le]
      rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r.val, (ha _).symm⟩
    · intro v hv
      obtain ⟨t, rfl⟩ := hv
      have ht : (∑ i : Fin 6, t i • Pi.single i 1) = t := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply, mul_ite]
      rw [show p t = ∑ i : Fin 6, p (t i • Pi.single i 1) by rw [← map_sum, ht]]
      refine AddSubgroup.sum_mem _ fun i _ => ?_
      rw [map_zsmul]
      apply AddSubgroup.zsmul_mem
      rw [← ha]
      let r : {r // IsRootCoordinate e6Cartan r} := ⟨Pi.single i 1, .simple i⟩
      have hr : (fun j => (foldedRoot r.val j : ℚ) / 2) ∈ foldedCorootLattice :=
        AddSubgroup.subset_closure (Set.mem_range_self r)
      exact ⟨_, hr, rfl⟩
  have h : foldedApartment '' (foldedCorootLattice : Set (Fin 4 → ℚ)) =
      Set.range fun t => e6Projection (e6Cartan.mulVec t) :=
    congrArg (fun L : AddSubgroup (Fin 6 → ℚ) => (L : Set (Fin 6 → ℚ))) hL
  exact ⟨h, h.trans e6ProjectedLattices⟩

private def foldedApartmentMap (K : Type*) [Field K] : (Fin 4 → K) →ₗ[K] (Fin 6 → K) where
  toFun := foldedApartment
  map_add' x y := by
    funext j
    fin_cases j <;> simp [foldedApartment, f4SimpleDoubled, Fin.sum_univ_succ] <;> ring
  map_smul' a x := by
    funext j
    fin_cases j <;> simp [foldedApartment, f4SimpleDoubled, Fin.sum_univ_succ] <;> ring

private theorem foldedApartment_partner {K : Type*} [Field K] (x : Fin 4 → K) (i : Fin 6) :
    foldedApartment x (e6Partner i) = foldedApartment x i := by
  fin_cases i <;> rfl

private theorem foldedDepth_root {K : Type*} [Field K] (r : FoldedRootDirection) (x : Fin 4 → K) :
    normalizedFoldedRoot K r x = (foldedDepthDenominator r : K) * (∑ j, (r.val j : K) * x j) / 2 := by
  rw [normalizedFoldedRoot_apply, normalizedFoldedNumerator, foldedDepthDenominator]
  split_ifs <;>
    simp only [Nat.cast_one, Nat.cast_ofNat, one_mul, Pi.smul_apply, Finset.mul_sum, Finset.sum_div] <;>
    apply Finset.sum_congr rfl <;> intro j _
  · ring
  · rw [nsmul_eq_mul]
    push_cast
    ring

theorem foldedReducedDirections : FoldedReducedDirections.{u} := by
  intro K _ _ D hD
  let depth (i : FoldedRootDirection) : K := (foldedDepthDenominator i : K)
  have hdepth (i : FoldedRootDirection) : depth i ≠ 0 := by
    unfold depth foldedDepthDenominator
    split_ifs <;> norm_num
  have hm (i : FoldedRootDirection) (k : Fin 4) :
      D.root i (Pi.single k 1) = depth i * (i.val k : K) / 2 := by
    rw [hD, foldedDepth_root]
    simp [depth, Pi.single_apply, mul_ite]
  have hprop (i j : FoldedRootDirection) (a : K) (ha : D.root j = a • D.root i) :
      i = j ∨ D.root j = -D.root i := by
    have hcoord (k : Fin 4) : (j.val k : K) = (a * depth i / depth j) * (i.val k : K) := by
      have h := LinearMap.congr_fun ha (Pi.single k 1)
      rw [LinearMap.smul_apply, smul_eq_mul, hm, hm] at h
      rw [div_mul_eq_mul_div, eq_div_iff (hdepth j)]
      linear_combination 2 * h
    rcases f4Reduced i.val j.val i.property j.property ⟨_, hcoord⟩ with h | h
    · exact Or.inl (Subtype.ext h.symm)
    · refine Or.inr ?_
      have hn : j.val ⬝ᵥ j.val = i.val ⬝ᵥ i.val := by
        rw [h, neg_dotProduct, dotProduct_neg, neg_neg]
      have hden : foldedDepthDenominator j = foldedDepthDenominator i := by
        rw [folded_norm, folded_norm] at hn
        unfold foldedDepthDenominator
        split_ifs at hn ⊢ <;> omega
      apply LinearMap.ext
      intro x
      rw [hD, LinearMap.neg_apply, foldedDepth_root, foldedDepth_root, hden]
      simp [h, neg_mul, Finset.sum_neg_distrib, neg_div]
  refine ⟨?_, hprop⟩
  intro i j hij
  rcases hprop i j (1 : K) (by simpa using hij.symm) with h | h
  · exact h
  · have hcontra := LinearMap.congr_fun (hij.trans h) (D.coroot i)
    simp only [LinearMap.neg_apply, D.diagonal] at hcontra
    norm_num at hcontra

theorem foldedTranslationLattice : FoldedTranslationLattice.{u} := by
  classical
  intro K _ _ D hD hD'
  apply le_antisymm (corootLattice_le_coweightLattice D)
  intro x hx
  let axis (i : Fin 4) : FoldedRootDirection := ⟨Pi.single i 2, Or.inr (Or.inl ⟨i, true, rfl⟩)⟩
  let diag : FoldedRootDirection := ⟨fun _ => 1, Or.inr (Or.inr fun _ => Or.inl rfl)⟩
  have haxis (i : Fin 4) : D.coroot (axis i) = Pi.single i (1 : K) := by
    funext j
    rw [hD']
    change ((Pi.single i 2 : Fin 4 → ℤ) j : K) / 2 = (Pi.single i 1 : Fin 4 → K) j
    by_cases h : j = i <;> simp [h]
  have hdiag : D.coroot diag = fun _ => (1 : K) / 2 := by
    funext j
    simp [hD', normalizedFoldedCoroot, diag]
  have hshort : ¬IsLongF4Doubled (axis 0).val := by decide +kernel
  have h0 : D.root (axis 0) x = 2 * x 0 := by
    rw [hD, foldedDepth_root]
    simp [foldedDepthDenominator, hshort, axis, Pi.single_apply, ite_mul]
  obtain ⟨b, hb⟩ := hx (axis 0)
  have hd (i : Fin 4) : ∃ k : ℤ, x i - x 0 = (k : K) := by
    by_cases hi : i = 0
    · exact ⟨0, by simp [hi]⟩
    let δ : FoldedRootDirection := ⟨Pi.single i 2 + Pi.single 0 (-2),
      Or.inl ⟨i, 0, true, false, hi, rfl⟩⟩
    have hlong : IsLongF4Doubled δ.val := ⟨i, 0, true, false, hi, rfl⟩
    have hv : D.root δ x = x i - x 0 := by
      rw [hD, foldedDepth_root]
      simp [foldedDepthDenominator, hlong, δ, Pi.add_apply, Int.cast_add, add_mul,
        Finset.sum_add_distrib, Pi.single_apply, ite_mul] <;> ring
    simpa only [hv] using hx δ
  choose t ht using hd
  have h0' : (b : K) / 2 = x 0 := by rw [h0] at hb; linear_combination -hb / 2
  have hx' : x = b • D.coroot diag + ∑ i : Fin 4, t i • D.coroot (axis i) := by
    funext j
    simp only [hdiag, haxis, Pi.add_apply, zsmul_eq_mul, Finset.sum_apply, Pi.mul_apply,
      Pi.intCast_apply, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    rw [← mul_div_assoc, mul_one, h0', ← ht j]
    ring
  rw [hx']
  refine AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self diag)) _) ?_
  exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.zsmul_mem _
    (AddSubgroup.subset_closure (Set.mem_range_self (axis i))) _

theorem e6FoldedDatumInCocharacters : E6FoldedDatumInCocharacters.{u,v,w,z} := by
  classical
  intro ι X Y K _ _ _ _ _ _ _ _ _ P _ B e σ hdim hσ hC E τ
  obtain ⟨φ, hφ⟩ := cocharacterApartmentCoordinates (K := K) P B e hdim
  obtain ⟨hvalues, ρ, hρ, _⟩ := e6DiagramCoordinates (K := K) P B e σ hσ hC
  have hτ (y : K ⊗[ℤ] Y) (j : Fin 6) : φ (τ y) j = φ y (e6Partner j) := by
    change φ.toLinearMap (τ y) j = φ.toLinearMap y (e6Partner j)
    rw [hφ]
    exact hvalues y j
  let U := φ.symm.toLinearMap.comp (foldedApartmentMap K)
  have hU (x : Fin 4 → K) : φ (U x) = foldedApartment x := φ.apply_symm_apply (foldedApartment x)
  let F : (Fin 4 → K) →ₗ[K] diagramFixedSpace τ := U.codRestrict _ (fun x => by
    change τ (U x) - U x = 0
    apply sub_eq_zero.mpr
    apply φ.injective
    funext j
    rw [hτ, hU]
    exact foldedApartment_partner x j)
  have hF : Function.Bijective F := by
    refine ⟨?_, ?_⟩
    · intro x y h
      have hh := congrArg (fun x : diagramFixedSpace τ => φ x.val) h
      change φ (U x) = φ (U y) at hh
      rw [hU, hU] at hh
      simpa only [foldedApartmentCoordinates.1] using congrArg unfoldApartment hh
    · intro y
      have hy : τ y.val = y.val := sub_eq_zero.mp y.property
      have hy₀ : φ y.val 0 = φ y.val 5 := by
        have h := hτ y.val 0
        rw [hy] at h
        exact h
      have hy₂ : φ y.val 2 = φ y.val 4 := by
        have h := hτ y.val 2
        rw [hy] at h
        exact h
      refine ⟨unfoldApartment (φ y.val), Subtype.ext (φ.injective ?_)⟩
      change φ (U (unfoldApartment (φ y.val))) = φ y.val
      rw [hU]
      exact foldedApartmentCoordinates.2.1 _ hy₀ hy₂
  let f := LinearEquiv.ofBijective F hF
  have hf (x : Fin 4 → K) : φ (f x).val = foldedApartment x := hU x
  let d (i : ι) : FoldedRootDirection := ⟨foldedRoot (ρ i).val,
    (e6Folding.2.2.2 _).mpr ⟨(ρ i).val, (ρ i).property, rfl⟩⟩
  have hd : Function.Surjective d := by
    intro p
    obtain ⟨r, hr, hpr⟩ := (e6Folding.2.2.2 p.val).mp p.property
    obtain ⟨i, hi⟩ := ρ.surjective ⟨r, hr⟩
    exact ⟨i, Subtype.ext (by simpa only [d, hi] using hpr)⟩
  have hfixed (i : ι) : (ρ i).val = e6Diagram.mulVec (ρ i).val ↔ σ.indexEquiv i = i := by
    rw [← (hρ i).2.2]
    exact ⟨fun h => ρ.injective (Subtype.ext h.symm), fun h => by rw [h]⟩
  obtain ⟨D, hroot, hcoroot, hclosed⟩ := foldedApartmentRootSystem (K := K)
  have hprojected (i : ι) : (f (D.coroot (d i))).val = diagramAverage τ (E.coroot i) := by
    have hcoord (j : Fin 6) : φ (E.coroot i) j = (e6Cartan.mulVec (ρ i).val j : K) := by
      change φ.toLinearMap (E.coroot i) j = _
      rw [hφ]
      change RootData.extendFunctional K (P.root' (e j)) (1 ⊗ₜ[ℤ] P.coroot i) = _
      rw [RootData.extendFunctional_one_tmul, (hρ i).2.1, map_sum]
      simp [Matrix.mulVec, dotProduct, hC, mul_comm]
    apply φ.injective
    funext j
    rw [hf, hcoroot]
    change foldedApartment (fun k => (foldedRoot (ρ i).val k : K) / 2) j = _
    rw [foldedApartmentCoordinates.2.2.2, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply,
      e6Diagram_apply]
    simp only [diagramAverage, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, map_smul, map_add, Pi.smul_apply, Pi.add_apply, hτ, hcoord, Int.cast_add,
      smul_eq_mul]
    ring
  refine ⟨f, d, D, ?_, hd, ?_, ?_, ?_, hroot, hcoroot, hclosed, ?_, hprojected, ?_⟩
  · intro x
    rw [← hf]
    exact congrArg (fun m : (K ⊗[ℤ] Y) →ₗ[K] (Fin 6 → K) => m (f x).val) hφ.symm
  · intro i j
    rw [Subtype.ext_iff]
    change (foldedRoot (ρ i).val = foldedRoot (ρ j).val) ↔ _
    rw [e6Folding.2.2.1 _ _ (ρ i).property (ρ j).property, ← (hρ i).2.2]
    constructor
    · exact fun h => h.imp (fun a => ρ.injective (Subtype.ext a)) (fun a => ρ.injective (Subtype.ext a))
    · exact fun h => h.imp (fun a => congrArg (fun p => (ρ p).val) a)
        (fun a => congrArg (fun p => (ρ p).val) a)
  · intro i
    exact ((e6Folding.2.1 _ (ρ i).property).2.1).trans (hfixed i)
  · intro i hi
    have horth := (e6Folding.2.1 _ (ρ i).property).1 (fun h => hi ((hfixed i).mp h))
    rw [← (hρ i).2.2] at horth
    convert horth using 1
    change P.toLinearMap (P.root i) (P.coroot (σ.indexEquiv i)) = _
    have hleft (y : Y) : P.toLinearMap (P.root i) y = ∑ j, (ρ i).val j * P.root' (e j) y := by
      rw [(hρ i).1, map_sum, LinearMap.sum_apply]
      simp
    rw [hleft, (hρ (σ.indexEquiv i)).2.1]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    change (P.root' (e j)) (∑ k, (ρ (σ.indexEquiv i)).val k • P.coroot (e k)) = _
    simp [hC, mul_comm]
  · intro i x
    have hx : simpleRootValues P B e K (f x).val = foldedApartment x :=
      (congrArg (fun m : (K ⊗[ℤ] Y) →ₗ[K] (Fin 6 → K) => m (f x).val) hφ).symm.trans (hf x)
    rw [hroot, foldedDepth_root, rootValuesFromCoordinates P B e i (ρ i).val (hρ i).1, hx,
      foldedApartmentCoordinates.2.2.1]
    change _ = (foldedDepthDenominator (d i) : K) * _
    ring
  · let L : (Fin 4 → K) →ₗ[K] (K ⊗[ℤ] Y) := (diagramFixedSpace τ).subtype.comp f.toLinearMap
    change (D.corootLattice.map L.toAddMonoidHom : Set (K ⊗[ℤ] Y)) =
      (E.corootLattice.map (diagramAverage τ).toAddMonoidHom : Set (K ⊗[ℤ] Y))
    simp only [ApartmentRoots.corootLattice, AddMonoidHom.map_closure, ← Set.range_comp]
    congr 2
    ext x
    constructor
    · rintro ⟨r, rfl⟩
      obtain ⟨i, rfl⟩ := hd r
      exact ⟨i, (hprojected i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨d i, hprojected i⟩

theorem e6ProjectedCocharacters : E6ProjectedCocharacters.{u,v,w,z} := by
  classical
  intro ι X Y K _ _ _ _ _ _ _ _ _ P _ B e σ hdim hσ hC E p
  obtain ⟨φ, hφ⟩ := cocharacterApartmentCoordinates (K := K) P B e hdim
  obtain ⟨hvalues, _⟩ := e6DiagramCoordinates (K := K) P B e σ hσ hC
  obtain ⟨hP, _, hQ⟩ := cocharacterLatticeCoordinates (K := K) P B e e6Cartan hC
  let castCoord (t : Fin 6 → ℤ) (i : Fin 6) : K := (t i : K)
  let projectCoord (t : Fin 6 → ℤ) (i : Fin 6) : K := (e6Projection t i : K)
  have hProjection (x : K ⊗[ℤ] Y) (t : Fin 6 → ℤ) (ht : φ x = castCoord t) :
      φ (p x) = projectCoord t := by
    have hmove (i : Fin 6) : φ (diagramCocharacters σ x) i = φ x (e6Partner i) := by
      change φ.toLinearMap _ i = φ.toLinearMap _ _
      rw [hφ]
      exact hvalues x i
    funext i
    change φ (diagramAverage (diagramCocharacters σ) x) i = (e6Projection t i : K)
    simp only [diagramAverage, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, map_smul, map_add, Pi.smul_apply, Pi.add_apply, hmove, ht, smul_eq_mul]
    rw [e6Projection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, e6Diagram_apply]
    push_cast
    unfold castCoord
    ring
  have hcoord : φ '' (E.coweightLattice : Set (K ⊗[ℤ] Y)) = Set.range castCoord := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, ht⟩ := (hP x).mp hx
      exact ⟨t, ((LinearMap.congr_fun hφ x).trans ht).symm⟩
    · rintro ⟨t, rfl⟩
      obtain ⟨x, hx⟩ := φ.surjective (castCoord t)
      refine ⟨x, (hP x).mpr ⟨t, ?_⟩, hx⟩
      exact (LinearMap.congr_fun hφ x).symm.trans hx
  have hcoroot : φ '' (E.corootLattice : Set (K ⊗[ℤ] Y)) =
      Set.range (castCoord ∘ e6Cartan.mulVec) := by
    change Set.image φ.toLinearMap _ = _
    rw [hφ]
    exact hQ
  have project_image (A : Set (K ⊗[ℤ] Y)) (a : (Fin 6 → ℤ) → Fin 6 → ℤ)
      (ha : φ '' A = Set.range (castCoord ∘ a)) :
      φ '' (p '' A) = Set.range (projectCoord ∘ a) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hm : φ x ∈ Set.range (castCoord ∘ a) := ha ▸ Set.mem_image_of_mem φ hx
      obtain ⟨t, ht⟩ := hm
      exact ⟨t, (hProjection x (a t) ht.symm).symm⟩
    · rintro ⟨t, rfl⟩
      have hm : castCoord (a t) ∈ φ '' A := ha.symm ▸ Set.mem_range_self t
      obtain ⟨x, hx, ht⟩ := hm
      exact ⟨p x, ⟨x, hx, rfl⟩, hProjection x (a t) ht⟩
  have hProjQ := project_image _ e6Cartan.mulVec hcoroot
  have hProjP := project_image _ id hcoord
  have hfields : Set.range (projectCoord ∘ e6Cartan.mulVec) = Set.range (projectCoord ∘ id) := by
    let c (v : Fin 6 → ℚ) (i : Fin 6) : K := v i
    change Set.range (c ∘ e6Projection ∘ e6Cartan.mulVec) = Set.range (c ∘ e6Projection)
    calc
      _ = c '' Set.range (e6Projection ∘ e6Cartan.mulVec) := Set.range_comp _ _
      _ = c '' Set.range e6Projection := congrArg (Set.image c) e6ProjectedLattices
      _ = _ := (Set.range_comp _ _).symm
  exact (Set.image_injective.mpr φ.injective) (hProjQ.trans (hfields.trans hProjP.symm))

end E6FiniteCalculation

private theorem folded_reflection_action {ι X Y K : Type*}
    [AddCommGroup X] [AddCommGroup Y] [Field K] [CharZero K]
    (P : RootDatum (ι := ι) X Y) (σ : P.Equiv P)
    (d : ι → FoldedRootDirection)
    (D : ApartmentRoots K (diagramFixedSpace (diagramCocharacters (K := K) σ)) FoldedRootDirection)
    (hpartner : ∀ i, d (σ.indexEquiv i) = d i)
    (hlong : ∀ i, IsLongF4Doubled (d i).val ↔ σ.indexEquiv i = i)
    (horth : ∀ i, σ.indexEquiv i ≠ i → P.pairing i (σ.indexEquiv i) = 0)
    (heval : ∀ i x, D.root (d i) x =
      (foldedDepthDenominator (d i) : K) * (ApartmentRoots.split P K).root i x.val)
    (hcor : ∀ i, (D.coroot (d i)).val =
      diagramAverage (diagramCocharacters σ) ((ApartmentRoots.split P K).coroot i)) :
    let E := ApartmentRoots.split P K
    ∀ i x,
      (σ.indexEquiv i = i → (D.linearReflection (d i) x).val = E.linearReflection i x.val) ∧
      (σ.indexEquiv i ≠ i → (D.linearReflection (d i) x).val =
        E.linearReflection i (E.linearReflection (σ.indexEquiv i) x.val)) := by
  intro E i x
  have hτ : diagramCocharacters σ (E.coroot i) = E.coroot (σ.indexEquiv i) := by
    change diagramCocharacters σ (1 ⊗ₜ[ℤ] P.coroot i) = 1 ⊗ₜ[ℤ] P.coroot (σ.indexEquiv i)
    simp only [diagramCocharacters, LinearEquiv.baseChange_tmul]
    congr 1
    apply σ.coweightEquiv.injective
    simp [RootPairing.Equiv.coweightEquiv_apply, RootPairing.Hom.coroot_coweightMap_apply]
  have hc : (D.coroot (d i)).val = (2 : K)⁻¹ • (E.coroot i + E.coroot (σ.indexEquiv i)) := by
    rw [hcor]
    change (2 : K)⁻¹ • (E.coroot i + diagramCocharacters σ (E.coroot i)) = _
    rw [hτ]
  constructor
  · intro hfix
    change x.val - D.root (d i) x • (D.coroot (d i)).val = x.val - E.root i x.val • E.coroot i
    have hc' : (D.coroot (d i)).val = E.coroot i := by
      rw [hc, hfix, ← two_smul K (E.coroot i), smul_smul,
        inv_mul_cancel₀ (two_ne_zero : (2 : K) ≠ 0), one_smul]
    rw [heval, foldedDepthDenominator, ite_eq_left ((hlong i).2 hfix), Nat.cast_one, one_mul, hc']
  · intro hfix
    have hshort : ¬IsLongF4Doubled (d i).val := fun h => hfix ((hlong i).1 h)
    have hd : (foldedDepthDenominator (d i) : K) = 2 := by simp [foldedDepthDenominator, hshort]
    have he : E.root (σ.indexEquiv i) x.val = E.root i x.val := by
      have he := heval (σ.indexEquiv i) x
      rw [hpartner, heval, hd] at he
      exact (mul_left_cancel₀ two_ne_zero he).symm
    have hz : E.root i (E.coroot (σ.indexEquiv i)) = 0 := by
      change RootData.extendFunctional K (P.root' i) (1 ⊗ₜ[ℤ] P.coroot (σ.indexEquiv i)) = 0
      simp [horth i hfix]
    change x.val - D.root (d i) x • (D.coroot (d i)).val =
      x.val - E.root (σ.indexEquiv i) x.val • E.coroot (σ.indexEquiv i) -
        E.root i (x.val - E.root (σ.indexEquiv i) x.val • E.coroot (σ.indexEquiv i)) • E.coroot i
    rw [map_sub, map_smul, hz, smul_zero, sub_zero, heval, hd, hc, he, smul_smul,
      mul_comm (2 : K), mul_assoc, mul_inv_cancel₀ two_ne_zero, mul_one, smul_add]
    abel

theorem foldedPinnedAlcoveGeometry : FoldedPinnedAlcoveGeometry.{u,v,w,z} := by
  intro ι X Y K _ _ _ _ _ _ _ _ _ _ _ _ P _ B e σ hr hσ hC E τ A
  obtain ⟨f, d, D₀, hf, hd, hfibre, hlong, horth, hroot₀, hcoroot₀, hR₀, heval₀, hcor₀, hlattice₀⟩ :=
    e6FoldedDatumInCocharacters (K := K) P B e σ hr hσ hC
  let D := D₀.transport f
  have heval (i : ι) (y : A) : D.root (d i) y = (foldedDepthDenominator (d i) : K) * E.root i y.val := by
    obtain ⟨v, rfl⟩ := f.surjective y
    exact (transported_root D₀ f (d i) v).trans (heval₀ i v)
  have hdpos (i : FoldedRootDirection) : 0 < foldedDepthDenominator i := by
    unfold foldedDepthDenominator
    split <;> decide
  have hdbound (i : FoldedRootDirection) : foldedDepthDenominator i ≤ 2 := by
    unfold foldedDepthDenominator
    split <;> decide
  have hwall (i : ι) (n : ℤ) (y : A) :
      let a := E.root i y.val + (n : K) / (foldedDepthDenominator (d i) : K)
      (a = 0 ↔ D.wallValue (d i, n) y = 0) ∧ (0 < a ↔ D.positive y (d i, n)) := by
    dsimp only
    change _ ∧ (0 < E.root i y.val + (n : K) / (foldedDepthDenominator (d i) : K) ↔
      0 < D.root (d i) y + (n : K))
    have hw := normalizeWall (E.root i y.val) (foldedDepthDenominator (d i)) (hdpos _) n
    simpa only [ApartmentRoots.wallValue, AffineArrangement.Datum.value, heval] using hw
  obtain ⟨x, c, _, hx, hs⟩ := pinnedAlcovePoint (K := K) P B e hr
  obtain ⟨φ, hφ⟩ := cocharacterApartmentCoordinates (K := K) P B e hr
  let p := f (unfoldApartment (fun _ => c))
  have hp : p.val = x := by
    apply φ.injective
    change φ.toLinearMap (f (unfoldApartment (fun _ => c))).val = φ.toLinearMap x
    rw [hφ, hf, (foldedApartmentCoordinates (K := K)).2.1 _ rfl rfl]
    exact (funext hx).symm
  have hsign (i : ι) : (0 < D.root (d i) p ↔ B.IsPos i) ∧
      0 < |D.root (d i) p| ∧ |D.root (d i) p| < 1 := by
    have hh : (0 : K) < (foldedDepthDenominator (d i) : K) := by exact_mod_cast hdpos (d i)
    have hb : (foldedDepthDenominator (d i) : K) ≤ 2 := by exact_mod_cast hdbound (d i)
    rw [heval, hp, mul_pos_iff_of_pos_left hh, abs_mul, abs_of_pos hh]
    obtain ⟨hpos, hn, hl⟩ := hs i
    refine ⟨hpos, mul_pos hh hn, ?_⟩
    calc
      _ ≤ 2 * |E.root i x| := mul_le_mul_of_nonneg_right hb hn.le
      _ < 1 := by linarith only [hl]
  let positive (j : FoldedRootDirection) : Prop := ∃ i, d i = j ∧ B.IsPos i
  have hpos (j : FoldedRootDirection) : 0 < D.root j p ↔ positive j :=
    ⟨fun h => by obtain ⟨i, rfl⟩ := hd j; exact ⟨i, rfl, (hsign i).1.mp h⟩,
      fun ⟨i, hi, h⟩ => hi ▸ (hsign i).1.mpr h⟩
  obtain ⟨hregular, hsigns⟩ := small_alcove_signs D p positive (fun j => by
    obtain ⟨i, rfl⟩ := hd j
    exact ⟨hpos _, (hsign i).2⟩)
  let : Finite FoldedRootDirection := Finite.of_surjective
    (fun j => (⟨foldedDirectionTable j, foldedTable_mem j⟩ : FoldedRootDirection))
    (fun j => (foldedTable_surjective j).imp fun _ hj => Subtype.ext hj)
  have hR := transported_reflectionClosed D₀ f hR₀
  have hD := transported_reducedDirections D₀ f (foldedReducedDirections D₀ hroot₀)
  have hgeom := affineApartmentGeometry D hR hD p hregular
  have heq : D.corootLattice = D.coweightLattice := by
    apply SetLike.coe_injective
    rw [← transported_corootLattice D₀ f, ← transported_coweightLattice D₀ f,
      foldedTranslationLattice D₀ hroot₀ hcoroot₀]
  have hlattice : A.subtype '' (D.corootLattice : Set A) =
      diagramAverage τ '' (E.corootLattice : Set (K ⊗[ℤ] Y)) := by
    rw [← transported_corootLattice D₀ f, Set.image_image]
    exact hlattice₀
  have hext : D.affineWeylGroup = D.extendedAffineWeylGroup := by
    ext g
    rw [affine_mem_iff D, extended_mem_iff D, heq]
  have hpartner (i : ι) : d (σ.indexEquiv i) = d i :=
    ((hfibre i (σ.indexEquiv i)).2 (Or.inr rfl)).symm
  refine ⟨d, D, p, hd, hfibre, hlong, horth, heval, hcor₀,
    folded_reflection_action P σ d D hpartner hlong horth heval hcor₀,
    hwall, fun i => (hsign i).1, hsigns, hgeom, hlattice, ?_, hext, ?_⟩
  · rw [← heq, hlattice]
    exact e6ProjectedCocharacters (K := K) P B e σ hr hσ hC
  · apply subsingleton_of_forall_eq (1 : alcoveStabilizer D (D.alcove p))
    intro g
    let w : D.affineWeylGroup := ⟨g.val.val, hext.symm ▸ g.val.property⟩
    have hw : w = 1 := (hgeom.simply_transitive p hregular).unique (y₁ := w) (y₂ := 1) g.property (by simp)
    have hv : g.val.val = (1 : A ≃ᵃ[K] A) := congrArg (fun w : D.affineWeylGroup => w.val) hw
    exact Subtype.ext (Subtype.ext hv)

end LinearAlgebraicGroups.Arithmetic.ExceptionalAffineRootSystems
