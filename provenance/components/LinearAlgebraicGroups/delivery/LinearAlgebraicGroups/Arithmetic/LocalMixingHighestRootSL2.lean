import Specs.LinearAlgebraicGroups.Arithmetic.LocalMixingHighestRootSL2
import LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
import LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalMixingHighestRootSL2

open _root_.LinearAlgebraicGroups.Specs
open Specs.Arithmetic.LocalMixingHighestRootSL2
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple
  IsPossiblyNonreducedRootSystem RealCharacters RealRootSpan realCharacter realRoot realRoots)
open LieAlgebrasAndRepresentations (rootReflection
  irreducible_iff_no_orthogonal_partition)

noncomputable section

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {R : Set E}

private theorem root_neg_mem (hR : IsPossiblyNonreducedRootSystem R) {x : E} (hx : x ∈ R) :
    -x ∈ R := by
  have hself : inner ℝ x x ≠ 0 := inner_self_ne_zero.mpr (hR.nonzero x hx)
  have h := hR.reflection_mem x hx x hx
  rw [rootReflection, mul_div_cancel_right₀ _ hself, two_smul] at h
  simpa using h

private theorem root_difference_of_inner_pos (hR : IsPossiblyNonreducedRootSystem R)
    {x y : E} (hx : x ∈ R) (hy : y ∈ R) (hne : x ≠ y) (hxy : 0 < inner ℝ x y) :
    x - y ∈ R := by
  obtain ⟨m, hm⟩ := hR.integral y hy x hx
  obtain ⟨n, hn⟩ := hR.integral x hx y hy
  have hxx : 0 < inner ℝ x x := real_inner_self_pos.mpr (hR.nonzero x hx)
  have hyy : 0 < inner ℝ y y := real_inner_self_pos.mpr (hR.nonzero y hy)
  have hyx : 0 < inner ℝ y x := by rwa [real_inner_comm]
  have hmpos : 0 < m := by exact_mod_cast (hm ▸ div_pos (by positivity) hyy)
  have hnpos : 0 < n := by exact_mod_cast (hn ▸ div_pos (by positivity) hxx)
  by_cases hm1 : m = 1
  · simpa only [rootReflection, hm, hm1, Int.cast_one, one_smul] using hR.reflection_mem y hy x hx
  by_cases hn1 : n = 1
  · have h : y - x ∈ R := by
      simpa only [rootReflection, hn, hn1, Int.cast_one, one_smul] using hR.reflection_mem x hx y hy
    simpa only [neg_sub] using root_neg_mem hR h
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show (2 : ℤ) ≤ m by omega)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (2 : ℤ) ≤ n by omega)
  have hm' := (div_eq_iff hyy.ne').mp hm
  have hn' := (div_eq_iff hxx.ne').mp hn
  have hsq : 0 < inner ℝ (x - y) (x - y) := real_inner_self_pos.mpr (sub_ne_zero.mpr hne)
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm y x] at hsq
  exfalso
  nlinarith [mul_nonneg (sub_nonneg.mpr hm2) hyy.le, mul_nonneg (sub_nonneg.mpr hn2) hxx.le,
    real_inner_comm y x]

private theorem root_difference_of_longest (hR : IsPossiblyNonreducedRootSystem R)
    {a b : E} (ha : a ∈ R) (hb : b ∈ R) (hne : b ≠ a)
    (hba : 0 < inner ℝ b a) (hl : ‖b‖ ≤ ‖a‖) :
    a - b ∈ R ∧ 0 < inner ℝ (a - b) a := by
  obtain ⟨m, hm⟩ := hR.integral a ha b hb
  have haa : 0 < inner ℝ a a := real_inner_self_pos.mpr (hR.nonzero a ha)
  have hmpos : 0 < m := by exact_mod_cast (hm ▸ div_pos (by positivity) haa)
  have hsq : 0 < inner ℝ (b - a) (b - a) := real_inner_self_pos.mpr (sub_ne_zero.mpr hne)
  simp only [inner_sub_left, inner_sub_right] at hsq
  have hbb : inner ℝ b b ≤ inner ℝ a a := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    gcongr
  have hlt : inner ℝ b a < inner ℝ a a := by linarith [real_inner_comm a b]
  have hmlt : m < 2 := by
    have h := (div_lt_iff₀ haa).mpr (show 2 * inner ℝ b a < 2 * inner ℝ a a by linarith)
    rw [hm] at h
    exact_mod_cast h
  have hm1 : m = 1 := by omega
  have hr : b - a ∈ R := by simpa only [rootReflection, hm, hm1, Int.cast_one, one_smul] using hR.reflection_mem a ha b hb
  refine ⟨by simpa only [neg_sub] using root_neg_mem hR hr, ?_⟩
  rwa [inner_sub_left, sub_pos]

/-- Every root has a nonzero pairing with some root outside the hyperplane
perpendicular to a fixed root in an irreducible reflection system. -/
private theorem root_neighbor_outside_hyperplane (hR : IsPossiblyNonreducedRootSystem R)
    (hI : LieAlgebrasAndRepresentations.IsIrreducible R) {a b : E} (ha : a ∈ R) (hb : b ∈ R) :
    ∃ y ∈ R, inner ℝ y a ≠ 0 ∧ inner ℝ b y ≠ 0 := by
  classical
  let B := {x ∈ R | ∀ y ∈ R, inner ℝ y a ≠ 0 → inner ℝ x y = 0}
  let A := R \ B
  by_contra! h
  have hbB : b ∈ B := ⟨hb, h⟩
  have hB : B ⊆ R := fun _ hx ↦ hx.1
  have haA : a ∈ A := ⟨ha, fun haB ↦
    inner_self_ne_zero.mpr (hR.nonzero a ha) (haB.2 a ha (inner_self_ne_zero.mpr (hR.nonzero a ha)))⟩
  have hcover : B ∪ A = R := Set.union_sdiff_cancel hB
  have horth : ∀ x ∈ B, ∀ z ∈ A, inner ℝ x z = 0 := by
    intro x hx z hz
    by_cases hza : inner ℝ z a = 0
    · obtain ⟨y, hy, hya, hzy⟩ : ∃ y ∈ R, inner ℝ y a ≠ 0 ∧ inner ℝ z y ≠ 0 := by
        by_contra! h'
        exact hz.2 ⟨hz.1, h'⟩
      have href := hR.reflection_mem z hz.1 y hy
      have hpair : inner ℝ (rootReflection z y) a = inner ℝ y a := by
        rw [rootReflection, inner_sub_left, real_inner_smul_left, hza, mul_zero, sub_zero]
      have hzero := hx.2 _ href (hpair.trans_ne hya)
      rw [rootReflection, inner_sub_right, real_inner_smul_right, hx.2 y hy hya, zero_sub,
        neg_eq_zero, mul_eq_zero] at hzero
      refine hzero.resolve_left (div_ne_zero (mul_ne_zero (by norm_num) ?_) ?_)
      · rwa [real_inner_comm]
      · exact inner_self_ne_zero.mpr (hR.nonzero z hz.1)
    · exact hx.2 z hz.1 hza
  rcases ((irreducible_iff_no_orthogonal_partition R hR.nonzero).mp hI).2 B A hcover horth with
    hempty | hempty
  · exact Set.notMem_empty b (hempty ▸ hbB)
  · exact Set.notMem_empty a (hempty ▸ haA)

private theorem root_acute_neighbor (hR : IsPossiblyNonreducedRootSystem R)
    (hI : LieAlgebrasAndRepresentations.IsIrreducible R) {a b : E} (ha : a ∈ R) (hb : b ∈ R) (hab : inner ℝ b a = 0) :
    ∃ y ∈ R, 0 < inner ℝ y a ∧ 0 < inner ℝ b y := by
  obtain ⟨z, hz, hza, hbz⟩ := root_neighbor_outside_hyperplane hR hI ha hb
  obtain ⟨y, hy, hya, hby⟩ : ∃ y ∈ R, 0 < inner ℝ y a ∧ inner ℝ b y ≠ 0 := by
    rcases lt_or_gt_of_ne hza with hn | hp
    · refine ⟨-z, root_neg_mem hR hz, ?_, ?_⟩
      · rwa [inner_neg_left, neg_pos]
      · rwa [inner_neg_right, neg_ne_zero]
    · exact ⟨z, hz, hp, hbz⟩
  rcases lt_or_gt_of_ne hby with hn | hp
  · refine ⟨rootReflection b y, hR.reflection_mem b hb y hy, ?_, ?_⟩
    · rwa [rootReflection, inner_sub_left, real_inner_smul_left, hab, mul_zero, sub_zero]
    · have hself : inner ℝ b b ≠ 0 := inner_self_ne_zero.mpr (hR.nonzero b hb)
      rw [rootReflection, inner_sub_right, real_inner_smul_right, div_mul_cancel₀ _ hself]
      linarith [real_inner_comm y b]
  · exact ⟨y, hy, hya, hp⟩

private theorem longest_root_difference (hR : IsPossiblyNonreducedRootSystem R)
    (hI : LieAlgebrasAndRepresentations.IsIrreducible R) {a b : E} (ha : a ∈ R) (hb : b ∈ R)
    (hl : ∀ z ∈ R, ‖z‖ ≤ ‖a‖) (hab : 0 ≤ inner ℝ b a) :
    b = a ∨ (a - b ∈ R ∧ 0 < inner ℝ (a - b) a) ∨
      ∃ x ∈ R, ∃ y ∈ R, 0 < inner ℝ x a ∧ 0 < inner ℝ y a ∧ a - b = x + y := by
  by_cases hba : b = a
  · exact Or.inl hba
  rcases hab.eq_or_lt with hz | hp
  · obtain ⟨c, hc, hca, hbc⟩ := root_acute_neighbor hR hI ha hb hz.symm
    have hne : c ≠ a := fun h ↦ by simp [h, hz.symm] at hbc
    have hcb : c ≠ b := fun h ↦ by simp [h, hz.symm] at hca
    obtain ⟨hd, hdpos⟩ := root_difference_of_longest hR ha hc hne hca (hl c hc)
    have he := root_difference_of_inner_pos hR hc hb hcb (by rwa [real_inner_comm])
    refine Or.inr (Or.inr ⟨a - c, hd, c - b, he, hdpos, ?_, by abel⟩)
    rwa [inner_sub_left, ← hz, sub_zero]
  · exact Or.inr (Or.inl (root_difference_of_longest hR ha hb hba hp (hl b hb)))

end Euclidean

section Relative

open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.Relative.RelativeChambers (IsRegular relativeRoots)
open Specs.Relative.RelativeReflections (Datum)
open Specs.Relative.RelativeWeylScheme (QuotientData)
open private exists_regular_cocharacter from LinearAlgebraicGroups.RootData.BorelsAndChambers

open private realCharacter_injective realRoots_eq_range realRoot_ne_zero relativeAction_root
  action_reflection relative_pairing_partition reductive_of_semisimple
  from LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F} {S : ClosedSubgroup G.val}

private def realCharacterHom (S : ClosedSubgroup G.val) :
    Character S.group →* Multiplicative (RealCharacters S) where
  toFun a := Multiplicative.ofAdd (realCharacter S a)
  map_one' := by
    change (1 : ℝ) ⊗ₜ[ℤ] (0 : Additive (Character S.group)) = 0
    simp only [TensorProduct.tmul_zero]
  map_mul' a b := by
    change (1 : ℝ) ⊗ₜ[ℤ] (Additive.ofMul a + Additive.ofMul b) = _
    exact TensorProduct.tmul_add (R := ℤ) (1 : ℝ) _ _

variable {D : QuotientData S} [IsCommMonObj S.group.X]

private theorem cartan_form_root_axioms (d : Datum D) (form : InnerProductSpace.Core ℝ (RealRootSpan S)) :
    letI := @InnerProductSpace.Core.toNormedAddCommGroup ℝ (RealRootSpan S) _ _ _ form
    letI := InnerProductSpace.ofCore form.toCore
    (∀ b a : relativeRoots S, 2 * inner ℝ (realRoot b) (realRoot a) / inner ℝ (realRoot a) (realRoot a) =
      (pairing S.group b.val (d.reflection a).coroot : ℝ)) →
    IsPossiblyNonreducedRootSystem (realRoots S) := by
  letI := @InnerProductSpace.Core.toNormedAddCommGroup ℝ (RealRootSpan S) _ _ _ form
  letI := InnerProductSpace.ofCore form.toCore
  intro h
  letI := d.freeCharacters
  letI := d.finiteRoots
  refine ⟨?_, ?_, ?_, ?_, Submodule.span_setOfPred_mem_eq_top⟩
  · rw [realRoots_eq_range]
    exact Set.finite_range _
  · rw [realRoots_eq_range]
    rintro _ ⟨a, rfl⟩
    exact realRoot_ne_zero a
  · rw [realRoots_eq_range]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    refine ⟨d.normalizerPerm (d.reflection a).label b, ?_⟩
    rw [← relativeAction_root d, action_reflection d, rootReflection, h]
  · rw [realRoots_eq_range]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨_, h b a⟩

private theorem cartan_form_irreducible
    (hG : IsAbsolutelyAlmostSimple G) (hS : IsMaximalSplitTorus S)
    (d : Datum D) (form : InnerProductSpace.Core ℝ (RealRootSpan S)) :
    letI := @InnerProductSpace.Core.toNormedAddCommGroup ℝ (RealRootSpan S) _ _ _ form
    letI := InnerProductSpace.ofCore form.toCore
    (∀ b a : relativeRoots S, 2 * inner ℝ (realRoot b) (realRoot a) / inner ℝ (realRoot a) (realRoot a) =
      (pairing S.group b.val (d.reflection a).coroot : ℝ)) →
    Nonempty (relativeRoots S) → LieAlgebrasAndRepresentations.IsIrreducible (realRoots S) := by
  letI := @InnerProductSpace.Core.toNormedAddCommGroup ℝ (RealRootSpan S) _ _ _ form
  letI := InnerProductSpace.ofCore form.toCore
  intro h ⟨a⟩
  have hR := cartan_form_root_axioms d form h
  have hreal : realRoots S = Set.range (realRoot (S := S)) := realRoots_eq_range
  apply (irreducible_iff_no_orthogonal_partition (realRoots S) hR.nonzero).mpr
  refine ⟨⟨realRoot a, hreal.symm ▸ Set.mem_range_self a⟩, ?_⟩
  intro A B hAB horth
  have hcover : realRoot ⁻¹' A ∪ realRoot ⁻¹' B = (Set.univ : Set (relativeRoots S)) := by
    apply Set.eq_univ_of_forall
    intro x
    change realRoot x ∈ A ∪ B
    rw [hAB, hreal]
    exact Set.mem_range_self x
  have hcross (x : relativeRoots S) (hx : realRoot x ∈ A)
      (y : relativeRoots S) (hy : realRoot y ∈ B) :
      pairing S.group y.val (d.reflection x).coroot = 0 ∧
      pairing S.group x.val (d.reflection y).coroot = 0 := by
    have hz := horth _ hx _ hy
    have hz' := (real_inner_comm (realRoot x) (realRoot y)).trans hz
    constructor
    · exact_mod_cast (show (pairing S.group y.val (d.reflection x).coroot : ℝ) = 0 by
        rw [← h, hz', mul_zero, zero_div])
    · exact_mod_cast (show (pairing S.group x.val (d.reflection y).coroot : ℝ) = 0 by
        rw [← h, hz, mul_zero, zero_div])
  have empty_of_preimage (X : Set (RealRootSpan S)) (hX : X ⊆ realRoots S)
      (he : realRoot ⁻¹' X = (∅ : Set (relativeRoots S))) : X = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨y, rfl⟩ := hreal ▸ hX hx
    exact Set.notMem_empty y (he ▸ (show y ∈ realRoot ⁻¹' X from hx))
  rcases relative_pairing_partition G hG (reductive_of_semisimple G hG.1) S hS d
    _ _ hcover hcross with he | he
  · exact Or.inl (empty_of_preimage A (hAB ▸ Set.subset_union_left) he)
  · exact Or.inr (empty_of_preimage B (hAB ▸ Set.subset_union_right) he)

private theorem exists_regular_perturbation (hS : IsMaximalSplitTorus S)
    (d : Datum D) (r : Cocharacter S.group) :
    ∃ c : Cocharacter S.group, IsRegular S c ∧
      (∀ b : relativeRoots S, 0 < pairing S.group b.val r → 0 < pairing S.group b.val c) ∧
      (∀ b : relativeRoots S, 0 < pairing S.group b.val c → 0 ≤ pairing S.group b.val r) := by
  classical
  obtain ⟨c₀, hc₀⟩ := exists_regular_cocharacter G S hS.1
  letI := d.finiteRoots
  letI := Fintype.ofFinite (relativeRoots S)
  let n : ℕ := Finset.univ.sup (fun b : relativeRoots S ↦ (pairing S.group b.val c₀).natAbs)
  let N : ℤ := (n : ℤ) + 1
  let c : Cocharacter S.group := (N • Additive.ofMul r + Additive.ofMul c₀).toMul
  have hpair (b : relativeRoots S) :
      pairing S.group b.val c = N * pairing S.group b.val r + pairing S.group b.val c₀ := by
    rw [← d.pairing_eq, ← d.pairing_eq b.val r, ← d.pairing_eq b.val c₀]
    change d.rootDatum.toLinearMap (Additive.ofMul b.val)
      (N • Additive.ofMul r + Additive.ofMul c₀) = _
    simp only [map_add, map_zsmul, zsmul_eq_mul, Int.cast_id]
  have hbound (b : relativeRoots S) : (pairing S.group b.val c₀).natAbs ≤ n :=
    Finset.le_sup (f := fun x : relativeRoots S ↦ (pairing S.group x.val c₀).natAbs)
      (Finset.mem_univ b)
  have hp (b : relativeRoots S) (hb : 0 < pairing S.group b.val r) :
      0 < pairing S.group b.val c := by
    rw [hpair]
    have h₁ : 1 ≤ pairing S.group b.val r := by omega
    have h₂ : 0 ≤ N := by dsimp [N]; positivity
    have h₃ := mul_le_mul_of_nonneg_left h₁ h₂
    have hb' := hbound b
    dsimp [N] at *
    omega
  have hn (b : relativeRoots S) (hb : pairing S.group b.val r < 0) :
      pairing S.group b.val c < 0 := by
    rw [hpair]
    have h₁ : pairing S.group b.val r ≤ -1 := by omega
    have h₂ : 0 ≤ N := by dsimp [N]; positivity
    have h₃ := mul_le_mul_of_nonneg_left h₁ h₂
    have hb' := hbound b
    dsimp [N] at *
    omega
  refine ⟨c, ?_, hp, fun b hb ↦ le_of_not_gt (fun h ↦ (not_lt_of_gt hb) (hn b h))⟩
  intro b
  rcases lt_trichotomy (pairing S.group b.val r) 0 with hb | hb | hb
  · exact (hn b hb).ne
  · simpa only [hpair, hb, mul_zero, zero_add] using hc₀ b
  · exact (hp b hb).ne'

omit [IsCommMonObj S.group.X] in
private theorem longest_is_highest_for_some_cocharacter
    (hG : IsAbsolutelyAlmostSimple G) (hS : IsMaximalSplitTorus S)
    (a : relativeRoots S) (ha : IsLongest S a) :
    ∃ c : Cocharacter S.group, IsRegular S c ∧ IsHighest S c a := by
  classical
  obtain ⟨D, comm, d, form, hcartan, hlong⟩ := ha
  letI := comm
  letI := @InnerProductSpace.Core.toNormedAddCommGroup ℝ (RealRootSpan S) _ _ _ form
  letI := InnerProductSpace.ofCore form.toCore
  letI := d.freeCharacters
  have hR := cartan_form_root_axioms d form hcartan
  have hI := cartan_form_irreducible hG hS d form hcartan ⟨a⟩
  let r := (d.reflection a).coroot
  obtain ⟨c, hc, hp, hn⟩ := exists_regular_perturbation hS d r
  let positive := {b ∈ relativeRoots S | 0 < pairing S.group b c}
  have hreal : realRoots S = Set.range (realRoot (S := S)) := realRoots_eq_range
  have hroot (b : relativeRoots S) : realRoot b ∈ realRoots S :=
    hreal.symm ▸ Set.mem_range_self b
  have ha₀ := real_inner_self_pos.mpr (realRoot_ne_zero a)
  have hsign (b : relativeRoots S) :
      (0 < pairing S.group b.val r ↔ 0 < inner ℝ (realRoot b) (realRoot a)) ∧
      (0 ≤ pairing S.group b.val r ↔ 0 ≤ inner ℝ (realRoot b) (realRoot a)) := by
    constructor
    · rw [← Int.cast_pos (R := ℝ), ← hcartan]
      simp only [div_pos_iff_of_pos_right ha₀, mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]
    · rw [← Int.cast_nonneg_iff (R := ℝ), ← hcartan]
      rw [div_nonneg_iff]
      simp only [ha₀.le, not_le.mpr ha₀, and_true, and_false, or_false,
        mul_nonneg_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)]
  have hpositive (b : relativeRoots S) (hb : 0 < inner ℝ (realRoot b) (realRoot a)) :
      b.val ∈ positive := ⟨b.property, hp b ((hsign b).1.mpr hb)⟩
  refine ⟨c, hc, hpositive a ha₀, ?_⟩
  intro b hb
  let b' : relativeRoots S := ⟨b, hb.1⟩
  have hba := (hsign b').2.mp (hn b' hb.2)
  have hnorm (z : RealRootSpan S) (hz : z ∈ realRoots S) : ‖z‖ ≤ ‖realRoot a‖ := by
    obtain ⟨x, rfl⟩ := hreal ▸ hz
    exact hlong x
  have hinj : Function.Injective (realCharacterHom S) := realCharacter_injective
  rcases longest_root_difference hR hI (hroot a) (hroot b') hnorm hba with he | ⟨he, hpos⟩ |
    ⟨x, hx, y, hy, hxp, hyp, he⟩
  · have he' : b = a.val := congrArg Subtype.val (Subtype.ext (hinj (congrArg Subtype.val he)))
    rw [he', mul_inv_cancel]
    exact Submonoid.one_mem _
  · obtain ⟨x, hx⟩ := hreal ▸ he
    have heq : a.val * b⁻¹ = x.val := by
      apply hinj
      rw [map_mul, map_inv]
      exact congrArg Subtype.val hx.symm
    rw [heq]
    exact Submonoid.subset_closure (hpositive x (hx.symm ▸ hpos))
  · obtain ⟨x', rfl⟩ := hreal ▸ hx
    obtain ⟨y', rfl⟩ := hreal ▸ hy
    have heq : a.val * b⁻¹ = x'.val * y'.val := by
      apply hinj
      rw [map_mul, map_mul, map_inv]
      exact congrArg Subtype.val he
    rw [heq]
    exact Submonoid.mul_mem _ (Submonoid.subset_closure (hpositive x' hxp))
      (Submonoid.subset_closure (hpositive y' hyp))

end Relative

section Parabolic

open Specs.BorelProper (IsParabolic)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.GeometricRadicals (IsReductive IsSplitTorus)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.Relative.RelativeChambers (IsRegular nonnegativeRoots relativeRoots)
open Specs.Relative.RelativeReflections (Datum)
open Specs.Relative.RelativeWeylScheme (QuotientData)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Arithmetic.TrialitarianFixedRootSL2 (RankOne)
open CocharacterDynamics (LimitDecomposition existsLimitDecomposition)

open private connected_of_geometricallyConnected pairing_inv from
  LinearAlgebraicGroups.RootData.BorelsAndChambers
open private limitParabolics_le isIso_of_section from
  LinearAlgebraicGroups.Relative.RelativeChambers
open private limitProperOfNegative limitIsIsoOfNonnegative from
  LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots
open private subgroupOf_trans from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy

variable {F : Type u} [Field F] {G : AffineAlgebraicGroup F} {S : ClosedSubgroup G.val}

private def pairingHom (hS : IsSplitTorus S.group) (c : Cocharacter S.group) :
    Character S.group →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (pairing S.group a c)
  map_one' := by
    obtain ⟨comm, _, _, _, _, P, _, hP⟩ :=
      RootData.CharacterPairing.perfectCharacterPairing S.group hS
    letI := comm
    rw [← hP]
    change P 0 (Additive.ofMul c) = 0
    rw [map_zero, LinearMap.zero_apply]
  map_mul' a b := by
    obtain ⟨comm, _, _, _, _, P, _, hP⟩ :=
      RootData.CharacterPairing.perfectCharacterPairing S.group hS
    letI := comm
    change pairing S.group (a * b) c = pairing S.group a c + pairing S.group b c
    rw [← hP, ← hP a, ← hP b]
    change P (Additive.ofMul a + Additive.ofMul b) (Additive.ofMul c) = _
    rw [map_add, LinearMap.add_apply]

private theorem highest_pairing_ge (hS : IsSplitTorus S.group)
    {c : Cocharacter S.group} {θ : relativeRoots S} (hθ : IsHighest S c θ)
    (d : Cocharacter S.group)
    (hd : ∀ x : relativeRoots S, 0 < pairing S.group x.val c → 0 ≤ pairing S.group x.val d)
    (b : relativeRoots S) (hb : 0 < pairing S.group b.val c) :
    pairing S.group b.val d ≤ pairing S.group θ.val d := by
  let P := pairingHom hS d
  let positive := {a ∈ relativeRoots S | 0 < pairing S.group a c}
  have h (x : Character S.group) (hx : x ∈ Submonoid.closure positive) :
      0 ≤ (P x).toAdd := by
    induction hx using Submonoid.closure_induction with
    | mem x hx => exact hd ⟨x, hx.1⟩ hx.2
    | one => rw [map_one]; exact le_rfl
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact add_nonneg hx hy
  have hb' := h (θ.val * b.val⁻¹) (hθ.2 b.val ⟨b.property, hb⟩)
  rw [map_mul, map_inv] at hb'
  change 0 ≤ pairing S.group θ.val d + -pairing S.group b.val d at hb'
  omega

private theorem relative_inverse_mem (hG : IsReductive G) (hS : IsMaximalSplitTorus S)
    (b : relativeRoots S) : b.val⁻¹ ∈ relativeRoots S := by
  obtain ⟨D, _⟩ := LinearAlgebraicGroups.Relative.RelativeWeylScheme.finiteConstantQuotient G hG S hS
  obtain ⟨comm, ⟨d⟩⟩ :=
    LinearAlgebraicGroups.Relative.RelativeReflections.relativeRootDatum G hG S hS D
  letI := comm
  let b' := d.normalizerPerm (d.reflection b).label b
  have hb' : b'.val = b.val⁻¹ := by
    change (d.normalizerPerm (d.reflection b).label b).val = _
    rw [d.rootAction, (d.reflection b).characterFormula, (d.reflection b).rootPairing]
    group
  rw [← hb']
  exact b'.property

private theorem positive_of_nonnegative_inclusion (hG : IsReductive G) (hS : IsMaximalSplitTorus S)
    {c d : Cocharacter S.group}
    (hcd : nonnegativeRoots S c ⊆ nonnegativeRoots S d)
    (b : relativeRoots S) (hb : 0 < pairing S.group b.val d) :
    0 < pairing S.group b.val c := by
  change ∀ ⦃a : relativeRoots S⦄, 0 ≤ pairing S.group a.val c →
    0 ≤ pairing S.group a.val d at hcd
  by_contra h
  have hc' : pairing S.group b.val c ≤ 0 := le_of_not_gt h
  let b' : relativeRoots S := ⟨b.val⁻¹, relative_inverse_mem hG hS b⟩
  have hc'' : 0 ≤ pairing S.group b'.val c := by
    change 0 ≤ pairing S.group b.val⁻¹ c
    rw [pairing_inv _ hS.1]
    exact neg_nonneg.mpr hc'
  have hd' := hcd (a := b') hc''
  change 0 ≤ pairing S.group b.val⁻¹ d at hd'
  rw [pairing_inv _ hS.1] at hd'
  omega

private theorem exists_maximal_limit_parabolic (hG : IsReductive G) (hS : IsMaximalSplitTorus S)
    {c : Cocharacter S.group} {θ : relativeRoots S} (hθ : IsHighest S c θ)
    (C : LimitDecomposition (c ≫ S.inclusion)) :
    ∃ (d : Cocharacter S.group) (D : LimitDecomposition (d ≫ S.inclusion)),
      IsParabolic G D.parabolic ∧ IsSubgroupOf C.parabolic D.parabolic ∧
      ¬ IsIso D.parabolic.inclusion ∧
      (∀ Q : ClosedSubgroup G.val, IsParabolic G Q → IsSubgroupOf D.parabolic Q →
        IsSubgroupOf Q D.parabolic ∨ IsIso Q.inclusion) ∧
      0 < pairing S.group θ.val d ∧
      ∀ b : relativeRoots S, 0 < pairing S.group b.val d → 0 < pairing S.group b.val c := by
  classical
  letI := hG.1
  letI : ConnectedSpace G.val.X.left := connected_of_geometricallyConnected hG.2.1
  letI : Finite (relativeRoots S) :=
    LinearAlgebraicGroups.Relative.RelativeChambers.relativeRootsFinite G S hS.1
  let feasible : Set (Σ d : Cocharacter S.group, LimitDecomposition (d ≫ S.inclusion)) :=
    {D | IsSubgroupOf C.parabolic D.2.parabolic ∧ ¬ IsIso D.2.parabolic.inclusion}
  let signs (D : Σ d : Cocharacter S.group, LimitDecomposition (d ≫ S.inclusion)) :=
    nonnegativeRoots S D.1
  let θ' : relativeRoots S := ⟨θ.val⁻¹, relative_inverse_mem hG hS θ⟩
  have hproper : ¬ IsIso C.parabolic.inclusion := by
    apply limitProperOfNegative G S c C θ'
    change pairing S.group θ.val⁻¹ c < 0
    rw [pairing_inv _ hS.1, neg_neg_iff_pos]
    exact hθ.1.2
  let candidates := signs '' feasible
  have hC : (⟨c, C⟩ : Σ d : Cocharacter S.group, LimitDecomposition (d ≫ S.inclusion)) ∈ feasible :=
    ⟨⟨𝟙 _, Category.id_comp _⟩, hproper⟩
  obtain ⟨M, hM⟩ := (Set.toFinite candidates).exists_maximal
    (Set.Nonempty.image signs ⟨⟨c, C⟩, hC⟩)
  obtain ⟨⟨d, D⟩, hD, hDM⟩ := hM.1
  have hcd := (limitParabolics_le G S hS.1 c d C D).mp hD.1
  have hpar := LinearAlgebraicGroups.Relative.RelativeChambers.limitParabolicThroughSplitTorus
    G hG S hS.1 d D
  refine ⟨d, D, hpar.1, hD.1, hD.2, ?_, ?_, positive_of_nonnegative_inclusion hG hS hcd⟩
  · intro Q hQ hDQ
    by_cases hQi : IsIso Q.inclusion
    · exact Or.inr hQi
    obtain ⟨q, E, hE⟩ := LinearAlgebraicGroups.Relative.RelativeChambers.parabolicThroughSplitTorus
      G S hS Q hQ (subgroupOf_trans hpar.2 hDQ)
    have hEi : ¬ IsIso E.parabolic.inclusion := by
      intro h
      obtain ⟨i, hi⟩ := hE.2
      exact hQi (isIso_of_section Q (inv E.parabolic.inclusion ≫ i)
        (by rw [Category.assoc, hi, IsIso.inv_hom_id]))
    have hdE := subgroupOf_trans hDQ hE.1
    have hsub := (limitParabolics_le G S hS.1 d q D E).mp hdE
    let j : Σ d : Cocharacter S.group, LimitDecomposition (d ≫ S.inclusion) := ⟨q, E⟩
    have hj : j ∈ feasible := ⟨subgroupOf_trans hD.1 hdE, hEi⟩
    have hjM : M ⊆ signs j := by
      rw [← hDM]
      exact hsub
    have hmax : nonnegativeRoots S q ⊆ nonnegativeRoots S d := by
      have hmem : signs j ∈ candidates := ⟨j, hj, rfl⟩
      have hjle := hM.2 hmem hjM
      rwa [← hDM] at hjle
    exact Or.inl (subgroupOf_trans hE.1 ((limitParabolics_le G S hS.1 q d E D).mpr hmax))
  · have hex : ∃ b : relativeRoots S, pairing S.group b.val d < 0 := by
      by_contra h
      apply hD.2 (limitIsIsoOfNonnegative G hG S hS.1 d D _)
      exact fun b ↦ le_of_not_gt (fun hb ↦ h ⟨b, hb⟩)
    obtain ⟨b, hb⟩ := hex
    let a : relativeRoots S := ⟨b.val⁻¹, relative_inverse_mem hG hS b⟩
    have ha : 0 < pairing S.group a.val d := by
      change 0 < pairing S.group b.val⁻¹ d
      rw [pairing_inv _ hS.1]
      omega
    have hap := positive_of_nonnegative_inclusion hG hS hcd a ha
    exact ha.trans_le (highest_pairing_ge hS.1 hθ d (fun x hx ↦ hcd hx.le) a hap)

end Parabolic

section ContractingWeights

open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (positiveRoots)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (characterValue pairing)
open Specs.OrderedRootProducts (Parametrizes RootSubgroupFamily)
open Specs.RootGroups (rootPoint)
open CocharacterDynamics (LimitDecomposition cocharacterPoint)
open private bivariateEvaluation bivariateEvaluation_X_zero bivariateEvaluation_X_one
  substitute substitute_X coeff_substitute fin_cases_one laurentParameter_zpow
  pointMap changeRing coordMap RootCoordinates coordinatesType mapCoordinates
  zeroCoordinates evalCoordinates evalCoordinates_zero evalCoordinates_natural
  evalCoordinates_scalar evalCoordinates_injective evalCoordinates_range
  from LinearAlgebraicGroups.Classification.RankOneRelations

variable {k : Type u} [Field k] {J : AffineAlgebraicGroup k} {T : ClosedSubgroup J.val}

private abbrev Bivariate (k : Type u) [CommRing k] := MvPolynomial (Fin 2) k

private def scales (m n : ℤ) : Fin 2 → LaurentPolynomial k :=
  Fin.cases (LaurentPolynomial.T m) (fun _ : Fin 1 ↦ LaurentPolynomial.T n)

private theorem bivariate_eq_zero_of_degree
    (m n w : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n) (hw : w < m + n)
    (p : Bivariate k)
    (hx : substitute (k := k) (Fin.cases (0 : k) (fun _ : Fin 1 ↦ 1)) p = 0)
    (hy : substitute (k := k) (Fin.cases (1 : k) (fun _ : Fin 1 ↦ 0)) p = 0)
    (he : substitute (scales (k := k) m n) p =
      MvPolynomial.C (LaurentPolynomial.T w) *
        substitute (fun _ : Fin 2 ↦ (1 : LaurentPolynomial k)) p) :
    p = 0 := by
  classical
  ext d
  simp only [AddMonoidAlgebra.coeff_zero]
  by_contra hne
  have hi : 0 < d 0 := by
    by_contra! h
    have e := congrArg (fun q : Bivariate k ↦ q.coeff d) hx
    rw [coeff_substitute] at e
    exact hne (by simpa [show d 0 = 0 by omega, fin_cases_one] using e)
  have hj : 0 < d 1 := by
    by_contra! h
    have e := congrArg (fun q : Bivariate k ↦ q.coeff d) hy
    rw [coeff_substitute] at e
    exact hne (by simpa [show d 1 = 0 by omega, fin_cases_one] using e)
  have hc := congrArg (fun q : Bivariate (LaurentPolynomial k) ↦ q.coeff d) he
  simp only [scales, coeff_substitute, MvPolynomial.coeff_C_mul, Fin.cases_zero, fin_cases_one,
    one_pow, mul_one, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add] at hc
  rw [mul_comm (LaurentPolynomial.T _) (algebraMap k (LaurentPolynomial k) _)] at hc
  have hne' : algebraMap k (LaurentPolynomial k) (p.coeff d) ≠ 0 :=
    fun h ↦ hne ((algebraMap k (LaurentPolynomial k)).injective (h.trans (map_zero _).symm))
  have hT := mul_left_cancel₀ hne' hc
  have hlarge : w < m * (d 0 : ℤ) + n * (d 1 : ℤ) := by
    have h₀ := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ d 0 by omega) hm
    have h₁ := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ d 1 by omega) hn
    simp only [mul_one] at h₀ h₁
    omega
  have hdeg := congrArg LaurentPolynomial.degree hT
  rw [LaurentPolynomial.degree_T, LaurentPolynomial.degree_T] at hdeg
  apply hlarge.ne'
  simpa only [mul_comm (m : ℤ), mul_comm (n : ℤ)] using WithBot.coe_injective hdeg

private theorem coordinates_eq_zero_of_degree (c : Cocharacter T.group)
    (m n : ℤ) (hm : 0 ≤ m) (hn : 0 ≤ n) (l : List (AbstractPairing.Root T))
    (hbound : ∀ a ∈ l, pairing T.group a.val c < m + n)
    (q : coordinatesType (Bivariate k) l)
    (hx : mapCoordinates (fun _ ↦ substitute (k := k) (Fin.cases (0 : k) (fun _ : Fin 1 ↦ 1))) l q =
      zeroCoordinates (Bivariate k) l)
    (hy : mapCoordinates (fun _ ↦ substitute (k := k) (Fin.cases (1 : k) (fun _ : Fin 1 ↦ 0))) l q =
      zeroCoordinates (Bivariate k) l)
    (he : mapCoordinates (fun _ ↦ substitute (scales (k := k) m n)) l q =
      mapCoordinates (fun a p ↦ MvPolynomial.C (LaurentPolynomial.T (pairing T.group a.val c)) *
        substitute (fun _ : Fin 2 ↦ (1 : LaurentPolynomial k)) p) l q) :
    q = zeroCoordinates (Bivariate k) l := by
  induction l with
  | nil => exact Subsingleton.elim _ _
  | cons a l ih =>
    apply Prod.ext
    · exact bivariate_eq_zero_of_degree m n _ hm hn (hbound a List.mem_cons_self) _
        (congrArg Prod.fst hx) (congrArg Prod.fst hy) (congrArg Prod.fst he)
    · exact ih (fun b hb ↦ hbound b (List.mem_cons_of_mem _ hb)) q.2
        (congrArg Prod.snd hx) (congrArg Prod.snd hy) (congrArg Prod.snd he)

/-- A polynomial line whose points lie in a contracting subgroup and whose
parameter scales by a specified power under the defining cocharacter. -/
private structure ContractingLine (c : Cocharacter T.group)
    (C : LimitDecomposition (c ≫ T.inclusion)) (m : ℤ) where
  point : (R : TestAlgebra k) → R → GroupPoints J.val R
  zero : ∀ R, point R 0 = 1
  natural : ∀ {R Q : TestAlgebra k} (f : R ⟶ Q) (r : R),
    changeRing f (point R r) = point Q (f.hom r)
  factors : ∀ R r, ∃ p : GroupPoints C.contracting.group R,
    pointMap R C.contracting.inclusion p = point R r
  scale : ∀ (R : TestAlgebra k) (t : Rˣ) (r : R),
    let g := pointMap R T.inclusion (cocharacterPoint c R t)
    g * point R r * g⁻¹ = point R ((↑(t ^ m) : R) * r)

private theorem map_zeroCoordinates {I : Type u} {A B : Type u} [Zero A] [Zero B]
    (f : A → B) (hf : f 0 = 0) (l : List I) :
    mapCoordinates (fun _ ↦ f) l (zeroCoordinates A l) = zeroCoordinates B l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact Prod.ext hf ih

private theorem contractingLines_commute {c : Cocharacter T.group}
    {C : LimitDecomposition (c ≫ T.inclusion)} {U : RootSubgroupFamily T}
    (X : RootCoordinates U) {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n)
    (x : ContractingLine c C m) (y : ContractingLine c C n)
    (l : List (AbstractPairing.Root T))
    (hprod : Parametrizes U l C.contracting.inclusion.hom.hom)
    (hbound : ∀ a ∈ l, pairing T.group a.val c < m + n) :
    ∀ R u v, Commute (x.point R u) (y.point R v) := by
  classical
  let commutator (R : TestAlgebra k) (u v : R) : GroupPoints J.val R :=
    x.point R u * y.point R v * (x.point R u)⁻¹ * (y.point R v)⁻¹
  let R₀ := CommAlgCat.of k (Bivariate k)
  let u₀ : R₀ := MvPolynomial.X 0
  let v₀ : R₀ := MvPolynomial.X 1
  obtain ⟨p, hp⟩ := x.factors R₀ u₀
  obtain ⟨p', hp'⟩ := y.factors R₀ v₀
  obtain ⟨q, hq⟩ := evalCoordinates_range X hprod R₀ (p * p' * p⁻¹ * p'⁻¹)
  have e₀ : evalCoordinates X R₀ l q = commutator R₀ u₀ v₀ := by
    simpa only [map_mul, map_inv, hp, hp', commutator] using hq
  have natural {R : TestAlgebra k} (f : R₀ ⟶ R) :
      evalCoordinates X R l (mapCoordinates (fun _ ↦ f.hom) l q) =
        commutator R (f.hom u₀) (f.hom v₀) := by
    rw [← evalCoordinates_natural, e₀]
    simp only [commutator, map_mul, map_inv, x.natural, y.natural]
  have axis (s : Fin 2 → k) (hs : s 0 = 0 ∨ s 1 = 0) :
      mapCoordinates (fun _ ↦ substitute (k := k) s) l q = zeroCoordinates (Bivariate k) l := by
    apply evalCoordinates_injective X hprod R₀
    rw [evalCoordinates_zero]
    have e := natural (CommAlgCat.ofHom (substitute (k := k) s))
    change evalCoordinates X R₀ l (mapCoordinates (fun _ ↦ substitute (k := k) s) l q) =
      commutator R₀ (substitute s u₀) (substitute s v₀) at e
    rw [e]
    simp only [u₀, v₀, substitute, MvPolynomial.aeval_X]
    rcases hs with h | h <;> simp [h, commutator, x.zero, y.zero]
  have weight :
      mapCoordinates (fun _ ↦ substitute (scales (k := k) m n)) l q =
        mapCoordinates (fun a p ↦ MvPolynomial.C (LaurentPolynomial.T (pairing T.group a.val c)) *
          substitute (fun _ : Fin 2 ↦ (1 : LaurentPolynomial k)) p) l q := by
    let A := LaurentPolynomial k
    let R := CommAlgCat.of k (Bivariate A)
    let τ : Rˣ := Units.map (MvPolynomial.C : A →+* Bivariate A).toMonoidHom
      (CocharacterDynamics.laurentParameter (CommAlgCat.of k k))
    let t := cocharacterPoint c R τ
    let g := pointMap R T.inclusion t
    let f₁ : R₀ ⟶ R := CommAlgCat.ofHom (substitute (fun _ : Fin 2 ↦ (1 : A)))
    let f₂ : R₀ ⟶ R := CommAlgCat.ofHom (substitute (scales (k := k) m n))
    have hτ (p : ℤ) : (↑(τ ^ p) : R) = MvPolynomial.C (LaurentPolynomial.T p) := by
      change (↑(Units.map (MvPolynomial.C : A →+* Bivariate A).toMonoidHom
        (CocharacterDynamics.laurentParameter (CommAlgCat.of k k)) ^ _) : Bivariate A) = _
      rw [← map_zpow, Units.coe_map, laurentParameter_zpow]
      rfl
    have hχ (a : AbstractPairing.Root T) :
        characterValue a.val R t = MvPolynomial.C (LaurentPolynomial.T (pairing T.group a.val c)) := by
      rw [(RootData.CharacterPairing.characterPairingComposition T.group a.val c).2 R τ]
      exact hτ _
    have he₀ : f₂.hom u₀ = (↑(τ ^ m) : R) * f₁.hom u₀ := by
      change substitute (scales (k := k) m n) (MvPolynomial.X 0) =
        _ * substitute (fun _ : Fin 2 ↦ (1 : A)) (MvPolynomial.X 0)
      rw [substitute_X, substitute_X, hτ]
      simp only [scales, Fin.cases_zero, map_one, one_mul]
    have he₁ : f₂.hom v₀ = (↑(τ ^ n) : R) * f₁.hom v₀ := by
      change substitute (scales (k := k) m n) (MvPolynomial.X 1) =
        _ * substitute (fun _ : Fin 2 ↦ (1 : A)) (MvPolynomial.X 1)
      rw [substitute_X, substitute_X, hτ]
      simp only [scales, fin_cases_one, map_one, one_mul]
    have hcomp (l' : List (AbstractPairing.Root T)) (z : coordinatesType R₀ l') :
        mapCoordinates (fun a b ↦ characterValue a.val R t * b) l'
            (mapCoordinates (fun _ ↦ f₁.hom) l' z) =
          mapCoordinates (fun a b ↦ MvPolynomial.C (LaurentPolynomial.T (pairing T.group a.val c)) *
            substitute (fun _ : Fin 2 ↦ (1 : A)) b) l' z := by
      induction l' with
      | nil => rfl
      | cons a l' ih =>
        exact Prod.ext (show characterValue a.val R t * f₁.hom z.1 = _ by rw [hχ]; rfl) (ih z.2)
    apply evalCoordinates_injective X hprod R
    change evalCoordinates X R l (mapCoordinates (fun _ ↦ f₂.hom) l q) = _
    rw [← hcomp l q, ← evalCoordinates_scalar X R l t, natural, natural, he₀, he₁]
    have hx := x.scale R τ (f₁.hom u₀)
    have hy := y.scale R τ (f₁.hom v₀)
    change commutator R _ _ = g * commutator R _ _ * g⁻¹
    dsimp only [commutator]
    change g * x.point R (f₁.hom u₀) * g⁻¹ = _ at hx
    change g * y.point R (f₁.hom v₀) * g⁻¹ = _ at hy
    rw [← hx, ← hy]
    group
  have qz := coordinates_eq_zero_of_degree c m n hm hn l hbound q
    (axis _ (Or.inl rfl)) (axis _ (Or.inr rfl)) weight
  intro R u v
  let f : R₀ ⟶ R := CommAlgCat.ofHom (bivariateEvaluation u v)
  have hf₀ : f.hom u₀ = u := bivariateEvaluation_X_zero (k := k) u v
  have hf₁ : f.hom v₀ = v := bivariateEvaluation_X_one (k := k) u v
  have h := natural f
  rw [hf₀, hf₁, qz] at h
  rw [map_zeroCoordinates f.hom (map_zero f.hom), evalCoordinates_zero] at h
  have h' := h.symm
  change x.point R u * y.point R v * (x.point R u)⁻¹ * (y.point R v)⁻¹ = 1 at h'
  change x.point R u * y.point R v = y.point R v * x.point R u
  calc
    x.point R u * y.point R v =
        (x.point R u * y.point R v * (x.point R u)⁻¹ * (y.point R v)⁻¹) *
          (y.point R v * x.point R u) := by group
    _ = y.point R v * x.point R u := by rw [h', one_mul]

private theorem commute_evalCoordinates {U : RootSubgroupFamily T} (X : RootCoordinates U)
    (R : TestAlgebra k) (x : GroupPoints J.val R) (l : List (AbstractPairing.Root T))
    (h : ∀ a ∈ l, ∀ r : R, Commute x (rootPoint (coordMap X a) R r)) :
    ∀ q : coordinatesType R l, Commute x (evalCoordinates X R l q) := by
  induction l with
  | nil => exact fun _ ↦ Commute.one_right x
  | cons a l ih =>
    intro q
    exact (h a List.mem_cons_self q.1).mul_right
      (ih (fun b hb ↦ h b (List.mem_cons_of_mem _ hb)) q.2)

end ContractingWeights

section ScalarExtension

open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (contractingSubgroup positiveRoots)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (absoluteRoots characterValue pairing)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.GeometricRadicals (IsReductive IsSplitTorus baseChangedSubgroup)
open Specs.OrderedRootProducts (RootSubgroupFamily)
open Specs.QuasiSplitOrbitLevis (MultiplicativeComparison PreservesUnits)
open Specs.Arithmetic.TrialitarianFixedRootSL2 (RankOne)
open Specs.Relative.RelativeChambers (relativeRoots)
open Specs.Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Specs.RootGroups (HasScalarAction rootPoint)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open CocharacterDynamics (LimitDecomposition cocharacterPoint existsLimitDecomposition unitPoint)
open private RootCoordinates coordMap pointMap changeRing changeRing_rootPoint rootPoint_zero
  RootCoordinates.mk RootCoordinates.action rootPoint_contraction evalCoordinates evalCoordinates_range from LinearAlgebraicGroups.Classification.RankOneRelations
open private RootCoordinate RootCoordinate.line RootCoordinate.iso RootCoordinate.scalar
  rootCoordinate_exists rootPoint_surjective cocharacterPoint_postcompose
  from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private extendSubgroup limits_subgroups_extend parabolic_of_cast contracting_of_cast
  from LinearAlgebraicGroups.RootData.RankOneFlag
open private pairing_extended pairing_restriction reductive_of_semisimple
  from LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
open private geometricallyMaximal_baseChange
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitBorelPairBaseChange
open private splitTorus_baseChange from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private subgroupInclusionFactors
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private commuteDescends
  from LinearAlgebraicGroups.Arithmetic.TrialitarianRelativeRoots
open private has_enumeration from LinearAlgebraicGroups.Flag.SimpleParabolicProduct

variable {F K : Type u} [Field F] [Field K] [Algebra F K] {G : AffineAlgebraicGroup F}
  {S T : ClosedSubgroup G.val}

private theorem pairing_of_restricted_root (i : S.group ⟶ T.group)
    (hS : IsSplitTorus S.group) (e : MultiplicativeComparison F K) (he : PreservesUnits e)
    (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
    (hrest : (fun a : Character S.group ↦ (groupBaseChange F K).map a ≫ e.inv) '' relativeRoots S =
      ((fun a : Character ((groupBaseChange F K).obj T.group) ↦
        (groupBaseChange F K).map i ≫ a) '' absoluteRoots (baseChangedSubgroup K T hT)) \ {1})
    (a : Character ((groupBaseChange F K).obj T.group))
    (ha : a ∈ absoluteRoots (baseChangedSubgroup K T hT)) :
    (∀ q : Cocharacter S.group,
      pairing ((groupBaseChange F K).obj T.group) a
        (e.hom ≫ (groupBaseChange F K).map q ≫ (groupBaseChange F K).map i) = 0) ∨
    ∃ b : relativeRoots S, ∀ q : Cocharacter S.group,
      pairing ((groupBaseChange F K).obj T.group) a
        (e.hom ≫ (groupBaseChange F K).map q ≫ (groupBaseChange F K).map i) =
        pairing S.group b.val q := by
  let E := groupBaseChange F K
  by_cases h : E.map i ≫ a = 1
  · exact Or.inl (fun q ↦ pairing_restriction K e i a h (splitTorus_baseChange hS) q)
  · have hm : E.map i ≫ a ∈
        ((fun b : Character (E.obj T.group) ↦ E.map i ≫ b) ''
          absoluteRoots (baseChangedSubgroup K T hT)) \ {1} :=
      ⟨⟨a, ha, rfl⟩, by simpa only [Set.mem_singleton_iff] using h⟩
    rw [← hrest] at hm
    obtain ⟨b, hb, heq⟩ := hm
    exact Or.inr ⟨⟨b, hb⟩, pairing_extended K e he i b a heq.symm⟩

private theorem baseChange_pointMap {A B : GroupScheme F} (f : A ⟶ B)
    (R : TestAlgebra K) (y : GroupPoints ((groupBaseChange F K).obj A) R) :
    baseChangePointGroupEquiv K B R (pointMap R ((groupBaseChange F K).map f) y) =
      pointMap ((restrictTestAlgebra F K).obj R) f (baseChangePointGroupEquiv K A R y) :=
  baseChangePointsSchemeNaturality F K f.hom.hom R y

private theorem baseChange_cocharacterPoint {A : GroupScheme F} (e : MultiplicativeComparison F K)
    (he : PreservesUnits e) (c : Cocharacter A) (R : TestAlgebra K) (t : Rˣ) :
    baseChangePointGroupEquiv K A R (cocharacterPoint (e.hom ≫ (groupBaseChange F K).map c) R t) =
      cocharacterPoint c ((restrictTestAlgebra F K).obj R) t := by
  rw [cocharacterPoint_postcompose]
  change baseChangePointGroupEquiv K A R
    (pointMap R ((groupBaseChange F K).map c) (cocharacterPoint e.hom R t)) = _
  rw [baseChange_pointMap]
  change pointMap _ c (baseChangePoint _ _ _ _ (unitPoint R t ≫ e.hom.hom.hom)) = _
  rw [he]
  rfl

private def extendedUpperLine {θ : relativeRoots S} (L : RankOne S)
    (hL : IsRankOneAt S θ L) (c : Cocharacter S.group) (hθ : 0 < pairing S.group θ.val c)
    (C : LimitDecomposition (c ≫ S.inclusion)) (i : S.group ⟶ T.group)
    (hi : i ≫ T.inclusion = S.inclusion)
    (e : MultiplicativeComparison F K) (he : PreservesUnits e)
    (hT : IsClosedImmersion ((groupBaseChange F K).map T.inclusion).hom.hom.left)
    (C' : LimitDecomposition
      ((e.hom ≫ (groupBaseChange F K).map c ≫ (groupBaseChange F K).map i) ≫
        (baseChangedSubgroup K T hT).inclusion)) :
    ContractingLine (J := baseChangedAlgebraicGroup K G) (T := baseChangedSubgroup K T hT)
      (e.hom ≫ (groupBaseChange F K).map c ≫ (groupBaseChange F K).map i)
      C' (pairing S.group θ.val c) := by
  let E := groupBaseChange F K
  let res := restrictTestAlgebra F K
  let x := L.upper.hom ≫ L.positive.inclusion
  let y (R : TestAlgebra K) (a : R) : GroupPoints (E.obj G.val) R :=
    (baseChangePointGroupEquiv K G.val R).symm (rootPoint x (res.obj R) a)
  have hy (R : TestAlgebra K) (a : R) :
      baseChangePointGroupEquiv K G.val R (y R a) = rootPoint x (res.obj R) a :=
    (baseChangePointGroupEquiv K G.val R).apply_symm_apply _
  have hcomp : (e.hom ≫ E.map c ≫ E.map i) ≫ (baseChangedSubgroup K T hT).inclusion =
      e.hom ≫ E.map (c ≫ S.inclusion) := by
    change (e.hom ≫ E.map c ≫ E.map i) ≫ E.map T.inclusion = _
    rw [Category.assoc, Category.assoc, ← E.map_comp, hi, ← E.map_comp]
  let C'' : LimitDecomposition (e.hom ≫ E.map (c ≫ S.inclusion)) := hcomp ▸ C'
  have hC := (limits_subgroups_extend G C e he C'').2.1
  have hC' : RankOneFlag.SameSubgroup C'.contracting (extendSubgroup K C.contracting) := by
    simpa only [C'', contracting_of_cast] using hC
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · intro R
    apply (baseChangePointGroupEquiv K G.val R).injective
    rw [hy, map_one, rootPoint_zero]
  · intro R Q f a
    apply (baseChangePointGroupEquiv K G.val Q).injective
    rw [hy]
    have h := baseChangePointsNaturality F K G.val.X f (y R a)
    change baseChangePointGroupEquiv K G.val Q (changeRing f (y R a)) =
      changeRing (res.map f) (baseChangePointGroupEquiv K G.val R (y R a)) at h
    refine h.trans ?_
    rw [hy, changeRing_rootPoint]
    rfl
  · intro R a
    obtain ⟨p, hp⟩ := (C.contracting_points (res.obj R) _).mp
      (rootPoint_contraction hL.1 c hθ (res.obj R) a)
    let q := (baseChangePointGroupEquiv K C.contracting.group R).symm p
    obtain ⟨j, hj⟩ := hC'.2
    refine ⟨pointMap R j q, ?_⟩
    change (q ≫ j.hom.hom) ≫ C'.contracting.inclusion.hom.hom = y R a
    rw [Category.assoc, ← Grp.comp_hom_hom, hj]
    change pointMap R (E.map C.contracting.inclusion) q = y R a
    apply (baseChangePointGroupEquiv K G.val R).injective
    rw [baseChange_pointMap, hy]
    exact (congrArg (pointMap (res.obj R) C.contracting.inclusion)
      ((baseChangePointGroupEquiv K C.contracting.group R).apply_symm_apply p)).trans hp
  · intro R t a
    let g := pointMap R (baseChangedSubgroup K T hT).inclusion
      (cocharacterPoint (e.hom ≫ E.map c ≫ E.map i) R t)
    change g * y R a * g⁻¹ = _
    have hg : g = cocharacterPoint (e.hom ≫ E.map (c ≫ S.inclusion)) R t := by
      rw [← hcomp, cocharacterPoint_postcompose]
      rfl
    have hg' : baseChangePointGroupEquiv K G.val R g =
        cocharacterPoint (c ≫ S.inclusion) (res.obj R) t := by
      rw [hg]
      exact baseChange_cocharacterPoint e he (c ≫ S.inclusion) R t
    apply (baseChangePointGroupEquiv K G.val R).injective
    simp only [map_mul, map_inv, hg', hy]
    rw [cocharacterPoint_postcompose]
    have h := hL.1 (res.obj R) (cocharacterPoint c (res.obj R) t) a
    simpa only [(RootData.CharacterPairing.characterPairingComposition _ θ.val c).2
      (res.obj R) t] using h

private def absoluteContractingLine {J : AffineAlgebraicGroup K} {T' : ClosedSubgroup J.val}
    {U : RootSubgroupFamily T'} (X : RootCoordinates U) (c : Cocharacter T'.group)
    (C : LimitDecomposition (c ≫ T'.inclusion)) (a : AbstractPairing.Root T')
    (h : 0 < pairing T'.group a.val c) :
    ContractingLine c C (pairing T'.group a.val c) where
  point R := rootPoint (coordMap X a) R
  zero R := rootPoint_zero _ R
  natural f r := changeRing_rootPoint _ f r
  factors R r := (C.contracting_points R _).mp (rootPoint_contraction (RootCoordinates.action X a) c h R r)
  scale R t r := by
    rw [← (RootData.CharacterPairing.characterPairingComposition _ a.val c).2 R t]
    exact RootCoordinates.action X a R (cocharacterPoint c R t) r

private theorem highestUpper_commutes_with_radical {θ : relativeRoots S}
    (hG : IsReductive G) (hS : IsMaximalSplitTorus S) (L : RankOne S)
    (hL : IsRankOneAt S θ L) (hSingle : HasSingleAbsoluteRoot S θ.val)
    {c d : Cocharacter S.group} (hθ : IsHighest S c θ)
    (hcd : ∀ b : relativeRoots S, 0 < pairing S.group b.val d → 0 < pairing S.group b.val c)
    (C : LimitDecomposition (c ≫ S.inclusion)) (D : LimitDecomposition (d ≫ S.inclusion)) :
    ∀ (R : TestAlgebra F) (x : GroupPoints L.positive.group R)
      (y : GroupPoints D.contracting.group R),
      Commute (pointMap R L.positive.inclusion x) (pointMap R D.contracting.inclusion y) := by
  obtain ⟨T, i, hTorus, hMax, hi, K, hK, hAlg, _, _, hT, _, hJ, hSplit, _, _⟩ := hSingle
  letI := hK
  letI := hAlg
  let J := baseChangedAlgebraicGroup K G
  let E := groupBaseChange F K
  let T' : ClosedSubgroup J.val := baseChangedSubgroup K T hT
  have hMax' : RankOneFlag.IsGeometricallyMaximal T' :=
    geometricallyMaximal_baseChange (K := K) G hG T hTorus hMax hSplit
  obtain ⟨e, he, _, hrest⟩ :=
    LinearAlgebraicGroups.Relative.RelativeChambers.relativeRootsByRestriction
      G S T i hi hS.1 hT hSplit
  let liftCochar (q : Cocharacter S.group) : Cocharacter T'.group :=
    e.hom ≫ E.map q ≫ E.map i
  have hlift (q : Cocharacter S.group) :
      liftCochar q ≫ T'.inclusion = e.hom ≫ E.map (q ≫ S.inclusion) := by
    change (e.hom ≫ E.map q ≫ E.map i) ≫ E.map T.inclusion = _
    rw [Category.assoc, Category.assoc, ← E.map_comp, hi, ← E.map_comp]
  let c' := liftCochar c
  let d' := liftCochar d
  have hpos (a : AbstractPairing.Root T') (ha : 0 < pairing T'.group a.val d') :
      0 < pairing T'.group a.val c' := by
    rcases pairing_of_restricted_root i hS.1 e he hT hrest a.val a.property with h | ⟨b, hb⟩
    · exact False.elim (ha.ne' (h d))
    · calc
        0 < pairing S.group b.val c := hcd b (lt_of_lt_of_eq ha (hb d))
        _ = pairing T'.group a.val c' := (hb c).symm
  have hbound (a : AbstractPairing.Root T') (ha : 0 < pairing T'.group a.val c') :
      pairing T'.group a.val c' ≤ pairing S.group θ.val c := by
    rcases pairing_of_restricted_root i hS.1 e he hT hrest a.val a.property with h | ⟨b, hb⟩
    · exact False.elim (ha.ne' (h c))
    · calc
        pairing T'.group a.val c' = pairing S.group b.val c := hb c
        _ ≤ pairing S.group θ.val c :=
          highest_pairing_ge hS.1 hθ c (fun _ hz ↦ hz.le) b (lt_of_lt_of_eq ha (hb c))
  obtain ⟨C'⟩ := existsLimitDecomposition J (c' ≫ T'.inclusion)
  obtain ⟨D'⟩ := existsLimitDecomposition J (d' ≫ T'.inclusion)
  let D'' : LimitDecomposition (e.hom ≫ E.map (d ≫ S.inclusion)) := (hlift d) ▸ D'
  have hD : RankOneFlag.SameSubgroup D'.contracting (extendSubgroup K D.contracting) := by
    simpa only [D'', contracting_of_cast] using (limits_subgroups_extend G D e he D'').2.1
  obtain ⟨hfinite, ⟨U⟩, hproducts⟩ := RootData.OrderedRootProducts.contractingProduct J hJ.1 T' hSplit hMax'
  letI : Finite (AbstractPairing.Root T') := hfinite
  let coords (a : AbstractPairing.Root T') : RootCoordinate U a :=
    Classical.choice (rootCoordinate_exists RootData.RootGroups.rootSubgroups J hJ.1 T' hSplit hMax' U a)
  let X : RootCoordinates U :=
    RootCoordinates.mk (fun a ↦ RootCoordinate.line (coords a))
      (fun a ↦ RootCoordinate.iso (coords a)) (fun a ↦ RootCoordinate.scalar (coords a))
  obtain ⟨lc, hcl⟩ := has_enumeration (positiveRoots T' c')
  obtain ⟨ld, hdl⟩ := has_enumeration (positiveRoots T' d')
  have hCprod := (hproducts c').2 C' U lc hcl
  have hDprod := (hproducts d').2 D' U ld hdl
  let upper := extendedUpperLine L hL c hθ.1.2 C i hi e he hT C'
  apply commuteDescends (K := K) L.positive D.contracting
  intro R x y
  obtain ⟨j, hj⟩ := hD.2
  let y' := pointMap R j y
  change Commute (pointMap R (E.map L.positive.inclusion) x)
    (pointMap R (E.map D.contracting.inclusion) y)
  obtain ⟨q, hq⟩ := evalCoordinates_range X hDprod R y'
  have hy' : pointMap R (E.map D.contracting.inclusion) y = evalCoordinates X R ld q := by
    rw [hq]
    change y ≫ (E.map D.contracting.inclusion).hom.hom =
      (y ≫ j.hom.hom) ≫ D'.contracting.inclusion.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hj]
    rfl
  rw [hy']
  apply commute_evalCoordinates X R _ ld
  intro a ha s
  let R₀ := (restrictTestAlgebra F K).obj R
  let x₀ := baseChangePointGroupEquiv K L.positive.group R x
  obtain ⟨r, hr⟩ := rootPoint_surjective L.upper R₀ x₀
  have hx : pointMap R (E.map L.positive.inclusion) x = upper.point R r := by
    apply (baseChangePointGroupEquiv K G.val R).injective
    rw [baseChange_pointMap]
    change pointMap R₀ L.positive.inclusion x₀ =
      baseChangePointGroupEquiv K G.val R ((baseChangePointGroupEquiv K G.val R).symm
        (rootPoint (L.upper.hom ≫ L.positive.inclusion) R₀ r))
    rw [MulEquiv.apply_symm_apply, ← hr]
    rfl
  have ha' := hpos a ((hdl.2 a).mp ha)
  let β := absoluteContractingLine X c' C' a ha'
  rw [hx]
  change Commute (upper.point R r) (β.point R s)
  exact contractingLines_commute X hθ.1.2.le ha'.le upper β lc hCprod
    (fun b hb ↦ lt_of_le_of_lt (hbound b ((hcl.2 b).mp hb)) (by omega)) R r s

theorem highestRootSL2 : Statement.{u} := by
  intro F _ _ _ _ G hG _ S hS _ ⟨θ, hlong, hSingle⟩ hRank
  have hRed := reductive_of_semisimple G hG.1
  obtain ⟨c, hc, hθ⟩ := longest_is_highest_for_some_cocharacter hG hS θ hlong
  obtain ⟨C⟩ := existsLimitDecomposition G (c ≫ S.inclusion)
  obtain ⟨L, hL⟩ := hRank θ hSingle
  obtain ⟨d, D, hpar, hCD, hproper, hmax, hθd, hcd⟩ :=
    exists_maximal_limit_parabolic hRed hS hθ C
  let U := contractingSubgroup D
  have hU : (subgroupOfSubgroup D.parabolic U).inclusion = D.contracting.inclusion :=
    D.contracting_in_G
  have hrad :=
    LinearAlgebraicGroups.Relative.SplitContractingRadical.contractingSubgroupIsRadical G hRed _ D
  refine ⟨c, θ, L, C, hc, hθ, hSingle, hL, D.parabolic, U, hpar, hCD, hproper, hmax,
    hrad.1, ?_, ?_⟩
  · have hfac : IsSubgroupOf L.positive D.contracting := by
      apply subgroupInclusionFactors (closedSubgroupAlgebraicGroup L.positive).property.1
      intro R p
      obtain ⟨x, rfl⟩ := rootPoint_surjective L.upper R p
      exact (D.contracting_points R _).mp (rootPoint_contraction hL.1 d hθd R x)
    obtain ⟨f, hf⟩ := hfac
    exact ⟨f, by rw [hU, hf]⟩
  · intro R x y
    rw [← Grp.comp_hom_hom]
    change Commute (pointMap R L.positive.inclusion x)
      (pointMap R (subgroupOfSubgroup D.parabolic U).inclusion y)
    rw [hU]
    exact highestUpper_commutes_with_radical hRed hS L hL hSingle hθ hcd C D R x y

end ScalarExtension

end
end LinearAlgebraicGroups.Arithmetic.LocalMixingHighestRootSL2
