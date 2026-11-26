import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.DominantOrder
import Mathlib.LinearAlgebra.RootSystem.BaseExists

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelPositivity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl
open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Representation.DominantOrder

open LinearAlgebraicGroups.Specs
open Specs.DominantOrder
open Module
open RootPairing (Base)

noncomputable section

variable {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- A finite free lattice embeds in its real coordinate space. -/
private def realCoordinates {J : Type*} [Finite J] (a : Basis J ℤ X) :
    X →ₗ[ℤ] (J → ℝ) :=
  LinearMap.pi fun j ↦ (Int.castRingHom ℝ).toIntLinearMap.comp (a.coord j)

private lemma realCoordinates_injective {J : Type*} [Finite J] (a : Basis J ℤ X) :
    Function.Injective (realCoordinates a) := by
  intro x y h
  apply a.repr.injective
  ext j
  exact Int.cast_injective (α := ℝ) (congrFun h j)

private lemma realCoordinates_basis {J : Type*} [Finite J] [Fintype J]
    (a : Basis J ℤ X) (j : J) :
    realCoordinates a (a j) = Pi.basisFun ℝ J j := by
  classical
  ext i
  simp [realCoordinates, Basis.coord_apply, Pi.basisFun_apply, Pi.single_apply,
    Finsupp.single_apply, eq_comm]

private lemma realCoordinates_eval {J : Type*} [Fintype J] (a : Basis J ℤ X)
    (f : X →ₗ[ℤ] ℝ) (x : X) :
    ((Pi.basisFun ℝ J).constr ℝ (fun j ↦ f (a j))) (realCoordinates a x) = f x := by
  let g := (Pi.basisFun ℝ J).constr ℝ (fun j ↦ f (a j))
  have h : (g.restrictScalars ℤ).comp (realCoordinates a) = f := by
    apply a.ext
    intro j
    change g (realCoordinates a (a j)) = f (a j)
    rw [realCoordinates_basis, Basis.constr_basis]
  exact LinearMap.congr_fun h x

private lemma mem_closure_image_iff {A B J : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A →ₗ[ℤ] B) (he : Function.Injective e) (v : J → A) (s : Set J) (x : A) :
    e x ∈ AddSubmonoid.closure ((e ∘ v) '' s) ↔ x ∈ AddSubmonoid.closure (v '' s) := by
  rw [Set.image_comp]
  change e x ∈ AddSubmonoid.closure (e.toAddMonoidHom '' v '' s) ↔ _
  rw [← AddMonoidHom.map_mclosure, AddSubmonoid.mem_map]
  constructor
  · rintro ⟨a, ha, hax⟩
    exact he hax ▸ ha
  · exact fun hx ↦ ⟨x, hx, rfl⟩

private lemma descend_vectors {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module ℝ B]
    (e : A →ₗ[ℤ] C) (he : Function.Injective e) (p : B →ₗ[ℤ] C)
    (hp : Function.Injective p) (a : I → A) (b : I → B) (s : Set I)
    (h : p ∘ b = e ∘ a) (hli : LinearIndepOn ℝ b s)
    (hclosure : ∀ i, b i ∈ AddSubmonoid.closure (b '' s) ∨
      -b i ∈ AddSubmonoid.closure (b '' s)) :
    LinearIndepOn ℤ a s ∧
      ∀ i, a i ∈ AddSubmonoid.closure (a '' s) ∨ -a i ∈ AddSubmonoid.closure (a '' s) := by
  have hval (i : I) : p (b i) = e (a i) := congrFun h i
  constructor
  · have hind := (hli.linearIndependent.restrict_scalars' ℤ).map' p
      (LinearMap.ker_eq_bot.mpr hp)
    refine LinearIndependent.of_comp e ?_
    simpa only [Function.comp_def, hval] using hind
  · intro i
    rcases hclosure i with hi | hi
    · left
      apply (mem_closure_image_iff e he _ _ _).mp
      rw [← h, ← hval]
      exact (mem_closure_image_iff p hp _ _ _).mpr hi
    · right
      apply (mem_closure_image_iff e he _ _ _).mp
      rw [← h, map_neg, ← hval, ← map_neg]
      exact (mem_closure_image_iff p hp _ _ _).mpr hi

set_option maxHeartbeats 700000 in
private theorem exists_base_for_regular [Finite I] [Module.Free ℤ X] [Module.Finite ℤ X]
    [IsTorsionFree ℤ X] (P : RootPairing I ℤ X Y) [P.IsReduced]
    (f : X →ₗ[ℤ] ℝ) (hf : ∀ i, f (P.root i) ≠ 0) :
    ∃ b : P.Base, ∀ i, b.IsPos i ↔ 0 < f (P.root i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let J := Module.Free.ChooseBasisIndex ℤ X
  let : Fintype J := Fintype.ofFinite J
  let a : Basis J ℤ X := Module.Free.chooseBasis ℤ X
  let V := J → ℝ
  let d : Basis J ℝ V := Pi.basisFun ℝ J
  let e : X →ₗ[ℤ] V := realCoordinates a
  let g : Y →ₗ[ℤ] Dual ℝ V :=
    (d.constr ℝ).toLinearMap.restrictScalars ℤ ∘ₗ
      LinearMap.pi (fun j ↦ (Int.castRingHom ℝ).toIntLinearMap.comp
        (P.toLinearMap (a j)))
  have he : Function.Injective e := realCoordinates_injective a
  have hp (x : X) (y : Y) : g y (e x) = (P.toLinearMap x y : ℝ) := by
    exact realCoordinates_eval a
      ((Int.castRingHom ℝ).toIntLinearMap.comp (P.toLinearMap.flip y)) x
  have hg : Function.Injective g := by
    intro y z hyz
    apply P.toLinearMap.flip.toPerfPair.injective
    ext x
    change P.toLinearMap x y = P.toLinearMap x z
    exact Int.cast_injective (α := ℝ) (by rw [← hp, ← hp, hyz])
  let Q : RootPairing I ℝ V (Dual ℝ V) :=
    { toLinearMap := Dual.eval ℝ V
      root := ⟨e ∘ P.root, he.comp P.root.injective⟩
      coroot := ⟨g ∘ P.coroot, hg.comp P.coroot.injective⟩
      root_coroot_two := fun i ↦ by
        change g (P.coroot i) (e (P.root i)) = 2
        rw [hp, P.root_coroot_two]
        norm_num
      reflectionPerm := P.reflectionPerm
      reflectionPerm_root := fun i j ↦ by
        change e (P.root j) - g (P.coroot i) (e (P.root j)) • e (P.root i) =
          e (P.root (P.reflectionPerm i j))
        rw [hp, Int.cast_smul_eq_zsmul ℝ, ← map_smul, ← map_sub, P.reflectionPerm_root]
      reflectionPerm_coroot := fun i j ↦ by
        change g (P.coroot j) - g (P.coroot j) (e (P.root i)) • g (P.coroot i) =
          g (P.coroot (P.reflectionPerm i j))
        rw [hp, Int.cast_smul_eq_zsmul ℝ (M := Dual ℝ V), ← map_smul, ← map_sub,
          P.reflectionPerm_coroot] }
  let R := Q.restrictScalars' ℝ
  let : R.IsRootSystem := by
    constructor
    · rw [← Submodule.span_setOfPred_mem_eq_top]
      congr
      ext ⟨x, hx⟩
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, congrArg Subtype.val hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext hi⟩
    · rw [← Submodule.span_setOfPred_mem_eq_top]
      congr
      ext ⟨x, hx⟩
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, congrArg Subtype.val hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext hi⟩
  let E := (Q.rootSpan ℝ).subtype.restrictScalars ℤ
  let H := (Q.corootSpan ℝ).subtype.restrictScalars ℤ
  have hE : Function.Injective E := Subtype.val_injective
  have hH : Function.Injective H := Subtype.val_injective
  have hpair (i j : I) : R.pairing i j = (P.pairing i j : ℝ) := by
    have h := Q.restrictScalars_pairing ℝ i j
    rw [Algebra.algebraMap_self_apply] at h
    exact h.trans (hp _ _)
  let : R.IsCrystallographic := ⟨fun i j ↦ ⟨P.pairing i j, (hpair i j).symm⟩⟩
  let : R.IsReduced := ⟨fun i j hij ↦ by
    have hR := R.coxeterWeight_eq_four_iff_not_linearIndependent.mpr hij
    have hP : P.coxeterWeight i j = 4 := Int.cast_injective (α := ℝ) (by
      simpa only [RootPairing.coxeterWeight, Int.cast_mul, Int.cast_ofNat, ← hpair] using hR)
    rcases RootPairing.IsReduced.eq_or_eq_neg i j
        (P.coxeterWeight_eq_four_iff_not_linearIndependent.mp hP) with h | h
    · exact Or.inl (hE (congrArg e h))
    · exact Or.inr (hE (by
        change e (P.root i) = -e (P.root j)
        rw [← map_neg, h]))⟩
  let F := (d.constr ℝ (fun j ↦ f (a j))).comp (Q.rootSpan ℝ).subtype
  have hF (i : I) : F (R.root i) = f (P.root i) := realCoordinates_eval a f _
  have hF₀ (i : I) : F (R.root i) ≠ 0 := hF i ▸ hf i
  let S := IsAddIndecomposable.baseOf R.root F.toAddMonoidHom
  let := R.indexNeg
  let B : R.Base := RootPairing.Base.mk' R S (R.linearIndepOn_root_baseOf' F hF₀)
    (fun i ↦ IsAddIndecomposable.mem_or_neg_mem_closure_baseOf R.root
      F.toAddMonoidHom i (hF₀ i) (by simp))
  obtain ⟨hli, hspan⟩ := descend_vectors e he E hE P.root R.root B.support rfl
    B.linearIndepOn_root B.root_mem_or_neg_mem
  obtain ⟨hli', hspan'⟩ := descend_vectors g hg H hH P.coroot R.coroot B.support rfl
    B.linearIndepOn_coroot B.coroot_mem_or_neg_mem
  let b : P.Base := ⟨B.support, hli, hli', hspan, hspan'⟩
  have hsimple (j : I) (hj : j ∈ b.support) : 0 < f (P.root j) := by
    rw [← hF]
    have hj' : j ∈ S := by
      change j ∈ (Set.toFinite S).toFinset at hj
      simpa using hj
    exact hj'.1
  refine ⟨b, fun i ↦ ?_⟩
  obtain ⟨c, -, hc | hc⟩ := b.exists_root_eq_sum_nat_or_neg i
  · have hh : b.height i = ∑ j ∈ b.support, (c j : ℤ) :=
      b.height_eq_sum (by simpa only [natCast_zsmul] using hc)
    have hfe : f (P.root i) = ∑ j ∈ b.support, c j • f (P.root j) := by
      simp only [hc, map_sum, map_nsmul]
    have hhn : 0 ≤ b.height i := hh ▸ Finset.sum_nonneg (fun j _ ↦ Int.natCast_nonneg (c j))
    have hfn : 0 ≤ f (P.root i) := by
      rw [hfe]
      exact Finset.sum_nonneg (fun j hj ↦ nsmul_nonneg (hsimple j hj).le _)
    exact iff_of_true ((b.isPos_iff').mpr hhn) (lt_of_le_of_ne hfn (Ne.symm (hf i)))
  · have hh : b.height i = ∑ j ∈ b.support, -(c j : ℤ) :=
      b.height_eq_sum (by simpa only [neg_smul, Finset.sum_neg_distrib, natCast_zsmul]
        using hc)
    have hfe : f (P.root i) = -∑ j ∈ b.support, c j • f (P.root j) := by
      simp only [hc, map_neg, map_sum, map_nsmul]
    have hhn : b.height i ≤ 0 := hh ▸ Finset.sum_nonpos (fun j _ ↦ by simp)
    have hfn : f (P.root i) ≤ 0 := by
      rw [hfe, neg_nonpos]
      exact Finset.sum_nonneg (fun j hj ↦ nsmul_nonneg (hsimple j hj).le _)
    exact iff_of_false (not_lt_of_ge hhn) (not_lt_of_ge hfn)

private lemma sum_coroot_pairing [Finite I] [IsTorsionFree ℤ Y]
    (P : RootPairing I ℤ X Y) [P.IsReduced] (b : P.Base) {S : Set I}
    (hS : IsBaseFor P S b) {i : I} (hi : i ∈ b.support) :
    P.toLinearMap (P.root i) (twoRhoCoroot P S) = 2 := by
  classical
  let := Fintype.ofFinite I
  let t := Finset.univ.filter (· ∈ S)
  have hmem (j : I) : j ∈ t ↔ b.IsPos j := by simpa [t] using (hS j).symm
  have hit : i ∈ t := (hmem i).mpr (b.isPos_of_mem_support hi)
  let s := P.reflectionPerm i
  have hinv (j : I) : s (s j) = j := P.reflectionPerm_involutive i j
  have hmap (j : I) (hj : j ∈ t.erase i) : s j ∈ t.erase i := by
    obtain ⟨hji, hjt⟩ := Finset.mem_erase.mp hj
    refine Finset.mem_erase.mpr ⟨?_, (hmem _).mpr (((hmem _).mp hjt).reflectionPerm hi hji)⟩
    intro h
    have hj' : j = s i := by rw [← h, hinv]
    have hn : ¬ b.IsPos (s i) := fun hp ↦
      (Base.IsPos.neg_iff_not b i).mp hp (b.isPos_of_mem_support hi)
    exact hn (hj' ▸ (hmem _).mp hjt)
  have hsum : ∑ j ∈ t.erase i, P.coroot (s j) = ∑ j ∈ t.erase i, P.coroot j :=
    Finset.sum_equiv s (fun j ↦ ⟨hmap j, fun h ↦ hinv j ▸ hmap (s j) h⟩)
      (fun _ _ ↦ rfl)
  let r := twoRhoCoroot P S
  have hr : (∑ j ∈ t.erase i, P.coroot j) + P.coroot i = r :=
    Finset.sum_erase_add _ _ hit
  have hrefl : P.coreflection i r = r - (2 : ℤ) • P.coroot i := by
    calc
      P.coreflection i r = (∑ j ∈ t.erase i, P.coroot (s j)) + -P.coroot i := by
        rw [← hr, map_add, map_sum, P.coreflection_apply_self]
        simp only [← P.coroot_reflectionPerm]
        rfl
      _ = r - (2 : ℤ) • P.coroot i := by rw [hsum, ← hr, two_smul]; abel
  rw [P.coreflection_apply] at hrefl
  exact smul_left_injective ℤ (P.flip.ne_zero i) (sub_right_inj.mp hrefl)

private lemma positive_flip [Finite I] (P : RootPairing I ℤ X Y)
    [P.IsReduced] [P.flip.IsReduced] (b : P.Base) (i : I) :
    b.flip.IsPos i ↔ b.IsPos i := by
  let := P.indexNeg
  have forward (j : I) (hj : b.IsPos j) : b.flip.IsPos j := by
    refine (hj.induction_on_reflect (p := fun k ↦ b.IsPos k → b.flip.IsPos k) ?_ ?_) hj
    · exact fun k hk _ ↦ b.flip.isPos_of_mem_support hk
    · intro k l ih hl hkl
      by_cases he : P.reflectionPerm l k = l
      · rw [he]
        exact b.flip.isPos_of_mem_support hl
      have hk : b.IsPos k := P.reflectionPerm_involutive l k ▸ hkl.reflectionPerm hl he
      have hne : k ≠ l := by
        rintro rfl
        exact (Base.IsPos.neg_iff_not b k).mp hkl (b.isPos_of_mem_support hl)
      exact (ih hk).reflectionPerm hl hne
  refine ⟨fun hi ↦ ?_, forward i⟩
  by_contra hn
  have hh : b.flip.IsPos (-i) := forward (-i) ((Base.IsPos.neg_iff_not b i).mpr hn)
  exact (Base.IsPos.neg_iff_not b.flip i).mp hh hi

private lemma positive_root_coefficients (P : RootPairing I ℤ X Y) (b : P.Base)
    {i : I} (hi : b.IsPos i) :
    ∃ c : I → ℤ, (∀ j, 0 ≤ c j) ∧
      (∃ j ∈ b.support, 0 < c j) ∧ P.root i = ∑ j ∈ b.support, c j • P.root j := by
  obtain ⟨c, _, hc, hr⟩ := b.exists_root_eq_sum_int i
  rw [b.isPos_iff, b.height_eq_sum hr] at hi
  refine ⟨c, ?_, ?_, hr⟩
  · rcases hc with hp | hn
    · exact hp.le
    · exact (not_lt_of_ge (Finset.sum_nonpos fun j _ ↦ hn.le j) hi).elim
  · by_contra! hn
    exact (not_lt_of_ge (Finset.sum_nonpos hn) hi)

private lemma eval_pos_root_nonneg (P : RootPairing I ℤ X Y) (b : P.Base)
    (f : X →ₗ[ℤ] ℤ) (hf : ∀ j ∈ b.support, 0 ≤ f (P.root j)) {i : I}
    (hi : b.IsPos i) : 0 ≤ f (P.root i) := by
  obtain ⟨c, hc, -, he⟩ := positive_root_coefficients P b hi
  rw [he, map_sum]
  exact Finset.sum_nonneg fun j hj ↦ by
    simpa only [map_smul, zsmul_eq_mul, Int.cast_id] using mul_nonneg (hc j) (hf j hj)

private lemma eval_pos_root_strict (P : RootPairing I ℤ X Y) (b : P.Base)
    (f : X →ₗ[ℤ] ℤ) (hf : ∀ j ∈ b.support, 0 < f (P.root j)) (i : I) :
    0 < f (P.root i) ↔ b.IsPos i := by
  have aux {j : I} (hj : b.IsPos j) : 0 < f (P.root j) := by
    obtain ⟨c, hc, ⟨l, hl, hcl⟩, he⟩ := positive_root_coefficients P b hj
    rw [he, map_sum]
    refine Finset.sum_pos' (fun k hk ↦ ?_) ⟨l, hl, ?_⟩
    · simpa only [map_smul, zsmul_eq_mul, Int.cast_id] using mul_nonneg (hc k) (hf k hk).le
    · simpa only [map_smul, zsmul_eq_mul, Int.cast_id] using mul_pos hcl (hf l hl)
  refine ⟨fun hp ↦ ?_, aux⟩
  by_contra hn
  let := P.indexNeg
  have hh := aux ((Base.IsPos.neg_iff_not b i).mpr hn)
  have hh' : 0 < -f (P.root i) := by simpa using hh
  exact (not_lt_of_ge hp.le) (neg_pos.mp hh')

private lemma weyl_pairing (P : RootPairing I ℤ X Y) (w : P.weylGroup) (x : X) (i : I) :
    P.toLinearMap (w.val.weightEquiv x) (P.coroot (P.weylGroupToPerm w i)) =
      P.toLinearMap x (P.coroot i) := by
  rw [w.val.toLinearMap_weightEquiv]
  apply congrArg (P.toLinearMap x)
  have h := RootPairing.Hom.coroot_coweightMap_apply P P (w.val.indexEquiv i) w.val.toHom
  simpa using h

private lemma reflection_increases (P : RootPairing I ℤ X Y) (r : Y) {i : I}
    (hi : P.toLinearMap (P.root i) r = 2) (x : X)
    (hx : P.toLinearMap x (P.coroot i) < 0) :
    P.toLinearMap x r <
      P.toLinearMap ((RootPairing.weylGroup.ofIdx P i).val.weightEquiv x) r := by
  change P.toLinearMap x r < P.toLinearMap (P.reflection i x) r
  simp [RootPairing.reflection_apply, LinearMap.sub_apply, LinearMap.smul_apply, hi]
  omega

private lemma dominant_orbit [Finite I] (P : RootPairing I ℤ X Y)
    [Finite P.weylGroup] [P.IsReduced] [P.flip.IsReduced] (b : P.Base)
    (r : Y) (v : X) (hr : ∀ i ∈ b.support, P.toLinearMap (P.root i) r = 2)
    (hv : ∀ i ∈ b.support, P.toLinearMap v (P.coroot i) = 2)
    (hfree : ∀ w : P.weylGroup, P.weylGroupToPerm w '' {i | b.IsPos i} =
      {i | b.IsPos i} → w = 1) (x : X) :
    ∃! y : X, IsDominant P b y ∧ ∃ w : P.weylGroup, w.val.weightEquiv x = y := by
  classical
  let := Fintype.ofFinite P.weylGroup
  let score (z : X) := P.toLinearMap z r
  obtain ⟨w, -, hw⟩ := Finset.exists_max_image Finset.univ
    (fun w : P.weylGroup ↦ score (w.val.weightEquiv x)) (by simp)
  have hdom : IsDominant P b (w.val.weightEquiv x) := by
    intro i hi
    by_contra! hn
    exact (not_lt_of_ge (hw (RootPairing.weylGroup.ofIdx P i * w) (Finset.mem_univ _)))
      (reflection_increases P r (hr i hi) _ hn)
  refine ⟨w.val.weightEquiv x, ⟨hdom, w, rfl⟩, ?_⟩
  rintro y ⟨hy, z, rfl⟩
  let a := w.val.weightEquiv x
  let c := z.val.weightEquiv x
  let t := Finset.univ.filter (fun g : P.weylGroup ↦ g.val.weightEquiv a = c)
  have ht : t.Nonempty := by
    refine ⟨z * w⁻¹, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change (z * w⁻¹) • (w • x) = z • x
    rw [mul_smul, inv_smul_smul]
  obtain ⟨g, hg, hmax⟩ := Finset.exists_max_image t
    (fun g : P.weylGroup ↦ score (g.val.weightEquiv v)) ht
  have hgc : g.val.weightEquiv a = c := (Finset.mem_filter.mp hg).2
  have hsign (j : I) : 0 < P.toLinearMap v (P.coroot j) ↔ b.IsPos j :=
    (eval_pos_root_strict P.flip b.flip (P.toLinearMap v)
      (fun i hi ↦ by change 0 < P.toLinearMap v (P.coroot i); rw [hv i hi]; decide) j).trans
        (positive_flip P b j)
  have hvreg (j : I) : P.toLinearMap v (P.coroot j) ≠ 0 := by
    intro hz
    let := P.indexNeg
    rcases Base.IsPos.or_neg b j with h | h
    · exact (hsign j).mpr h |>.ne' hz
    · have h' := (hsign (-j)).mpr h
      simp [hz] at h'
  have hgv (j : I) :
      P.toLinearMap (g.val.weightEquiv v) (P.coroot (P.weylGroupToPerm g j)) =
        P.toLinearMap v (P.coroot j) := weyl_pairing P g v j
  have hgpos (i : I) (hi : i ∈ b.support) :
      0 < P.toLinearMap (g.val.weightEquiv v) (P.coroot i) := by
    let j := (P.weylGroupToPerm g).symm i
    have hj : P.weylGroupToPerm g j = i := Equiv.apply_symm_apply _ _
    have he := hgv j
    rw [hj] at he
    have hne : P.toLinearMap (g.val.weightEquiv v) (P.coroot i) ≠ 0 := he ▸ hvreg j
    by_contra! hn
    have hn' := lt_of_le_of_ne hn hne
    have hjneg : ¬ b.IsPos j := fun h ↦ (not_lt_of_ge hn) (he ▸ (hsign j).mpr h)
    let := P.indexNeg
    have hna := eval_pos_root_nonneg P.flip b.flip (P.toLinearMap a)
      (fun j hj ↦ hdom j hj)
      ((positive_flip P b (-j)).mpr ((Base.IsPos.neg_iff_not b j).mpr hjneg))
    change 0 ≤ P.toLinearMap a (P.coroot (-j)) at hna
    change 0 ≤ P.toLinearMap a (P.coroot (P.reflectionPerm j j)) at hna
    simp only [RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self,
      map_neg] at hna
    have hac := weyl_pairing P g a j
    rw [hj, hgc] at hac
    have hi0 : P.toLinearMap c (P.coroot i) = 0 :=
      le_antisymm (hac ▸ neg_nonneg.mp hna) (hy i hi)
    let sg := RootPairing.weylGroup.ofIdx P i * g
    have hsg : sg ∈ t := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change P.reflection i (g.val.weightEquiv a) = c
      rw [hgc, P.reflection_apply]
      simp [hi0]
    exact (not_lt_of_ge (hmax sg hsg)) (reflection_increases P r (hr i hi) _ hn')
  have hsign' (j : I) : 0 < P.toLinearMap (g.val.weightEquiv v) (P.coroot j) ↔ b.IsPos j :=
    (eval_pos_root_strict P.flip b.flip (P.toLinearMap (g.val.weightEquiv v))
      (fun i hi ↦ hgpos i hi) j).trans (positive_flip P b j)
  have hpres : P.weylGroupToPerm g '' {i | b.IsPos i} = {i | b.IsPos i} := by
    ext i
    change (∃ j, b.IsPos j ∧ P.weylGroupToPerm g j = i) ↔ b.IsPos i
    refine ⟨?_, ?_⟩
    · rintro ⟨j, hj, rfl⟩
      exact (hsign' _).mp (by rw [hgv]; exact (hsign j).mpr hj)
    · intro hi
      let j := (P.weylGroupToPerm g).symm i
      have hj : P.weylGroupToPerm g j = i := Equiv.apply_symm_apply _ _
      refine ⟨j, (hsign j).mp ?_, hj⟩
      rw [← hgv, hj]
      exact (hsign' i).mpr hi
  have h1 := hfree g hpres
  exact (by simpa [h1] using hgc.symm : c = a)

private theorem laws [Finite I] [IsTorsionFree ℤ X] [IsTorsionFree ℤ Y]
    (P : RootPairing I ℤ X Y) [Finite P.weylGroup] [P.IsReduced] [P.flip.IsReduced]
    (S : Set I) (b : P.Base) (hS : IsBaseFor P S b)
    (hfree : ∀ w : P.weylGroup, P.weylGroupToPerm w '' S = S → w = 1) :
    Laws P S b := by
  classical
  have r (i : I) (hi : i ∈ b.support) := sum_coroot_pairing P b hS hi
  let v := twoRhoCoroot P.flip S
  have vpair (i : I) (hi : i ∈ b.support) : P.toLinearMap v (P.coroot i) = 2 :=
    sum_coroot_pairing P.flip b.flip
      (fun j ↦ (positive_flip P b j).trans (hS j)) hi
  have hset : {i | b.IsPos i} = S := Set.ext hS
  have orbit := dominant_orbit P b (twoRhoCoroot P S) v r vpair
    (fun w h ↦ hfree w (by simpa only [hset] using h))
  have nonnegative (x : X) (hx : IsDominant P b x) :
      0 ≤ P.toLinearMap x (twoRhoCoroot P S) := by
    unfold twoRhoCoroot
    rw [map_sum]
    refine Finset.sum_nonneg fun j hj ↦ ?_
    exact eval_pos_root_nonneg P.flip b.flip (P.toLinearMap x) hx
      ((positive_flip P b j).mpr ((hS j).mpr (Finset.mem_filter.mp hj).2))
  have increase (x y : X) (h : DominanceLT P b x y) :
      P.toLinearMap x (twoRhoCoroot P S) < P.toLinearMap y (twoRhoCoroot P S) := by
    obtain ⟨⟨c, hc⟩, hne⟩ := h
    have hex : ∃ i : b.support, 0 < c i := by
      by_contra! hz
      have hzero (i : b.support) : c i = 0 := Nat.eq_zero_of_le_zero (hz i)
      exact hne (sub_eq_zero.mp (by simpa [hzero] using hc)).symm
    have hsum := congrArg (P.toLinearMap.flip (twoRhoCoroot P S)) hc
    have hpairs (i : b.support) : P.toLinearMap (P.root i) (twoRhoCoroot P S) = 2 :=
      r i i.property
    simp only [map_sub, map_sum, map_nsmul, LinearMap.flip_apply, hpairs] at hsum
    have hp : 0 < ∑ i : b.support, c i • (2 : ℤ) := by
      refine Finset.sum_pos' (fun i _ ↦ by positivity) ?_
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, Finset.mem_univ _, by positivity⟩
    omega
  refine ⟨orbit, nonnegative, r, fun x y _ _ h ↦ increase x y h, ?_, ?_⟩
  · let measure (x : DominantWeights P b) :=
      (P.toLinearMap x.val (twoRhoCoroot P S)).toNat
    refine (InvImage.wf measure Nat.lt_wfRel.wf).mono ?_
    intro x y h
    change measure x < measure y
    have hxy := increase x.val y.val h
    have hx := nonnegative x.val x.property
    exact (Int.toNat_lt_toNat (hx.trans_lt hxy)).mpr hxy
  · intro hI x y h
    let : IsEmpty I := hI
    obtain ⟨⟨c, hc⟩, hn⟩ := h
    exact hn (sub_eq_zero.mp (by simpa using hc)).symm

/-- The dominant order, conditional on the two frozen root datum interfaces. -/
theorem dominantOrder_conditional
    (positivity : Specs.BorelPositivity.Statement.{u})
    (_datumAndWeyl : Specs.DatumAndWeyl.Statement.{u}) : Statement.{u} := by
  intro k _ G hG T hT hmax
  obtain ⟨h, D, hW, -, action, -⟩ := positivity G hG T hT hmax
  let := h
  let := D.finiteRoots
  let := D.freeCharacters
  let := D.finiteCharacters
  let := D.reduced
  let := D.reducedCoroots
  let := Module.IsReflexive.of_isPerfPair D.rootDatum.toLinearMap
  let := Module.IsReflexive.of_isPerfPair D.rootDatum.toLinearMap.flip
  refine ⟨h, D, hW, ?_⟩
  intro S hS
  have injective : Function.Injective (fun w : D.rootDatum.weylGroup ↦
      D.rootDatum.weylGroupToPerm w '' S) := by
    intro w v hwv
    obtain ⟨_, _, hu⟩ := action.2.2 S _ hS (action.2.1 v S hS)
    exact (hu w hwv).trans (hu v rfl).symm
  let : Finite D.rootDatum.weylGroup := Finite.of_injective _ injective
  have hfree (w : D.rootDatum.weylGroup)
      (hw : D.rootDatum.weylGroupToPerm w '' S = S) : w = 1 :=
    injective (by simpa using hw)
  obtain ⟨f, hf, hpos⟩ := hS
  refine ⟨?_, fun b hb ↦ laws D.rootDatum S b hb hfree⟩
  obtain ⟨b, hb⟩ := exists_base_for_regular D.rootDatum f (by simpa only [D.root_eq] using hf)
  exact ⟨b, fun i ↦ by simpa only [hpos, Set.mem_ofPred_eq, D.root_eq] using hb i⟩

end

end LinearAlgebraicGroups.Representation.DominantOrder

universe v8_closure_d8baef8c4d61ab0d_u0
theorem _root_.«LinearAlgebraicGroups».«Representation».«DominantOrder».«dominantOrder» : _root_.«LinearAlgebraicGroups».«Specs».«DominantOrder».«Statement».{v8_closure_d8baef8c4d61ab0d_u0} :=
  @_root_.«LinearAlgebraicGroups».«Representation».«DominantOrder».«dominantOrder_conditional».{v8_closure_d8baef8c4d61ab0d_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelPositivity».«borelPositivity».{v8_closure_d8baef8c4d61ab0d_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«DatumAndWeyl».«datumAndWeyl».{v8_closure_d8baef8c4d61ab0d_u0})
