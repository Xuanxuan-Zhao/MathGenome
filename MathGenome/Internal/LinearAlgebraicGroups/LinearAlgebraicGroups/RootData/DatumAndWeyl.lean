import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.DatumAndWeyl
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelNormalizer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbstractPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.WeylScheme
import Mathlib.Tactic.Linarith
import Batteries.Tactic.OpenPrivate

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelNormalizer
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

universe u

namespace LinearAlgebraicGroups.RootData.DatumAndWeyl

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Datum Root)
open Specs.BorelNormalizer (InducesTorusConjugation)
open Specs.BorelsAndChambers (IsPositiveSystem)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.NormalizerLatticeAction (ConstantGroup SplitImage)
open Specs.SchemeDerivedGroup (FactorsThrough)

open private isTorus_of_split from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

noncomputable section

private theorem translatedRootEvaluation {Index M N : Type*} [AddCommGroup M]
    [AddCommGroup N] {P : RootDatum Index M N} (a : P.Aut) (f : M →ₗ[ℤ] ℝ)
    (i : Index) :
    f.comp a.weightEquiv.symm.toLinearMap (P.root (a.indexEquiv i)) = f (P.root i) := by
  change f (a.weightEquiv.symm (P.root (a.indexEquiv i))) = _
  rw [← RootPairing.Hom.root_weightMap_apply P P i a.toHom, ← a.weightEquiv_apply,
    LinearEquiv.symm_apply_apply]

/-- A Weyl translate of a regular functional has the root signs of any
other regular functional. Maximize the sum of products of their evaluations on roots. -/
private theorem sameSigns {Index M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (P : RootDatum Index M N) [Finite Index]
    (x y : M →ₗ[ℤ] ℝ) (hx : ∀ i, x (P.root i) ≠ 0) (hy : ∀ i, y (P.root i) ≠ 0) :
    ∃ w : P.weylGroup, ∀ i,
      0 < x (w.val.weightEquiv.symm (P.root i)) ↔ 0 < y (P.root i) := by
  classical
  letI := Fintype.ofFinite Index
  let act (a : P.Aut) (f : M →ₗ[ℤ] ℝ) := f.comp a.weightEquiv.symm.toLinearMap
  let B (f g : M →ₗ[ℤ] ℝ) : ℝ := ∑ i, f (P.root i) * g (P.root i)
  have symmetry (f g : M →ₗ[ℤ] ℝ) : B f g = B g f := by
    simp only [B, mul_comm (f (P.root _))]
  have sub_smul_left (f g c : M →ₗ[ℤ] ℝ) (a : ℝ) :
      B (f - a • c) g = B f g - a * B c g := by
    simp only [B, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  have neg_right (f g : M →ₗ[ℤ] ℝ) : B f (-g) = - B f g := by
    simp only [B, LinearMap.neg_apply, mul_neg, Finset.sum_neg_distrib]
  have invariant (a : P.Aut) (f g : M →ₗ[ℤ] ℝ) : B (act a f) (act a g) = B f g := by
    change (∑ i, act a f (P.root i) * act a g (P.root i)) = _
    rw [← a.indexEquiv.sum_comp]
    simp only [act, translatedRootEvaluation, B]
  -- The score depends on a permutation of a finite set of roots.
  let score (w : P.weylGroup) := B (act w.val x) y
  let scoreOfPerm (σ : Equiv.Perm Index) := ∑ i, x (P.root i) * y (P.root (σ i))
  have hscore (w : P.weylGroup) : score w = scoreOfPerm w.val.indexEquiv := by
    dsimp only [score, scoreOfPerm, B]
    rw [← w.val.indexEquiv.sum_comp]
    simp only [act, translatedRootEvaluation]
  have hf : (Set.range score).Finite := (Set.finite_range scoreOfPerm).subset (by
    rintro _ ⟨w, rfl⟩
    exact ⟨w.val.indexEquiv, (hscore w).symm⟩)
  have hn : (Set.range score).Nonempty := ⟨score 1, 1, rfl⟩
  obtain ⟨m, hm, hmax⟩ := hf.toFinset.exists_max_image id (hf.toFinset_nonempty.mpr hn)
  obtain ⟨w, rfl⟩ := hf.mem_toFinset.mp hm
  refine ⟨w, fun i ↦ ?_⟩
  let z := act w.val x
  let c := (Int.castAddHom ℝ).toIntLinearMap.comp (P.coroot' i)
  let s := RootPairing.weylGroup.ofIdx P i
  have reflection (f : M →ₗ[ℤ] ℝ) : act s.val f = f - f (P.root i) • c := by
    apply LinearMap.ext
    intro t
    have hs : s.val.weightEquiv.symm = P.reflection i := by
      change (RootPairing.Equiv.reflection P i).weightEquiv⁻¹ = _
      rw [← RootPairing.Equiv.weightEquiv_inv, RootPairing.Equiv.reflection_inv,
        RootPairing.Equiv.reflection_weightEquiv]
    change f (s.val.weightEquiv.symm t) = _
    rw [hs, P.reflection_apply]
    simp only [map_sub, map_smul, c, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, Int.coe_castAddHom,
      zsmul_eq_mul, mul_comm (f (P.root i))]
  have ci : c (P.root i) = 2 := by
    change (↑(P.coroot' i (P.root i)) : ℝ) = 2
    rw [P.coroot_root_two]
    norm_num
  have cref : act s.val c = -c := by
    rw [reflection, ci, two_smul, sub_add_eq_sub_sub, sub_self, zero_sub]
  have hnorm : 0 < B c c := by
    have h := Finset.single_le_sum (f := fun j ↦ c (P.root j) * c (P.root j))
      (fun j _ ↦ mul_self_nonneg _) (Finset.mem_univ i)
    rw [ci] at h
    change (2 : ℝ) * 2 ≤ B c c at h
    linarith
  have href := invariant s.val y c
  rw [reflection y, cref, neg_right, sub_smul_left] at href
  have hsign : 2 * B y c = y (P.root i) * B c c := by linarith
  have hcomp : act (s * w).val x = act s.val z := by
    apply LinearMap.ext
    intro t
    change x ((s.val * w.val).weightEquiv.symm t) =
      x (w.val.weightEquiv.symm (s.val.weightEquiv.symm t))
    rw [RootPairing.Equiv.mul_eq_comp, RootPairing.Equiv.weightEquiv_comp_toLin,
      LinearEquiv.symm_trans_apply]
  -- A sign mismatch would increase the score after reflection.
  have hle := hmax (score (s * w)) (hf.mem_toFinset.mpr ⟨s * w, rfl⟩)
  change B (act (s * w).val x) y ≤ B z y at hle
  rw [hcomp, reflection, sub_smul_left, symmetry c y] at hle
  have hprod : 0 ≤ z (P.root i) * B y c := by linarith
  have hz : z (P.root i) ≠ 0 := by
    change act w.val x (P.root i) ≠ 0
    dsimp only [act]
    rw [← w.val.indexEquiv.apply_symm_apply i, translatedRootEvaluation]
    exact hx _
  change 0 < z (P.root i) ↔ 0 < y (P.root i)
  constructor
  · intro hp
    by_contra! hn
    have hyneg := lt_of_le_of_ne hn (hy i)
    have hb : B y c < 0 := by linarith [mul_neg_of_neg_of_pos hyneg hnorm]
    exact (not_lt_of_ge hprod) (mul_neg_of_pos_of_neg hp hb)
  · intro hp
    by_contra! hn
    have hzneg := lt_of_le_of_ne hn hz
    have hb : 0 < B y c := by linarith [mul_pos hp hnorm]
    exact (not_lt_of_ge hprod) (mul_neg_of_neg_of_pos hzneg hb)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}

private theorem rationalSectionsEquiv {Q : GroupScheme k} {W : Type u} [Group W]
    (C : ConstantGroup Q W) :
    ∃ e : W ≃* (𝟙_ (SchemeOver k) ⟶ Q.X), ∀ w, e w = C.sectionPoint w := by
  have hconst (w : W) : C.families (𝟙_ (SchemeOver k)) (C.sectionPoint w) =
      LocallyConstant.const _ w := by
    have h : toUnit (𝟙_ (SchemeOver k)) = 𝟙 (𝟙_ (SchemeOver k)) := by subsingleton
    simpa only [h, Category.id_comp] using C.constant (𝟙_ (SchemeOver k)) w
  let p : (𝟙_ (SchemeOver k)).left := IsLocalRing.closedPoint k
  have hc : Function.Bijective C.sectionPoint := by
    constructor
    · intro a b hab
      have h := (hconst a).symm.trans
        ((congrArg (C.families (𝟙_ (SchemeOver k))) hab).trans (hconst b))
      exact congrArg (fun f : LocallyConstant (𝟙_ (SchemeOver k)).left W ↦ f p) h
    · intro q
      refine ⟨C.families _ q p, (C.families _).injective ?_⟩
      rw [hconst]
      apply LocallyConstant.ext
      intro x
      change C.families _ q p = C.families _ q x
      have hpx : p = x := @Subsingleton.elim (Spec (CommRingCat.of k)) inferInstance p x
      rw [hpx]
  exact ⟨MulEquiv.ofBijective C.sectionPoint hc, fun _ ↦ rfl⟩

private theorem inducedConjugation_unique {g : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    {a b : T.group ≅ T.group}
    (ha : InducesTorusConjugation T g a) (hb : InducesTorusConjugation T g b) : a = b := by
  letI : IsClosedImmersion T.inclusion.hom.hom.left := T.isClosedImmersion
  letI : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
  apply Iso.ext
  apply Grp.hom_ext
  apply (cancel_mono T.inclusion.hom.hom).mp
  exact ha.trans hb.symm

private theorem labelConjugation {N : ClosedSubgroup G.val} {Q : GroupScheme k}
    {q : N.group ⟶ Q} (I : SplitImage T.inclusion N.inclusion q)
    (w : I.labels) (n : 𝟙_ (SchemeOver k) ⟶ N.group.X)
    (hn : n ≫ q.hom.hom = I.constantGroup.sectionPoint w) :
    InducesTorusConjugation T (n ≫ N.inclusion.hom.hom) (I.conjugation w) := by
  have h : toUnit (𝟙_ (SchemeOver k)) = 𝟙 (𝟙_ (SchemeOver k)) := by subsingleton
  have hfamily := I.conjugates _ n w (by simpa only [h, Category.id_comp] using hn)
  have he := congrArg (fun f ↦ lift (𝟙 T.group.X) (toUnit T.group.X) ≫ f) hfamily
  simpa only [InducesTorusConjugation, conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv,
    lift_fst_assoc, lift_snd_assoc, Category.id_comp, Category.assoc] using he.symm

private theorem quotientPoint_eq {N : ClosedSubgroup G.val} {Q : GroupScheme k}
    {q : N.group ⟶ Q} {j : T.group ⟶ N.group} {hj : IsClosedImmersion j.hom.hom.left}
    (hi : j ≫ N.inclusion = T.inclusion) (hker : IsSchemeKernel q ⟨T.group, j, hj⟩)
    (n m : 𝟙_ (SchemeOver k) ⟶ N.group.X)
    (h : FactorsThrough T ((n ≫ N.inclusion.hom.hom)⁻¹ * (m ≫ N.inclusion.hom.hom))) :
    n ≫ q.hom.hom = m ≫ q.hom.hom := by
  letI : IsClosedImmersion N.inclusion.hom.hom.left := N.isClosedImmersion
  letI : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
  obtain ⟨t, ht⟩ := h
  have ht' : t ≫ j.hom.hom = n⁻¹ * m := by
    apply (cancel_mono N.inclusion.hom.hom).mp
    have hji := congrArg (fun a : T.group ⟶ G.val ↦ t ≫ a.hom.hom) hi
    change t ≫ j.hom.hom ≫ N.inclusion.hom.hom = t ≫ T.inclusion.hom.hom at hji
    change t ≫ T.inclusion.hom.hom = _ at ht
    simpa only [Category.assoc, MonObj.mul_comp, GrpObj.inv_comp] using hji.trans ht
  have hq : (t ≫ j.hom.hom) ≫ q.hom.hom = (1 : 𝟙_ (SchemeOver k) ⟶ Q.X) := by
    rw [Category.assoc, hker.w, ← Category.assoc, comp_toUnit]
    rfl
  rw [ht', MonObj.mul_comp, GrpObj.inv_comp, inv_mul_eq_one] at hq
  exact hq

variable [IsCommMonObj T.group.X]

private theorem automorphism_eq_of_weight {D : Datum T} {a b : D.rootDatum.Aut}
    (h : ∀ χ : Character T.group, a.weightEquiv (Additive.ofMul χ) =
      b.weightEquiv (Additive.ofMul χ)) : a = b := by
  apply RootPairing.Equiv.weightHom_injective D.rootDatum
  apply LinearEquiv.ext
  intro x
  exact h (Additive.toMul x)

private theorem actionOnDatum (D : Datum T) {N : ClosedSubgroup G.val} {Q : GroupScheme k}
    {q : N.group ⟶ Q} (I : SplitImage T.inclusion N.inclusion q)
    (hN : RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g))
    (hlift : ∀ w : I.labels, ∃ n : 𝟙_ (SchemeOver k) ⟶ N.group.X,
      n ≫ q.hom.hom = I.constantGroup.sectionPoint w) :
    ∃ A : I.labels →* D.rootDatum.Aut, Function.Injective A ∧
      (∀ w (χ : Character T.group),
        (A w).weightEquiv (Additive.ofMul χ) = Additive.ofMul (w.val χ)) ∧
      (∀ w (cochar : Cocharacter T.group),
        (A w).coweightEquiv.symm (Additive.ofMul cochar) =
          Additive.ofMul (cochar ≫ (I.conjugation w).hom)) := by
  classical
  obtain ⟨N', hN', act, hact⟩ := D.normalizerAction
  have existsAction (w : I.labels) : ∃ a : D.rootDatum.Aut,
      (∀ χ : Character T.group, a.weightEquiv (Additive.ofMul χ) = Additive.ofMul (w.val χ)) ∧
      (∀ cochar : Cocharacter T.group, a.coweightEquiv.symm (Additive.ofMul cochar) =
        Additive.ofMul (cochar ≫ (I.conjugation w).hom)) := by
    obtain ⟨n, hn⟩ := hlift w
    have hnorm := (hN _ _).mpr ⟨n, rfl⟩
    obtain ⟨n', hn'⟩ := (hN' _ _).mp hnorm
    obtain ⟨e, he, hweight, hcochar⟩ := hact n'
    have he' : InducesTorusConjugation T (n ≫ N.inclusion.hom.hom) e := by
      dsimp only [InducesTorusConjugation]
      simpa only [Category.assoc, hn'] using he
    have heq := inducedConjugation_unique he' (labelConjugation I w n hn)
    subst e
    exact ⟨act n', fun χ ↦ by rw [hweight, I.characterAction], hcochar⟩
  choose A hw hc using existsAction
  let F : I.labels →* D.rootDatum.Aut :=
    { toFun := A
      map_one' := automorphism_eq_of_weight (D := D) fun χ ↦ by
        rw [hw]
        rfl
      map_mul' := fun a b ↦ automorphism_eq_of_weight (D := D) fun χ ↦ by
        rw [hw]
        change Additive.ofMul (a.val (b.val χ)) =
          ((A a).weightEquiv * (A b).weightEquiv) (Additive.ofMul χ)
        rw [RootPairing.Equiv.weightEquiv_mul, LinearEquiv.trans_apply, hw, hw] }
  refine ⟨F, ?_, hw, hc⟩
  intro a b hab
  change A a = A b at hab
  apply Subtype.ext
  apply MulEquiv.ext
  intro χ
  apply Additive.ofMul.injective
  rw [← hw a, ← hw b, hab]

private theorem reflectionConjugation (D : Datum T) (i : Root T) :
    ∃ (g : 𝟙_ (SchemeOver k) ⟶ G.val.X), Normalizes T.inclusion g ∧
      ∃ e : T.group ≅ T.group, InducesTorusConjugation T g e ∧
        ∀ χ : Character T.group,
          (RootPairing.Equiv.reflection D.rootDatum i).weightEquiv (Additive.ofMul χ) =
            Additive.ofMul (e.inv ≫ χ) := by
  obtain ⟨C, cochar, _, _, Dpos, Dneg, _, Q, F, P, A, p, n, _, _, h⟩ := D.attached i
  dsimp only at h
  obtain ⟨_, _, r, hr⟩ := h
  refine ⟨r.representative, r.normalizes, r.conjugation, r.conjugates, fun χ ↦ ?_⟩
  have hpair : D.rootDatum.coroot' i (Additive.ofMul χ) =
      CharacterPairing.pairing T.group χ r.coroot := by
    rw [hr]
    exact D.pairing_eq χ (Additive.toMul (D.rootDatum.coroot i))
  rw [RootPairing.Equiv.reflection_weightEquiv, RootPairing.reflection_apply, hpair,
    D.root_eq, r.reflection, ofMul_mul, ofMul_zpow, neg_smul, sub_eq_add_neg]

private def positiveSystem (x : Additive (Character T.group) →ₗ[ℤ] ℝ) : Set (Root T) :=
  {i | 0 < x (Additive.ofMul i.val)}

private theorem positiveSystem_image (D : Datum T) (a : D.rootDatum.Aut)
    (f : Character T.group → Character T.group)
    (hf : ∀ χ, a.weightEquiv (Additive.ofMul χ) = Additive.ofMul (f χ))
    (x : Additive (Character T.group) →ₗ[ℤ] ℝ) :
    f '' (Subtype.val '' positiveSystem x) =
      Subtype.val '' positiveSystem (x.comp a.weightEquiv.symm.toLinearMap) := by
  have hroot (i : Root T) : f i.val = (a.indexEquiv i).val := by
    apply Additive.ofMul.injective
    rw [← hf, ← D.root_eq, ← D.root_eq]
    exact (RootPairing.Hom.root_weightMap_apply D.rootDatum D.rootDatum i a.toHom)
  have hsign (i : Root T) : a.indexEquiv i ∈
      positiveSystem (x.comp a.weightEquiv.symm.toLinearMap) ↔ i ∈ positiveSystem x := by
    simp only [positiveSystem, Set.mem_ofPred_eq, ← D.root_eq, translatedRootEvaluation]
  ext χ
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨a.indexEquiv i, (hsign i).mpr hi, (hroot i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    let j := a.indexEquiv.symm i
    have hj : a.indexEquiv j = i := a.indexEquiv.apply_symm_apply i
    exact ⟨j.val, ⟨j, (hsign j).mp (hj.symm ▸ hi), rfl⟩, (hroot j).trans (congrArg Subtype.val hj)⟩

/-- The identification of the root datum Weyl group with the constant
normalizer quotient, conditional on the ordered upstream propositions. -/
theorem datumAndWeyl_conditional
    (_ : BorelNormalizer.BorelNormalizerIntersection.{u})
    (_ : BorelNormalizer.GeometricBorelNormalizer.{u})
    (_ : BorelNormalizer.GeometricWeylSimplyTransitiveOnBorels.{u})
    (_ : BorelNormalizer.GroundFieldBorelNormalizer.{u})
    (_ : BorelNormalizer.LieQuotientZeroWeight.{u})
    (_ : BorelNormalizer.WeylSimplyTransitiveOnBorels.{u})
    (hPositive : BorelNormalizer.WeylSimplyTransitiveOnPositiveSystems.{u}) :
    Specs.DatumAndWeyl.Statement.{u} := by
  classical
  intro k _ G hG T hT hmax
  obtain ⟨hComm, hD⟩ :=
    LinearAlgebraicGroups.RootData.AbstractPairing.abstractPairing G hG T hT hmax
  letI := hComm
  obtain ⟨D⟩ := hD
  letI := D.finiteRoots
  obtain ⟨N, j, hj, W, q, hN, hi, hq, hfinite, hetale, _, hsplit⟩ :=
    Reductive.WeylScheme.weylScheme G hG T (isTorus_of_split hT) hmax
  obtain ⟨⟨I⟩, hlift⟩ := hsplit hT
  have liftLabel (w : I.labels) := (hlift (I.constantGroup.sectionPoint w)).2
  obtain ⟨sectionEquiv, hsection⟩ := rationalSectionsEquiv I.constantGroup
  obtain ⟨A, hA, hweight, hcochar⟩ := actionOnDatum D I hN liftLabel
  have inclusion : D.rootDatum.weylGroup ≤ A.range := by
    change Subgroup.closure (Set.range (RootPairing.Equiv.reflection D.rootDatum)) ≤ A.range
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨g, hg, e, he, hreflect⟩ := reflectionConjugation D i
    obtain ⟨n, hn⟩ := (hN _ _).mp hg
    obtain ⟨w, hw⟩ := sectionEquiv.surjective (n ≫ q.hom.hom)
    rw [hsection] at hw
    have he' := labelConjugation I w n hw.symm
    rw [hn] at he'
    have heq := inducedConjugation_unique he' he
    refine ⟨w, automorphism_eq_of_weight (D := D) fun χ ↦ ?_⟩
    rw [hweight, I.characterAction, heq, hreflect]
  obtain ⟨⟨S, hS⟩, _, hsimply⟩ := hPositive G hG T hT hmax
  have sameLabel {S₁ S₂ : Set (Root T)} (h₁ : IsPositiveSystem T S₁) (h₂ : IsPositiveSystem T S₂)
      {a b : I.labels} (ha : (fun χ ↦ a.val χ) '' (Subtype.val '' S₁) = Subtype.val '' S₂)
      (hb : (fun χ ↦ b.val χ) '' (Subtype.val '' S₁) = Subtype.val '' S₂) : a = b := by
    obtain ⟨g, e, hg, _, _, hfree⟩ := hsimply S₁ S₂ h₁ h₂
    obtain ⟨n, hn⟩ := (hN _ _).mp hg
    have hcompare (w : I.labels)
        (hw : (fun χ ↦ w.val χ) '' (Subtype.val '' S₁) = Subtype.val '' S₂) :
        n ≫ q.hom.hom = I.constantGroup.sectionPoint w := by
      obtain ⟨m, hm⟩ := liftLabel w
      have hnorm := (hN _ _).mpr ⟨m, rfl⟩
      have hconj := labelConjugation I w m hm
      have hfactor := (hfree _ _ hnorm hconj).mp (by simpa only [← I.characterAction] using hw)
      rw [← hn] at hfactor
      exact (quotientPoint_eq hi hq.1 n m hfactor).trans hm
    apply sectionEquiv.injective
    simpa only [hsection] using (hcompare a ha).symm.trans (hcompare b hb)
  obtain ⟨x, hRegular, _⟩ := hS
  have hx (i : Root T) : x (D.rootDatum.root i) ≠ 0 := by
    rw [D.root_eq]
    exact hRegular i
  have isPositive (f : Additive (Character T.group) →ₗ[ℤ] ℝ)
      (hf : ∀ i : Root T, f (D.rootDatum.root i) ≠ 0) :
      IsPositiveSystem T (positiveSystem f) :=
    ⟨f, fun i ↦ by simpa only [D.root_eq] using hf i, rfl⟩
  have allMem (w : I.labels) : A w ∈ D.rootDatum.weylGroup := by
    let y := x.comp (A w).weightEquiv.symm.toLinearMap
    have hy (i : Root T) : y (D.rootDatum.root i) ≠ 0 := by
      change (x.comp (A w).weightEquiv.symm.toLinearMap) (D.rootDatum.root i) ≠ 0
      rw [← (A w).indexEquiv.apply_symm_apply i, translatedRootEvaluation]
      exact hx _
    obtain ⟨v, hv⟩ := sameSigns D.rootDatum x y hx hy
    obtain ⟨v', hv'⟩ := inclusion v.property
    have hsigns : positiveSystem (x.comp v.val.weightEquiv.symm.toLinearMap) = positiveSystem y := by
      ext i
      simpa only [positiveSystem, Set.mem_ofPred_eq, ← D.root_eq, LinearMap.comp_apply,
        LinearEquiv.coe_coe] using hv i
    have hw := positiveSystem_image D (A w) _ (hweight w) x
    have hv'Image := positiveSystem_image D (A v') _ (hweight v') x
    rw [hv', hsigns] at hv'Image
    have heq := sameLabel (isPositive x hx) (isPositive y hy) hw hv'Image
    rw [heq, hv']
    exact v.property
  let F : I.labels →* D.rootDatum.weylGroup := A.codRestrict _ allMem
  have hF : Function.Bijective F := by
    refine ⟨fun a b hab ↦ hA (congrArg Subtype.val hab), ?_⟩
    intro v
    obtain ⟨w, hw⟩ := inclusion v.property
    exact ⟨w, Subtype.ext hw⟩
  let e := (MulEquiv.ofBijective F hF).symm
  have he (v : D.rootDatum.weylGroup) : A (e v) = v.val :=
    congrArg Subtype.val (e.symm_apply_apply v)
  refine ⟨hComm, D, ⟨⟨N, j, hj, W, q, hN, hi, hq, hfinite, hetale, I, e, ?_, ?_⟩⟩⟩
  · intro v χ
    rw [← he v, hweight]
  · intro v cochar
    rw [← he v, hcochar]

end

end LinearAlgebraicGroups.RootData.DatumAndWeyl

universe v8_closure_19b040e3f9bb51ab_u0
theorem _root_.«LinearAlgebraicGroups».«RootData».«DatumAndWeyl».«datumAndWeyl» : _root_.«LinearAlgebraicGroups».«Specs».«DatumAndWeyl».«Statement».{v8_closure_19b040e3f9bb51ab_u0} :=
  @_root_.«LinearAlgebraicGroups».«RootData».«DatumAndWeyl».«datumAndWeyl_conditional».{v8_closure_19b040e3f9bb51ab_u0} (@_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«borelNormalizerIntersection».{v8_closure_19b040e3f9bb51ab_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«geometricBorelNormalizer».{v8_closure_19b040e3f9bb51ab_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«geometricWeylSimplyTransitiveOnBorels».{v8_closure_19b040e3f9bb51ab_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«groundFieldBorelNormalizer».{v8_closure_19b040e3f9bb51ab_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«lieQuotientZeroWeight».{v8_closure_19b040e3f9bb51ab_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«weylSimplyTransitiveOnBorels».{v8_closure_19b040e3f9bb51ab_u0}) (@_root_.«LinearAlgebraicGroups».«RootData».«BorelNormalizer».«weylSimplyTransitiveOnPositiveSystems».{v8_closure_19b040e3f9bb51ab_u0})
