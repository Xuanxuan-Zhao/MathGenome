import Specs.LinearAlgebraicGroups.Flag.OpenCell
import LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
import LinearAlgebraicGroups.Solvable.WordDomainGeometry
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.RootData.BorelPositivity
import LinearAlgebraicGroups.RootData.BorelsAndChambers
import LinearAlgebraicGroups.RootData.OrderedRootProducts
import LinearAlgebraicGroups.RootData.SimpleRoots

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups.Flag.OpenCell

open _root_.LinearAlgebraicGroups.Specs
open Specs.OpenCell (cellMap translatedCellMap doubleOrbitMap InFppfDoubleOrbit)
open OrderedRootProducts (Enumerates RootSubgroupFamily Parametrizes rootCellMap)
open CocharacterDynamics (multiplyFactors)
open AbstractPairing (Datum Root)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open CharacterDescent (Cocharacter)
open CharacterPairing (pairing)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem cellMap_comp {T B Bneg : ClosedSubgroup G.val}
    {Uneg : ClosedSubgroup Bneg.group} {Upos : ClosedSubgroup B.group}
    {R : RootSubgroupFamily T} {Lneg Lpos : List (Root T)}
    (en : Parametrizes R Lneg (Uneg.inclusion.hom.hom ≫ Bneg.inclusion.hom.hom))
    (ep : Parametrizes R Lpos (Upos.inclusion.hom.hom ≫ B.inclusion.hom.hom))
    (ho : IsOpenImmersion (rootCellMap T R Lneg Lpos).left) :
    IsOpenImmersion (cellMap T Uneg Upos).left := by
  obtain ⟨en, hn⟩ := en
  obtain ⟨ep, hp⟩ := ep
  let e := tensorIso en (tensorIso (Iso.refl T.group.X) ep)
  have he : e.hom ≫ cellMap T Uneg Upos = rootCellMap T R Lneg Lpos := by
    simp only [e, tensorIso_hom, Iso.refl_hom, cellMap, rootCellMap, multiplyFactors,
      MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc,
      Category.id_comp]
    change (fst _ _ ≫ en.hom ≫ Uneg.inclusion.hom.hom ≫ Bneg.inclusion.hom.hom) *
      ((snd _ _ ≫ fst _ _ ≫ T.inclusion.hom.hom) *
        (snd _ _ ≫ snd _ _ ≫ ep.hom ≫ Upos.inclusion.hom.hom ≫ B.inclusion.hom.hom)) = _
    rw [hn, hp]
  let f := Over.forget (Spec (CommRingCat.of k))
  have h := congrArg (fun m => f.map m) he
  rw [f.map_comp] at h
  change IsOpenImmersion (f.map (rootCellMap T R Lneg Lpos)) at ho
  rw [← h] at ho
  exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion
    (f.map e.hom) (f.map (cellMap T Uneg Upos))).mp ho

private def leftTranslation {A : SchemeOver k} [GrpObj A]
    (n : 𝟙_ (SchemeOver k) ⟶ A) : A ≅ A where
  hom := (toUnit _ ≫ n) * 𝟙 A
  inv := (toUnit _ ≫ n⁻¹) * 𝟙 A
  hom_inv_id := by
    simp only [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, ← mul_assoc]
    rw [← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one]
    exact one_mul _
  inv_hom_id := by
    simp only [MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, ← mul_assoc]
    rw [← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one]
    exact one_mul _

private theorem conjugationByPoint (H : GroupScheme k) (n : 𝟙_ (SchemeOver k) ⟶ H.X) :
    ∃ σ : H ≅ H, ∀ {Y : SchemeOver k} (p : Y ⟶ H.X),
      p ≫ σ.hom.hom.hom = (toUnit Y ≫ n) * p * (toUnit Y ≫ n)⁻¹ := by
  let e := (leftTranslation n).trans (GrpObj.mulRight n⁻¹)
  have he {Y : SchemeOver k} (p : Y ⟶ H.X) :
      p ≫ e.hom = (toUnit Y ≫ n) * p * (toUnit Y ≫ n)⁻¹ := by
    simp only [e, Iso.trans_hom, leftTranslation, GrpObj.mulRight, ← Hom.mul_def,
      MonObj.comp_mul, comp_toUnit_assoc, Category.comp_id, GrpObj.comp_inv]
  refine ⟨Grp.mkIso e ?_ ?_, fun p ↦ he p⟩
  · rw [he]
    let c : (𝟙_ (SchemeOver k)) ⟶ H.X := toUnit _ ≫ n
    change c * 1 * c⁻¹ = 1
    group
  · have hfac : (fst H.X H.X * snd H.X H.X : _ ⟶ H.X) = μ[H.X] := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    have hmap : (e.hom ⊗ₘ e.hom) ≫ μ[H.X] =
        (fst H.X H.X ≫ e.hom) * (snd H.X H.X ≫ e.hom) := by
      rw [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]
    rw [he, hmap, he, he, ← hfac]
    group

private theorem translatedCellOpen {T B Bneg : ClosedSubgroup G.val}
    {Uneg : ClosedSubgroup Bneg.group} {Upos : ClosedSubgroup B.group}
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (h : IsOpenImmersion (cellMap T Uneg Upos).left) :
    IsOpenImmersion (translatedCellMap T Uneg Upos n).left := by
  have he : translatedCellMap T Uneg Upos n = cellMap T Uneg Upos ≫ (leftTranslation n).hom := by
    simp [translatedCellMap, leftTranslation, MonObj.comp_mul, comp_toUnit_assoc]
  rw [he]
  exact IsOpenImmersion.comp _ _

/-- A monomorphism of test schemes has the same sections as its fppf image. -/
private theorem factors_of_locallyFactors {X Y Z : SchemeOver k} (m : X ⟶ Z) [Mono m]
    (g : Y ⟶ Z) (S : Sieve Y) (hS : S ∈ Fppf.schemeTopology k Y)
    (h : ∀ {V} (p : V ⟶ Y), S p → ∃ y, y ≫ m = p ≫ g) :
    ∃ y, y ≫ m = g := by
  classical
  let v : S.arrows.FamilyOfElements (yoneda.obj X) := fun _ p hp ↦ (h p hp).choose
  have hv {V} (p : V ⟶ Y) (hp : S p) : v p hp ≫ m = p ≫ g := (h p hp).choose_spec
  have hcompat : v.Compatible := by
    intro A B W p q a b ha hb hab
    apply (cancel_mono m).mp
    change (p ≫ v a ha) ≫ m = (q ≫ v b hb) ≫ m
    rw [Category.assoc, Category.assoc, hv a ha, hv b hb, ← Category.assoc,
      ← Category.assoc, hab]
  have sheaf (T : SchemeOver k) : Presieve.IsSheaf (Fppf.schemeTopology k) (yoneda.obj T) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  obtain ⟨y, hy, -⟩ := sheaf X S hS v hcompat
  refine ⟨y, ?_⟩
  have hsep := (sheaf Z S hS).isSeparatedFor
  apply hsep.ext
  intro V p hp
  change p ≫ (y ≫ m) = p ≫ g
  have hres : p ≫ y = v p hp := hy p hp
  rw [← Category.assoc, hres, hv p hp]

private theorem inDoubleOrbit_iff_of_factorizations {X : SchemeOver k}
    {B : ClosedSubgroup G.val} {n : 𝟙_ (SchemeOver k) ⟶ G.val.X}
    (m : X ⟶ G.val.X) [Mono m]
    (a : X ⟶ B.group.X ⊗ B.group.X) (b : B.group.X ⊗ B.group.X ⟶ X)
    (ha : a ≫ doubleOrbitMap B n = m) (hb : b ≫ m = doubleOrbitMap B n)
    {Y : SchemeOver k} (g : Y ⟶ G.val.X) :
    (∃ y, y ≫ m = g) ↔ InFppfDoubleOrbit B n g := by
  let S := (Sieve.generate (Presieve.singleton (doubleOrbitMap B n))).pullback g
  change _ ↔ S ∈ Fppf.schemeTopology k Y
  constructor
  · rintro ⟨y, rfl⟩
    have hs : (⊤ : Sieve Y) ≤
        (Sieve.generate (Presieve.singleton (doubleOrbitMap B n))).pullback (y ≫ m) := by
      intro V p _
      exact ⟨_, p ≫ y ≫ a, _, ⟨⟩, by simp [ha]⟩
    exact (Fppf.schemeTopology k).superset_covering hs ((Fppf.schemeTopology k).top_mem Y)
  · intro hS
    apply factors_of_locallyFactors m g S hS
    rintro V p ⟨W, q, _, ⟨⟩, hq⟩
    exact ⟨q ≫ b, by rw [Category.assoc, hb, hq]⟩

section WeylLength

open Specs.SimpleRoots (inversions positive wordLength)
open RootPairing
open private length_inverse rightInversions rightInversions_card_mul
  from LinearAlgebraicGroups.RootData.SimpleRoots

variable {I M N : Type u} [AddCommGroup M] [AddCommGroup N]
    {P : RootPairing I ℤ M N} [Finite I]

private theorem support_subset_of_same_positives (b b' : P.Base)
    (h : ∀ i, b.IsPos i ↔ b'.IsPos i) : b.support ⊆ b'.support := by
  intro i hi
  have hp := (h i).mp (b.isPos_of_mem_support hi)
  have he := hp.induction_on_add
    (p := fun a => b'.IsPos a ∧ (a ∈ b.support → a ∈ b'.support))
    (fun j hj => ⟨b'.isPos_of_mem_support hj, fun _ => hj⟩)
    (fun j l a ha hj hl => ⟨hj.1.add (b'.isPos_of_mem_support hl) ha, fun hs => by
      have hj' := b.isPos_iff.mp ((h j).mpr hj.1)
      have hl' := b.isPos_iff.mp ((h l).mpr (b'.isPos_of_mem_support hl))
      have hsimple := b.height_one_of_mem_support hs
      have hsum := b.height_add ha
      omega⟩)
  exact he.2 hi

private theorem base_eq_of_same_positives (b b' : P.Base)
    (h : ∀ i, b.IsPos i ↔ b'.IsPos i) : b = b' := by
  have he : b.support = b'.support := Finset.Subset.antisymm
    (support_subset_of_same_positives b b' h)
    (support_subset_of_same_positives b' b fun i => (h i).symm)
  cases b
  cases b'
  cases he
  rfl

omit [Finite I] in
private theorem rootOfNeg :
    letI := P.indexNeg
    ∀ i : I, P.root (-i) = -P.root i := by
  intro i
  change P.root (P.reflectionPerm i i) = -P.root i
  rw [P.root_reflectionPerm, P.reflection_apply_self]

/-- A simple root that stays positive would add one inversion after
multiplication by its reflection, contradicting maximal length. -/
private theorem longest_flips_sign [Module.Free ℤ M] [Module.Finite ℤ M] [P.IsReduced]
    (b : P.Base) (f : M →ₗ[ℤ] ℤ) (hf : ∀ i, f (P.root i) ≠ 0)
    (hb : ∀ i, b.IsPos i ↔ i ∈ positive P f) (w : P.weylGroup)
    (hw : ∀ v : P.weylGroup, wordLength P b v ≤ wordLength P b w) (i : I) :
    b.IsPos (P.weylGroupToPerm w i) ↔ ¬ b.IsPos i := by
  obtain ⟨b', hb'⟩ := RootData.SimpleRoots.baseFor P f hf
  have he : b = b' := base_eq_of_same_positives b b'
    fun j => (hb j).trans (hb'.positive_iff j).symm
  subst b'
  have length_eq (v : P.weylGroup) : wordLength P b v = (rightInversions P f v).ncard := by
    rw [← length_inverse P b v, hb'.length_eq]
    simp only [inversions, rightInversions, inv_inv]
  have simple (j : b.support) : ¬ b.IsPos (P.weylGroupToPerm w j.val) := by
    intro hj
    have h := hw (w * RootPairing.weylGroup.ofIdx P j.val)
    simp only [length_eq] at h
    rw [rightInversions_card_mul P b f hb w j ((hb _).mp hj)] at h
    omega
  let := P.indexNeg
  have negative_of_positive {j : I} (hj : b.IsPos j) :
      ¬ b.IsPos (P.weylGroupToPerm w j) := by
    have h : b.IsPos (-(P.weylGroupToPerm w j)) := by
      refine hj.induction_on_add (p := fun a => b.IsPos (-(P.weylGroupToPerm w a))) ?_ ?_
      · intro a ha
        exact (Base.IsPos.neg_iff_not b _).mpr (simple ⟨a, ha⟩)
      · intro a c d hd ha hc
        apply ha.add ((Base.IsPos.neg_iff_not b _).mpr (simple ⟨c, hc⟩))
        simp only [rootOfNeg, ← P.weylGroup_apply_root, hd, smul_add, neg_add_rev]
        abel
    exact (Base.IsPos.neg_iff_not b _).mp h
  constructor
  · intro hi' hi
    exact negative_of_positive hi hi'
  · intro hi
    have h := negative_of_positive ((Base.IsPos.neg_iff_not b i).mpr hi)
    have hperm : P.weylGroupToPerm w (-i) = -(P.weylGroupToPerm w i) := by
      apply P.root.injective
      rw [← P.weylGroup_apply_root, rootOfNeg, smul_neg, P.weylGroup_apply_root, rootOfNeg]
    rwa [hperm, Base.IsPos.neg_iff_not, not_not] at h

end WeylLength

private theorem monoInclusion {H : GroupScheme k} (A : ClosedSubgroup H) :
    Mono A.inclusion := by
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have : IsClosedImmersion (F.map A.inclusion) := A.isClosedImmersion
  exact F.mono_of_mono_map inferInstance

private theorem radicalIso {H : AffineAlgebraicGroup k} {A B : ClosedSubgroup H.val}
    (hA : GeometricRadicals.IsUnipotentRadical H A)
    (hB : GeometricRadicals.IsUnipotentRadical H B) :
    ∃ e : A.group ≅ B.group, e.hom ≫ B.inclusion = A.inclusion := by
  obtain ⟨f, hf⟩ := hB.2.2 A hA.1 hA.2.1
  obtain ⟨g, hg⟩ := hA.2.2 B hB.1 hB.2.1
  have := monoInclusion A
  have := monoInclusion B
  exact ⟨⟨f, g, (cancel_mono A.inclusion).mp (by simp [hf, hg]),
    (cancel_mono B.inclusion).mp (by simp [hf, hg])⟩, hf⟩

set_option backward.isDefEq.respectTransparency false in
private theorem radicalProductFor {T B : ClosedSubgroup G.val}
    {U V : ClosedSubgroup B.group} (R : RootSubgroupFamily T) (l : List (Root T))
    (hU : GeometricRadicals.IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup B) U)
    (hV : GeometricRadicals.IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup B) V)
    (hp : Parametrizes R l (V.inclusion.hom.hom ≫ B.inclusion.hom.hom)) :
    Parametrizes R l (U.inclusion.hom.hom ≫ B.inclusion.hom.hom) := by
  obtain ⟨e, he⟩ := radicalIso hV hU
  obtain ⟨j, hj⟩ := hp
  let F := Grp.forget (SchemeOver k)
  refine ⟨j.trans (F.mapIso e), ?_⟩
  have hmap := congrArg F.map he
  rw [F.map_comp] at hmap
  change j.hom ≫ F.map e.hom ≫ F.map U.inclusion ≫ F.map B.inclusion = _
  rw [← Category.assoc (F.map e.hom), hmap]
  exact hj

private theorem existsEnumeration {I : Type u} [Finite I] (S : Set I) :
    ∃ l : List I, Enumerates l S := by
  classical
  let fs := (Set.toFinite S).toFinset
  exact ⟨fs.toList, Finset.nodup_toList _, fun i ↦ by simp [fs]⟩

private theorem matchClosedCharts {T B : ClosedSubgroup G.val} {U : ClosedSubgroup B.group}
    {C : ClosedSubgroup G.val} (R : RootSubgroupFamily T) (l : List (Root T))
    (hc : Parametrizes R l C.inclusion.hom.hom)
    (hu : Parametrizes R l (U.inclusion.hom.hom ≫ B.inclusion.hom.hom)) :
    ∃ e : C.group.X ≅ U.group.X,
      e.hom ≫ U.inclusion.hom.hom ≫ B.inclusion.hom.hom = C.inclusion.hom.hom := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨u, hu⟩ := hu
  exact ⟨c.symm.trans u, by
    change (c.inv ≫ u.hom) ≫ U.inclusion.hom.hom ≫ B.inclusion.hom.hom = _
    rw [Category.assoc, hu, ← hc, c.inv_hom_id_assoc]⟩

private theorem testSplit {B : ClosedSubgroup G.val} {T : ClosedSubgroup G.val}
    {U : ClosedSubgroup B.group} (j : T.group ⟶ B.group)
    [IsIso (multiplyFactors j U.inclusion)] {Y : SchemeOver k}
    (b : Y ⟶ B.group.X) :
    ∃ (t : Y ⟶ T.group.X) (u : Y ⟶ U.group.X),
      b = (t ≫ j.hom.hom) * (u ≫ U.inclusion.hom.hom) := by
  let z := b ≫ inv (multiplyFactors j U.inclusion)
  exact ⟨z ≫ fst _ _, z ≫ snd _ _, by
    change b = (z ≫ fst _ _ ≫ j.hom.hom) * (z ≫ snd _ _ ≫ U.inclusion.hom.hom)
    rw [← MonObj.comp_mul, ← multiplyFactors]
    dsimp only [z]
    rw [Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]⟩

private theorem ambientSplit {T B : ClosedSubgroup G.val} {U : ClosedSubgroup B.group}
    {j : T.group ⟶ B.group} (hj : j ≫ B.inclusion = T.inclusion)
    [IsIso (multiplyFactors j U.inclusion)]
    {Y : SchemeOver k} (b : Y ⟶ B.group.X) :
    ∃ (t : Y ⟶ T.group.X) (u : Y ⟶ U.group.X),
      b ≫ B.inclusion.hom.hom =
        (t ≫ T.inclusion.hom.hom) * (u ≫ U.inclusion.hom.hom ≫ B.inclusion.hom.hom) := by
  obtain ⟨t, u, h⟩ := testSplit (U := U) j b
  refine ⟨t, u, ?_⟩
  have hj' : j.hom.hom ≫ B.inclusion.hom.hom = T.inclusion.hom.hom :=
    congrArg (fun f : T.group ⟶ G.val ↦ f.hom.hom) hj
  rw [h, MonObj.mul_comp, Category.assoc, Category.assoc, hj']

/-- Test-scheme factorization of the double orbit once conjugation on the
opposite radical and on the torus has been identified. -/
private theorem translatedDoubleOrbit {T B Bneg : ClosedSubgroup G.val}
    {Uneg : ClosedSubgroup Bneg.group} {Upos : ClosedSubgroup B.group}
    {j : T.group ⟶ B.group} (hj : j ≫ B.inclusion = T.inclusion)
    [IsIso (multiplyFactors j Upos.inclusion)]
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X)
    (c : T.group ≅ T.group) (e : Uneg.group.X ≅ Upos.group.X)
    (hc : c.hom.hom.hom ≫ T.inclusion.hom.hom =
      (toUnit _ ≫ n) * T.inclusion.hom.hom * (toUnit _ ≫ n)⁻¹)
    (he : e.hom ≫ Upos.inclusion.hom.hom ≫ B.inclusion.hom.hom =
      (toUnit _ ≫ n) * (Uneg.inclusion.hom.hom ≫ Bneg.inclusion.hom.hom) *
        (toUnit _ ≫ n)⁻¹)
    (ho : IsOpenImmersion (translatedCellMap T Uneg Upos n).left)
    {Y : SchemeOver k} (g : Y ⟶ G.val.X) :
    (∃ y, y ≫ translatedCellMap T Uneg Upos n = g) ↔ InFppfDoubleOrbit B n g := by
  let m := translatedCellMap T Uneg Upos n
  let X := Uneg.group.X ⊗ (T.group.X ⊗ Upos.group.X)
  have cellEval {S : SchemeOver k} (a : S ⟶ Uneg.group.X) (t : S ⟶ T.group.X)
      (u : S ⟶ Upos.group.X) :
      lift a (lift t u) ≫ m = (toUnit S ≫ n) *
        ((a ≫ Uneg.inclusion.hom.hom ≫ Bneg.inclusion.hom.hom) *
          ((t ≫ T.inclusion.hom.hom) * (u ≫ Upos.inclusion.hom.hom ≫ B.inclusion.hom.hom))) := by
    simp [m, translatedCellMap, cellMap, multiplyFactors, MonObj.comp_mul,
      comp_toUnit_assoc, lift_fst_assoc, lift_snd_assoc]
  have orbitEval {S : SchemeOver k} (x y : S ⟶ B.group.X) :
      lift x y ≫ doubleOrbitMap B n =
        (x ≫ B.inclusion.hom.hom) * (toUnit S ≫ n) * (y ≫ B.inclusion.hom.hom) := by
    simp [doubleOrbitMap, MonObj.comp_mul, comp_toUnit_assoc, lift_fst_assoc, lift_snd_assoc]
  have conjugateT {S : SchemeOver k} (t : S ⟶ T.group.X) :
      t ≫ c.inv.hom.hom ≫ T.inclusion.hom.hom =
        (toUnit S ≫ n)⁻¹ * (t ≫ T.inclusion.hom.hom) * (toUnit S ≫ n) := by
    have hh := congrArg (fun f ↦ (t ≫ c.inv.hom.hom) ≫ f) hc
    have hid : c.inv.hom.hom ≫ c.hom.hom.hom = 𝟙 T.group.X :=
      (Grp.forget (SchemeOver k)).mapIso c |>.inv_hom_id
    simp only [Category.assoc, reassoc_of% hid, MonObj.comp_mul,
      GrpObj.comp_inv, comp_toUnit_assoc] at hh
    rw [hh]
    group
  have conjugateU {S : SchemeOver k} (u : S ⟶ Upos.group.X) :
      u ≫ e.inv ≫ Uneg.inclusion.hom.hom ≫ Bneg.inclusion.hom.hom =
        (toUnit S ≫ n)⁻¹ * (u ≫ Upos.inclusion.hom.hom ≫ B.inclusion.hom.hom) * (toUnit S ≫ n) := by
    have hh := congrArg (fun f ↦ (u ≫ e.inv) ≫ f) he
    simp only [Category.assoc, Iso.inv_hom_id_assoc, MonObj.comp_mul, GrpObj.comp_inv,
      comp_toUnit_assoc] at hh
    rw [hh]
    group
  have forward (a : X ⟶ Uneg.group.X) (t : X ⟶ T.group.X) (u : X ⟶ Upos.group.X) :
      ∃ f : X ⟶ B.group.X ⊗ B.group.X, f ≫ doubleOrbitMap B n = lift a (lift t u) ≫ m := by
    refine ⟨lift (a ≫ e.hom ≫ Upos.inclusion.hom.hom)
      ((t ≫ j.hom.hom) * (u ≫ Upos.inclusion.hom.hom)), ?_⟩
    have ht : j.hom.hom ≫ B.inclusion.hom.hom = T.inclusion.hom.hom :=
      congrArg (fun f : T.group ⟶ G.val ↦ f.hom.hom) hj
    rw [orbitEval, MonObj.mul_comp, Category.assoc t, ht, cellEval]
    simp only [Category.assoc]
    rw [he, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc]
    group
  have backward (b₁ b₂ : B.group.X ⊗ B.group.X ⟶ B.group.X) :
      ∃ f : B.group.X ⊗ B.group.X ⟶ X, f ≫ m = lift b₁ b₂ ≫ doubleOrbitMap B n := by
    obtain ⟨t₁, u₁, h₁⟩ := ambientSplit (U := Upos) hj b₁⁻¹
    obtain ⟨t₂, u₂, h₂⟩ := ambientSplit (U := Upos) hj b₂
    have hh : b₁ ≫ B.inclusion.hom.hom =
        (u₁⁻¹ ≫ Upos.inclusion.hom.hom ≫ B.inclusion.hom.hom) *
          (t₁⁻¹ ≫ T.inclusion.hom.hom) := by
      rw [GrpObj.inv_comp] at h₁
      rw [inv_eq_iff_eq_inv] at h₁
      simp only [h₁, mul_inv_rev, GrpObj.inv_comp]
    refine ⟨lift (u₁⁻¹ ≫ e.inv) (lift ((t₁⁻¹ ≫ c.inv.hom.hom) * t₂) u₂), ?_⟩
    rw [cellEval, orbitEval, MonObj.mul_comp, hh, h₂]
    simp only [Category.assoc, conjugateT, conjugateU]
    group
  obtain ⟨a, ha⟩ := forward (fst _ _) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _)
  obtain ⟨b, hb⟩ := backward (fst _ _) (snd _ _)
  have : IsOpenImmersion m.left := ho
  have : Mono m := Over.mono_of_mono_left _
  apply inDoubleOrbit_iff_of_factorizations m a b _ _ g
  · have hId : lift (fst Uneg.group.X (T.group.X ⊗ Upos.group.X))
        (lift (snd Uneg.group.X (T.group.X ⊗ Upos.group.X) ≫ fst T.group.X Upos.group.X)
          (snd Uneg.group.X (T.group.X ⊗ Upos.group.X) ≫ snd T.group.X Upos.group.X)) = 𝟙 X := by
      rw [← comp_lift, lift_fst_snd, Category.comp_id, lift_fst_snd]
    exact ha.trans (congrArg (· ≫ m) hId |>.trans (Category.id_comp _))
  · simpa only [lift_fst_snd, Category.id_comp] using hb

open CocharacterDynamics (oppositeCocharacter unitPoint)
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private opposite_point pointHom unitEquiv unitPointHom_apply unitPoint_inv
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private theorem oppositeCocharacter_eq_inv {H : GroupScheme k} [IsCommMonObj H.X]
    (c : Cocharacter H) : oppositeCocharacter c = c⁻¹ := by
  apply Grp.hom_ext
  apply hom_ext_of_points (isAffine_Spec _)
  intro R p
  let t := unitEquiv R p
  have ht : unitPoint R t = p :=
    (unitPointHom_apply R t).symm.trans ((unitEquiv R).symm_apply_apply p)
  have h := opposite_point c R t
  change pointHom (oppositeCocharacter c) R (unitPoint R t) =
    pointHom c R (unitPoint R t⁻¹) at h
  rw [unitPoint_inv, map_inv, ht] at h
  change p ≫ (oppositeCocharacter c).hom.hom = (p ≫ c.hom.hom)⁻¹ at h
  simpa only [Grp.Hom.hom_hom_inv, GrpObj.comp_inv] using h

private theorem oppositePositiveRoots {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) {c : Cocharacter T.group} (h : IsRegular T c) :
    positiveRoots T (oppositeCocharacter c) = (positiveRoots T c)ᶜ := by
  ext i
  change 0 < pairing T.group i.val (oppositeCocharacter c) ↔ ¬ 0 < pairing T.group i.val c
  have hn := h i
  have hp : pairing T.group i.val (oppositeCocharacter c) = -pairing T.group i.val c := by
    rw [oppositeCocharacter_eq_inv, ← D.pairing_eq, ← D.pairing_eq]
    change D.rootDatum.toLinearMap (Additive.ofMul i.val) (-(Additive.ofMul c)) =
      -D.rootDatum.toLinearMap (Additive.ofMul i.val) (Additive.ofMul c)
    exact map_neg _ _
  rw [hp]
  omega

private theorem pairingTransport {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (e : DatumAndWeyl.Identification D) (w : D.rootDatum.weylGroup)
    (c : Cocharacter T.group) (i : Root T) :
    pairing T.group (D.rootDatum.weylGroupToPerm w i).val
        (c ≫ (e.image.conjugation (e.labelEquiv w)).hom) =
      pairing T.group i.val c := by
  rw [← D.pairing_eq, ← D.pairing_eq, ← D.root_eq, ← D.root_eq, ← e.cocharacterAction]
  rw [← D.rootDatum.weylGroup_apply_root]
  change D.rootDatum.toLinearMap
      (w.val.weightEquiv (D.rootDatum.root i))
      (w.val.coweightEquiv.symm (Additive.ofMul c)) = _
  rw [w.val.toLinearMap_weightEquiv, LinearEquiv.apply_symm_apply]

private theorem transportedChamber
    {T B : ClosedSubgroup G.val} [IsCommMonObj T.group.X] {D : Datum T}
    (e : DatumAndWeyl.Identification D) (b : D.rootDatum.Base)
    (hb : ∀ i : Root T, b.IsPos i ↔ i ∈ subgroupRoots T B)
    (w : D.rootDatum.weylGroup)
    (hw : ∀ v : D.rootDatum.weylGroup,
      SimpleRoots.wordLength D.rootDatum b v ≤ SimpleRoots.wordLength D.rootDatum b w)
    {c : Cocharacter T.group} (hc : IsRegular T c) (hcB : positiveRoots T c = subgroupRoots T B) :
    positiveRoots T (oppositeCocharacter c ≫ (e.image.conjugation (e.labelEquiv w)).hom) =
      subgroupRoots T B := by
  let := D.finiteRoots
  let := D.freeCharacters
  let := D.finiteCharacters
  let := D.reduced
  let f := Specs.SimpleRoots.evaluate D c
  have he (i : Root T) : f (D.rootDatum.root i) = pairing T.group i.val c := by
    change D.rootDatum.toLinearMap (D.rootDatum.root i) (Additive.ofMul c) = _
    rw [D.root_eq, D.pairing_eq]
  have hreg (i : Root T) : f (D.rootDatum.root i) ≠ 0 := by rw [he]; exact hc i
  have hpos (i : Root T) : b.IsPos i ↔ i ∈ Specs.SimpleRoots.positive D.rootDatum f := by
    rw [hb, ← hcB]
    change 0 < pairing T.group i.val c ↔ 0 < f (D.rootDatum.root i)
    rw [he]
  ext i
  obtain ⟨j, rfl⟩ := (D.rootDatum.weylGroupToPerm w).surjective i
  rw [← hb, longest_flips_sign b f hreg hpos w hw]
  change 0 < pairing T.group _ _ ↔ ¬ b.IsPos j
  rw [pairingTransport, ← show j ∈ positiveRoots T (oppositeCocharacter c) ↔
    0 < pairing T.group j.val (oppositeCocharacter c) from Iff.rfl,
    oppositePositiveRoots D hc, Set.mem_compl_iff, hcB, hb]

open GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (closedSubgroupAlgebraicGroup)
open Specs.OrderedRootProducts (ContractingProduct)
open CocharacterDynamics (LimitDecomposition)

private theorem normalizerOnTorus {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (e : DatumAndWeyl.Identification D) (w : D.rootDatum.weylGroup)
    (n : 𝟙_ (SchemeOver k) ⟶ e.normalizer.group.X)
    (hn : n ≫ e.quotient.hom.hom = e.image.constantGroup.sectionPoint (e.labelEquiv w)) :
    let nG := n ≫ e.normalizer.inclusion.hom.hom
    ((e.image.conjugation (e.labelEquiv w)).hom ≫ T.inclusion).hom.hom =
      (toUnit _ ≫ nG) * T.inclusion.hom.hom * (toUnit _ ≫ nG)⁻¹ := by
  dsimp
  have hunit : toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ := Subsingleton.elim _ _
  have h := e.image.conjugates _ n (e.labelEquiv w) (by simpa only [hunit, Category.id_comp] using hn)
  have hh := congrArg (fun f ↦ lift (𝟙 T.group.X) (toUnit T.group.X) ≫ f) h
  simpa only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv,
    lift_fst_assoc, lift_snd_assoc, Category.id_comp, Grp.comp_hom_hom] using hh.symm

set_option backward.isDefEq.respectTransparency false in
private theorem splitWithSpecifiedRadical {T B : ClosedSubgroup G.val}
    {U : ClosedSubgroup B.group} (h : BorelPositivity.RadicalDecomposition T B)
    (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U) :
    ∃ j : T.group ⟶ B.group, j ≫ B.inclusion = T.inclusion ∧
      IsIso (multiplyFactors j U.inclusion) := by
  obtain ⟨V, j, q, hV, _, hj, _, _, hm, _⟩ := h
  obtain ⟨e, he⟩ := radicalIso hU hV
  refine ⟨j, hj, ?_⟩
  let F := Grp.forget (SchemeOver k)
  let i := tensorIso (Iso.refl T.group.X) (F.mapIso e)
  have hib : e.hom.hom.hom ≫ V.inclusion.hom.hom = U.inclusion.hom.hom :=
    congrArg (fun (f : U.group ⟶ B.group) ↦ f.hom.hom) he
  have hh : i.hom ≫ multiplyFactors j V.inclusion = multiplyFactors j U.inclusion := by
    change (𝟙 T.group.X ⊗ₘ e.hom.hom.hom) ≫ multiplyFactors j V.inclusion =
      multiplyFactors j U.inclusion
    simp only [multiplyFactors, MonObj.comp_mul,
      tensorHom_fst_assoc, tensorHom_snd_assoc, Category.id_comp, hib]
  rw [← hh]
  let : IsIso (multiplyFactors j V.inclusion) := hm
  infer_instance

private theorem radicalChart {T B : ClosedSubgroup G.val}
    (h : Specs.BorelPositivity.RadicalDecomposition T B)
    {U : ClosedSubgroup B.group} (hU : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U)
    (R : RootSubgroupFamily T) (l : List (Root T)) (hl : Enumerates l (subgroupRoots T B)) :
    Parametrizes R l (U.inclusion.hom.hom ≫ B.inclusion.hom.hom) := by
  obtain ⟨V, _, _, hV, _, _, _, _, _, hprod⟩ := h
  exact radicalProductFor R l hU hV (hprod R l hl)

private theorem contractingChart (h : ContractingProduct.{u}) (hG : IsReductive G)
    {T : ClosedSubgroup G.val} (hT : IsSplitTorus T.group) (hmax : IsGeometricallyMaximal T)
    {B : ClosedSubgroup G.val} {U : ClosedSubgroup B.group}
    (R : RootSubgroupFamily T) (l : List (Root T)) (hl : Enumerates l (subgroupRoots T B))
    (hp : Parametrizes R l (U.inclusion.hom.hom ≫ B.inclusion.hom.hom))
    (c : Cocharacter T.group) (hc : positiveRoots T c = subgroupRoots T B) :
    ∃ D : LimitDecomposition (c ≫ T.inclusion),
      ∃ f : D.contracting.group.X ≅ U.group.X,
        f.hom ≫ U.inclusion.hom.hom ≫ B.inclusion.hom.hom = D.contracting.inclusion.hom.hom := by
  obtain ⟨D⟩ := (h G hG T hT hmax).2.2 c |>.1
  have hD := (h G hG T hT hmax).2.2 c |>.2 D R l (hc.symm ▸ hl)
  obtain ⟨f, hf⟩ := matchClosedCharts R l hD hp
  exact ⟨D, f, hf⟩

open CocharacterDynamics (orbit cocharacterPoint laurentAlgebra laurentParameter)
open AdjointRepresentation (GroupPoints)
open private subgroupInclusionFactors from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

set_option backward.isDefEq.respectTransparency false in
/-- A homomorphism taking one cocharacter to another preserves its polynomial contraction. -/
private theorem contractingFactors {a b : Cocharacter G.val} (f : G.val ⟶ G.val)
    (D : LimitDecomposition a) (E : LimitDecomposition b) (h : a ≫ f = b) :
    ∃ j : D.contracting.group ⟶ E.contracting.group,
      j ≫ E.contracting.inclusion = D.contracting.inclusion ≫ f := by
  subst b
  have := G.property.1
  have := D.contracting.isClosedImmersion
  refine subgroupInclusionFactors
    (isAffine_of_isAffineHom D.contracting.inclusion.hom.hom.left) E.contracting
    (D.contracting.inclusion ≫ f) fun R x ↦ ?_
  let y := pointHom D.contracting.inclusion R x
  rcases (D.contracting_points R y).mpr ⟨x, rfl⟩ with ⟨p, hp, hzero⟩
  refine (E.contracting_points R _).mp ⟨p ≫ f.hom.hom, ?_, ?_⟩
  · have hOrbit : orbit (a ≫ f) (pointHom (D.contracting.inclusion ≫ f) R x) =
        orbit a y ≫ f.hom.hom := by
      let t := cocharacterPoint a (laurentAlgebra R) (laurentParameter R)
      let Y : GroupPoints G.val (laurentAlgebra R) :=
        mapPoints (CocharacterDynamics.laurentConstants R) y
      change (t ≫ f.hom.hom) * (Y ≫ f.hom.hom) * (t ≫ f.hom.hom)⁻¹ =
        (t * Y * t⁻¹) ≫ f.hom.hom
      rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
    rw [hOrbit, ← hp]
    exact (Category.assoc _ _ _).symm
  · have hz := congrArg (· ≫ f.hom.hom) hzero
    simpa only [mapPoints, Category.assoc, MonObj.one_comp] using hz

private theorem contractingIso {a b : Cocharacter G.val} (e : G.val ≅ G.val)
    (D : LimitDecomposition a) (E : LimitDecomposition b) (h : a ≫ e.hom = b) :
    ∃ j : D.contracting.group ≅ E.contracting.group,
      j.hom ≫ E.contracting.inclusion = D.contracting.inclusion ≫ e.hom := by
  obtain ⟨f, hf⟩ := contractingFactors e.hom D E h
  obtain ⟨g, hg⟩ := contractingFactors e.inv E D (by rw [← h, Category.assoc, e.hom_inv_id,
    Category.comp_id])
  have := monoInclusion D.contracting
  have := monoInclusion E.contracting
  refine ⟨⟨f, g, (cancel_mono D.contracting.inclusion).mp ?_,
    (cancel_mono E.contracting.inclusion).mp ?_⟩, hf⟩
  · rw [Category.assoc, hg, reassoc_of% hf, e.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, hf, reassoc_of% hg, e.inv_hom_id, Category.comp_id, Category.id_comp]

open private LinearAlgebraicGroups.baseChangeMapPullback from LinearAlgebraicGroups.Affine.Components
open private irreducible_of_geometricallyConnected
  from LinearAlgebraicGroups.Solvable.WordDomainGeometry

private theorem denseAfterExtension {X : SchemeOver k} (m : X ⟶ G.val.X)
    (hx : Nonempty X.left) (hG : GeometricallyConnected G.val.X.hom)
    (hm : IsOpenImmersion m.left) (K : Type u) [Field K] [Algebra k K] :
    DenseRange ((baseChange k K).map m).left := by
  let Gk := (groupBaseChange k K).obj G.val
  let q := fieldSpecMap k K
  have hpb : IsPullback (pullback.fst G.val.X.hom q) Gk.X.hom G.val.X.hom q :=
    IsPullback.of_hasPullback _ _
  have : LocallyOfFiniteType Gk.X.hom := MorphismProperty.of_isPullback hpb G.property.2.1
  have : QuasiCompact Gk.X.hom := MorphismProperty.of_isPullback hpb G.property.2.2
  have : GeometricallyConnected Gk.X.hom := MorphismProperty.of_isPullback hpb hG
  have : IrreducibleSpace ((baseChange k K).obj G.val.X).left :=
    irreducible_of_geometricallyConnected Gk
  have : IsOpenImmersion ((baseChange k K).map m).left :=
    MorphismProperty.of_isPullback (LinearAlgebraicGroups.baseChangeMapPullback (K := K) m).flip hm
  have : Surjective q := ⟨fun p ↦ ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  obtain ⟨x⟩ := hx
  obtain ⟨y, _⟩ := (pullback.fst X.hom q).surjective x
  change Dense (Set.range (⇑(((baseChange k K).map m).left)))
  exact (IsOpenImmersion.isOpen_range _).dense ⟨_, y, rfl⟩

set_option backward.isDefEq.respectTransparency false in
private theorem matchConjugateRadicals {a b : Cocharacter G.val}
    (σ : G.val ≅ G.val) (hc : a ≫ σ.hom = b)
    (D : LimitDecomposition a) (E : LimitDecomposition b)
    {Bneg B : ClosedSubgroup G.val} {Uneg : ClosedSubgroup Bneg.group}
    {Upos : ClosedSubgroup B.group}
    (f : D.contracting.group.X ≅ Uneg.group.X) (g : E.contracting.group.X ≅ Upos.group.X)
    (hf : f.hom ≫ Uneg.inclusion.hom.hom ≫ Bneg.inclusion.hom.hom =
      D.contracting.inclusion.hom.hom)
    (hg : g.hom ≫ Upos.inclusion.hom.hom ≫ B.inclusion.hom.hom =
      E.contracting.inclusion.hom.hom) :
    ∃ iso : Uneg.group.X ≅ Upos.group.X,
      iso.hom ≫ Upos.inclusion.hom.hom ≫ B.inclusion.hom.hom =
        (Uneg.inclusion.hom.hom ≫ Bneg.inclusion.hom.hom) ≫ σ.hom.hom.hom := by
  obtain ⟨j, hj⟩ := contractingIso σ D E hc
  let j' := (Grp.forget (SchemeOver k)).mapIso j
  refine ⟨f.symm.trans (j'.trans g), ?_⟩
  have hcomp : j'.hom ≫ E.contracting.inclusion.hom.hom =
      D.contracting.inclusion.hom.hom ≫ σ.hom.hom.hom :=
    congrArg (fun (m : D.contracting.group ⟶ G.val) ↦ m.hom.hom) hj
  change (f.inv ≫ j'.hom ≫ g.hom) ≫ Upos.inclusion.hom.hom ≫ B.inclusion.hom.hom = _
  simp only [Category.assoc, hg, hcomp]
  rw [← hf]
  simp only [Category.assoc, f.inv_hom_id_assoc]

/-- The multiplication cell is open and remains dense after field extension.
Its left translate by a longest Weyl representative represents the fppf
double orbit. -/
theorem openCell : Specs.OpenCell.Statement.{u} := by
  intro k _ G hG T hT hMax B Bneg hB hBneg hTB hTBneg hOpp Uneg Upos hUneg hUpos
  obtain ⟨comm₀, D₀, _, corr, _, ⟨R⟩, dec⟩ :=
    RootData.BorelPositivity.borelPositivity G hG T hT hMax
  let := comm₀
  let := D₀.finiteRoots
  obtain ⟨c, hRegular, hPositive⟩ :=
    (RootData.BorelsAndChambers.positiveSystemsFromCocharacters G hG T hT hMax
      (subgroupRoots T B)).mp (corr.1 B hB hTB)
  have hNegative : positiveRoots T (oppositeCocharacter c) = subgroupRoots T Bneg := by
    rw [oppositePositiveRoots D₀ hRegular, hPositive]
    exact hOpp.symm
  obtain ⟨ln, hn⟩ := existsEnumeration (subgroupRoots T Bneg)
  obtain ⟨lp, hp⟩ := existsEnumeration (subgroupRoots T B)
  have rn := radicalChart (dec Bneg hBneg hTBneg) hUneg R ln hn
  have rp := radicalChart (dec B hB hTB) hUpos R lp hp
  have ho := cellMap_comp rn rp
    (RootData.OrderedRootProducts.regularRootCell G hG T hT hMax c hRegular R ln lp
      (hNegative.symm ▸ hn) (hPositive.symm ▸ hp))
  have hne : Nonempty (Uneg.group.X ⊗ (T.group.X ⊗ Upos.group.X)).left :=
    ⟨(lift η[Uneg.group.X] (lift η[T.group.X] η[Upos.group.X])).left
      (IsLocalRing.closedPoint k)⟩
  refine ⟨ho, denseAfterExtension _ hne hG.2.1 ho, ?_⟩
  intro comm
  let := comm
  intro D e b hb w hw n hnq
  dsimp only
  let nG := n ≫ e.normalizer.inclusion.hom.hom
  let torusConjugation := e.image.conjugation (e.labelEquiv w)
  let cn := oppositeCocharacter c
  let cp := cn ≫ torusConjugation.hom
  obtain ⟨σ, hσ⟩ := conjugationByPoint G.val nG
  have hTorus : (torusConjugation.hom ≫ T.inclusion).hom.hom =
      (toUnit T.group.X ≫ nG) * T.inclusion.hom.hom * (toUnit T.group.X ≫ nG)⁻¹ :=
    normalizerOnTorus e w n hnq
  have hσT : T.inclusion ≫ σ.hom = torusConjugation.hom ≫ T.inclusion := by
    apply Grp.hom_ext
    change T.inclusion.hom.hom ≫ σ.hom.hom.hom = (torusConjugation.hom ≫ T.inclusion).hom.hom
    rw [hσ, hTorus]
  have hcp : positiveRoots T cp = subgroupRoots T B :=
    transportedChamber e b hb w hw hRegular hPositive
  obtain ⟨N, fn, hfn⟩ :=
    contractingChart RootData.OrderedRootProducts.contractingProduct hG hT hMax R ln hn rn cn hNegative
  obtain ⟨P, fp, hfp⟩ :=
    contractingChart RootData.OrderedRootProducts.contractingProduct hG hT hMax R lp hp rp cp hcp
  have hconjcochar : (cn ≫ T.inclusion) ≫ σ.hom = cp ≫ T.inclusion := by
    rw [Category.assoc, hσT, ← Category.assoc]
  obtain ⟨φ, hφ⟩ := matchConjugateRadicals σ hconjcochar N P fn fp hfn hfp
  rw [hσ] at hφ
  obtain ⟨j, hj, hm⟩ := splitWithSpecifiedRadical (dec B hB hTB) hUpos
  let : IsIso (multiplyFactors j Upos.inclusion) := hm
  have hOpen := translatedCellOpen nG ho
  refine ⟨hOpen, fun {_} g ↦ ?_⟩
  exact translatedDoubleOrbit hj nG torusConjugation φ hTorus hφ hOpen g

end
end LinearAlgebraicGroups.Flag.OpenCell
