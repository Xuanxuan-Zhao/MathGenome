import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalParahoricResidueWeyl
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbstractPairing
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalParahoricResidueWeyl

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Datum Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character)
open Specs.CharacterPairing (absoluteRoots)
open Specs.DatumAndWeyl (Identification)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint markedRootPoint
  markedWall markedWeylWord wallMatrix rankOneMatrixWord)
open Specs.ExceptionalParahoricResidueWeyl (MarkedResidueWeylComparison markedCharacter)
open Specs.IntegralRootRelations (upper lower)
open Specs.IntegralSemisimpleModel (Model fibre forgetFibrePoint splitTorus)
open Specs.Pinning (BasedRootDatum transportCharacter)

open private fibrePointsEquiv forgetFibrePoint_comp from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private markedWall_section markedLabel_weight from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private conjugation conjugation_apply from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private groundIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusSections
open private charactersOfIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.CharacterPairing
open private coroot_functional_of_reflection from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.Pinning
open private quotientLabel quotientLabel_spec quotientLabel_conjugates
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.AbstractPairing
open private inducedConjugation_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl

noncomputable section

attribute [local instance] Specs.IntegralSemisimpleModel.integerAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
set_option linter.style.haveILetI false

variable {k : Type u} [Field k] {E : BasedRootDatum.{u}} {M : Model E}

private abbrev RationalPoint (H : GroupScheme k) := 𝟙_ (SchemeOver k) ⟶ H.X

private abbrev ground : TestAlgebra k := CommAlgCat.of k k

private abbrev groundScheme (k : Type u) [Field k] :=
  unop ((testSpec k).rightOp.obj (ground (k := k)))

private def groundSectionIso : groundScheme k ≅ 𝟙_ (SchemeOver k) := groundIso

private def integralSection {H : GroupScheme k} (i : H ⟶ (fibre k).obj M.group) :
    RationalPoint H →* Specs.IntegralSemisimpleModel.IntegralPoints M.group (integralRing k) :=
  ((fibrePointsEquiv M.group (ground (k := k))).toMonoidHom.comp
    (IsMonHom.monoidHom i.hom.hom _)).comp
    { toFun := fun g => toUnit _ ≫ g
      map_one' := MonObj.comp_one _
      map_mul' := fun _ _ => MonObj.comp_mul _ _ _ }

private theorem integralSection_apply {H : GroupScheme k} (i : H ⟶ (fibre k).obj M.group)
    (g : RationalPoint H) :
    integralSection i g =
      forgetFibrePoint M.group (ground (k := k)) (toUnit _ ≫ g ≫ i.hom.hom) := by
  change forgetFibrePoint M.group _ ((toUnit _ ≫ g) ≫ i.hom.hom) = _
  rw [Category.assoc]

private theorem rootPoint_mem_range {H : GroupScheme k} (i : H ⟶ (fibre k).obj M.group)
    (a : E.I) (z : k)
    (h : ∃ r : (fibre k).obj M.line.group ⟶ H, r ≫ i = (fibre k).map (M.root a)) :
    markedRootPoint M.toIntegralMarking (integralRing k) a z ∈ (integralSection i).range := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨v, hv⟩ := (Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective
    M.line.group (ground (k := k))).2 (M.line.point (integralRing k) z)
  let t := groundSectionIso (k := k)
  have ht : toUnit (groundScheme k) = t.hom := Subsingleton.elim _ _
  refine ⟨t.inv ≫ v ≫ r.hom.hom, ?_⟩
  rw [integralSection_apply]
  simp only [Category.assoc, ht, Iso.hom_inv_id_assoc]
  have he : r.hom.hom ≫ i.hom.hom = ((fibre k).map (M.root a)).hom.hom :=
    congrArg (fun f => f.hom.hom) hr
  rw [he, forgetFibrePoint_comp, hv]
  rfl

private theorem wall_mem_range {H : GroupScheme k} (i : H ⟶ (fibre k).obj M.group)
    (a : E.I)
    (hp : ∃ r : (fibre k).obj M.line.group ⟶ H, r ≫ i = (fibre k).map (M.root a))
    (hn : ∃ r : (fibre k).obj M.line.group ⟶ H,
      r ≫ i = (fibre k).map (M.root (E.datum.reflectionPerm a a))) :
    markedWall M.toIntegralMarking (integralRing k) a 1 ∈ (integralSection i).range := by
  let R := integralRing k
  let f : Matrix.SpecialLinearGroup (Fin 2) R →*
      Specs.IntegralSemisimpleModel.IntegralPoints M.group R := ((M.rankOne a).app R).hom
  have hu (z : R) : f (upper z) ∈ (integralSection i).range := by
    change (M.rankOne a).app R (upper z) ∈ _
    rw [M.rankOneUpper]
    exact rootPoint_mem_range i a z hp
  have hl (z : R) : f (lower z) ∈ (integralSection i).range := by
    change (M.rankOne a).app R (lower z) ∈ _
    rw [M.rankOneLower]
    exact rootPoint_mem_range i (E.datum.reflectionPerm a a) z hn
  change f (wallMatrix (1 : Rˣ)) ∈ _
  unfold wallMatrix rankOneMatrixWord
  simp only [map_mul]
  exact (integralSection i).range.mul_mem ((integralSection i).range.mul_mem (hu _) (hl _)) (hu _)

private theorem normalizes_of_conjugation {H : GroupScheme k}
    (T : ClosedSubgroup H) (p : RationalPoint H) (e : T.group ≅ T.group)
    (he : (e.hom ≫ T.inclusion).hom.hom =
      (toUnit T.group.X ≫ p) * T.inclusion.hom.hom * (toUnit T.group.X ≫ p)⁻¹) :
    Normalizes T.inclusion p := by
  let e' := (Grp.forget (SchemeOver k)).mapIso e
  refine ⟨e' ⊗ᵢ Iso.refl _, ?_, ?_⟩
  · change (e'.hom ⊗ₘ 𝟙 _) ≫ snd _ _ = snd _ _
    rw [tensorHom_snd, Category.comp_id]
  · change (e'.hom ⊗ₘ 𝟙 _) ≫ fst _ _ ≫ T.inclusion.hom.hom = _
    rw [tensorHom_fst_assoc]
    change fst _ _ ≫ (e.hom ≫ T.inclusion).hom.hom = _
    rw [he]
    have hunit : fst T.group.X (𝟙_ (SchemeOver k)) ≫ toUnit T.group.X =
        snd T.group.X (𝟙_ (SchemeOver k)) := Subsingleton.elim _ _
    simp only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc _ (toUnit _),
      hunit]

private theorem section_conjugation_comp {H P : GroupScheme k} (d : H ⟶ P)
    (p : RationalPoint H) :
    conjugation p ≫ d = d ≫ conjugation (p ≫ d.hom.hom) := by
  apply Grp.hom_ext
  simp only [Grp.comp_hom_hom, conjugation_apply]
  rw [← Category.id_comp (conjugation p).hom.hom, conjugation_apply]
  simp only [Category.id_comp, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

private theorem markedWall_action (F : MarkedFibre M k)
    {G : AffineAlgebraicGroup k} (T : ClosedSubgroup G.val)
    (i : G.val ⟶ (fibre k).obj M.group) (hi : IsClosedImmersion i.hom.hom.left)
    (τ : (fibre k).obj (splitTorus E) ≅ T.group)
    (hτ : τ.hom ≫ T.inclusion ≫ i = (fibre k).map M.torus)
    (a : E.I) (p : RationalPoint G.val)
    (hp : integralSection i p = markedWall M.toIntegralMarking (integralRing k) a 1) :
    ∃ e : T.group ≅ T.group,
      Specs.BorelNormalizer.InducesTorusConjugation T p e ∧
      ∀ z : E.X, transportCharacter e (markedCharacter F τ z) =
        markedCharacter F τ (E.datum.reflection a z) := by
  let P := F.realization.pinned.pair
  let d := i ≫ F.groupIso.hom
  let b := F.torusIso.symm ≪≫ τ
  have hd : T.inclusion ≫ d = b.inv ≫ P.T.inclusion := by
    have ht := congrArg (fun f => τ.inv ≫ f ≫ F.groupIso.hom) hτ
    dsimp only [b, d, Iso.trans_inv, Iso.symm_inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, F.torus_comm] using ht
  obtain ⟨q, hq⟩ := markedWall_section F a
  obtain ⟨g, w, hT, hχ, hg⟩ :=
    LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent.markedFieldReflection F a
  have hinj (R : TestAlgebra k) : Function.Injective (markedFibrePoint F R) := by
    letI := ((Grp.forget (SchemeOver k)).mapIso F.groupIso).isIso_inv
    exact (Classification.IntegralSemisimpleModel.forgetFibrePoint_bijective M.group R).1.comp
      (fun _ _ h => (cancel_mono F.groupIso.inv.hom.hom).mp h)
  have hq' : p ≫ d.hom.hom = q := by
    let t := groundSectionIso (k := k)
    have hu : toUnit (groundScheme k) = t.hom := Subsingleton.elim _ _
    letI := t.isIso_hom
    apply (cancel_epi t.hom).mp
    rw [← hu]
    apply hinj (ground (k := k))
    calc
      markedFibrePoint F (ground (k := k)) (toUnit _ ≫ p ≫ d.hom.hom) =
          integralSection i p := by
        have hIso : F.groupIso.hom.hom.hom ≫ F.groupIso.inv.hom.hom = 𝟙 _ :=
          congrArg (fun f => f.hom.hom) F.groupIso.hom_inv_id
        rw [integralSection_apply]
        change forgetFibrePoint M.group (ground (k := k))
          ((toUnit _ ≫ p ≫ (i ≫ F.groupIso.hom).hom.hom) ≫ F.groupIso.inv.hom.hom) = _
        simp only [Grp.comp_hom_hom, Category.assoc, hIso, Category.comp_id]
      _ = _ := hp.trans (hq (ground (k := k))).symm
  have hg' : g.hom = conjugation q := by
    apply Grp.hom_ext
    apply hom_ext_of_points P.G.property.1
    intro R t
    let f := (fibrePointsEquiv M.group R).toMonoidHom.comp
      (IsMonHom.monoidHom F.groupIso.inv.hom.hom ((testSpec k).obj (op R)))
    change (t ≫ g.hom.hom.hom : GroupPoints P.G.val R) = t ≫ (conjugation q).hom.hom
    apply hinj R
    rw [hg R t, conjugation_apply]
    change _ = f ((toUnit _ ≫ q) * t * (toUnit _ ≫ q)⁻¹)
    rw [map_mul, map_mul, map_inv]
    change _ = markedFibrePoint F R (toUnit _ ≫ q) * markedFibrePoint F R t *
      (markedFibrePoint F R (toUnit _ ≫ q))⁻¹
    rw [hq R]
  let e := b.symm ≪≫ w ≪≫ b
  refine ⟨e, ?_, ?_⟩
  · haveI : IsClosedImmersion i.hom.hom.left := hi
    letI : Mono i.hom.hom := Over.mono_of_mono_left _
    letI := ((Grp.forget (SchemeOver k)).mapIso F.groupIso).isIso_hom
    haveI : Mono d.hom.hom := by
      change Mono (i.hom.hom ≫ F.groupIso.hom.hom.hom)
      infer_instance
    have hconj : e.hom ≫ T.inclusion = T.inclusion ≫ conjugation p := by
      apply Grp.hom_ext
      apply (cancel_mono d.hom.hom).mp
      change ((e.hom ≫ T.inclusion) ≫ d).hom.hom =
        ((T.inclusion ≫ conjugation p) ≫ d).hom.hom
      rw [Category.assoc, Category.assoc, section_conjugation_comp, hq', ← hg',
        ← Category.assoc T.inclusion d, hd, Category.assoc, hT]
      simp [e, P, Category.assoc]
    change (e.hom ≫ T.inclusion).hom.hom = _
    rw [hconj, Grp.comp_hom_hom, conjugation_apply]
  · intro z
    change e.inv ≫ b.inv ≫ Additive.toMul (F.realization.datumIso.val.weightEquiv z) =
      b.inv ≫ Additive.toMul (F.realization.datumIso.val.weightEquiv (E.datum.reflection a z))
    have heinv : e.inv ≫ b.inv = b.inv ≫ w.inv := by
      change ((b.inv ≫ w.inv) ≫ b.hom) ≫ b.inv = _
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc e.inv b.inv, heinv, Category.assoc]
    exact congrArg (fun χ => b.inv ≫ χ) (hχ z)

private def markedLattice (F : MarkedFibre M k) {T : GroupScheme k}
    (τ : (fibre k).obj (splitTorus E) ≅ T) : E.X ≃ₗ[ℤ] Additive (Character T) :=
  F.realization.datumIso.val.weightEquiv.trans
    (charactersOfIso (F.torusIso.symm ≪≫ τ)).toAdditive.toIntLinearEquiv

private theorem reflection_of_marked_action
    {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) {a : E.I} {j : Root T} (L : E.X ≃ₗ[ℤ] Additive (Character T.group))
    (hroot : L (E.datum.root a) = D.rootDatum.root j)
    (v : D.rootDatum.weylGroup)
    (hv : ∀ z, v.val.weightEquiv (L z) = L (E.datum.reflection a z)) :
    v = RootPairing.weylGroup.ofIdx D.rootDatum j := by
  let c := (E.datum.coroot' a).comp L.symm.toLinearMap
  have hc : c (D.rootDatum.root j) = 2 := by
    rw [← hroot]
    change E.datum.coroot' a (L.symm (L (E.datum.root a))) = 2
    rw [L.symm_apply_apply, E.datum.coroot_root_two]
  have hform (x : Additive (Character T.group)) :
      v.val.weightEquiv x = x - c x • D.rootDatum.root j := by
    obtain ⟨z, rfl⟩ := L.surjective x
    rw [hv, RootPairing.reflection_apply, map_sub, map_smul, hroot]
    change _ = L z - E.datum.coroot' a (L.symm (L z)) • D.rootDatum.root j
    rw [L.symm_apply_apply]
  have hcoroot := coroot_functional_of_reflection D.rootDatum j v.val c hc hform
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective D.rootDatum
  apply LinearEquiv.ext
  intro x
  change v.val.weightEquiv x = (RootPairing.Equiv.reflection D.rootDatum j).weightEquiv x
  rw [hform, RootPairing.Equiv.reflection_weightEquiv, RootPairing.reflection_apply]
  exact congrArg (fun n : ℤ => x - n • D.rootDatum.root j)
    (LinearMap.congr_fun hcoroot x).symm

private theorem wall_section (F : MarkedFibre M k)
    {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) (J : Identification D)
    (i : G.val ⟶ (fibre k).obj M.group) (hi : IsClosedImmersion i.hom.hom.left)
    (τ : (fibre k).obj (splitTorus E) ≅ T.group)
    (hτ : τ.hom ≫ T.inclusion ≫ i = (fibre k).map M.torus)
    (a : E.I) (j : Root T) (hj : markedCharacter F τ (E.datum.root a) = j.val)
    (hp : ∃ r : (fibre k).obj M.line.group ⟶ G.val, r ≫ i = (fibre k).map (M.root a))
    (hn : ∃ r : (fibre k).obj M.line.group ⟶ G.val,
      r ≫ i = (fibre k).map (M.root (E.datum.reflectionPerm a a))) :
    ∃ n : RationalPoint J.normalizer.group,
      quotientLabel J.image n = J.labelEquiv (RootPairing.weylGroup.ofIdx D.rootDatum j) ∧
      integralSection (J.normalizer.inclusion ≫ i) n =
        markedWall M.toIntegralMarking (integralRing k) a 1 ∧
      ∀ z, (RootPairing.weylGroup.ofIdx D.rootDatum j).val.weightEquiv (markedLattice F τ z) =
        markedLattice F τ (E.datum.reflection a z) := by
  obtain ⟨p, hp'⟩ := wall_mem_range i a hp hn
  obtain ⟨e, he, hχ⟩ := markedWall_action F T i hi τ hτ a p hp'
  obtain ⟨n, hn'⟩ := (J.representsNormalizer _ p).mp (normalizes_of_conjugation T p e he)
  let v := J.labelEquiv.symm (quotientLabel J.image n)
  have he' : e = J.image.conjugation (quotientLabel J.image n) := by
    apply inducedConjugation_unique he
    rw [← hn']
    exact quotientLabel_conjugates J.image n
  have hv (z : E.X) : v.val.weightEquiv (markedLattice F τ z) =
      markedLattice F τ (E.datum.reflection a z) := by
    change v.val.weightEquiv (Additive.ofMul (markedCharacter F τ z)) =
      Additive.ofMul (markedCharacter F τ (E.datum.reflection a z))
    rw [J.characterAction, show J.labelEquiv v = quotientLabel J.image n from
      J.labelEquiv.apply_symm_apply _, J.image.characterAction, ← he']
    exact congrArg Additive.ofMul (hχ z)
  have hroot : markedLattice F τ (E.datum.root a) = D.rootDatum.root j := by
    change Additive.ofMul (markedCharacter F τ (E.datum.root a)) = _
    rw [hj, D.root_eq]
  have hv' := reflection_of_marked_action D (markedLattice F τ) hroot v hv
  refine ⟨n, ?_, ?_, ?_⟩
  · rw [← hv']
    exact (J.labelEquiv.apply_symm_apply _).symm
  · rw [integralSection_apply, Grp.comp_hom_hom, ← Category.assoc n, hn',
      ← integralSection_apply]
    exact hp'
  · simpa only [← hv'] using hv

private theorem closure_equivalence {A B C : Type*} [Group A] [Group B] [Group C]
    (s : Set A) (t : Set B) (f : A →* C) (g : B →* C)
    (hf : Function.Injective f) (hg : Function.Injective g) (h : f '' s = g '' t) :
    ∃ e : Subgroup.closure s ≃* Subgroup.closure t,
      ∀ x, g (e x).val = f x.val := by
  let f' := f.domRestrict (Subgroup.closure s)
  let g' := g.domRestrict (Subgroup.closure t)
  let e₁ := MonoidHom.ofInjective (f := f') (hf.comp Subtype.val_injective)
  let e₂ := MonoidHom.ofInjective (f := g') (hg.comp Subtype.val_injective)
  have hr : f'.range = g'.range := by
    change (f.domRestrict (Subgroup.closure s)).range =
      (g.domRestrict (Subgroup.closure t)).range
    rw [MonoidHom.domRestrict_range, MonoidHom.domRestrict_range,
      MonoidHom.map_closure, MonoidHom.map_closure, h]
  let e := (e₁.trans (MulEquiv.subgroupCongr hr)).trans e₂.symm
  refine ⟨e, fun x => ?_⟩
  have he : e₂ (e x) = MulEquiv.subgroupCongr hr (e₁ x) := e₂.apply_symm_apply _
  exact congrArg Subtype.val he

/-- The integral wall lifts give the Weyl action and representatives of the
split residue subgroup for all surviving root indices. -/
theorem markedResidueWeylComparison : MarkedResidueWeylComparison.{u} := by
  intro k _ E M F G _ T _ _ i hi τ hτ S hopp hroots hr _ D J
  classical
  let L := markedLattice F τ
  let s := RootPairing.weylGroup.ofIdx E.datum
  let r := RootPairing.weylGroup.ofIdx D.rootDatum
  let W := Subgroup.closure (s '' S)
  have hmark (a : E.I) : markedCharacter F τ (E.datum.root a) =
      transportCharacter (F.torusIso.symm ≪≫ τ) (F.realization.datumIso.val.indexEquiv a).val :=
    congrArg (transportCharacter (F.torusIso.symm ≪≫ τ)) (markedLabel_weight F a).symm
  let j (a : S) : Root T := ⟨markedCharacter F τ (E.datum.root a.val),
    (hmark a.val).symm ▸ (hroots ▸ ⟨a.val, a.property, rfl⟩ :
      transportCharacter (F.torusIso.symm ≪≫ τ) (F.realization.datumIso.val.indexEquiv a.val).val
        ∈ absoluteRoots T)⟩
  have hj : Function.Surjective j := by
    intro b
    have hb := (Set.ext_iff.mp hroots b.val).mpr b.property
    obtain ⟨a, ha, he⟩ := hb
    exact ⟨⟨a, ha⟩, Subtype.ext ((hmark a).trans he)⟩
  have hw (a : S) := wall_section F D J i hi τ hτ a.val (j a) rfl
    (hr a.val a.property) (hr _ (hopp a.val a.property))
  choose n hlabel hsigned hact using hw
  let transport : (E.X ≃ₗ[ℤ] E.X) →*
      (Additive (Character T.group) ≃ₗ[ℤ] Additive (Character T.group)) :=
    { toFun := fun e => L.symm.trans (e.trans L)
      map_one' := by
        apply LinearEquiv.ext
        intro x
        exact L.apply_symm_apply x
      map_mul' := by
        intro f g
        apply LinearEquiv.ext
        intro x
        change L (f (g (L.symm x))) = L (f (L.symm (L (g (L.symm x)))))
        rw [LinearEquiv.symm_apply_apply] }
  have ht : Function.Injective transport := by
    intro a b h
    apply LinearEquiv.ext
    intro x
    have e := LinearEquiv.congr_fun h (L x)
    change L (a (L.symm (L x))) = L (b (L.symm (L x))) at e
    rw [L.symm_apply_apply] at e
    exact L.injective e
  let f := transport.comp ((RootPairing.Equiv.weightHom E.datum).domRestrict E.datum.weylGroup)
  let g := RootPairing.Equiv.weightHom D.rootDatum
  have hf : Function.Injective f :=
    ht.comp ((RootPairing.Equiv.weightHom_injective E.datum).comp Subtype.val_injective)
  have hg := RootPairing.Equiv.weightHom_injective D.rootDatum
  have hgen (a : S) : f (s a.val) = g (r (j a)).val := by
    apply LinearEquiv.ext
    intro x
    obtain ⟨z, rfl⟩ := L.surjective x
    change L ((s a.val).val.weightEquiv (L.symm (L z))) = (r (j a)).val.weightEquiv (L z)
    rw [L.symm_apply_apply]
    change L ((RootPairing.Equiv.reflection E.datum a.val).weightEquiv z) = _
    rw [RootPairing.Equiv.reflection_weightEquiv]
    exact (hact a z).symm
  have himage : f '' (s '' S) = g '' Set.range (RootPairing.Equiv.reflection D.rootDatum) := by
    ext v
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨(r (j ⟨a, ha⟩)).val, ⟨j ⟨a, ha⟩, rfl⟩, (hgen ⟨a, ha⟩).symm⟩
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      obtain ⟨a, rfl⟩ := hj b
      exact ⟨s a.val, ⟨a.val, a.property, rfl⟩, hgen a⟩
  obtain ⟨θ, hθ⟩ := closure_equivalence (s '' S) _ f g hf hg himage
  change W ≃* D.rootDatum.weylGroup at θ
  have hθgen (a : S) (wa : W) (ha : wa.val = s a.val) : θ wa = r (j a) := by
    apply Subtype.ext
    apply hg
    change g (θ wa).val = g (r (j a)).val
    calc
      g (θ wa).val = f wa.val := hθ wa
      _ = f (s a.val) := congrArg f ha
      _ = g (r (j a)).val := hgen a
  refine ⟨θ, ?_, ?_⟩
  · intro w z
    have e := LinearEquiv.congr_fun (hθ w) (L z)
    change (θ w).val.weightEquiv (L z) = L (w.val.val.weightEquiv (L.symm (L z))) at e
    rw [L.symm_apply_apply] at e
    exact e.symm
  have liftWord (l : List E.I) (hl : ∀ a ∈ l, a ∈ S) :
      ∃ (w : W) (p : RationalPoint J.normalizer.group),
        w.val = (l.map s).prod ∧
        quotientLabel J.image p = J.labelEquiv (θ w) ∧
        integralSection (J.normalizer.inclusion ≫ i) p =
          markedWeylWord M.toIntegralMarking (integralRing k) l := by
    induction l with
    | nil => exact ⟨1, 1, rfl, by simp, by change _ = 1; exact map_one _⟩
    | cons a l ih =>
      let a' : S := ⟨a, hl a List.mem_cons_self⟩
      let w₀ : W := ⟨s a, Subgroup.subset_closure ⟨a, a'.property, rfl⟩⟩
      obtain ⟨w, p, hw, hq, hp⟩ := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))
      refine ⟨w₀ * w, n a' * p, ?_, ?_, ?_⟩
      · change s a * w.val = s a * (l.map s).prod
        rw [hw]
      · rw [map_mul, hlabel a', hq, map_mul, map_mul, hθgen a' w₀ rfl]
      · rw [map_mul, hsigned a', hp]
        rfl
  intro l hl w hw'
  obtain ⟨w', p, hw, hq, hp⟩ := liftWord l hl
  have e : w' = w := Subtype.ext (hw.trans hw'.symm)
  refine ⟨p, ?_, ?_⟩
  · have h := quotientLabel_spec J.image p
    have hu : toUnit (𝟙_ (SchemeOver k)) = 𝟙 _ := Subsingleton.elim _ _
    simpa only [hu, Category.id_comp, hq, e] using h
  · change forgetFibrePoint M.group (ground (k := k))
        (toUnit (groundScheme k) ≫ p ≫ J.normalizer.inclusion.hom.hom ≫ i.hom.hom) = _
    exact (integralSection_apply (J.normalizer.inclusion ≫ i) p).symm.trans hp

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalParahoricResidueWeyl
