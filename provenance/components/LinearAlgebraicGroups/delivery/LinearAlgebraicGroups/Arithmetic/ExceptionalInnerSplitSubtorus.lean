import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerSplitSubtorus
import LinearAlgebraicGroups.Descent.Forms
import LinearAlgebraicGroups.Descent.FiniteFieldFlags
import LinearAlgebraicGroups.Reductive.SplitToriConjugacy
import LinearAlgebraicGroups.Flag.StandardParabolicLevi
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalInnerSplitSubtorus

open _root_.LinearAlgebraicGroups.Specs
open Specs.ExceptionalInnerSplitSubtorus (coefficientChange)
open Specs.CharacterDescent (Character Cocharacter StandardLattice)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.SchemeDerivedGroup (IsSubgroupOf)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

open private twistGroupBaseChangeIso coefficientMap coefficientMap_spec
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private standard standardAct descend_standard_hom from LinearAlgebraicGroups.Descent.Forms
open private extendedGroupIso extendedSpecIso extendedSpecIso_natural
  from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private schemeHopfHomEquiv splitGroupHomEquiv
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private splitPresentation from LinearAlgebraicGroups.RootData.CharacterPairing
open private latticeCharacter latticeCharacter_comp from LinearAlgebraicGroups.RootData.RankOneFlag
open private common_kernel from LinearAlgebraicGroups.Flag.StandardParabolicLevi
open private splitCoordinateChange splitCoordinates splitTorus_baseChange
  splitTorus_hom_descends groupBaseChange_map_injective
  from LinearAlgebraicGroups.Reductive.SplitToriConjugacy

private abbrev underlying (F : Type u) [Field F] : GroupScheme F ⥤ Scheme :=
  Grp.forget (SchemeOver F) ⋙ Over.forget (Spec (CommRingCat.of F))

private theorem underlying_injective {X Y : GroupScheme F} {f g : X ⟶ Y}
    (h : (underlying F).map f = (underlying F).map g) : f = g := by
  apply Grp.hom_ext
  exact Over.OverMorphism.ext h

private theorem coefficientChange_natural (τ : Gal(K/F)) {X Y : GroupScheme F} (f : X ⟶ Y) :
    (underlying K).map ((groupBaseChange F K).map f) ≫ coefficientChange τ Y =
      coefficientChange τ X ≫ (underlying K).map ((groupBaseChange F K).map f) :=
  congrArg (fun g ↦ (underlying K).map g) ((twistGroupBaseChangeIso τ).hom.naturality f)

private theorem coefficientChange_epi (τ : Gal(K/F)) (X : GroupScheme F) :
    Epi (coefficientChange τ X) :=
  inferInstanceAs (Epi ((underlying K).mapIso ((twistGroupBaseChangeIso τ).app X)).hom)

private theorem standardAct_eq_coefficient (P : HopfAlgebraCategory F) (τ : Gal(K/F))
    (x : extendedHopf K P) :
    (standardAct K P).act τ x = coefficientMap τ P x := by
  induction x using TensorProduct.inductionOn with
  | tmul r p => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private theorem generator_equivariant {P Q : HopfAlgebraCategory F}
    (τ : Gal(K/F)) (hτ : Subgroup.zpowers τ = ⊤) (a : extendedHopf K P ⟶ extendedHopf K Q)
    (ha : ∀ x : extendedHopf K P, a.hom (coefficientMap τ P x) = coefficientMap τ Q (a.hom x)) :
    (standard K P).Equivariant (standard K Q) a := by
  let p := standardAct K P
  let q := standardAct K Q
  let H : Subgroup Gal(K/F) :=
    { carrier := { σ | ∀ x, a.hom (p.act σ x) = q.act σ (a.hom x) }
      one_mem' := fun x ↦ by rw [p.one_act, q.one_act]
      mul_mem' := fun {s t} hs ht x ↦ by
        rw [p.mul_act, q.mul_act, hs, ht]
      inv_mem' := fun {s} hs x ↦ by
        apply (q.act s).injective
        rw [← hs, ← p.mul_act, ← q.mul_act, mul_inv_cancel, p.one_act, q.one_act] }
  have hmem : τ ∈ H := by
    intro x
    exact (congrArg a.hom (standardAct_eq_coefficient P τ x)).trans
      ((ha x).trans (standardAct_eq_coefficient Q τ (a.hom x)).symm)
  have hH : Subgroup.zpowers τ ≤ H := Subgroup.zpowers_le.mpr hmem
  rw [hτ] at hH
  exact fun σ ↦ hH (Subgroup.mem_top σ)

set_option maxHeartbeats 900000 in
/-- Effective descent of morphisms between scalar extensions of affine groups, using the
single coefficient operator for a generator of the Galois group. -/
private theorem descend_equivariant_affine_map [IsGalois F K]
    {P Q : HopfAlgebraCategory F} (τ : Gal(K/F)) (hτ : Subgroup.zpowers τ = ⊤)
    (f : (groupBaseChange F K).obj (specGroup Q) ⟶
      (groupBaseChange F K).obj (specGroup P))
    (hf : (underlying K).map f ≫ coefficientChange τ (specGroup P) =
      coefficientChange τ (specGroup Q) ≫ (underlying K).map f) :
    ∃ g : specGroup Q ⟶ specGroup P, (groupBaseChange F K).map g = f := by
  let eP := extendedGroupIso K P
  let eQ := extendedGroupIso K Q
  let H := underlying K
  let a := (schemeHopfHomEquiv (extendedHopf K P) (extendedHopf K Q)).symm
    (eQ.hom ≫ f ≫ eP.inv)
  have ha : specGroupMap a = eQ.hom ≫ f ≫ eP.inv :=
    (schemeHopfHomEquiv _ _).apply_symm_apply _
  have ha' : specGroupMap a ≫ eP.hom = eQ.hom ≫ f := by
    rw [ha]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let cP := Spec.map (CommRingCat.ofHom (coefficientMap τ P).toRingHom)
  let cQ := Spec.map (CommRingCat.ofHom (coefficientMap τ Q).toRingHom)
  have hp : H.map eP.hom ≫ coefficientChange τ (specGroup P) = cP ≫ H.map eP.hom :=
    coefficientMap_spec τ P
  have hq : H.map eQ.hom ≫ coefficientChange τ (specGroup Q) = cQ ≫ H.map eQ.hom :=
    coefficientMap_spec τ Q
  have hmap : H.map (specGroupMap a) ≫ H.map eP.hom = H.map eQ.hom ≫ H.map f := by
    rw [← H.map_comp, ← H.map_comp, ha']
  have hcomm : H.map (specGroupMap a) ≫ cP = cQ ≫ H.map (specGroupMap a) := by
    apply (cancel_mono (H.mapIso eP).hom).mp
    change (_ ≫ _) ≫ H.map eP.hom = (_ ≫ _) ≫ H.map eP.hom
    rw [Category.assoc, ← hp, ← Category.assoc, hmap, Category.assoc, hf,
      ← Category.assoc, hq, Category.assoc]
    simp only [Category.assoc, hmap]
    rfl
  have halg : ∀ x : extendedHopf K P,
      a.hom (coefficientMap τ P x) = coefficientMap τ Q (a.hom x) := by
    let aR : CommRingCat.of (K ⊗[F] P) ⟶ CommRingCat.of (K ⊗[F] Q) :=
      CommRingCat.ofHom a.hom.toAlgHom.toRingHom
    let pR := CommRingCat.ofHom (coefficientMap τ P).toRingHom
    let qR := CommRingCat.ofHom (coefficientMap τ Q).toRingHom
    have hR : pR ≫ aR = aR ≫ qR := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp]
      exact hcomm
    intro x
    have h := congrArg (fun f : CommRingCat.of (K ⊗[F] P) ⟶
      CommRingCat.of (K ⊗[F] Q) ↦ f.hom x) hR
    exact h
  obtain ⟨g, hg⟩ := descend_standard_hom a (generator_equivariant τ hτ a halg)
  refine ⟨specGroupMap g, (cancel_epi eQ.hom).mp ?_⟩
  have hn : specGroupMap (extendedHopfMap K g) ≫ eP.hom =
      eQ.hom ≫ (groupBaseChange F K).map (specGroupMap g) :=
    Grp.hom_ext _ _ (extendedSpecIso_natural K g)
  rw [hg] at hn
  exact hn.symm.trans ha'

private theorem closedImmersion_of_affine_baseChange {P Q : HopfAlgebraCategory F}
    (g : specGroup Q ⟶ specGroup P)
    (hg : IsClosedImmersion ((groupBaseChange F K).map g).hom.hom.left) :
    IsClosedImmersion g.hom.hom.left := by
  let a := (schemeHopfHomEquiv P Q).symm g
  have ha : specGroupMap a = g := (schemeHopfHomEquiv _ _).apply_symm_apply _
  let eP := extendedGroupIso K P
  let eQ := extendedGroupIso K Q
  let H := underlying K
  have hn : specGroupMap (extendedHopfMap K a) ≫ eP.hom =
      eQ.hom ≫ (groupBaseChange F K).map (specGroupMap a) :=
    Grp.hom_ext _ _ (extendedSpecIso_natural K a)
  rw [ha] at hn
  have hn' : H.map (specGroupMap (extendedHopfMap K a)) =
      H.map eQ.hom ≫ H.map ((groupBaseChange F K).map g) ≫ H.map eP.inv := by
    have he := congrArg (fun f ↦ H.map (f ≫ eP.inv)) hn
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Functor.map_comp] using he
  have hcl : IsClosedImmersion (H.map (specGroupMap (extendedHopfMap K a))) := by
    rw [hn']
    change IsClosedImmersion ((H.mapIso eQ).hom ≫
      H.map ((groupBaseChange F K).map g) ≫ (H.mapIso eP).inv)
    let h' : IsClosedImmersion (H.map ((groupBaseChange F K).map g)) := hg
    let h'' := IsClosedImmersion.comp (H.map ((groupBaseChange F K).map g)) (H.mapIso eP).inv
    exact IsClosedImmersion.comp (H.mapIso eQ).hom _
  have hs := (hopfMapClosedImmersion K (extendedHopfMap K a)).mp hcl
  rw [← ha]
  apply (hopfMapClosedImmersion F a).mpr
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective F K a.hom.toLinearMap).mp
  have he : ∀ x, (a.hom.toLinearMap.lTensor K) x = (extendedHopfMap K a).hom x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r x => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  intro y
  obtain ⟨x, hx⟩ := hs y
  exact ⟨x, (he x).trans hx⟩

open scoped CategoryTheory.MonObj in
private theorem split_hom_ext {X Y : GroupScheme F} (hX : IsSplitTorus X) (hY : IsSplitTorus Y)
    {f g : X ⟶ Y} (h : ∀ t : Character Y, f ≫ t = g ≫ t) :
    f = g := by
  obtain ⟨r, ⟨e⟩⟩ := splitPresentation hX
  obtain ⟨s, ⟨d⟩⟩ := splitPresentation hY
  let M := StandardLattice.{u} r
  let N := StandardLattice.{u} s
  obtain ⟨a, ha⟩ := (splitGroupHomEquiv (k := F) N M).surjective (e.hom ≫ f ≫ d.inv)
  obtain ⟨b, hb⟩ := (splitGroupHomEquiv (k := F) N M).surjective (e.hom ≫ g ≫ d.inv)
  change specGroupMap (groupAlgebraMap F a) = _ at ha
  change specGroupMap (groupAlgebraMap F b) = _ at hb
  have eq : a = b := by
    apply MonoidHom.ext
    intro x
    apply (latticeCharacter (k := F) M).injective
    rw [← latticeCharacter_comp, ← latticeCharacter_comp, ha, hb]
    simpa only [Category.assoc] using
      congrArg (e.hom ≫ ·) (h (d.inv ≫ latticeCharacter (k := F) N x))
  rw [eq, hb] at ha
  exact (cancel_epi e.hom).mp ((cancel_mono d.inv).mp (by simpa only [Category.assoc] using ha.symm))

/-- The largest split subtorus in the fixed group of a split-torus automorphism. -/
private theorem fixed_split_subtorus {A : GroupScheme F} (hA : IsSplitTorus A) (b : A ≅ A) :
    ∃ T : ClosedSubgroup A, IsSplitTorus T.group ∧ T.inclusion ≫ b.hom = T.inclusion ∧
      ∀ {R : GroupScheme F}, IsSplitTorus R → ∀ f : R ⟶ A, f ≫ b.hom = f →
        ∃ g : R ⟶ T.group, g ≫ T.inclusion = f := by
  let χ (t : Character A) := (b.hom ≫ t) / t
  have hχ {R : GroupScheme F} (hR : IsSplitTorus R) (f : R ⟶ A) :
      (∀ t, f ≫ χ t = 1) ↔ f ≫ b.hom = f := by
    let pullback : Character A →* Character R :=
      { toFun := fun t ↦ f ≫ t
        map_one' := by simp
        map_mul' := fun x y ↦ Grp.hom_ext _ _ (MonObj.comp_mul f.hom.hom x.hom.hom y.hom.hom) }
    constructor
    · intro h
      apply split_hom_ext hR hA
      intro t
      have ht := h t
      change pullback ((b.hom ≫ t) / t) = 1 at ht
      rw [map_div, div_eq_one] at ht
      exact (Category.assoc f b.hom t).trans ht
    · intro h t
      change pullback ((b.hom ≫ t) / t) = 1
      rw [map_div, div_eq_one]
      exact (Category.assoc f b.hom t).symm.trans (congrArg (· ≫ t) h)
  obtain ⟨T, hT, hk, _, hfac⟩ := common_kernel hA χ
  exact ⟨T, hT, (hχ hT T.inclusion).mp hk, fun hR f hf ↦ hfac hR f ((hχ hR f).mpr hf)⟩

private theorem gm_isSplitTorus (F : Type u) [Field F] :
    IsSplitTorus (specGroup (groupAlgebra F IntegerCharacters)) := by
  obtain ⟨e⟩ := CharacterDescent.standardSplitTorus (k := F) 1
  let a : StandardLattice.{u} 1 ≃* IntegerCharacters.{u} :=
    MulEquiv.funUnique (Fin 1) IntegerCharacters
  exact ⟨1, ⟨(hopfSpec (CommRingCat.of F)).mapIso
    (CommHopfAlgCat.isoMk (MonoidAlgebra.domCongrBialgEquiv F F a)).op ≪≫ e⟩⟩

private theorem transported_coefficient (τ : Gal(K/F)) {U A D : GroupScheme F}
    (i : (groupBaseChange F K).obj U ≅ (groupBaseChange F K).obj A)
    (b : (groupBaseChange F K).obj A ≅ (groupBaseChange F K).obj A)
    (hi : i.hom.hom.hom.left ≫ coefficientChange τ A ≫ b.hom.hom.hom.left =
      coefficientChange τ U ≫ i.hom.hom.hom.left)
    (w : (groupBaseChange F K).obj D ⟶ (groupBaseChange F K).obj U)
    (j : D ⟶ A) (hj : w ≫ i.hom = (groupBaseChange F K).map j) :
    (underlying K).map w ≫ coefficientChange τ U ≫ (underlying K).map i.hom =
      coefficientChange τ D ≫ (underlying K).map (w ≫ i.hom ≫ b.hom) := by
  let H := underlying K
  have hh : H.map i.hom ≫ coefficientChange τ A ≫ H.map b.hom =
      coefficientChange τ U ≫ H.map i.hom := hi
  calc
    _ = H.map (w ≫ i.hom) ≫ coefficientChange τ A ≫ H.map b.hom := by
      rw [← hh, Functor.map_comp, Category.assoc]
    _ = (coefficientChange τ D ≫ H.map ((groupBaseChange F K).map j)) ≫ H.map b.hom := by
      rw [hj, ← Category.assoc, coefficientChange_natural τ j]
    _ = _ := by
      rw [← hj]
      simp only [Functor.map_comp, Category.assoc]
      rfl

/-- A finite cyclic descent datum on a split torus determines a largest split subtorus
on the descended group, and the cocharacters of that subtorus are exactly the
integral fixed cocharacters. -/
theorem largestSplitSubtorus : Specs.ExceptionalInnerSplitSubtorus.LargestSplitSubtorus.{u} := by
  intro F K _ _ _ _ _ τ hτ U A hA i b hi
  let B := groupBaseChange F K
  let H := underlying K
  obtain ⟨T, hT, hb, hfactor⟩ := fixed_split_subtorus (splitTorus_baseChange (K := K) hA) b
  obtain ⟨r, ⟨t⟩⟩ := splitPresentation hT
  let Q := splitCoordinates F r
  let D := specGroup Q
  let d : B.obj D ≅ T.group := (splitCoordinateChange (k := F) K r).symm ≪≫ t
  have hD : IsSplitTorus D := ⟨r, CharacterDescent.standardSplitTorus r⟩
  let w : B.obj D ⟶ B.obj U.val := d.hom ≫ T.inclusion ≫ i.inv
  have hw : w ≫ i.hom = d.hom ≫ T.inclusion := by simp [w]
  have hwfixed : w ≫ i.hom ≫ b.hom = w ≫ i.hom := by
    rw [← Category.assoc, hw, Category.assoc, hb]
  obtain ⟨j, hj⟩ := splitTorus_hom_descends hD hA (w ≫ i.hom)
  have hcomm := transported_coefficient τ i b hi w j hj.symm
  rw [hwfixed, H.map_comp w i.hom] at hcomm
  have heq : H.map w ≫ coefficientChange τ U.val = coefficientChange τ D ≫ H.map w := by
    apply (cancel_mono (H.mapIso i).hom).mp
    change (H.map w ≫ coefficientChange τ U.val) ≫ H.map i.hom =
      (coefficientChange τ D ≫ H.map w) ≫ H.map i.hom
    simp only [Category.assoc]
    exact hcomm
  obtain ⟨P, _, ⟨a⟩⟩ := groupPresentation U
  let v : B.obj D ⟶ B.obj (specGroup P) := w ≫ B.map a.inv
  have hv : H.map v ≫ coefficientChange τ (specGroup P) = coefficientChange τ D ≫ H.map v := by
    change H.map (w ≫ B.map a.inv) ≫ _ = _ ≫ H.map (w ≫ B.map a.inv)
    rw [Functor.map_comp, Category.assoc, coefficientChange_natural τ a.inv, ← Category.assoc,
      heq, Category.assoc]
  obtain ⟨g, hg⟩ := descend_equivariant_affine_map τ hτ v hv
  have hgc : IsClosedImmersion (H.map (B.map g)) := by
    rw [hg]
    change IsClosedImmersion (H.map (d.hom ≫ T.inclusion ≫ i.inv ≫ B.map a.inv))
    simp only [Functor.map_comp]
    change IsClosedImmersion ((H.mapIso d).hom ≫ H.map T.inclusion ≫
      (H.mapIso i).inv ≫ (H.mapIso (B.mapIso a)).inv)
    let hTclosed : IsClosedImmersion (H.map T.inclusion) := T.isClosedImmersion
    let hcomp := IsClosedImmersion.comp (H.mapIso i).inv (H.mapIso (B.mapIso a)).inv
    let hcomp' := IsClosedImmersion.comp (H.map T.inclusion)
      ((H.mapIso i).inv ≫ (H.mapIso (B.mapIso a)).inv)
    exact IsClosedImmersion.comp (H.mapIso d).hom _
  have hcl : IsClosedImmersion g.hom.hom.left := closedImmersion_of_affine_baseChange g hgc
  let S : ClosedSubgroup U.val :=
    ⟨D, g ≫ a.hom, IsClosedImmersion.comp g.hom.hom.left ((underlying F).mapIso a).hom⟩
  have hS : B.map S.inclusion = w := by
    change B.map (g ≫ a.hom) = w
    rw [B.map_comp, hg]
    change (w ≫ B.map a.inv) ≫ B.map a.hom = w
    rw [Category.assoc, ← B.map_comp, Iso.inv_hom_id, B.map_id, Category.comp_id]
  refine ⟨S, hD, ?_, ?_⟩
  · intro R hR
    let z := B.map R.inclusion
    obtain ⟨l, hl⟩ := splitTorus_hom_descends hR hA (z ≫ i.hom)
    have hc := transported_coefficient τ i b hi z l hl.symm
    rw [← Category.assoc, coefficientChange_natural τ R.inclusion, Category.assoc,
      ← Functor.map_comp] at hc
    let _ := coefficientChange_epi τ R.group
    have hz : z ≫ i.hom ≫ b.hom = z ≫ i.hom :=
      underlying_injective ((cancel_epi (coefficientChange τ R.group)).mp hc.symm)
    obtain ⟨m, hm⟩ := hfactor (splitTorus_baseChange (K := K) hR) (z ≫ i.hom) hz
    obtain ⟨n, hn⟩ := splitTorus_hom_descends hR hD (m ≫ d.inv)
    change B.map n = m ≫ d.inv at hn
    refine ⟨n, groupBaseChange_map_injective (K := K) ?_⟩
    apply (cancel_mono i.hom).mp
    change B.map (n ≫ S.inclusion) ≫ i.hom = z ≫ i.hom
    rw [B.map_comp, hn, hS, Category.assoc, hw, Category.assoc, Iso.inv_hom_id_assoc, hm]
  · change Function.Injective (fun η : Cocharacter (B.obj D) ↦ η ≫ B.map S.inclusion ≫ i.hom) ∧
      Set.range (fun η : Cocharacter (B.obj D) ↦ η ≫ B.map S.inclusion ≫ i.hom) =
        { μ | μ ≫ b.hom = μ }
    have hmap (η : Cocharacter (B.obj D)) :
        η ≫ B.map S.inclusion ≫ i.hom = η ≫ d.hom ≫ T.inclusion := by
      rw [hS, hw]
    let _ := T.isClosedImmersion
    let _ : Mono T.inclusion.hom.hom := Over.mono_of_mono_left _
    let _ : Mono T.inclusion := (Grp.forget _).mono_of_mono_map ‹Mono T.inclusion.hom.hom›
    constructor
    · intro x y h
      change x ≫ B.map S.inclusion ≫ i.hom = y ≫ B.map S.inclusion ≫ i.hom at h
      rw [hmap, hmap] at h
      exact (cancel_mono d.hom).mp ((cancel_mono T.inclusion).mp
        (by simpa only [Category.assoc] using h))
    · ext μ
      constructor
      · rintro ⟨η, rfl⟩
        change (η ≫ B.map S.inclusion ≫ i.hom) ≫ b.hom =
          η ≫ B.map S.inclusion ≫ i.hom
        rw [hmap, Category.assoc, Category.assoc, hb]
      · intro hμ
        obtain ⟨m, hm⟩ := hfactor (gm_isSplitTorus K) μ hμ
        refine ⟨m ≫ d.inv, ?_⟩
        change (m ≫ d.inv) ≫ B.map S.inclusion ≫ i.hom = μ
        rw [hmap, Category.assoc, Iso.inv_hom_id_assoc, hm]

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalInnerSplitSubtorus
