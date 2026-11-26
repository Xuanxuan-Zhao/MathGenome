import Specs.LinearAlgebraicGroups.RootData.BorelPositivity
import LinearAlgebraicGroups.RootData.BorelNormalizer
import LinearAlgebraicGroups.RootData.BorelsAndChambers
import LinearAlgebraicGroups.RootData.DatumAndWeyl
import LinearAlgebraicGroups.RootData.OrderedRootProducts
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.RootData.BorelPositivity

open _root_.LinearAlgebraicGroups.Specs
open Specs.AbstractPairing (Datum Root)
open Specs.BorelNormalizer (InducesTorusConjugation)
open Specs.BorelPositivity (BorelCorrespondence RadicalDecomposition WeylAction)
open Specs.BorelsAndChambers (IsPositiveSystem contractingSubgroup subgroupRoots)
open RootData.BorelNormalizer (weylSimplyTransitiveOnPositiveSystems)
open RootData.BorelsAndChambers
  (borelsThroughT positiveSystemsFromCocharacters regularCocharacterBorel)
open RootData.DatumAndWeyl (datumAndWeyl)
open RootData.OrderedRootProducts (contractingProduct)

open private lieImage_eq_of_same from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private automorphism_eq_of_weight inducedConjugation_unique labelConjugation
  quotientPoint_eq reflectionConjugation from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private pushSubgroup radical_transport subgroupIso
  from LinearAlgebraicGroups.RootData.OrderedRootProducts
open Specs.CharacterDescent (Character Cocharacter)
open Specs.GeometricBorelConjugacy (IsKBorel)
open Specs.GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical
  baseChangedSubgroup)
open Specs.RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open Specs.SchemeDerivedGroup (FactorsThrough IsSubgroupOf)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition multiplyFactors)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

private theorem subgroup_inclusion_trans {H : GroupScheme k} {A B C : ClosedSubgroup H}
    (hAB : IsSubgroupOf A B) (hBC : IsSubgroupOf B C) : IsSubgroupOf A C := by
  rcases hAB with ⟨f, hf⟩
  rcases hBC with ⟨g, hg⟩
  exact ⟨f ≫ g, by simpa only [Category.assoc, hg] using hf⟩

private theorem roots_eq_of_same {T B B' : ClosedSubgroup G.val}
    (h : SameSubgroup B B') : subgroupRoots T B = subgroupRoots T B' := by
  simp only [subgroupRoots, lieImage_eq_of_same h]

private theorem borelCorrespondence_of_chambers
    (hCochar : Specs.BorelsAndChambers.PositiveSystemsFromCocharacters.{u})
    (hBorels : Specs.BorelsAndChambers.BorelsThroughT.{u})
    (hG : IsReductive G) {T : ClosedSubgroup G.val} (hs : IsSplitTorus T.group)
    (hm : IsGeometricallyMaximal T) : BorelCorrespondence T := by
  obtain ⟨hRegular, hUnique⟩ := hBorels G hG T hs hm
  have positive (B : ClosedSubgroup G.val) (hB : IsKBorel B) (hTB : IsSubgroupOf T B) :
      IsPositiveSystem T (subgroupRoots T B) := by
    obtain ⟨c, _, hr, _, he⟩ := hRegular B hB hTB
    exact (hCochar G hG T hs hm _).mpr ⟨c, hr, he.symm⟩
  refine ⟨positive, ?_, ?_⟩
  · intro S hS
    obtain ⟨B, hB, hTB, he, _⟩ := (hUnique S).mp hS
    exact ⟨B, hB, hTB, he⟩
  · intro B B' hB hB' hTB hTB'
    refine ⟨?_, roots_eq_of_same⟩
    intro he
    obtain ⟨_, _, _, _, hC⟩ := (hUnique _).mp (positive B hB hTB)
    have hCB := hC B hB hTB rfl
    have hCB' := hC B' hB' hTB' he.symm
    exact ⟨subgroup_inclusion_trans hCB.2 hCB'.1, subgroup_inclusion_trans hCB'.2 hCB.1⟩

private theorem character_image {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (I : Specs.DatumAndWeyl.Identification D)
    (w : D.rootDatum.weylGroup) (S : Set (Root T)) :
    Subtype.val '' ((D.rootDatum.weylGroupToPerm w) '' S) =
      (fun χ : Character T.group ↦ (I.image.conjugation (I.labelEquiv w)).inv ≫ χ) ''
        (Subtype.val '' S) := by
  rw [Set.image_image, Set.image_image]
  apply congrArg (fun f : Root T → Character T.group ↦ f '' S)
  funext α
  have h := D.rootDatum.weylGroup_apply_root w α
  change w.val.weightEquiv (D.rootDatum.root α) =
    D.rootDatum.root (D.rootDatum.weylGroupToPerm w α) at h
  rw [D.root_eq, D.root_eq, I.characterAction, I.image.characterAction] at h
  exact (congrArg Additive.toMul h).symm

/-- Read the Weyl group label of the image of a rational normalizer point. -/
private def rationalWeylLabel {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (I : Specs.DatumAndWeyl.Identification D) :
    (𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X) →* D.rootDatum.weylGroup :=
  I.labelEquiv.symm.toMonoidHom.comp
    ((LocallyConstant.evalMonoidHom (IsLocalRing.closedPoint k)).comp
      ((I.image.constantGroup.families _).toMonoidHom.comp
        (IsMonHom.monoidHom I.quotient.hom.hom _)))

private theorem rationalWeylLabel_conjugation {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (I : Specs.DatumAndWeyl.Identification D)
    (n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X) :
    InducesTorusConjugation T (n ≫ I.normalizer.inclusion.hom.hom)
      (I.image.conjugation (I.labelEquiv (rationalWeylLabel I n))) := by
  let w := I.labelEquiv (rationalWeylLabel I n)
  let F := I.image.constantGroup.families (𝟙_ (SchemeOver k))
  have hw : w = F (n ≫ I.quotient.hom.hom) (IsLocalRing.closedPoint k) :=
    I.labelEquiv.apply_symm_apply _
  have hn : n ≫ I.quotient.hom.hom = toUnit _ ≫ I.image.constantGroup.sectionPoint w := by
    apply F.injective
    change I.image.constantGroup.families _ _ = I.image.constantGroup.families _ _
    rw [I.image.constantGroup.constant]
    apply LocallyConstant.ext
    intro x
    change F (n ≫ I.quotient.hom.hom) x = w
    rw [hw, Subsingleton.elim (α := PrimeSpectrum k) x (IsLocalRing.closedPoint k)]
  have hunit : toUnit (𝟙_ (SchemeOver k)) = 𝟙 (𝟙_ (SchemeOver k)) := Subsingleton.elim _ _
  exact labelConjugation I.image w n (by simpa only [hunit, Category.id_comp] using hn)

private theorem rationalWeylLabel_surjective {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (I : Specs.DatumAndWeyl.Identification D) :
    Function.Surjective (rationalWeylLabel I) := by
  intro w
  refine RootPairing.weylGroup.induction D.rootDatum
    (pred := fun x hx ↦ ∃ n, rationalWeylLabel I n = ⟨x, hx⟩) ?_ ?_ ?_ w.property
  · intro α
    obtain ⟨g, hg, e, he, hReflection⟩ := reflectionConjugation D α
    obtain ⟨n, hn⟩ := (I.representsNormalizer _ _).mp hg
    have hconj := inducedConjugation_unique (hn ▸ rationalWeylLabel_conjugation I n) he
    refine ⟨n, Subtype.ext (automorphism_eq_of_weight (D := D) ?_)⟩
    intro χ
    rw [I.characterAction, I.image.characterAction, hconj, hReflection]
  · exact ⟨1, map_one _⟩
  · rintro _ _ _ _ ⟨n, hn⟩ ⟨n', hn'⟩
    exact ⟨n * n', by rw [map_mul, hn, hn']; rfl⟩

private theorem label_eq_of_torus_factor {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (I : Specs.DatumAndWeyl.Identification D)
    (n n' : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X)
    (h : FactorsThrough T ((n ≫ I.normalizer.inclusion.hom.hom)⁻¹ *
      (n' ≫ I.normalizer.inclusion.hom.hom))) :
    rationalWeylLabel I n = rationalWeylLabel I n' := by
  exact congrArg (fun x ↦ I.labelEquiv.symm
    ((I.image.constantGroup.families _ x) (IsLocalRing.closedPoint k)))
    (quotientPoint_eq I.inclusion_eq I.isQuotient.1 n n' h)

private theorem weylAction_of_normalizer
    (hPositive : Specs.BorelNormalizer.WeylSimplyTransitiveOnPositiveSystems.{u})
    (hG : IsReductive G) {T : ClosedSubgroup G.val} (hs : IsSplitTorus T.group)
    (hm : IsGeometricallyMaximal T) [IsCommMonObj T.group.X]
    {D : Datum T} (I : Specs.DatumAndWeyl.Identification D) : WeylAction D := by
  have normalize (n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X) :=
    (I.representsNormalizer _ _).mpr ⟨n, rfl⟩
  have induces (n : 𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X) :
      InducesTorusConjugation T (n ≫ I.normalizer.inclusion.hom.hom)
        (I.image.conjugation (I.labelEquiv (rationalWeylLabel I n))) :=
    rationalWeylLabel_conjugation I n
  obtain ⟨hex, hstable, htrans⟩ := hPositive G hG T hs hm
  have image_eq {w : D.rootDatum.weylGroup} {S S' : Set (Root T)} :
      (D.rootDatum.weylGroupToPerm w) '' S = S' ↔
        (fun χ : Character T.group ↦ (I.image.conjugation (I.labelEquiv w)).inv ≫ χ) ''
          (Subtype.val '' S) = Subtype.val '' S' := by
    rw [← character_image I]
    exact ((Set.image_injective.mpr Subtype.val_injective).eq_iff).symm
  refine ⟨hex, ?_, ?_⟩
  · intro w S hS
    obtain ⟨n, hn⟩ := rationalWeylLabel_surjective I w
    obtain ⟨e, S', he, hS', hIm⟩ := hstable S hS _ (normalize n)
    have hc := inducedConjugation_unique he (induces n)
    rw [hc, hn] at hIm
    rw [image_eq.mpr hIm]
    exact hS'
  · intro S S' hS hS'
    obtain ⟨g, e, hg, he, hIm, hu⟩ := htrans S S' hS hS'
    obtain ⟨n, hn⟩ := (I.representsNormalizer _ _).mp hg
    let w := rationalWeylLabel I n
    have hc := inducedConjugation_unique (hn ▸ induces n) he
    refine ⟨w, image_eq.mpr (by rw [hc]; exact hIm), ?_⟩
    intro w' hw'
    obtain ⟨n', hn'⟩ := rationalWeylLabel_surjective I w'
    have hIm' := image_eq.mp hw'
    rw [← hn'] at hIm'
    have hf := (hu _ _ (normalize n') (induces n')).mp hIm'
    rw [← hn] at hf
    exact hn'.symm.trans (label_eq_of_torus_factor I n n' hf).symm


private theorem closedSubgroup_eq {H L : GroupScheme k} {f g : L ⟶ H}
    {hf : IsClosedImmersion f.hom.hom.left} {hg : IsClosedImmersion g.hom.hom.left}
    (h : f = g) : (⟨L, f, hf⟩ : ClosedSubgroup H) = ⟨L, g, hg⟩ := by
  subst g
  rfl

private theorem baseChanged_radical_transport {A B : AffineAlgebraicGroup k}
    (b : A.val ≅ B.val) (U : ClosedSubgroup A.val)
    (hU : IsClosedImmersion ((groupBaseChange k (AlgebraicClosure k)).map U.inclusion).hom.hom.left)
    (hr : IsUnipotentRadical (GeometricRadicals.GeometricGroup A)
      (baseChangedSubgroup (AlgebraicClosure k) U hU)) :
    ∃ hR : IsClosedImmersion ((groupBaseChange k (AlgebraicClosure k)).map
        (pushSubgroup b U).inclusion).hom.hom.left,
      IsUnipotentRadical (GeometricRadicals.GeometricGroup B)
        (baseChangedSubgroup (AlgebraicClosure k) (pushSubgroup b U) hR) := by
  let F := groupBaseChange k (AlgebraicClosure k)
  let Rbar := pushSubgroup (F.mapIso b) (baseChangedSubgroup (AlgebraicClosure k) U hU)
  have he : Rbar.inclusion = F.map (pushSubgroup b U).inclusion :=
    (F.map_comp U.inclusion b.hom).symm
  have hclosed : IsClosedImmersion (F.map (pushSubgroup b U).inclusion).hom.hom.left := by
    rw [← he]
    exact Rbar.isClosedImmersion
  refine ⟨hclosed, ?_⟩
  have hbase : IsUnipotentRadical (GeometricRadicals.GeometricGroup B) Rbar :=
    radical_transport (A := GeometricRadicals.GeometricGroup A)
      (B := GeometricRadicals.GeometricGroup B) (F.mapIso b) (baseChangedSubgroup (AlgebraicClosure k) U hU) hr
  have hEq : Rbar = baseChangedSubgroup (AlgebraicClosure k) (pushSubgroup b U) hclosed :=
    closedSubgroup_eq he
  exact hEq ▸ hbase

private theorem transportedLimitKernel {H C P : GroupScheme k}
    {c : Cocharacter H}
    (D : LimitDecomposition c)
    (a : C ≅ D.centralizer.group) (b : D.parabolic.group ≅ P) :
    IsPullback (D.contractingToParabolic ≫ b.hom).hom.hom
      (toUnit D.contracting.group.X) (b.inv ≫ D.limit ≫ a.inv).hom.hom η[C.X] := by
  let bX := (Grp.forget (SchemeOver k)).mapIso b
  let aX := (Grp.forget (SchemeOver k)).mapIso a
  refine D.isKernel.of_iso (Iso.refl D.contracting.group.X) bX
    (Iso.refl (𝟙_ (SchemeOver k))) aX.symm ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · subsingleton
  · change D.limit.hom.hom ≫ a.inv.hom.hom =
      b.hom.hom.hom ≫ (b.inv ≫ D.limit ≫ a.inv).hom.hom
    exact congrArg (fun f : D.parabolic.group ⟶ C ↦ f.hom.hom) (b.hom_inv_id_assoc (D.limit ≫ a.inv)).symm
  · change η[D.centralizer.group.X] ≫ a.inv.hom.hom = η[C.X] ≫ 𝟙 C.X
    rw [Category.comp_id]
    exact IsMonHom.one_hom a.inv.hom.hom

private theorem transportedLimitProduct {H C P : GroupScheme k}
    {c : Cocharacter H}
    (D : LimitDecomposition c)
    (a : C ≅ D.centralizer.group) (b : D.parabolic.group ≅ P) :
    IsIso (multiplyFactors (a.hom ≫ D.sectionMap ≫ b.hom)
      (D.contractingToParabolic ≫ b.hom)) := by
  let bX := (Grp.forget (SchemeOver k)).mapIso b
  let aX := (Grp.forget (SchemeOver k)).mapIso a
  let m : C.X ⊗ D.contracting.group.X ⟶ D.centralizer.group.X ⊗ D.contracting.group.X :=
    a.hom.hom.hom ⊗ₘ 𝟙 _
  have : IsIso a.hom.hom.hom := aX.isIso_hom
  have : IsIso b.hom.hom.hom := bX.isIso_hom
  have : IsIso m := inferInstanceAs (IsIso (a.hom.hom.hom ⊗ₘ 𝟙 D.contracting.group.X))
  have := D.product_iso
  have hmul : m ≫ multiplyFactors D.sectionMap D.contractingToParabolic ≫ b.hom.hom.hom =
      multiplyFactors (a.hom ≫ D.sectionMap ≫ b.hom) (D.contractingToParabolic ≫ b.hom) := by
    simp only [m, multiplyFactors, ← Category.assoc, MonObj.mul_comp]
    simp only [MonObj.comp_mul, Category.assoc, tensorHom_fst_assoc,
      tensorHom_snd_assoc, Category.id_comp]
    rfl
  rw [← hmul]
  infer_instance

private theorem decomposition_of_cocharacter
    (hRegular : Specs.BorelsAndChambers.RegularCocharacterBorel.{u})
    (hBorels : Specs.BorelsAndChambers.BorelsThroughT.{u})
    (hProduct : Specs.OrderedRootProducts.ContractingProduct.{u})
    (hG : IsReductive G) {T B : ClosedSubgroup G.val} (hs : IsSplitTorus T.group)
    (hm : IsGeometricallyMaximal T) (hB : IsKBorel B) (hTB : IsSubgroupOf T B) :
    RadicalDecomposition T B := by
  obtain ⟨c, D, hc, hBD, hroots⟩ := (hBorels G hG T hs hm).1 B hB hTB
  obtain ⟨hC, _, _, _, hU, hRbar, hUbar⟩ := hRegular G hG T hs hm c hc D
  obtain ⟨a, ha⟩ := subgroupIso (A := T) (B := D.centralizer) ⟨hC.2, hC.1⟩
  obtain ⟨b, hb⟩ := subgroupIso (A := D.parabolic) (B := B) ⟨hBD.2, hBD.1⟩
  let U := contractingSubgroup D
  let R := pushSubgroup b U
  let j := a.hom ≫ D.sectionMap ≫ b.hom
  let q := b.inv ≫ D.limit ≫ a.inv
  have hR : IsUnipotentRadical (closedSubgroupAlgebraicGroup B) R :=
    radical_transport (A := closedSubgroupAlgebraicGroup D.parabolic)
      (B := closedSubgroupAlgebraicGroup B) b U hU
  have hbase := baseChanged_radical_transport (A := closedSubgroupAlgebraicGroup D.parabolic)
    (B := closedSubgroupAlgebraicGroup B) b U hRbar hUbar
  refine ⟨R, j, q, hR, hbase, ?_, ?_, transportedLimitKernel D a b,
    transportedLimitProduct D a b, ?_⟩
  · simp only [j, Category.assoc, hb, D.section_in_G, ha]
  · simp only [j, q, Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% D.section_limit, Iso.hom_inv_id]
  · intro V l hl
    rw [hroots] at hl
    obtain ⟨p, hp⟩ := ((hProduct G hG T hs hm).2.2 c).2 D V l hl
    refine ⟨p, ?_⟩
    have he : R.inclusion ≫ B.inclusion = D.contracting.inclusion := by
      change (D.contractingToParabolic ≫ b.hom) ≫ B.inclusion = D.contracting.inclusion
      rw [Category.assoc, hb, D.contracting_in_G]
    rw [show R.inclusion.hom.hom ≫ B.inclusion.hom.hom = D.contracting.inclusion.hom.hom from
      congrArg (fun f : D.contracting.group ⟶ G.val ↦ f.hom.hom) he]
    exact hp

/-- The Borel correspondence, the simply transitive action of the Weyl group,
and the ordered root group description of the unipotent radical. -/
theorem borelPositivity : Specs.BorelPositivity.Statement.{u} := by
  intro k _ G hG T hs hm
  obtain ⟨hcomm, D, ⟨I⟩⟩ := datumAndWeyl G hG T hs hm
  have := hcomm
  refine ⟨hcomm, D, ⟨I⟩,
    borelCorrespondence_of_chambers positiveSystemsFromCocharacters borelsThroughT hG hs hm,
    weylAction_of_normalizer weylSimplyTransitiveOnPositiveSystems hG hs hm I,
    (contractingProduct G hG T hs hm).2.1, ?_⟩
  intro B hB hTB
  exact decomposition_of_cocharacter regularCocharacterBorel borelsThroughT contractingProduct
    hG hs hm hB hTB

end

end LinearAlgebraicGroups.RootData.BorelPositivity
