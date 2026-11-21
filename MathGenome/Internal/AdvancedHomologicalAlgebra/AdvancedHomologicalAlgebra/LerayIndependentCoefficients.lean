import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.LerayIndependentCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.LerayAndDegenerations
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedSectionsIndependentCoefficients
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
open TopologicalSpace Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 1000000

namespace AdvancedHomologicalAlgebra.LerayIndependentCoefficients

open SheafTheory HigherDirectImageLocalTheory HigherDirectImagesOriginalTheory
open OriginalDerivedSectionsTheory DerivedSectionsTheory SheafUniverseTransport
open Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients
open Specs.AdvancedHomologicalAlgebra.LerayIndependentCoefficients

open private siteTransportData cohomologyCoherence exactDescent derivedModelTransport
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DerivedSectionsIndependentCoefficients
open GrothendieckSpectralSequence GrothendieckEdges HypercohomologyDerivedNaturality
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

attribute [local instance] HasDerivedCategory.standard

section Diagram

variable {C C' : Type*} [Category* C] [Category* C'] [Abelian C] [Abelian C']
    (E : C ⥤ C') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]

private theorem filteredChange (X : RowDiagram C)
    (h : FilteredAbutment X) : FilteredAbutment (changeCoefficientsObj E X) := by
  constructor
  · intro p n
    haveI := h.mono p n
    exact E.map_mono _
  · intro p n
    exact (E.map_comp _ _).symm.trans (congrArg E.map (h.down_inclusion p n))
  · intro n
    obtain ⟨N, hN⟩ := h.converges n
    refine ⟨N, fun r hr p ↦ ?_⟩
    obtain ⟨hd, ⟨e⟩⟩ := hN r hr p
    refine ⟨?_, ⟨changeGradedIso E X r p n e⟩⟩
    change E.map (X.differential r p n) = 0
    rw [hd, E.map_zero]

private lemma changeGradedProjection (X : RowDiagram C) (k : ℕ) (p n : ℤ)
    (e : X.page k p n ≅ cokernel (X.down p n)) :
    cokernel.π ((changeCoefficientsObj E X).down p n) ≫ (changeGradedIso E X k p n e).inv =
      E.map (cokernel.π (X.down p n) ≫ e.inv) := by
  change cokernel.π (E.map (X.down p n)) ≫
      ((PreservesCokernel.iso E (X.down p n)).inv ≫ E.map e.inv) = _
  rw [← PreservesCokernel.π_iso_hom, assoc, Iso.hom_inv_id_assoc, E.map_comp]

variable (X : RowDiagram C)

private theorem zeroOnLaterPages (p n : ℤ) (h : IsZero (X.page 0 p n)) (r : ℕ) :
    IsZero (X.page r p n) := by
  induction r with
  | zero => exact h
  | succ r ih =>
    let d := (r : ℤ) + 2
    have e := X.nextIso r (p - d) (n - 1)
    have hz : IsZero ((RowDiagram.pageComplex X r (p - d) (n - 1)).X₂) := by
      change IsZero (X.page r (p - d + d) (n - 1 + 1))
      simpa only [sub_add_cancel] using ih
    simpa only [sub_add_cancel, d] using
      (ShortComplex.isZero_homology_of_isZero_X₂ _ hz).of_iso e

private theorem downIso (h : FilteredAbutment X) (p n : ℤ) (hz : IsZero (X.page 0 p n)) :
    IsIso (X.down p n) := by
  haveI : Mono (X.down p n ≫ X.inclusion p n) := by
    rw [h.down_inclusion]
    exact h.mono (p + 1) n
  haveI : Mono (X.down p n) := mono_of_mono _ (X.inclusion p n)
  obtain ⟨N, hN⟩ := h.converges n
  obtain ⟨_, ⟨e⟩⟩ := hN N le_rfl p
  have hz' := (zeroOnLaterPages X p n hz N).of_iso e.symm
  haveI : Epi (X.down p n) :=
    Abelian.epi_of_cokernel_π_eq_zero _ (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- Vanishing outside an interval of the second page forces the stated
filtration bounds, starting from any effective bounds of the finite model. -/
private theorem boundsFromSupport (h : FilteredAbutment X) (n : ℤ)
    (hfinite : ∃ a b : ℤ, (∀ p, p ≤ a → IsIso (X.inclusion p n)) ∧
      (∀ p, b ≤ p → IsZero (X.step p n)))
    (upper : ℤ) (left : ∀ p : ℤ, p < 0 → IsZero (X.page 0 p n))
    (right : ∀ p : ℤ, upper < p → IsZero (X.page 0 p n)) (p : ℤ) :
    (p ≤ 0 → IsIso (X.inclusion p n)) ∧ (upper < p → IsZero (X.step p n)) := by
  obtain ⟨a, b, ha, hb⟩ := hfinite
  constructor
  · intro hp
    let base := min a p
    have hk : ∀ k : ℕ, base + (k : ℤ) ≤ p → IsIso (X.inclusion (base + k) n) := by
      intro k
      induction k with
      | zero => intro _; rw [Int.natCast_zero, add_zero]; exact ha base (min_le_left _ _)
      | succ k ih =>
        intro hk
        have heq : base + (↑(k + 1) : ℤ) = base + (k : ℤ) + 1 := by omega
        haveI := ih (by omega)
        haveI := downIso X h (base + k) n (left _ (by omega))
        rw [heq, ← h.down_inclusion]
        infer_instance
    have heq : base + (↑((p - base).toNat) : ℤ) = p := by
      have := min_le_right a p
      dsimp [base]
      omega
    have hfin := hk (p - base).toNat (by omega)
    rw [heq] at hfin
    exact hfin
  · intro hp
    let base := max b p
    have hk : ∀ k : ℕ, p ≤ base - (k : ℤ) → IsZero (X.step (base - k) n) := by
      intro k
      induction k with
      | zero => intro _; simpa using hb base (le_max_left _ _)
      | succ k ih =>
        intro hk
        let j := base - (↑(k + 1) : ℤ)
        have heq : j + 1 = base - (k : ℤ) := by dsimp [j]; omega
        have hz : IsZero (X.step (j + 1) n) := by rw [heq]; exact ih (by omega)
        haveI := downIso X h j n (right _ (by dsimp [j]; omega))
        exact hz.of_iso (asIso (X.down j n)).symm
    have heq : base - (↑((base - p).toNat) : ℤ) = p := by
      have := le_max_right b p
      dsimp [base]
      omega
    simpa only [heq] using hk (base - p).toNat (by omega)

end Diagram

section Coordinates

variable {C C' : Type*} [Category* C] [Category* C'] (e : C ≌ C')
  {A B : C} {A' B' : C'}

/-- A commuting change-of-coordinates square, read using the inverse
equivalence at its upper edge. -/
private theorem inverseSquare (s : A ≅ B) (t : A' ≅ B')
    (x : e.functor.obj A ≅ A') (y : e.functor.obj B ≅ B')
    (h : e.functor.mapIso s ≪≫ y = x ≪≫ t) :
    e.inverse.map t.inv ≫ e.inverse.map x.inv ≫ e.unitIso.inv.app A =
      e.inverse.map y.inv ≫ e.unitIso.inv.app B ≫ s.inv := by
  have hinv := congrArg Iso.inv h
  change y.inv ≫ e.functor.map s.inv = t.inv ≫ x.inv at hinv
  rw [← e.inverse.map_comp_assoc, ← hinv, e.inverse.map_comp, assoc]
  congr 1
  exact e.unitIso.inv.naturality s.inv

private lemma mapStalkSquare {A C C' : Type*} [Category* A] [Category* C] [Category* C']
    (F H : A ⥤ C) (e : F ≅ H) (B : C ⥤ C') {I J : A} (z : I ≅ J)
    {U : C} {V : C'} (c : H.obj I ⟶ U) (w : B.obj U ⟶ V) :
    B.map (F.map z.hom) ≫ B.map (e.hom.app J) ≫ B.map (H.map z.inv ≫ c) ≫ w =
      B.map (e.hom.app I) ≫ B.map c ≫ w := by
  have h : F.map z.hom ≫ e.hom.app J ≫ H.map z.inv ≫ c = e.hom.app I ≫ c := by
    rw [← assoc (F.map z.hom), e.hom.naturality, assoc,
      ← H.map_comp_assoc, z.hom_inv_id, H.map_id, id_comp]
  simpa only [Functor.map_comp, assoc] using congrArg (fun t ↦ B.map t ≫ w) h

end Coordinates

section Original

universe a m u v r s

variable {X : TopCat.{u}} {Y : TopCat.{v}} {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}}
    (f : RingedMap R S)

set_option hygiene false in
local notation "AX" => AmbientSheaves.{max a m v s} R
set_option hygiene false in
local notation "AY" => AmbientSheaves.{max a m u r} S
set_option hygiene false in
local notation "CY" => SectionModules.{max a m u r} S ⊤
set_option hygiene false in
local notation "R'" => liftedRing.{max a m v s} R
set_option hygiene false in
local notation "S'" => liftedRing.{max a m u r} S
set_option hygiene false in
local notation "D" => ambientDirectImage.{max a m} f
set_option hygiene false in
local notation "D'" => transportedDirectImage.{max a m} f
set_option hygiene false in
local notation "GY" => sectionsValue.{max a m u r} S (⊤ : Opens Y)
set_option hygiene false in
local notation "GY'" => DerivedSectionsTheory.globalSections S'
set_option hygiene false in
local notation "JX" => transport.{max a m v s} R
set_option hygiene false in
local notation "JY" => transport.{max a m u r} S
set_option hygiene false in
local notation "LY" => ModuleCat.restrictScalars.{max a m u v r s}
  (sectionRingEquiv.{max a m u r} S (⊤ : Opens (liftedSpace.{max a m u v r s} Y))).symm.toRingHom
set_option hygiene false in
local notation "LiftX" => liftSheafCoefficients.{max a u v r s,u,r,m} R
set_option hygiene false in
local notation "FM" => transportedMap.{max a m} f
set_option hygiene false in
local notation "FS" => transportedScalars.{max a m} f
set_option hygiene false in
local notation "B" => originalScalarsFunctor.{a,m,u,v,r,s} (S := S)
set_option hygiene false in
local notation "IX" => d.site.functor
set_option hygiene false in
local notation "SX" => sheafInput.{a,m,u,v,r,s} (R := R)

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{max a m u v r s}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{max a m u v r s}]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{max a m u v r s}]
    [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{max a m u v r s}]
    [EnoughInjectives AX] [EnoughInjectives AY]
    [(JX).IsEquivalence] [(JY).IsEquivalence]

variable (L : liftedLeray.{a,m} f) {c : SectionsData.{max a m} f}
  (d : SiteTransportData.{max a m} f c L.sections) (h : PageTransport.{a,m} f d)

private def pageTransport (c : SectionsData.{max a m} f) :
    PageTransport.{a,m} f (siteTransportData.{max a m} f c L.sections) where
  targetSite := exactDescent JY
  pushforward := derivedModelTransport D D' JX JY
    (pushforwardTransportExpected.{max a m,u,v,r,s} f)
    (fun M hM ↦ ((JX).asEquivalence.map_injective_iff M).mpr hM)
  sections := derivedModelTransport GY GY' JY LY (targetSectionsSquare.{max a m} f)
    (fun M hM ↦ ((JY).asEquivalence.map_injective_iff M).mpr hM)

/-- The exact coordinates in HA-H06-Carrier agree with the cohomology of the
same lifted HA-H06 comparison after cancelling the composition isomorphism. -/
private lemma liftedTargetNormalized (n : ℤ) :
    L.derivedTargetIso n = L.package.iteratedIso n ≪≫ (d.coordinates.cohomologyIso f n).symm := by
  rw [LerayAndDegenerations.LerayData.derivedTargetIso, L.package.canonical]
  apply Iso.ext
  apply NatTrans.ext
  funext K
  let V := (DerivedSectionsTheory.globalSections R').rightDerivedFunctorPlus.obj K
  let H := DerivedCategory.homologyFunctor
    (ModuleCat.{max a m u v r s} (sectionRing S' ⊤)) n
  let e := d.coordinates
  have ht : DerivedCategory.Plus.ι.map (e.identify.hom.app V) ≫
      e.descent.termwise.hom.app V = L.sections.restriction.termwise.hom.app V :=
    congrArg (fun i ↦ i.hom.app V) e.termwise
  have hh : (e.descent.cohomology n).hom.app V =
      H.map (e.descent.termwise.hom.app V) ≫
        (L.sections.restriction.homology n).hom.app (DerivedCategory.Plus.ι.obj V) := by
    have hh := congrArg (fun i ↦ i.hom.app V) (e.homology n)
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerRight_hom,
      isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, associator_hom_app, associator_inv_app,
      id_comp, comp_id] using hh
  have he : H.map (L.sections.restriction.termwise.hom.app V) ≫
      (L.sections.restriction.homology n).hom.app (DerivedCategory.Plus.ι.obj V) =
      (DerivedCategory.Plus.homologyFunctor _ n).map (e.identify.hom.app V) ≫
        (e.descent.cohomology n).hom.app V := by
    rw [hh]
    change _ = H.map (DerivedCategory.Plus.ι.map (e.identify.hom.app V)) ≫ _
    rw [← H.map_comp_assoc, ht]
  simp only [LerayAndDegenerations.LerayData.comparison, SectionsDerivedData.cohomologyIso,
    LiftedRestrictionCoordinates.cohomologyIso, LiftedRestrictionCoordinates.iterated,
    SectionsDerivedData.iteratedIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom, isoWhiskerRight_inv,
    isoWhiskerLeft_inv, whiskerRight_app, whiskerLeft_app, associator_hom_app,
    associator_inv_app, Functor.map_comp, assoc, comp_id, id_comp]
  rw [he]
  erw [id_comp]

private lemma abutmentCommutes (hc : d.CohomologyCoherence f) (n : ℤ) :
    derivedTargetIso.{a,m} f L d n = derivedTargetViaComparison.{a,m} f L d n := by
  have hl := liftedTargetNormalized.{a,m} f L d n
  apply Iso.ext
  apply NatTrans.ext
  funext K
  let E := targetScalarEquivalence.{a,m,u,v,r,s} (S := S)
  have hs : E.functor.mapIso ((c.cohomologyIso n).app K) ≪≫
      (iteratedAbutmentCoordinates.{a,m} f d n).app K =
    (derivedAbutmentCoordinates.{a,m} f d n).app K ≪≫
      (d.coordinates.cohomologyIso f n).app ((IX).obj K) := by
    apply Iso.ext
    simp only [iteratedAbutmentCoordinates, derivedAbutmentCoordinates,
      Iso.app_hom, Iso.trans_hom, Functor.mapIso_hom, NatTrans.comp_app,
      associator_hom_app, id_comp]
    exact hc K n
  have hInv := inverseSquare E ((c.cohomologyIso n).app K)
    ((d.coordinates.cohomologyIso f n).app ((IX).obj K))
    ((derivedAbutmentCoordinates.{a,m} f d n).app K)
    ((iteratedAbutmentCoordinates.{a,m} f d n).app K) hs
  simp only [derivedTargetIso, derivedTargetViaComparison, hl, lowerCoordinates,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_inv, Functor.map_comp, assoc]
  exact congrArg (fun k ↦ (B).map ((L.package.iteratedIso n).hom.app ((IX).obj K)) ≫ k) hInv

private lemma stalkAbutmentCommutes (M : SheafOfModules.{m} R) (n : ℕ) :
    ((sequenceOnStalkIso.{a,m} f L d).hom.app M).target (n : ℤ) ≫
      (sheafTargetIso.{a,m} f L d n).hom.app M =
    (derivedTargetIso.{a,m} f L d n).hom.app
      ((DerivedCategory.Plus.singleFunctor AX 0).obj ((LiftX).obj M)) := by
  let A := (DerivedCategory.Plus.singleFunctor AX 0).obj ((LiftX).obj M)
  let z := (sheafStalkCoordinate.{a,m} f d).app M
  let C := LerayAndDegenerations.hypercohomology R' (n : ℤ) ⋙ liftedRestriction.{max a m} f
  let P := sequence D' GY' L.package.row
  let e := L.derivedTargetIso (n : ℤ)
  let c := (derivedAbutmentCoordinates.{a,m} f d (n : ℤ)).inv.app A
  let w := (targetScalarEquivalence.{a,m,u,v,r,s} (S := S)).unitIso.inv.app ((derivedTargetValue.{a,m} f (n : ℤ)).obj A)
  have hSeq : ((sequenceOnStalkIso.{a,m} f L d).hom.app M).target (n : ℤ) =
      (B).map ((P ⋙ targetEval (n : ℤ)).map z.hom) := by
    change (𝟙 _ ≫ (P ⋙ changeCoefficients B).map z.hom ≫ 𝟙 _).target (n : ℤ) = _
    rw [id_comp, comp_id]
    rfl
  have hCoord : (sheafAbutmentCoordinates.{a,m} f d n).inv.app M = C.map z.inv ≫ c := by
    change C.map z.inv ≫ 𝟙 _ ≫ c = _
    rw [id_comp]
  rw [hSeq]
  dsimp only [sheafTargetIso, derivedTargetIso, lowerCoordinates, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_inv, LerayAndDegenerations.LerayData.sheafTargetIso]
  rw [hCoord]
  exact mapStalkSquare (P ⋙ targetEval (n : ℤ)) C e B z c w

private lemma stalkSecondCommutes (M : SheafOfModules.{m} R) (p q : ℕ) :
    ((sequenceOnStalkIso.{a,m} f L d).hom.app M).page 0 (p : ℤ) ((p : ℤ) + (q : ℤ)) ≫
      (sheafSecondIso.{a,m} f L d h p q).hom.app M =
    (derivedSecondIso.{a,m} f L d h p (q : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor AX 0).obj ((LiftX).obj M)) := by
  let A := (DerivedCategory.Plus.singleFunctor AX 0).obj ((LiftX).obj M)
  let z := (sheafStalkCoordinate.{a,m} f d).app M
  let H := secondValue D' GY' p (q : ℤ)
  let P := sequence D' GY' L.package.row
  let Q := pageEval (C := ModuleCat.{max a m u v r s} (sectionRing S' ⊤))
    0 (p : ℤ) ((p : ℤ) + (q : ℤ))
  let e := L.derivedSecondIso p (q : ℤ)
  let v := (derivedPageCoordinates.{a,m} f h p (q : ℤ)).inv.app A
  let w := (targetScalarEquivalence.{a,m,u,v,r,s} (S := S)).unitIso.inv.app
    ((derivedSecondValue.{a,m} f p (q : ℤ)).obj A)
  have hSeq : ((sequenceOnStalkIso.{a,m} f L d).hom.app M).page
      0 (p : ℤ) ((p : ℤ) + (q : ℤ)) = (B).map ((P ⋙ Q).map z.hom) := by
    change (𝟙 _ ≫ (P ⋙ changeCoefficients B).map z.hom ≫ 𝟙 _).page
      0 (p : ℤ) ((p : ℤ) + (q : ℤ)) = _
    rw [id_comp, comp_id]
    rfl
  have hCoord : (sheafPageCoordinates.{a,m} f h p q).inv.app M = H.map z.inv ≫ v := by
    change H.map z.inv ≫ 𝟙 _ ≫ v = _
    rw [id_comp]
  have hPage : (L.sheafSecondIso p q).hom.app ((SX).obj M) =
      e.hom.app ((DerivedCategory.Plus.singleFunctor (Modules R') 0).obj ((SX).obj M)) := by
    simp only [LerayAndDegenerations.LerayData.sheafSecondIso, L.edges.objectCase.secondIso_eq,
      e, LerayAndDegenerations.LerayData.derivedSecondIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
      associator_hom_app, associator_inv_app, id_comp]
    erw [comp_id]
  rw [hSeq]
  dsimp only [sheafSecondIso, derivedSecondIso, lowerCoordinates, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, Iso.app_inv]
  rw [hCoord, hPage]
  exact mapStalkSquare (P ⋙ Q) H e B z v w

private lemma liftedRowSquare (M : Modules R') (n : ℕ) :
    (L.edges.rowPage n).hom.app M ≫ (L.rowEdge n).app M =
      (L.edges.filtered M).row n ≫ (L.sheafTargetIso n).hom.app M := by
  have h := L.edges.first_comparison n M
  rw [L.edges.target_identification n] at h
  simp only [LerayAndDegenerations.LerayData.rowEdge,
    LerayAndDegenerations.LerayData.sheafTargetIso, LerayAndDegenerations.LerayData.derivedTargetIso,
    NatTrans.comp_app, Iso.trans_hom, isoWhiskerLeft_hom, whiskerLeft_app] at h ⊢
  rw [← assoc, h, assoc]

private lemma liftedColumnSquare (M : Modules R') (n : ℕ) :
    (L.sheafTargetIso n).hom.app M ≫ (L.columnEdge n).app M =
      (L.edges.filtered M).column n ≫ (L.edges.columnPage n).hom.app M := by
  have h := L.edges.second_comparison n M
  rw [L.edges.target_identification n] at h
  simp only [LerayAndDegenerations.LerayData.columnEdge,
    LerayAndDegenerations.LerayData.sheafTargetIso, LerayAndDegenerations.LerayData.derivedTargetIso,
    NatTrans.comp_app, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerLeft_inv, whiskerLeft_app,
    assoc, Iso.hom_inv_id_app_assoc] at h ⊢
  exact h

private lemma originalRowSquare (M : SheafOfModules.{m} R) (n : ℕ) :
    (rowPageIso.{a,m} f L d h n).hom.app M ≫ (rowEdge.{a,m} f L d h n).app M =
      (B).map ((L.edges.filtered ((SX).obj M)).row n) ≫
        (sheafTargetIso.{a,m} f L d n).hom.app M := by
  simp only [rowPageIso, rowEdge, sheafTargetIso, NatTrans.comp_app, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    assoc, Iso.hom_inv_id_app_assoc]
  rw [← (B).map_comp_assoc, liftedRowSquare.{a,m} f L, (B).map_comp, assoc]

private lemma originalColumnSquare (M : SheafOfModules.{m} R) (n : ℕ) :
    (sheafTargetIso.{a,m} f L d n).hom.app M ≫ (columnEdge.{a,m} f L d h n).app M =
      (B).map ((L.edges.filtered ((SX).obj M)).column n) ≫
        (columnPageIso.{a,m} f L d h n).hom.app M := by
  simp only [columnPageIso, columnEdge, sheafTargetIso, NatTrans.comp_app, Iso.trans_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    assoc, Iso.hom_inv_id_app_assoc]
  rw [← (B).map_comp_assoc, liftedColumnSquare.{a,m} f L, (B).map_comp, assoc]

private lemma derivedFiltered (K : DerivedCategory.Plus AX) :
    FilteredAbutment ((derivedSequence.{a,m} f L d).obj K) :=
  filteredChange B _ ⟨L.package.inclusion_mono ((IX).obj K),
    L.package.down_inclusion ((IX).obj K), L.package.convergence ((IX).obj K)⟩

private lemma sheafFiltered (M : SheafOfModules.{m} R) :
    FilteredAbutment ((sheafSequence.{a,m} f L).obj M) :=
  filteredChange B _ ⟨L.package.inclusion_mono ((DerivedCategory.Plus.singleFunctor (Modules R') 0).obj ((SX).obj M)),
    L.package.down_inclusion _, L.package.convergence _⟩

include d h in
private lemma derivedSupport (K : DerivedCategory.Plus AX) (b : ℤ) (hK : K.IsGE b)
    (k : ℕ) (p n : ℤ) (outside : p < 0 ∨ n - p < b) :
    IsZero (((derivedSequence.{a,m} f L d).obj K).page k p n) := by
  apply zeroOnLaterPages
  by_cases hp : p < 0
  · have e := L.package.negative ((IX).obj K) p (n - p) hp
    have heq : p + (n - p) = n := by omega
    rw [heq] at e
    exact (B).map_isZero e
  · let p₀ := p.toNat
    have hp₀ : (p₀ : ℤ) = p := Int.toNat_of_nonneg (by omega)
    have hpn : (p₀ : ℤ) + (n - p) = n := by omega
    have hD := preservesLowerBounds AX AY D K b hK
    letI := hD
    have hz := DerivedCategory.Plus.isZero_homology_of_isGE ((D).rightDerivedFunctorPlus.obj K)
      b (n - p) (by omega)
    let C := cohomologyValue.{max a m u r} S ⊤ p₀
    letI : C.Additive := by dsimp [C, cohomologyValue, rightValue]; infer_instance
    have hz' := (C.map_isZero hz).of_iso ((derivedSecondIso.{a,m} f L d h p₀ (n - p)).app K)
    change IsZero (((derivedSequence.{a,m} f L d).obj K).page 0 (p₀ : ℤ) ((p₀ : ℤ) + (n - p))) at hz'
    rw [hpn, hp₀] at hz'
    exact hz'

private lemma sheafSupport (M : SheafOfModules.{m} R) (k : ℕ) (p n : ℤ)
    (h : p < 0 ∨ n < p) : IsZero (((sheafSequence.{a,m} f L).obj M).page k p n) :=
  zeroOnLaterPages _ p n ((B).map_isZero (L.edges.objectCase.quadrant ((SX).obj M) p n h)) k

private lemma finiteChange (A : RowDiagram _) (n : ℤ)
    (h : ∃ a b : ℤ, (∀ p, p ≤ a → IsIso (A.inclusion p n)) ∧
      (∀ p, b ≤ p → IsZero (A.step p n))) :
    ∃ a b : ℤ, (∀ p, p ≤ a → IsIso ((changeCoefficientsObj B A).inclusion p n)) ∧
      (∀ p, b ≤ p → IsZero ((changeCoefficientsObj B A).step p n)) := by
  obtain ⟨lo, hi, hl, hh⟩ := h
  refine ⟨lo, hi, ?_, fun p hp ↦ (B).map_isZero (hh p hp)⟩
  intro p hp
  haveI := hl p hp
  change IsIso ((B).map (A.inclusion p n))
  infer_instance

include d h in
private lemma derivedBounds (K : DerivedCategory.Plus AX) (b : ℤ) (hK : K.IsGE b) (p n : ℤ) :
    (p ≤ 0 → IsIso (((derivedSequence.{a,m} f L d).obj K).inclusion p n)) ∧
    (n - b < p → IsZero (((derivedSequence.{a,m} f L d).obj K).step p n)) :=
  boundsFromSupport _ (derivedFiltered.{a,m} f L d K) n (finiteChange.{a,m,u,v,r,s} (S := S) _ n (L.package.finite ((IX).obj K) n))
    (n - b) (fun i hi ↦ derivedSupport.{a,m} f L d h K b hK 0 i n (Or.inl hi))
    (fun i hi ↦ derivedSupport.{a,m} f L d h K b hK 0 i n (Or.inr (by omega))) p

private lemma sheafBounds (M : SheafOfModules.{m} R) (p n : ℤ) :
    (p ≤ 0 → IsIso (((sheafSequence.{a,m} f L).obj M).inclusion p n)) ∧
    (n < p → IsZero (((sheafSequence.{a,m} f L).obj M).step p n)) :=
  boundsFromSupport _ (sheafFiltered.{a,m} f L M) n (finiteChange.{a,m,u,v,r,s} (S := S) _ n (L.package.finite
    ((DerivedCategory.Plus.singleFunctor (Modules R') 0).obj ((SX).obj M)) n))
    n (fun i hi ↦ sheafSupport.{a,m} f L M 0 i n (Or.inl hi))
    (fun i hi ↦ sheafSupport.{a,m} f L M 0 i n (Or.inr hi)) p

private lemma stableComparisons (W : DerivedCategory.Plus (Modules S')) :
    StableComparisons.{a,m} f L W := by
  let F := modelData GY' L.package.row W
  let i := modelIso GY' L.package.row W
  intro n
  obtain ⟨s₀, _, hs⟩ := F.convergence.stabilization n
  obtain ⟨d₀, _, hd⟩ := F.convergence.differential F.pages n
  refine ⟨(max s₀ d₀).toNat, ?_⟩
  intro k hk p
  obtain ⟨e⟩ := F.convergence.limit F.pages ((k : ℤ) + 2) p n (by omega)
    (hs _ (by omega) p)
  refine ⟨e, ?_, ?_⟩
  · haveI : IsIso (i.hom.page k (p + ((k : ℤ) + 2)) (n + 1)) :=
      ((pageEval k _ _).mapIso i).isIso_hom
    have hzero : (diagram GY' F).differential k p n = 0 := hd _ (by omega) (by omega) p
    have h := i.hom.differential_comm k p n
    rw [hzero, comp_zero] at h
    have hh : (L.package.row.derived.obj W).differential k p n = 0 :=
      (cancel_mono (i.hom.page k _ _)).mp (h.symm.trans zero_comp.symm)
    change (B).map _ = 0
    rw [hh, Functor.map_zero]
  · exact changeGradedProjection B _ k p n (modelGradedIso.{a,m} f L W k p n e)

private lemma originalLowerBound (K : CochainComplex.Plus (SheafOfModules.{m} R)) (b : ℤ)
    (h : K.obj.IsStrictlyGE b) :
    ((originalComplexImage.{a,m,u,v,r,s} (R := R)).obj K).IsGE b := by
  letI := h
  rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
  change (DerivedCategory.Q.obj (((LiftX).mapHomologicalComplex (.up ℤ)).obj K.obj)).IsGE b
  infer_instance

end Original

/-- Global Leray on the original ringed spaces, at an adequate coefficient
level. The same normalized comparison gives the derived and sheaf targets. -/
theorem globalLeray.{a,m,u,v,r,s} : globalLerayType.{a,m,u,v,r,s} := by
  intro X Y R S f
  letI := sectionHasSheafify.{max a m v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a m v r s,u} X
  letI := sectionHasSheafify.{max a m u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a m u r s,v} Y
  obtain ⟨hX, hY, eX, c, hm, _⟩ :=
    DerivedSectionsIndependentCoefficients.transportComparison.{max a m,u,v,r,s} f
  let eY := SheafUniverseTransport.ambient_equivalence.{max a m u r,v,s} Y S
  letI := hX
  letI := hY
  letI := eX
  letI := eY
  obtain ⟨L, hr, hc⟩ := LerayAndDegenerations.leray.{max a m u v r s}
    (liftedRing.{max a m v s} R) (liftedRing.{max a m u r} S)
    (transportedMap.{max a m} f) (transportedScalars.{max a m} f)
  let d := siteTransportData.{max a m} f c L.sections
  let h := pageTransport.{a,m} f L c
  have hd : d.CohomologyCoherence f :=
    cohomologyCoherence.{max a m} f c L.sections d
  refine ⟨hX, hY, eX, eY, L, c, d, h, hm, ?_⟩
  refine
    { cohomology_commutes := hd
      derived_target := abutmentCommutes.{a,m} f L d hd
      sheaf_target := stalkAbutmentCommutes.{a,m} f L d
      sheaf_second := stalkSecondCommutes.{a,m} f L d h
      finite_derived := derivedFiltered.{a,m} f L d
      finite_sheaf := sheafFiltered.{a,m} f L
      stable_derived := fun K ↦ stableComparisons.{a,m} f L
        ((transportedDirectImage.{max a m} f).rightDerivedFunctorPlus.obj (d.site.functor.obj K))
      stable_sheaf := fun M ↦ stableComparisons.{a,m} f L
        ((transportedDirectImage.{max a m} f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (Modules (liftedRing.{max a m v s} R)) 0).obj
            ((sheafInput.{a,m,u,v,r,s} (R := R)).obj M)))
      original_lower_bound := originalLowerBound.{a,m,u,v,r,s} (R := R)
      derived_support := derivedSupport.{a,m} f L d h
      derived_bounds := derivedBounds.{a,m} f L d h
      sheaf_support := sheafSupport.{a,m} f L
      sheaf_bounds := sheafBounds.{a,m} f L
      row_square := originalRowSquare.{a,m} f L d h
      column_square := originalColumnSquare.{a,m} f L d h
      row_isIso := ?_
      column_isIso := ?_ }
  · intro M hM n
    let M' := (sheafInput.{a,m,u,v,r,s} (R := R)).obj M
    have hz (q : ℕ) (hq : 0 < q) :
        IsZero ((higherDirectImage (liftedRing.{max a m v s} R)
          (liftedRing.{max a m u r} S) (transportedMap.{max a m} f)
          (transportedScalars.{max a m} f) q).obj M') :=
      ((transport.{max a m u r} S).map_isZero (hM q hq)).of_iso
        ((sheafHigherCoordinates.{a,m} f h q).app M).symm
    haveI := hr M' hz n
    dsimp only [rowEdge, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    infer_instance
  · intro M hM n
    let M' := (sheafInput.{a,m,u,v,r,s} (R := R)).obj M
    have hz (p q : ℕ) (hp : 0 < p) :
        IsZero ((higherDirectImage (liftedRing.{max a m v s} R)
          (liftedRing.{max a m u r} S) (transportedMap.{max a m} f)
          (transportedScalars.{max a m} f) q ⋙
            sectionCohomology (liftedRing.{max a m u r} S) ⊤ p).obj M') :=
      ((targetScalarEquivalence.{a,m,u,v,r,s} (S := S)).functor.map_isZero (hM p q hp)).of_iso
        ((sheafPageCoordinates.{a,m} f h p q).app M).symm
    haveI := hc M' hz n
    dsimp only [columnEdge, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    infer_instance

end AdvancedHomologicalAlgebra.LerayIndependentCoefficients
