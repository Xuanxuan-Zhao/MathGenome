import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.HigherDirectImagesOriginalTheory
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.SheafCohomology (resolutionModelMap)
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients

universe a m u v r s w t

set_option quotPrecheck false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients

attribute [local instance] HasDerivedCategory.standard

def directImage : directImageType.{m,u,v,r,s} := @directImageValue.{m,u,v,r,s}

def higher : higherType.{a,u,v,r,s} := higherExpected.{a,u,v,r,s}

def originalHigher : originalHigherType.{a,m,u,v,r,s} := originalHigherExpected.{a,m,u,v,r,s}

def localPresheaf : localPresheafType.{a,u,v,r,s} := localPresheafExpected.{a,u,v,r,s}

theorem sections : sectionsType.{m,u,v,r,s} := by
  intro X Y R S f M N k V W j c x
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem leftExact : leftExactType.{m,u,v,r,s} := by
  intro X Y R S f
  constructor
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  refine ⟨isLimitOfReflects (SheafOfModules.forget S) ?_⟩
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro V
  exact isLimitOfPreserves
    (SheafOfModules.evaluation.{m} R ((inverseOpens f.continuousMap).op.obj V) ⋙
      ModuleCat.restrictScalars (f.scalars V)) hc

def coefficientLiftComparison : coefficientLiftType.{a,m,u,v,r,s} :=
  @coefficientLiftComparisonValue.{a,m,u,v,r,s}

theorem coefficientLiftComparison_sections :
    coefficientLiftNormalizedType.{a,m,u,v,r,s} := by
  intro X Y R S f M V x
  rfl

def pushforwardTransport : pushforwardTransportType.{a,u,v,r,s} := pushforwardTransportExpected.{a,u,v,r,s}

theorem pushforwardTransport_sections :
    pushforwardTransportNormalizedType.{a,u,v,r,s} := by
  intro X Y R S f M V x
  exact ⟨rfl, fun _ ↦ rfl⟩

open AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients (compareResolutions)
open AdvancedHomologicalAlgebra.AcyclicTermComparison (rightAcyclic_of_injective)

theorem higherTransport : higherTransportType.{a,u,v,r,s} := by
  intro X Y R S hR hR' eS f
  letI := sectionHasSheafify.{max a v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
  letI := sectionHasSheafify.{max a u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
  exact compareResolutions _ _ _ _ (pushforwardTransport.{a,u,v,r,s} f)
    (fun I hI ↦ by
      letI : Injective ((transport.{max a v s} R).obj I) :=
        ((transport.{max a v s} R).asEquivalence.map_injective_iff I).2 hI
      exact rightAcyclic_of_injective _ _)

theorem pushforwardFlasque : pushforwardFlasqueType.{m,u,v,r,s} := by
  intro X Y R S f M h V W i
  exact h (invOpen f V) (invOpen f W) ((inverseOpens f.continuousMap).map i)

theorem adequateEnoughInjectives : adequateEnoughInjectivesType.{a,u,v,r,s} := by
  intro X Y R S _
  exact ⟨ambient_enough_injectives.{max a v s,u,r} X R,
    ambient_enough_injectives.{max a u r,v,s} Y S⟩

theorem injectiveImageAcyclic : injectiveImageAcyclicType.{a,u,v,r,s} := by
  intro X Y R S hS f I hI
  have h := pushforwardFlasque f I (original_injectives_flasque.{max a v s,u,r} X R I hI)
  exact ⟨h, fun V q ↦ SheafCohomologyOriginalCoefficients.flasque.{max a u r,v,s} S V _ h q⟩

open private mapAugmentation_id exactPostcomposition
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients

section ModelComparison

variable {A P B : Type*} [Category* A] [Category* P] [Category* B]
  [Abelian A] [Abelian P] [Abelian B] [EnoughInjectives A]
  (F : A ⥤ P) (G : A ⥤ B) (H : P ⥤ B)
  [F.Additive] [G.Additive] [H.Additive] [H.PreservesHomology]
  (c : F ⋙ H ≅ G)

/-- Applying an exact functor to the resolution computes its comparison with
another derived functor on the same domain. -/
private theorem compareOnSameResolution :
    ∃ e : ∀ q : ℕ, rightValue F q ⋙ H ≅ rightValue G q,
      ∀ (M : A) (I : CochainComplex A ℤ) [I.IsStrictlyGE 0]
        (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I) (hi : QuasiIso i),
        (∀ k : ℤ, Injective (I.X k)) → ∀ q : ℕ,
        H.map (resolutionModelMap F i hi q) ≫ (e q).hom.app M =
          ((((F.mapHomologicalComplex (.up ℤ)).obj I).sc (q : ℤ)).mapHomologyIso H).inv ≫
            HomologicalComplex.homologyMap
              ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).hom.app I) (q : ℤ) ≫
            resolutionModelMap G i hi q := by
  let c' : F ⋙ H ≅ (𝟭 A) ⋙ G := c
  obtain ⟨e, he⟩ := compareResolutions F G (𝟭 A) H c'
    (fun I hI ↦ by letI := hI; exact rightAcyclic_of_injective _ I)
  refine ⟨fun q ↦ e q, ?_⟩
  intro M I _ i hi hI q
  obtain ⟨hi', h⟩ := he M I i hi hI
  have hq := h q
  simp only [mapAugmentation_id, modelComparison, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Category.assoc] at hq
  exact hq

end ModelComparison

theorem sheafification : sheafificationType.{a,u,v,r,s} := by
  intro X Y R S hR f
  letI := sectionHasSheafify.{max a v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
  letI := sectionHasSheafify.{max a u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
  let D := ambientDirectImage.{a} f
  let H := associate.{a,u,v,r,s} (S := S)
  let c : (D ⋙ SheafOfModules.forget S) ⋙ H ≅ D :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft D (asIso (PresheafOfModules.sheafificationAdjunction.{max a u v r s}
        (𝟙 S.obj)).counit) ≪≫ Functor.rightUnitor _
  obtain ⟨e, he⟩ := compareOnSameResolution (presheafSections.{a} f) D H c
  refine ⟨e, ?_⟩
  intro M I _ i hi hI q
  rw [sheafModelIso, Iso.trans_hom, Category.assoc]
  exact he M I i hi hI q

theorem originalLocalDescription : originalLocalDescriptionType.{a,m,u,v,r,s} := by
  intro X Y R S hR f
  obtain ⟨e, he⟩ := sheafification.{max a m,u,v,r,s} f
  refine ⟨fun q ↦ isoWhiskerLeft (liftSheafCoefficients.{max a u v r s,u,r,m} R) (e q), ?_⟩
  intro M I _ i hi hI q
  exact he _ I i hi hI q

theorem localEvaluation : localEvaluationType.{a,u,v,r,s} := by
  intro X Y R S hR f
  letI := sectionHasSheafify.{max a v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
  letI := sectionHasSheafify.{max a u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
  have h (V : Opens Y) :
      ∃ e : ∀ q : ℕ,
        localPresheafValue.{a} f q ⋙ evaluateLocal.{a,u,v,r,s} V ≅ localValue.{a} f V q,
        ∀ (M : AmbientSheaves.{max a v s} R)
          (I : CochainComplex (AmbientSheaves.{max a v s} R) ℤ) [I.IsStrictlyGE 0]
          (i : (CochainComplex.singleFunctor (AmbientSheaves.{max a v s} R) 0).obj M ⟶ I)
          (hi : QuasiIso i), (∀ k : ℤ, Injective (I.X k)) → ∀ q : ℕ,
          (evaluateLocal.{a,u,v,r,s} (S := S) V).map
              (resolutionModelMap (presheafSections.{a} f) i hi q) ≫ (e q).hom.app M =
            (evaluationModelIso.{a} f I V q).hom ≫
              (sectionScalars.{max a u v r s} f V).map
                (resolutionModelMap (sectionsValue.{max a v s} R (invOpen f V)) i hi q) := by
    let P := presheafSections.{a} f
    let E := evaluateLocal.{a,u,v,r,s} (S := S) V
    let Γ := sectionsValue.{max a v s} R (invOpen f V)
    let H := sectionScalars.{max a u v r s} f V
    let c : P ⋙ E ≅ Γ ⋙ H := Iso.refl _
    obtain ⟨e, he⟩ := compareOnSameResolution P (Γ ⋙ H) E c
    obtain ⟨d, _, _, hd⟩ := exactPostcomposition Γ H
    refine ⟨fun q ↦ e q ≪≫ (d q).symm, ?_⟩
    intro M I _ i hi hI q
    have hd' :
        resolutionModelMap (Γ ⋙ H) i hi q ≫ (d q).inv.app M =
          ((((Γ.mapHomologicalComplex (.up ℤ)).obj I).sc (q : ℤ)).mapHomologyIso H).hom ≫
            H.map (resolutionModelMap Γ i hi q) := by
      rw [← cancel_mono ((d q).hom.app M), Category.assoc, Iso.inv_hom_id_app,
        Category.comp_id, Category.assoc, hd M I i hi hI q, Iso.hom_inv_id_assoc]
    let K := ((E.mapHomologicalComplex (.up ℤ)).obj
      ((P.mapHomologicalComplex (.up ℤ)).obj I))
    have hcomp : (Functor.mapHomologicalComplexCompIso c (.up ℤ)).hom.app I = 𝟙 K := by
      ext k
      rfl
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, ← Category.assoc]
    rw [he M I i hi hI q, hcomp, HomologicalComplex.homologyMap_id K]
    simp only [evaluationModelIso, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom,
      Category.assoc, hd']
    rfl
  choose e he using h
  exact ⟨e, fun M I _ i hi hI V q ↦ he V M I i hi hI q⟩

/-- The canonical homology comparison for a composite is the composite of
the canonical homology comparisons. -/
private theorem homologyComparisonComp {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    (S : ShortComplex A) (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology] [(F ⋙ G).PreservesHomology] :
    S.mapHomologyIso (F ⋙ G) = ((S.map F).mapHomologyIso G) ≪≫ G.mapIso (S.mapHomologyIso F) := by
  let h := S.leftHomologyData
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq h (F ⋙ G),
    ShortComplex.LeftHomologyData.mapHomologyIso_eq (h.map F) G,
    ShortComplex.LeftHomologyData.mapHomologyIso_eq h F]
  ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc, Functor.map_comp,
    Functor.comp_map]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, (G.map_id _), Category.id_comp]
  have hc : (h.map (F ⋙ G)).cyclesIso.hom = ((h.map F).map G).cyclesIso.hom := by
    rw [← cancel_mono ((h.map (F ⋙ G)).i)]
    exact ((h.map (F ⋙ G)).cyclesIso_hom_comp_i).trans
      (((h.map F).map G).cyclesIso_hom_comp_i).symm
  rw [← cancel_epi ((S.map (F ⋙ G)).homologyπ), ← Category.assoc, ← Category.assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, hc]
  rfl

section Restrictions

variable {X : TopCat.{u}} {Y : TopCat.{v}}
  {R : X.Sheaf RingCat.{r}} {S : Y.Sheaf RingCat.{s}} (f : RingedMap R S)
  {V W : Opens Y} (j : W ⟶ V)

set_option hygiene false in
local notation "A" => AmbientSheaves.{max a v s} R
set_option hygiene false in
local notation "E" => evaluateLocal.{a,u,v,r,s} (S := S)
set_option hygiene false in
local notation "T" => sectionScalars.{max a u v r s} f
set_option hygiene false in
local notation "XScalars" => restrictSectionScalars.{max a v s} X R ((inverseOpens f.continuousMap).map j)
set_option hygiene false in
local notation "YScalars" => restrictSectionScalars.{max a u r} Y S j

/-- The restriction of the presheaf homology on a resolution is the original
section restriction on the same resolution, with the given scalar action. -/
private theorem restrictionOnModel (I : CochainComplex A ℤ) (q : ℕ) :
    let P := ((presheafSections.{a} f).mapHomologicalComplex (.up ℤ)).obj I
    let L := ((sectionsValue.{max a v s} R (invOpen f W)).mapHomologicalComplex (.up ℤ)).obj I
    let c := restrictSections.{max a v s} X R ((inverseOpens f.continuousMap).map j)
    (P.homology (q : ℤ)).map j.op ≫ (YScalars).map (evaluationModelIso.{a} f I W q).hom =
      (evaluationModelIso.{a} f I V q).hom ≫
        (T V).map (HomologicalComplex.homologyMap
          ((c.mapHomologicalComplex (.up ℤ)).app I) (q : ℤ)) ≫
        (T V).map ((L.sc (q : ℤ)).mapHomologyIso XScalars).hom ≫
        (restrictionScalarsIso.{a} f j).hom.app (L.homology (q : ℤ)) := by
  dsimp only
  let P := (((presheafSections.{a} f).mapHomologicalComplex (.up ℤ)).obj I).sc (q : ℤ)
  let K := (((sectionsValue.{max a v s} R (invOpen f V)).mapHomologicalComplex (.up ℤ)).obj I).sc (q : ℤ)
  let L := (((sectionsValue.{max a v s} R (invOpen f W)).mapHomologicalComplex (.up ℤ)).obj I).sc (q : ℤ)
  let σ := restrictionScalarsIso.{a} f j
  let H := YScalars
  let ρ : E V ⟶ E W ⋙ H := PresheafOfModules.restriction S.obj j.op
  let c := restrictSections.{max a v s} X R ((inverseOpens f.continuousMap).map j)
  let d : K ⟶ L.map XScalars := (HomologicalComplex.shortComplexFunctor _ _ (q : ℤ)).map
    ((c.mapHomologicalComplex (.up ℤ)).app I)
  have hd : P.mapNatTrans ρ = (T V).mapShortComplex.map d ≫ L.mapNatTrans σ.hom := by
    ext <;> rfl
  have hσ :
      ShortComplex.homologyMap (L.mapNatTrans σ.hom) ≫ (L.mapHomologyIso (T W ⋙ H)).hom =
        (L.mapHomologyIso (XScalars ⋙ T V)).hom ≫ σ.hom.app L.homology := by
    simp only [H, ShortComplex.homologyMap_mapNatTrans, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hρ := NatTrans.app_homology ρ P
  change ρ.app P.homology ≫
      H.map ((P.mapHomologyIso (E W)).inv ≫ (L.mapHomologyIso (T W)).hom) =
    ((P.mapHomologyIso (E V)).inv ≫ (K.mapHomologyIso (T V)).hom) ≫
      (T V).map (ShortComplex.homologyMap d) ≫ (T V).map (L.mapHomologyIso XScalars).hom ≫
        σ.hom.app L.homology
  rw [hρ, hd, ShortComplex.homologyMap_comp,
    homologyComparisonComp P (E W) H]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    ← H.map_comp_assoc, Iso.hom_inv_id, H.map_id, Category.id_comp]
  have hh :
      L.mapHomologyIso (T W ⋙ H) = (P.map (E W)).mapHomologyIso H ≪≫
        H.mapIso (L.mapHomologyIso (T W)) :=
    homologyComparisonComp L (T W) H
  rw [← show (L.mapHomologyIso (T W ⋙ H)).hom =
      ((P.map (E W)).mapHomologyIso H).hom ≫ H.map (L.mapHomologyIso (T W)).hom
      from congrArg Iso.hom hh]
  rw [hσ, homologyComparisonComp L XScalars (T V)]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [ShortComplex.mapHomologyIso_hom_naturality_assoc]

end Restrictions

theorem localRestrictions : localRestrictionsType.{a,u,v,r,s} := by
  intro X Y R S hR f e he V W j
  letI := sectionHasSheafify.{max a v r s,u} X
  letI := sectionWEqualsLocallyBijective.{max a v r s,u} X
  let j' := (inverseOpens f.continuousMap).map j
  obtain ⟨k, _, _, hk⟩ := SheafCohomologyOriginalCoefficients.restrictionMap.{max a v s,u,r}
    X R j'
  refine ⟨k, hk, ?_⟩
  intro q M
  dsimp only
  obtain ⟨I, i, _, hi, hI, hb⟩ := InjectiveComplexReplacement.replacement
    (AmbientSheaves.{max a v s} R)
    ((CochainComplex.singleFunctor (AmbientSheaves.{max a v s} R) 0).obj M) 0 inferInstance
  letI := hb
  let p := resolutionModelMap (presheafSections.{a} f) i hi q
  let Γ := sectionsValue.{max a v s} R (invOpen f V)
  let Γ' := sectionsValue.{max a v s} R (invOpen f W)
  let c := restrictSections.{max a v s} X R j'
  let L := ((Γ'.mapHomologicalComplex (.up ℤ)).obj I)
  let H := restrictSectionScalars.{max a u r} Y S j
  let J := restrictSectionScalars.{max a v s} X R j'
  let T := sectionScalars.{max a u v r s} f
  let E := evaluateLocal.{a,u,v,r,s} (S := S)
  let σ := restrictionScalarsIso.{a} f j
  letI : IsIso p := SheafCohomology.resolutionModelMap_isIso _ i hi
    (fun n ↦ by letI := hI n; exact rightAcyclic_of_injective _ _) q
  have hV := he M I i hi hI V q
  have hW := he M I i hi hI W q
  change (E V).map p ≫ _ = _ at hV
  change (E W).map p ≫ _ = _ at hW
  let P := (((presheafSections.{a} f).mapHomologicalComplex (.up ℤ)).obj I).homology (q : ℤ)
  let Q := (localPresheafValue.{a} f q).obj M
  have hn : P.map j.op ≫ H.map ((E W).map p) = (E V).map p ≫ Q.map j.op :=
    p.naturality j.op
  apply (cancel_epi ((E V).map p)).mp
  change (E V).map p ≫ (Q.map j.op ≫ H.map ((e W q).hom.app M)) =
    (E V).map p ≫ ((e V q).hom.app M ≫ (localRestrictionOf.{a} f j q (k q)).app M)
  rw [← Category.assoc, ← hn, Category.assoc, ← H.map_comp, hW, H.map_comp]
  rw [← Category.assoc, restrictionOnModel.{a} f j I q]
  rw [reassoc_of% hV]
  change _ =
    (evaluationModelIso.{a} f I V q).hom ≫ (T V).map (resolutionModelMap Γ i hi q) ≫
      ((T V).map ((k q).app M) ≫ _)
  conv_rhs => rw [← (T V).map_comp_assoc, hk M I i hi hI q]
  simp only [(T V).map_comp, Category.assoc]
  exact congrArg (fun z ↦ (evaluationModelIso.{a} f I V q).hom ≫
    (T V).map (HomologicalComplex.homologyMap
      ((c.mapHomologicalComplex (.up ℤ)).app I) (q : ℤ)) ≫
    (T V).map ((L.sc (q : ℤ)).mapHomologyIso J).hom ≫ z)
    (σ.hom.naturality (resolutionModelMap Γ' i hi q)).symm

theorem flasqueHigherVanishing : flasqueHigherVanishingType.{a,u,v,r,s} := by
  intro X Y R S hR f M hM q
  letI := sectionHasSheafify.{max a u r s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a u r s,v} Y
  obtain ⟨e, _⟩ := sheafification.{a,u,v,r,s} f
  obtain ⟨d, _⟩ := localEvaluation.{a,u,v,r,s} f
  let P := (localPresheafValue.{a} f (q + 1)).obj M
  have hP : IsZero P := (IsZero.iff_id_eq_zero P).2 (by
    ext1 V
    let V' := V.unop
    have hV := SheafCohomologyOriginalCoefficients.flasque.{max a v s,u,r} R
      (invOpen f V') M hM q
    have h := ((sectionScalars.{max a u v r s} f V').map_isZero hV).of_iso
      ((d V' (q + 1)).app M)
    exact (IsZero.iff_id_eq_zero _).mp h)
  exact ((associate.{a,u,v,r,s} (S := S)).map_isZero hP).of_iso ((e (q + 1)).app M).symm

theorem relativeAcyclic : relativeAcyclicType.{a,u,v,r,s,w,t} := by
  intro X Y Z R S T hS f g I hI q
  apply flasqueHigherVanishing.{max a u r,v,w,s,t} g _ _ q
  exact pushforwardFlasque f I
    (original_injectives_flasque.{max a v s w t,u,r} X R I hI)

theorem relativeUnitIso : relativeUnitIsoType.{a,u,v,r,s,w,t} := by
  intro X Y Z R S T hS f g I hI
  letI := sectionHasSheafify.{max a u r w t s,v} Y
  letI := sectionWEqualsLocallyBijective.{max a u r w t s,v} Y
  letI := sectionHasSheafify.{max a u r v s t,w} Z
  letI := sectionWEqualsLocallyBijective.{max a u r v s t,w} Z
  let G := ambientDirectImage.{max a u r} g
  letI : PreservesFiniteLimits G := leftExact.{max a u v w r s t,v,w,s,t} g
  exact (AcyclicTermComparison.rightVanishing _ _ G _).2
    (relativeAcyclic.{a,u,v,r,s,w,t} f g I hI)

end AdvancedHomologicalAlgebra.HigherDirectImagesIndependentCoefficients
