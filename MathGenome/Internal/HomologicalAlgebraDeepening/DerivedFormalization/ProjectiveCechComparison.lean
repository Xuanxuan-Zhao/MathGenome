import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveCechComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ProjectiveTwists
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.OrderedCechComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.AffineTildeAcyclicity

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Batteries.Tactic.OpenPrivate

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open HomologicalComplex
open AdvancedHomologicalAlgebra.Cech AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.CechSequenceOriginal
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open Specs.DerivedFormalization.OrderedCechComparison
open Specs.DerivedFormalization.ProjectiveCechComparison
open DerivedFormalization.ProjectiveTwists

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace DerivedFormalization.ProjectiveCechComparison

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

def standardCechCover : Cover (globalOpen k n) (Index n) :=
  coverValue k n (standardCover k n)

theorem tupleOpen_eq_intersection {p : ℕ} (t : Fin (p + 1) → Index n) :
    tupleOpen (standardCechCover k n) t = intersection k n (tupleIndices n t) := by
  rw [tupleOpen_eq_iInf]
  change (⨅ j, chart k n (t j)) = (Finset.univ.image t).inf (chart k n)
  refine le_antisymm (Finset.le_inf fun j hj ↦ ?_) (le_iInf fun j ↦ ?_)
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hj
    exact iInf_le _ a
  · exact Finset.inf_le (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

theorem tupleIndices_nonempty {p : ℕ} (t : Fin (p + 1) → Index n) :
    (tupleIndices n t).Nonempty :=
  ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

theorem tupleIndices_reindex_subset {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1))
    (t : Fin (q + 1) → Index n) :
    tupleIndices n (t ∘ f) ⊆ tupleIndices n t := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_image.mpr ⟨f j, Finset.mem_univ _, rfl⟩

theorem tupleIndices_card {p : ℕ} (t : IncreasingTuple (Index n) p) :
    (tupleIndices n t.1).card = p + 1 := by
  rw [tupleIndices, Finset.card_image_of_injective _ t.2.injective,
    Finset.card_univ, Fintype.card_fin]

/-- The strictly increasing indices enumerate all subsets of the indicated size. -/
def increasingTupleEquivFinset (p : ℕ) :
    IncreasingTuple (Index n) p ≃ {J : Finset (Index n) // J.card = p + 1} where
  toFun t := ⟨tupleIndices n t.1, tupleIndices_card n t⟩
  invFun J := ⟨J.1.orderEmbOfFin J.2, (J.1.orderEmbOfFin J.2).strictMono⟩
  left_inv t := Subtype.ext (Finset.orderEmbOfFin_unique (tupleIndices_card n t)
    (fun i ↦ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) t.2).symm
  right_inv J := Subtype.ext (Finset.image_orderEmbOfFin_univ J.1 J.2)

set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 12000

open private restrictionValueIso
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomology

open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
attribute [local instance] HasDerivedCategory.standard

private def restrictSectionsIso {A X : Scheme.{u}} (f : A ⟶ X) [IsOpenImmersion f] :
    Scheme.Modules.restrictFunctor f ⋙
      SheafOfModules.evaluation A.ringCatSheaf (op ⊤) ⋙
      ModuleCat.restrictScalars (f.appIso ⊤).hom.hom ≅
    SheafOfModules.evaluation X.ringCatSheaf (op (f ''ᵁ ⊤)) := by
  refine NatIso.ofComponents (fun M ↦ ?_) (fun g ↦ ?_)
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    symm
    let N := M.val.obj (op (f ''ᵁ ⊤))
    change ((N.smul ((f.appIso ⊤).inv ((f.appIso ⊤).hom r))).asHom.hom x) =
      (N.smul r).asHom.hom x
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  · apply ModuleCat.hom_ext
    ext x
    rfl

private instance schemeEvaluation_additive (X : Scheme.{u}) (V : X.Opens) :
    (SheafOfModules.evaluation.{u} X.ringCatSheaf (op V)).Additive where
  map_add := by intros; rfl

private instance schemeRestrict_additive {A X : Scheme.{u}} (f : A ⟶ X) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).Additive where
  map_add := by intros; rfl

private def isoRestrictionEquivalence {A X : Scheme.{u}} (e : A ≅ X) :
    X.Modules ≌ A.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor e.hom)
    (Scheme.Modules.restrictFunctor e.inv)
    ((Scheme.Modules.restrictFunctorId (X := X)).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id.symm ≪≫
      Scheme.Modules.restrictFunctorComp e.inv e.hom)
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId)

private def restrictionFactorization {A X : Scheme.{u}} (U : X.Opens) (e : A ≅ U.toScheme) :
    Scheme.Modules.restrictFunctor (e.hom ≫ U.ι) ≅
      restriction X.ringCatSheaf U ⋙ (isoRestrictionEquivalence e).functor :=
  Scheme.Modules.restrictFunctorComp e.hom U.ι ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U).symm _

private lemma restrictChart_acyclic {A X : Scheme.{u}} (U : X.Opens) (e : A ≅ U.toScheme)
    (M : X.Modules) (q : ℕ)
    (h : IsZero ((sectionCohomology A.ringCatSheaf ⊤ q).obj
      ((Scheme.Modules.restrictFunctor (e.hom ≫ U.ι)).obj M))) :
    IsZero ((sectionCohomology X.ringCatSheaf U q).obj M) := by
  let f := e.hom ≫ U.ι
  let J := Scheme.Modules.restrictFunctor f
  let L := ModuleCat.restrictScalars.{u} (f.appIso ⊤).hom.hom
  let E := SheafOfModules.evaluation.{u} A.ringCatSheaf (op ⊤)
  let V : X.Opens := f ''ᵁ ⊤
  let G := SheafOfModules.evaluation.{u} X.ringCatSheaf (op V)
  have hV : V = U := by
    dsimp [V, f]
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
  let i := restrictionFactorization U e
  let R := restriction X.ringCatSheaf U
  have hR := AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction.Expected.restriction_exact X.ringCatSheaf U
  letI : PreservesFiniteLimits R := hR.1
  letI : PreservesFiniteColimits R := hR.2
  letI : PreservesFiniteLimits J := preservesFiniteLimits_of_natIso i.symm
  letI : PreservesFiniteColimits J := preservesFiniteColimits_of_natIso i.symm
  have hJ (N : X.Modules) (hN : Injective N) : Injective (J.obj N) := by
    haveI : Injective (R.obj N) :=
      AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction.restriction_injective X.ringCatSheaf U N hN
    exact Injective.of_iso (i.app N).symm
      ((isoRestrictionEquivalence e).functor.injective_obj (R.obj N))
  letI : E.Additive := schemeEvaluation_additive A ⊤
  letI : G.Additive := schemeEvaluation_additive X V
  letI : L.Additive := by dsimp [L]; infer_instance
  let α := restrictionValueIso J (E ⋙ L) G (restrictSectionsIso f) hJ q
  have hz : IsZero ((rightValue (E ⋙ L) q).obj (J.obj M)) := by
    let N := J.obj M
    let I := injectiveResolution N
    let emb := ComplexShape.embeddingUpIntGE 0
    let K := I.cocomplex.extend emb
    let ι : (CochainComplex.singleFunctor A.Modules 0).obj N ⟶ K :=
      (extendSingleIso emb N (0 : ℕ) (0 : ℤ) rfl).inv ≫ extendMap I.ι emb
    have hι : QuasiIso ι := by dsimp [ι]; infer_instance
    have hK (i : ℤ) : Injective (K.X i) := by
      by_cases hi : 0 ≤ i
      · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hi
        exact Injective.of_iso (I.cocomplex.extendXIso emb (i := j) (i' := (j : ℤ))
          (by simp [emb])).symm (I.injective j)
      · exact IsZero.injective (I.cocomplex.isZero_extend_X emb i (by
          intro j hj
          have he : emb.f j = (j : ℤ) := by simp [emb]
          omega))
    obtain ⟨a⟩ := AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightComputation _ _ E N K ι hι hK q
    obtain ⟨b⟩ := AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightComputation _ _ (E ⋙ L) N K ι hι hK q
    have ha := h.of_iso a.symm
    let T := ((E.mapHomologicalComplex (.up ℤ)).obj K)
    let hcomp := (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ L)) (.up ℤ)).app K
    let hhom := (T.sc (q : ℤ)).mapHomologyIso L
    exact (L.map_isZero ha).of_iso
      (b ≪≫ (homologyFunctor _ (.up ℤ) (q : ℤ)).mapIso hcomp ≪≫ hhom)
  have hfinal : IsZero ((sectionCohomology X.ringCatSheaf V q).obj M) :=
    hz.of_iso (α.app M)
  exact hV ▸ hfinal

private def nativeCoefficientIso {X : TopCat.{u}} (S : X.Sheaf RingCat.{u})
    (F : SheafOfModules.{u} S) : nativeCoefficient.{u,u,u} S F ≅ F :=
  (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun _ ↦ ULift.moduleEquiv.toModuleIso) (by intros; rfl))

/-- The module-valued model has the usual sheaf cohomology as its underlying abelian group. -/
theorem cohomologyForgetIso {X : TopCat.{u}} (S : X.Sheaf RingCat.{u}) (U : Opens X)
    [EnoughInjectives (AmbientSheaves.{u} S)] (F : SheafOfModules.{u} S) (q : ℕ) :
    Nonempty ((forget₂ (ModuleCat.{u} (sectionRing S U)) AddCommGrpCat.{u}).obj
      ((coefficientCohomologyValue.{u,u,u} X S U q).obj F) ≅
        (abelianCohomology X U q).obj ((SheafOfModules.toSheaf S).obj F)) := by
  let L := forget₂ (ModuleCat.{u} (sectionRing S U)) AddCommGrpCat.{u}
  obtain ⟨e, _⟩ := AdvancedHomologicalAlgebra.SheafCohomology.forget S U
  exact ⟨L.mapIso ((sectionCohomology S U q).mapIso (nativeCoefficientIso S F)) ≪≫ (e q).app F⟩

private def chartRestrictionIso (J : Finset (Index n)) (i : Index n) (hi : i ∈ J)
    (m : ℤ) :
    let U : (projectiveSpace k n).Opens := intersection k n J
    let e := (chartScheme k n J ⟨i, hi⟩).symm
    (Scheme.Modules.restrictFunctor (e.hom ≫ U.ι)).obj (twistingSheaf k n m) ≅
      tilde (ModuleCat.of (ChartRing k n J) (ChartRing k n J)) := by
  dsimp only
  let U : (projectiveSpace k n).Opens := intersection k n J
  let e := (chartScheme k n J ⟨i, hi⟩).symm
  let M : (projectiveSpace k n).Modules := twistingSheaf k n m
  let E := Scheme.Modules.overEquiv U
  let a := twistTrivialization k n i m U (intersection_le_chart k n hi)
  let b : (Scheme.Modules.restrictFunctor U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫ E.functor.mapIso a.symm ≪≫
      U.sheafOfModulesEquivOverUnit (projectiveSpace k n).ringCatSheaf
  exact (Scheme.Modules.restrictFunctorComp e.hom U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor e.hom).mapIso b ≪≫
    Scheme.Modules.restrictUnitIso e.hom ≪≫ tildeSelf.symm

/-- The actual twist has vanishing higher cohomology on every nonempty standard intersection. -/
theorem intersection_acyclic (J : Finset (Index n)) (hJ : J.Nonempty) (m : ℤ)
    [EnoughInjectives (AmbientSheaves.{u} (R k n))] (q : ℕ) (hq : 0 < q) :
    IsZero (Cohomology k n (twistingSheaf k n m) (intersection k n J) q) := by
  obtain ⟨i, hi⟩ := hJ
  letI : IsNoetherianRing (ChartRing k n J) := chartRing_noetherian k n J ⟨i, hi⟩
  let A := CommRingCat.of (ChartRing k n J)
  let M := ModuleCat.of A A
  have h : IsZero ((sectionCohomology (Spec A).ringCatSheaf ⊤ q).obj (tilde M)) := by
    exact (CommutativeAlgebraNotes.tildeBasicOpenIntersectionAcyclic A M ∅ q hq).1
  let e := (chartScheme k n J ⟨i, hi⟩).symm
  let U : (projectiveSpace k n).Opens := intersection k n J
  have ha := restrictChart_acyclic U e (twistingSheaf k n m) q
    (h.of_iso ((sectionCohomology (Spec A).ringCatSheaf ⊤ q).mapIso
      (chartRestrictionIso k n J i hi m)))
  exact ha.of_iso ((sectionCohomology (R k n) U q).mapIso
    (nativeCoefficientIso (R k n) (twistingSheaf k n m)))

theorem twist_acyclicOnIntersections (m : ℤ)
    [EnoughInjectives (AmbientSheaves.{u} (R k n))] :
    AcyclicOnIntersections (R k n) (standardCechCover k n) (twistingSheaf k n m) := by
  intro p t q hq
  change IsZero (Cohomology k n (twistingSheaf k n m)
    (tupleOpen (standardCechCover k n) t) q)
  exact (tupleOpen_eq_intersection k n t).symm ▸
    intersection_acyclic k n (tupleIndices n t) (tupleIndices_nonempty n t) m q hq

section Ordered

variable {X : TopCat.{u}} (S : X.Sheaf RingCat.{u}) {U : Opens X}
  {I : Type} [LinearOrder I] (c : Cover U I)

private def projectionIso (F : SheafOfModules.{u} S) (q : ℕ) :
    ((rawComplexFunctor.{u,u,u,0} S c).obj F).homology q ≅ IncreasingH S c F q :=
  (DerivedFormalization.OrderedCechComparison.homotopyEquiv S c (F := F.val)).toHomologyIso q

private lemma projectionIso_natural {F G : SheafOfModules.{u} S} (f : F ⟶ G) (q : ℕ) :
    (projectionIso S c F q).hom ≫ homologyMap (increasingMap S c f.val) q =
      homologyMap ((rawComplexFunctor.{u,u,u,0} S c).map f) q ≫ (projectionIso S c G q).hom := by
  change homologyMap (projection S c F.val) q ≫ homologyMap (increasingMap S c f.val) q =
    homologyMap (orderedCochainMap S c f.val) q ≫ homologyMap (projection S c G.val) q
  rw [← homologyMap_comp, ← homologyMap_comp,
    DerivedFormalization.OrderedCechComparison.projection_naturality]

private lemma orderedComparisonOfCover :
    ∃ h : EnoughInjectives (SheafOfModules.{u} S), letI := h; OrderedComparison S c := by
  obtain ⟨h, data, e, η, hbij, hnat, hmodel⟩ := acyclic_cover_comparison.{u,u,u,0} S c
  letI := h
  let B (F : SheafOfModules.{u} S) (hF : AcyclicOnIntersections S c F) (q : ℕ) :=
    (LinearEquiv.ofBijective (originalComparisonMap S c q (η q) F) (hbij F q hF)).toModuleIso
  refine ⟨h, data, e, η, (fun F hF q ↦ (projectionIso S c F q).symm ≪≫ B F hF q), hmodel, ?_, ?_⟩
  · intro F hF q
    change (projectionIso S c F q).hom ≫ ((projectionIso S c F q).inv ≫ (B F hF q).hom) = _
    rw [Iso.hom_inv_id_assoc]
    rfl
  · intro F G hF hG f q
    have hb : homologyMap ((rawComplexFunctor.{u,u,u,0} S c).map f) q ≫ (B G hG q).hom =
        (B F hF q).hom ≫ (SectionH S (U := U) q).map f :=
      ModuleCat.hom_ext (LinearMap.ext (hnat f q))
    apply (cancel_epi (projectionIso S c F q).hom).1
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, projectionIso_natural, Category.assoc, Iso.hom_inv_id_assoc]
    exact hb

private theorem restrictScalars_comparison_naturality {A B : Type u} [Ring A] [Ring B]
    (φ : A →+* B) {C D : CochainComplex (ModuleCat.{u} B) ℕ} (g : C ⟶ D) (q : ℕ)
    {P Q : ModuleCat.{u} B} (f : P ⟶ Q) (e : C.homology q ≅ P) (e' : D.homology q ≅ Q)
    (h : homologyMap g q ≫ e'.hom = e.hom ≫ f) :
    let L := ModuleCat.restrictScalars.{u} φ
    homologyMap ((L.mapHomologicalComplex (.up ℕ)).map g) q ≫
        ((D.sc q).mapHomologyIso L ≪≫ L.mapIso e').hom =
      ((C.sc q).mapHomologyIso L ≪≫ L.mapIso e).hom ≫ L.map f := by
  let L := ModuleCat.restrictScalars.{u} φ
  have hn : homologyMap ((L.mapHomologicalComplex (.up ℕ)).map g) q ≫
        ((D.sc q).mapHomologyIso L).hom =
      ((C.sc q).mapHomologyIso L).hom ≫ L.map (homologyMap g q) :=
    ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor (ModuleCat.{u} B) (.up ℕ) q).map g) L
  change homologyMap ((L.mapHomologicalComplex (.up ℕ)).map g) q ≫
      (((D.sc q).mapHomologyIso L).hom ≫ L.map e'.hom) =
    (((C.sc q).mapHomologyIso L).hom ≫ L.map e.hom) ≫ L.map f
  rw [← Category.assoc, hn, Category.assoc, ← L.map_comp, h, L.map_comp, Category.assoc]

section RestrictComparison

variable {A : Type u} [Ring A] [EnoughInjectives (SheafOfModules.{u} S)]

/-- Exact restriction of scalars transports a Čech comparison over the section ring. -/
def restrictComparison (φ : A →+* sectionRing S U) (F : SheafOfModules.{u} S)
    (q : ℕ) (e : IncreasingH S c F q ≅ (SectionH S (U := U) q).obj F) :
    let L := ModuleCat.restrictScalars.{u} φ
    ((L.mapHomologicalComplex (.up ℕ)).obj (increasingComplex S c F.val)).homology q ≅
      L.obj ((SectionH S (U := U) q).obj F) :=
  let L := ModuleCat.restrictScalars.{u} φ
  ((increasingComplex S c F.val).sc q).mapHomologyIso L ≪≫ L.mapIso e

/-- The comparison remains natural in coefficient morphisms after restriction of scalars. -/
theorem restrictComparison_naturality (φ : A →+* sectionRing S U)
    {F G : SheafOfModules.{u} S} (f : F ⟶ G) (q : ℕ)
    (eF : IncreasingH S c F q ≅ (SectionH S (U := U) q).obj F)
    (eG : IncreasingH S c G q ≅ (SectionH S (U := U) q).obj G)
    (h : homologyMap (increasingMap S c f.val) q ≫ eG.hom =
      eF.hom ≫ (SectionH S (U := U) q).map f) :
    let L := ModuleCat.restrictScalars.{u} φ
    homologyMap ((L.mapHomologicalComplex (.up ℕ)).map (increasingMap S c f.val)) q ≫
        (restrictComparison S c φ G q eG).hom =
      (restrictComparison S c φ F q eF).hom ≫ L.map ((SectionH S (U := U) q).map f) :=
  restrictScalars_comparison_naturality φ (increasingMap S c f.val) q
    ((SectionH S (U := U) q).map f) eF eG h

end RestrictComparison

end Ordered

/-- The comparison over the global section ring, natural in acyclic coefficients. -/
theorem orderedComparison : orderedComparisonType.{u} := by
  intro k _ n c
  exact orderedComparisonOfCover (R k n) c

def groundScalars : ∀ (k : Type u) [Field k] (n : ℕ), k →+* GlobalRing k n :=
  groundScalarsValue

open private basicStructureEquiv_value ratio_constant_value variable_powers_le_nonZeroDivisors
  from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ProjectiveTwists

private theorem groundScalars_restrict_chart (i : Index n) (a : k) :
    (projectiveSpace k n).presheaf.map (homOfLE (le_top : chart k n i ≤ ⊤)).op (groundScalars k n a) =
      (Proj.awayToSection (grading k n) (variablePolynomial k n i)) (constantInSingleton k n i a) := by
  let X := projectiveSpace k n
  let f := variablePolynomial k n i
  let V : X.Opens := Proj.basicOpen (grading k n) f
  let e := Proj.basicOpenIsoSpec (grading k n) f (variable_degree k n i) (by decide)
  let φ : CommRingCat.of k ⟶ CommRingCat.of (HomogeneousLocalization.Away (grading k n) f) :=
    CommRingCat.ofHom (constantInSingleton k n i)
  let g := Expected.structureMapValue k n
  have hi : e.inv ≫ V.ι = Proj.awayι (grading k n) f (variable_degree k n i) (by decide) := rfl
  have h₁ : e.inv ≫ V.ι ≫ g = Spec.map φ := by
    rw [← Category.assoc, hi]
    dsimp only [g, Expected.structureMapValue]
    rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
    rfl
  have h₂ : V.ι ≫ g = e.hom ≫ Spec.map φ := (e.inv_comp_eq).mp h₁
  have h₃ : g.appTop ≫ V.ι.appTop = (Spec.map φ).appTop ≫ e.hom.appTop := by
    rw [← Scheme.Hom.comp_appTop, h₂, Scheme.Hom.comp_appTop]
  let sc : CommRingCat.of k ⟶ X.presheaf.obj (op ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop
  have h₄ : sc ≫ V.ι.appTop ≫ V.topIso.hom =
      φ ≫ Proj.awayToSection (grading k n) f := by
    change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop) ≫
      V.ι.appTop ≫ V.topIso.hom = _
    rw [Category.assoc, ← Category.assoc g.appTop, h₃]
    simp only [Category.assoc]
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc, Proj.basicOpenIsoSpec_hom]
    change φ ≫ (Scheme.ΓSpecIso _).inv ≫
      (Proj.basicOpenToSpec (grading k n) f).app ⊤ ≫ V.topIso.hom = _
    rw [Proj.basicOpenToSpec_app_top]
    change φ ≫ (Scheme.ΓSpecIso _).inv ≫
      ((Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection (grading k n) f ≫ V.topIso.inv) ≫
        V.topIso.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
  have h₅ : V.ι.appTop ≫ V.topIso.hom = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
    rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← X.presheaf.map_comp, ← op_comp]
    rfl
  rw [Category.assoc, h₅] at h₄
  exact congrArg (fun m : CommRingCat.of k ⟶ X.presheaf.obj (op V) => m a) h₄

/-- The action from the structure map is by the actual polynomial constants. -/
theorem groundScalars_value (a : k) (x : globalOpen k n) :
    structureToFunctions k n (globalOpen k n) (groundScalars k n a) x =
      intoFraction k n (MvPolynomial.C a) := by
  have hmem : x.1 ∈ ⨆ i, chart k n i := by
    rw [standardCover k n]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hmem
  change structureToFunctions k n (chart k n i)
    ((projectiveSpace k n).presheaf.map (homOfLE (le_top : chart k n i ≤ ⊤)).op
      (groundScalars k n a)) ⟨x.1, hi⟩ = _
  rw [groundScalars_restrict_chart]
  exact (basicStructureEquiv_value k n _ (variable_degree k n i) (by decide) _ rfl
    (variable_powers_le_nonZeroDivisors k n i) (constantInSingleton k n i a) ⟨x.1, hi⟩).trans
      (ratio_constant_value k n i a)

/-- Exact restriction of scalars identifies the two cohomology models over the ground field. -/
def groundCohomologyIso (c : Cover (globalOpen k n) (Index n)) (F : SheafOfModules.{u} (R k n))
    [EnoughInjectives (AmbientSheaves.{u} (R k n))] (q : ℕ)
    (e : (CechComplex k n c F).homology q ≅ Cohomology k n F (globalOpen k n) q) :
    (GroundComplex k n c F).homology q ≅ GroundCohomology k n F q :=
  restrictComparison (R k n) c (groundScalarsValue k n) F q e

open private zeroPoint zeroPoint_mem_intersection from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ProjectiveTwists

private def sectionOpenEq {V W : OpensOfProj k n} (h : V = W) (m : ℤ) :
    TwistSections k n m V ≃ TwistSections k n m W :=
  h ▸ Equiv.refl _

private theorem sectionOpenEq_apply {V W : OpensOfProj k n} (h : V = W) (m : ℤ)
    (s : TwistSections k n m V) (x : W) :
    (sectionOpenEq k n h m s).val x = s.val ⟨x, h.symm ▸ x.2⟩ := by
  subst W
  rfl

/-- The coordinates of the twist, indexed by the actual tuple intersections. -/
def localizedCoordinates :
    LocalizedCoordinates k n (standardCechCover k n) (twistingSheaf k n) :=
  fun m _ t ↦ (degreePieceSections k n (tupleIndices n t) (tupleIndices_nonempty n t) m).trans
    (sectionOpenEq k n (tupleOpen_eq_intersection k n t).symm m)

theorem localizedCoordinates_value (m : ℤ) {p : ℕ} (t : Fin (p + 1) → Index n)
    (a : DegreePiece k n (tupleIndices n t) m) (x : tupleOpen (standardCechCover k n) t) :
    (show TwistSections k n m _ from localizedCoordinates k n m p t a).val x =
      chartToFraction k n (tupleIndices n t) a.val := by
  change (sectionOpenEq k n _ m (degreePieceSections k n (tupleIndices n t) _ m a)).val x = _
  rw [sectionOpenEq_apply, degreePieceSections_value]

theorem localizedCoordinates_symm_value (m : ℤ) {p : ℕ} (t : Fin (p + 1) → Index n)
    (s : TwistSections k n m (tupleOpen (standardCechCover k n) t))
    (x : tupleOpen (standardCechCover k n) t) :
    chartToFraction k n (tupleIndices n t) ((localizedCoordinates k n m p t).symm s).val =
      s.val x := by
  rw [← localizedCoordinates_value k n m t _ x]
  exact congrArg (fun y : TwistSections k n m _ ↦ y.val x)
    ((localizedCoordinates k n m p t).apply_symm_apply s)

/-- Face restrictions use the canonical further localization of the degree piece. -/
theorem localizedCoordinates_restrict (m : ℤ) {p q : ℕ} (f : Fin (p + 1) → Fin (q + 1))
    (t : Fin (q + 1) → Index n) (a : DegreePiece k n (tupleIndices n (t ∘ f)) m) :
    restriction k n (tupleOpen_reindex_le (standardCechCover k n) f t) m
        (localizedCoordinates k n m p (t ∘ f) a) =
      localizedCoordinates k n m q t (degreeRestriction k n (tupleIndices_reindex_subset n f t) m a) := by
  apply Subtype.ext
  funext x
  let h := tupleOpen_reindex_le (standardCechCover k n) f t
  change (show TwistSections k n m _ from localizedCoordinates k n m p (t ∘ f) a).val
    ⟨x, h x.2⟩ =
      (show TwistSections k n m _ from localizedCoordinates k n m q t
        (degreeRestriction k n (tupleIndices_reindex_subset n f t) m a)).val x
  rw [localizedCoordinates_value, localizedCoordinates_value, degreeRestriction_value,
    localizationRestriction_value]

/-- The constants in the degree-zero chart ring. -/
def chartScalars (J : Finset (Index n)) : k →+* ChartRing k n J :=
  (HomogeneousLocalization.fromZeroRingHom (grading k n)
    (Submonoid.powers (chartProduct k n J))).comp (constantInDegreeZero k n)

private theorem chartScalars_value (J : Finset (Index n)) (r : k) :
    chartRingToFraction k n J (chartScalars k n J r) = intoFraction k n (MvPolynomial.C r) := by
  refine (homogeneousToFraction_mk k n _ _ _).trans ?_
  change fraction k n (MvPolynomial.C r) 1 = _
  simp [fraction]

abbrev LocalizedGroundTerm (m : ℤ) {p : ℕ} (t : Fin (p + 1) → Index n) :=
  (ModuleCat.restrictScalars (chartScalars k n (tupleIndices n t))).obj
    (ModuleCat.of (ChartRing k n (tupleIndices n t))
      (degreeSubmodule k n (tupleIndices n t) (tupleIndices_nonempty n t) m))

/-- The localized degree pieces and Čech terms agree over the polynomial constants. -/
def localizedCoordinatesLinear (m : ℤ) {p : ℕ} (t : Fin (p + 1) → Index n) :
    LocalizedGroundTerm k n m t ≃ₗ[k]
      (GroundRestriction k n).obj (localSections (R k n) (twistingSheaf k n m).val
        (globalOpen k n) (tupleOpen (standardCechCover k n) t)
        (tupleOpen_le (standardCechCover k n) t)) where
  toEquiv := localizedCoordinates k n m p t
  map_add' a b := by
    apply Subtype.ext
    funext x
    let w := localizedCoordinates k n m p t
    change (show TwistSections k n m _ from w (a + b)).val x =
      (show TwistSections k n m _ from w a).val x + (show TwistSections k n m _ from w b).val x
    rw [localizedCoordinates_value, localizedCoordinates_value, localizedCoordinates_value]
    exact map_add _ _ _
  map_smul' r a := by
    apply Subtype.ext
    funext x
    let w := localizedCoordinates k n m p t
    change (show TwistSections k n m _ from w (r • a)).val x =
      structureToFunctions k n (globalOpen k n) (groundScalars k n r) ⟨x, trivial⟩ *
        (show TwistSections k n m _ from w a).val x
    rw [localizedCoordinates_value, localizedCoordinates_value, groundScalars_value]
    change chartToFraction k n (tupleIndices n t)
        (algebraMap (ChartRing k n (tupleIndices n t)) _ (chartScalars k n (tupleIndices n t) r) * a.val) =
      intoFraction k n (MvPolynomial.C r) * chartToFraction k n (tupleIndices n t) a.val
    rw [map_mul]
    exact congrArg (· * chartToFraction k n (tupleIndices n t) a.val) (chartScalars_value k n _ r)

theorem localized_differential :
    LocalizedDifferential k n (standardCechCover k n) (localizedCoordinates k n) := by
  intro m p s t
  let c := standardCechCover k n
  let F := (twistingSheaf k n m).val
  let x : tupleOpen c t.1 :=
    ⟨zeroPoint k n, (tupleOpen_eq_intersection k n t.1).symm ▸
      zeroPoint_mem_intersection k n (tupleIndices n t.1)⟩
  rw [localizedCoordinates_symm_value k n m t.1 _ x, increasingDifferential_apply]
  let evaluate : localSections (R k n) F (globalOpen k n) (tupleOpen c t.1) (tupleOpen_le c t.1) →+
      RationalFunctions k n :=
    { toFun := fun y ↦ (show TwistSections k n m _ from y).val x
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change evaluate (∑ _, _) = _
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [map_zsmul]
  congr 1
  let h := tupleOpen_reindex_le c j.succAbove t.1
  rw [localizedCoordinates_symm_value k n m (t.1 ∘ j.succAbove) _ ⟨x, h x.2⟩]
  rfl

/-- Multiplication by a global section acts by multiplication by its restriction. -/
def multiplyBySection :
    GlobalMultiply k n (twistingSheaf k n) := by
  intro a b s
  refine { val := { app := fun U ↦ ?_, naturality := fun {U V} f ↦ ?_ } }
  · apply ModuleCat.ofHom
    refine
      { toFun := fun z ↦ sectionMul k n a b U.unop (restriction k n le_top a s) z
        map_add' := fun x y ↦ ?_
        map_smul' := fun r x ↦ ?_ }
    · apply Subtype.ext
      funext v
      exact mul_add _ _ _
    · apply Subtype.ext
      funext v
      exact mul_left_comm _ _ _
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

open scoped TensorProduct in
/-- The action of a global section uses the tensor multiplication of the twists. -/
theorem multiplyBySection_app (a b : ℤ) (s : TwistSections k n a (globalOpen k n))
    (U : OpensOfProj k n) (z : TwistSections k n b U) :
    (multiplyBySection k n a b s).val.app (op U) z =
      (PresheafOfModules.sheafificationHomEquiv (𝟙 (moduleRingSheaf k n).obj)
        (twistMultiplication k n a b)).app (op U)
          (restriction k n le_top a s ⊗ₜ z) := by
  rw [twistMultiplication_presheaf]
  exact (twistPresheafMultiplication_tmul k n a b U _ _).symm

/-- In the increasing complex a coefficient morphism acts componentwise. -/
private theorem increasingMapComponent_apply {X : TopCat.{u}} (S : X.Sheaf RingCat.{u})
    {U : Opens X} {I : Type} [LinearOrder I] (c : Cover U I)
    {F G : PresheafOfModules.{u} S.obj} (f : F ⟶ G) (p : ℕ)
    (z : IncreasingCochains S c F p) (t : IncreasingTuple I p) :
    increasingMapComponent S c f p z t = f.app (op (tupleOpen c t.1)) (z t) := by
  obtain ⟨y, rfl⟩ := projectionComponent_surjective S c F p z
  rw [increasingMap_projection_apply]
  rfl

/-- The induced cochain map is multiplication by the localized global section. -/
theorem multiplyBySection_cochain_value (a b : ℤ)
    (s : TwistSections k n a (globalOpen k n)) (p : ℕ)
    (z : IncreasingCochains (R k n) (standardCechCover k n) (twistingSheaf k n b).val p)
    (t : IncreasingTuple (Index n) p) :
    let J := tupleIndices n t.1
    let c := standardCechCover k n
    let s' := restriction k n (tupleOpen_le c t.1) a s
    chartToFraction k n J
        ((localizedCoordinates k n (a + b) p t.1).symm
          (increasingMapComponent (R k n) c (multiplyBySection k n a b s).val p z t)).val =
      chartToFraction k n J ((localizedCoordinates k n a p t.1).symm s').val *
        chartToFraction k n J ((localizedCoordinates k n b p t.1).symm (z t)).val := by
  dsimp only
  let c := standardCechCover k n
  let x : tupleOpen c t.1 :=
    ⟨zeroPoint k n, (tupleOpen_eq_intersection k n t.1).symm ▸
      zeroPoint_mem_intersection k n (tupleIndices n t.1)⟩
  rw [localizedCoordinates_symm_value k n (a + b) t.1 _ x,
    localizedCoordinates_symm_value k n a t.1 _ x,
    localizedCoordinates_symm_value k n b t.1 _ x, increasingMapComponent_apply]
  rfl

theorem projectiveComparison : projectiveComparisonType.{u} := by
  intro k _ n _hn
  let c := standardCechCover k n
  let w : SectionCoordinates k n (twistingSheaf k n) := fun _ _ ↦ Equiv.refl _
  obtain ⟨h, H⟩ := orderedComparison k n c
  letI := h
  refine ⟨c, twistingSheaf k n, w, localizedCoordinates k n, multiplyBySection k n, h,
    rfl, ⟨by intros; rfl, by intros; rfl, by intros; rfl⟩,
    fun m _ t a x ↦ localizedCoordinates_value k n m t a x,
    localized_differential k n, by unfold GlobalMultiplyFormula; intros; rfl,
    fun m J hJ q hq ↦ intersection_acyclic k n J hJ m q hq,
    (fun m ↦ twist_acyclicOnIntersections k n m), H, ?_⟩
  obtain ⟨_, _, _, α, _, _, _⟩ := H
  intro m q
  exact ⟨groundCohomologyIso k n c (twistingSheaf k n m) q
    (α _ (twist_acyclicOnIntersections k n m) q)⟩

end DerivedFormalization.ProjectiveCechComparison
