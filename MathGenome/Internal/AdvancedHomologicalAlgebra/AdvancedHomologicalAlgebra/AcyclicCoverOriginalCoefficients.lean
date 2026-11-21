import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AcyclicCoverComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.EdgesAndFiveTerms
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits TopologicalSpace Opposite
open HomologicalComplex
open AdvancedHomologicalAlgebra.Cech
open AdvancedHomologicalAlgebra.SheafTheory (sectionRing)
open AdvancedHomologicalAlgebra.CechSequenceOriginal
open Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients
  (NaturalityData CarrierModelComparison)
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
  (coefficientCohomologyValue cohomologyValue)
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.DoubleTotalization
open AdvancedHomologicalAlgebra.DoubleComplexFirstPages (verticalHomology)
open AdvancedHomologicalAlgebra.CechToCohomology
  (natToIntDoubleComplex natToIntDoubleComplexMap natToIntDoubleComplexRowIso
    natToIntDoubleComplex_inQuadrant natToIntDoubleComplex_finiteDiagonals
    mapExtendIso mapExtendIso_hom_f mapExtendXIso)
open AdvancedHomologicalAlgebra.EdgesAndFiveTerms

universe a u r v b w₁ w₂ w₃ w₄

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3500
set_option maxHeartbeats 1000000

namespace AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients

open private rowIso_naturality transportAugmentationClass mappedAugmentation_homology
  singleAugmentation_homology row_edge_augmentation
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AcyclicCoverComparison

open private extendZeroRowAugmentation extendZeroRowAugmentation_f
  extendZeroRowAugmentation_closed zeroRowTotalMap zeroRowTotalMap_f
  verticalAugmentation_closed extendedColumnIso
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r}) {U : Opens X}
  {T : Type v} (c : Cover U T)

private lemma embed_nat (n : ℕ) : embedding.f n = (n : ℤ) := by simp [embedding]

private abbrev ambientComplexFunctor :
    AmbientSheaves.{a} R ⥤ CochainComplex (CochainModules.{u,r,a,v} R (U := U)) ℕ :=
  SheafOfModules.forget R ⋙ cochainFunctor.{u,r,a,v} R c

private abbrev sourceComplex (F : SheafOfModules.{a} R) :=
  (liftedRawCochainComplex.{a,u,r,v} R c F).extend embedding

private abbrev sourceComplexMap {F G : SheafOfModules.{a} R} (f : F ⟶ G) :
    sourceComplex R c F ⟶ sourceComplex R c G :=
  extendMap ((liftedComplexFunctor.{a,u,r,v} R c).map f) embedding

private lemma sourceModel_naturality {F G : SheafOfModules.{a} R} (f : F ⟶ G) (n : ℕ) :
    homologyMap (sourceComplexMap R c f) (n : ℤ) ≫ (sourceModel.{a,u,r,v} R c G n).hom =
      (sourceModel.{a,u,r,v} R c F n).hom ≫ (sourceCohomology.{a,u,r,v} R c n).map f := by
  let L := rawCochainLift.{a,u,r,v} R c
  let g := (rawComplexFunctor.{a,u,r,v} R c).map f
  let g' := (L.mapHomologicalComplex (.up ℕ)).map g
  have h₁ := extendHomologyIso_hom_naturality g' embedding (embed_nat n)
  have h₂ := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor _ (.up ℕ) n).map g) L
  change homologyMap g' n ≫ ((((rawComplexFunctor.{a,u,r,v} R c).obj G).sc n).mapHomologyIso L).hom =
    ((((rawComplexFunctor.{a,u,r,v} R c).obj F).sc n).mapHomologyIso L).hom ≫ L.map (homologyMap g n) at h₂
  dsimp only [sourceModel, Iso.trans_hom]
  change homologyMap (extendMap g' embedding) (n : ℤ) ≫ (_ ≫ _) =
    (_ ≫ _) ≫ L.map (homologyMap g n)
  erw [← assoc, h₁, assoc, h₂, ← assoc]

private abbrev cechTerm (p : ℕ) :=
  cochainFunctor.{u,r,a,v} R c ⋙ eval (CochainModules.{u,r,a,v} R (U := U)) (.up ℕ) p

variable (e : CoefficientComparison.{a,u,r,v} R c)

private abbrev axisCoefficient {F : SheafOfModules.{a} R}
    (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)) :=
  e.iso.hom.app F.val ≫ verticalAugmentation.{u,r,a,v} R c I

private abbrev verticalAxis {F : SheafOfModules.{a} R}
    (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)) :=
  extendZeroRowAugmentation (doubleComplex.{u,r,a,v} R c I.cocomplex)
    (axisCoefficient R c e I)

private lemma axis_closed_nat {F : SheafOfModules.{a} R}
    (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)) (p : ℕ) :
    (axisCoefficient R c e I).f p ≫ ((doubleComplex.{u,r,a,v} R c I.cocomplex).X p).d 0 1 = 0 := by
  rw [comp_f, assoc, verticalAugmentation_closed, comp_zero]

private lemma vertical_cycle {F : SheafOfModules.{a} R}
    (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)) (p q : ℤ)
    (hq : (ComplexShape.up ℤ).Rel 0 q) :
    (verticalAxis R c e I).f p ≫ ((doubleComplexInt.{u,r,a,v} R c I.cocomplex).X p).d 0 q = 0 :=
  extendZeroRowAugmentation_closed _ _ (axis_closed_nat R c e I) p q hq

private abbrev verticalTotal {F : SheafOfModules.{a} R}
    (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)) :=
  zeroRowTotalMap (doubleComplex.{u,r,a,v} R c I.cocomplex)
    (axisCoefficient R c e I) (axis_closed_nat R c e I)

private lemma verticalTotal_f {F : SheafOfModules.{a} R}
    (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)) (p : ℤ) :
    (verticalTotal R c e I).f p = (verticalAxis R c e I).f p ≫
      sumInjection (doubleComplexInt.{u,r,a,v} R c I.cocomplex) p 0 p (add_zero p) :=
  zeroRowTotalMap_f _ _ _ p

private lemma verticalTotal_normalized {F : SheafOfModules.{a} R}
    (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)) :
    IsVerticalAugmentation R c e F I (verticalTotal R c e I) := by
  intro p
  rw [verticalTotal_f, verticalAxis, extendZeroRowAugmentation_f]
  simp only [axisCoefficient, comp_f, assoc]
  rfl

private lemma coefficientIso_naturality {F G : SheafOfModules.{a} R} (f : F ⟶ G) :
    (liftedComplexFunctor.{a,u,r,v} R c).map f ≫ e.iso.hom.app G.val =
      e.iso.hom.app F.val ≫ (ambientComplexFunctor.{a,u,r,v} R c).map
        ((liftSheafCoefficients.{max u r,u,r,a} R).map f) :=
  e.iso.hom.naturality f.val

private lemma negativeEntry (K : CochainComplex (AmbientSheaves.{a} R) ℕ)
    (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero (((doubleComplexInt.{u,r,a,v} R c K).X p).X q) :=
  natToIntDoubleComplex_inQuadrant (doubleComplex.{u,r,a,v} R c K) p q (by omega)

private lemma sourceNegative (F : SheafOfModules.{a} R) (p : ℤ) (hp : p < 0) :
    IsZero ((sourceComplex R c F).X p) :=
  (liftedRawCochainComplex.{a,u,r,v} R c F).isZero_extend_X embedding p
    (fun n hn => by rw [embed_nat] at hn; omega)

private lemma zeroRowTotal_naturality {B : Type*} [Category* B] [Abelian B]
    {K K' : HomologicalComplex₂ B (.up ℕ) (.up ℕ)}
    [(natToIntDoubleComplex K).HasTotal (.up ℤ)] [(natToIntDoubleComplex K').HasTotal (.up ℤ)]
    {A A' : CochainComplex B ℕ} (f : A ⟶ A') (φ : K ⟶ K')
    (g : A ⟶ K.flip.X 0) (g' : A' ⟶ K'.flip.X 0)
    (hg : ∀ p, g.f p ≫ (K.X p).d 0 1 = 0)
    (hg' : ∀ p, g'.f p ≫ (K'.X p).d 0 1 = 0)
    (h : f ≫ g' = g ≫ ((HomologicalComplex₂.flipFunctor _ _ _).map φ).f 0) :
    extendMap f embedding ≫ zeroRowTotalMap K' g' hg' =
      zeroRowTotalMap K g hg ≫ HomologicalComplex₂.total.map (natToIntDoubleComplexMap φ) (.up ℤ) := by
  let ψ := natToIntDoubleComplexMap φ
  have hAxis : extendMap f embedding ≫ extendZeroRowAugmentation K' g' =
      extendZeroRowAugmentation K g ≫ ((HomologicalComplex₂.flipFunctor _ _ _).map ψ).f 0 := by
    apply (cancel_mono (natToIntDoubleComplexRowIso K' 0).hom).1
    simp only [extendZeroRowAugmentation, assoc, Iso.inv_hom_id, comp_id]
    erw [rowIso_naturality φ, Iso.inv_hom_id_assoc, ← extendMap_comp, ← extendMap_comp, h]
  apply HomologicalComplex.hom_ext
  intro n
  simp only [comp_f, zeroRowTotalMap_f, assoc, sumInjection, HomologicalComplex₂.ιTotal_map]
  simpa only [comp_f, assoc, HomologicalComplex₂.flipFunctor] using congrArg
    (fun k => k.f n ≫ (natToIntDoubleComplex K').ιTotal (.up ℤ) n 0 n (add_zero n)) hAxis

private lemma verticalNaturality {F G : SheafOfModules.{a} R} (f : F ⟶ G)
    {I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)} {J : InjectiveResolution (nativeCoefficient.{u,r,a} R G)}
    (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = (liftSheafCoefficients.{max u r,u,r,a} R).map f ≫ J.ι.f 0) :
    sourceComplexMap R c f ≫ verticalTotal R c e J = verticalTotal R c e I ≫
      HomologicalComplex₂.total.map (doubleComplexIntMap.{u,r,a,v} R c φ) (.up ℤ) := by
  refine zeroRowTotal_naturality ((liftedComplexFunctor.{a,u,r,v} R c).map f)
    (doubleComplexMap.{u,r,a,v} R c φ) (axisCoefficient R c e I) (axisCoefficient R c e J)
    (axis_closed_nat R c e I) (axis_closed_nat R c e J) ?_
  let H := ambientComplexFunctor.{a,u,r,v} R c
  change (liftedComplexFunctor.{a,u,r,v} R c).map f ≫ e.iso.hom.app G.val ≫ H.map (J.ι.f 0) =
    (e.iso.hom.app F.val ≫ H.map (I.ι.f 0)) ≫ H.map (φ.f 0)
  rw [← assoc, coefficientIso_naturality R c e f, assoc, assoc,
    ← H.map_comp, ← H.map_comp, comm]

private lemma column_cycle_nat {M : AmbientSheaves.{a} R} (I : InjectiveResolution M) (p : ℕ) :
    (cechTerm.{a,u,r,v} R c p).map ((SheafOfModules.forget.{max a u r} R).map (I.ι.f 0)) ≫
      ((doubleComplex.{u,r,a,v} R c I.cocomplex).X p).d 0 1 = 0 :=
  verticalAugmentation_closed.{u,r,a,v} R c I p

variable [EnoughInjectives (AmbientSheaves.{a} R)]

private def verticalClassMap {F : SheafOfModules.{a} R} {I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)}
    (D : NaturalityData.{u,r,a,v} R c) :
    sourceComplex R c F ⟶ verticalHomology (doubleComplexInt.{u,r,a,v} R c I.cocomplex) 0 :=
  extendMap (degreeZeroMap R c e F) embedding ≫ (D.vertical I 0).inv

private lemma verticalClassMap_f {F : SheafOfModules.{a} R} {I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)}
    (D : NaturalityData.{u,r,a,v} R c) (p : ℤ) :
    let K := (doubleComplexInt.{u,r,a,v} R c I.cocomplex).X p
    (verticalClassMap R c e (I := I) D).f p =
      K.liftCycles ((verticalAxis R c e I).f p) 1 (by simp) (vertical_cycle R c e I p 1 (by simp)) ≫ K.homologyπ 0 := by
  dsimp only
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    let G := cechTerm.{a,u,r,v} R c p
    let K := (doubleComplex.{u,r,a,v} R c I.cocomplex).X p
    let L := (doubleComplexInt.{u,r,a,v} R c I.cocomplex).X (p : ℤ)
    let i := extendedColumnIso (doubleComplex.{u,r,a,v} R c I.cocomplex) p
    let x := (liftedRawCochainComplex.{a,u,r,v} R c F).extendXIso embedding (embed_nat p)
    let z := (cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R 0).obj (nativeCoefficient.{u,r,a} R F))).extendXIso embedding (embed_nat p)
    let k := L.liftCycles ((verticalAxis R c e I).f (p : ℤ)) 1 (by simp) (vertical_cycle R c e I (p : ℤ) 1 (by simp))
    let b := K.liftCycles (G.map ((SheafOfModules.forget.{max a u r} R).map (I.ι.f 0))) 1 (by simp) (column_cycle_nat.{a,u,r,v} R c I p)
    let _ := D.exactTuple p
    have hc : k ≫ L.iCycles 0 ≫ i.hom.f 0 ≫ (K.extendXIso embedding (embed_nat 0)).hom =
        (x ≪≫ (eval (CochainModules.{u,r,a,v} R (U := U)) (.up ℕ) p).mapIso (e.iso.app F.val)).hom ≫ b ≫ K.iCycles 0 := by
      rw [← assoc k, liftCycles_i]
      change (verticalAxis R c e I).f (p : ℤ) ≫ (intBicomplexTermIso (doubleComplex.{u,r,a,v} R c I.cocomplex) p 0).hom = _
      rw [verticalAxis, extendZeroRowAugmentation_f]
      simp only [Iso.trans_hom, Functor.mapIso_hom, eval_map, assoc, Iso.inv_hom_id, comp_id,
        b, liftCycles_i]
      rfl
    have hclass := transportAugmentationClass i _ k b hc
    have hmap : b ≫ K.homologyπ 0 ≫
        (((underlyingComplex.{u,r,a} R I.cocomplex).sc 0).mapHomologyIso G).hom ≫
        G.map (I.isoRightDerivedObj (SheafOfModules.forget.{max a u r} R) 0).inv =
        G.map ((SheafOfModules.forget.{max a u r} R).toRightDerivedZero.app (nativeCoefficient.{u,r,a} R F)) :=
      mappedAugmentation_homology I (SheafOfModules.forget.{max a u r} R) G b (by
        change b ≫ K.iCycles 0 = _
        simp only [b, liftCycles_i])
    let _ : IsIso ((D.vertical I 0).hom.f (p : ℤ)) :=
      inferInstanceAs (IsIso ((eval (CochainModules.{u,r,a,v} R (U := U)) (.up ℤ) (p : ℤ)).map (D.vertical I 0).hom))
    apply (cancel_mono ((D.vertical I 0).hom.f (p : ℤ) ≫ z.hom)).1
    have he := congrArg (fun k => k.f (p : ℤ)) (D.vertical I 0).inv_hom_id
    simp only [comp_f, id_f] at he
    change ((extendMap (degreeZeroMap R c e F) embedding).f (p : ℤ) ≫
      (D.vertical I 0).inv.f (p : ℤ)) ≫ _ = (k ≫ L.homologyπ 0) ≫ _
    rw [assoc, reassoc_of% he, D.vertical_component I p 0, extendMap_f _ _ (embed_nat p)]
    simp only [assoc, verticalComponent, Iso.trans_hom]
    change x.hom ≫ _ = k ≫ L.homologyπ 0 ≫ (homologyMapIso i 0).hom ≫
      (K.extendHomologyIso embedding (embed_nat 0)).hom ≫
      (((underlyingComplex.{u,r,a} R I.cocomplex).sc 0).mapHomologyIso G).hom ≫
      G.map (I.isoRightDerivedObj (SheafOfModules.forget.{max a u r} R) 0).inv
    rw [reassoc_of% hclass]
    simp only [Iso.trans_hom, Functor.mapIso_hom, eval_map, assoc]
    rw [hmap]
    change x.hom ≫ (degreeZeroMap R c e F).f p ≫ z.inv ≫ z.hom = _
    rw [Iso.inv_hom_id, comp_id]
    rfl
  · exact (sourceNegative R c F _ (lt_of_not_ge hp)).eq_of_src _ _

private lemma vertical_at_zero {F : SheafOfModules.{a} R} {I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)}
    (D : NaturalityData.{u,r,a,v} R c) (p : ℤ) :
    IsIso (homologyMap (mkHomFromSingle (K := (doubleComplexInt.{u,r,a,v} R c I.cocomplex).X p)
      (j := 0) ((verticalAxis R c e I).f p) (vertical_cycle R c e I p)) 0) := by
  let K := (doubleComplexInt.{u,r,a,v} R c I.cocomplex).X p
  let A := (sourceComplex R c F).X p
  let f : (single (CochainModules.{u,r,a,v} R (U := U)) (.up ℤ) 0).obj A ⟶ K :=
    mkHomFromSingle ((verticalAxis R c e I).f p) (vertical_cycle R c e I p)
  let g := verticalClassMap R c e (I := I) D
  have he : IsIso (degreeZeroMap R c e F) := by
    unfold degreeZeroMap
    infer_instance
  let _ : IsIso g := by
    change IsIso (((embedding.extendFunctor (CochainModules.{u,r,a,v} R (U := U))).map (degreeZeroMap R c e F)) ≫
      (D.vertical I 0).inv)
    infer_instance
  have hg : IsIso (g.f p) := inferInstanceAs (IsIso ((eval (CochainModules.{u,r,a,v} R (U := U)) (.up ℤ) p).map g))
  have h : (singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫ homologyMap f 0 = g.f p := by
    rw [verticalClassMap_f R c e D]
    exact singleAugmentation_homology K A ((verticalAxis R c e I).f p) (vertical_cycle R c e I p)
  let _ : IsIso ((singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫ homologyMap f 0) := by
    rw [h]
    exact hg
  exact IsIso.of_isIso_comp_left ((singleObjHomologySelfIso (.up ℤ) 0 A).inv) (homologyMap f 0)

private lemma vertical_off_zero {F : SheafOfModules.{a} R} {I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)}
    (D : NaturalityData.{u,r,a,v} R c) (hF : AcyclicOnIntersections.{a,u,r,v} R c F)
    (p q : ℤ) (hq : q ≠ 0) :
    IsZero (((doubleComplexInt.{u,r,a,v} R c I.cocomplex).X p).homology q) := by
  by_cases hp : 0 ≤ p
  · by_cases hq' : 0 ≤ q
    · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq'
      let M := nativeCoefficient.{u,r,a} R F
      let e := (eval (CochainModules.{u,r,a,v} R (U := U)) (.up ℤ) (p : ℤ)).mapIso (D.vertical I q) ≪≫
        (cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)).extendXIso embedding (embed_nat p)
      apply e.isZero_iff.2
      apply ModuleCat.isZero_iff_subsingleton.2
      have h (t : Fin (p + 1) → T) :
          Subsingleton (((localCohomology.{u,r,a} R q).obj M).obj (op (tupleOpen c t))) :=
        ModuleCat.isZero_iff_subsingleton.1
          (((originalLocalSectionsIso.{u,r,a} R (tupleOpen c t) q).app M).isZero_iff.2 (hF p t q (by omega)))
      change Subsingleton (∀ t : Fin (p + 1) → T,
        ((localCohomology.{u,r,a} R q).obj M).obj (op (tupleOpen c t)))
      exact ⟨fun x y => funext fun t => (h t).elim (x t) (y t)⟩
    · exact (ExactAt.of_isZero
        (negativeEntry.{a,u,r,v} R c I.cocomplex p q (Or.inr (lt_of_not_ge hq')))).isZero_homology
  · exact (ExactAt.of_isZero
      (negativeEntry.{a,u,r,v} R c I.cocomplex p q (Or.inl (lt_of_not_ge hp)))).isZero_homology

private lemma vertical_quasiIso {F : SheafOfModules.{a} R}
    (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F))
    (D : NaturalityData.{u,r,a,v} R c) (hF : AcyclicOnIntersections.{a,u,r,v} R c F) :
    QuasiIso (verticalTotal R c e I) := by
  let K := doubleComplexInt.{u,r,a,v} R c I.cocomplex
  obtain ⟨f, hf, h⟩ := AugmentedDoubleComplexComparison.cochain_column_assembly K
    (natToIntDoubleComplex_finiteDiagonals (doubleComplex.{u,r,a,v} R c I.cocomplex))
    (fun p q hq => negativeEntry.{a,u,r,v} R c I.cocomplex p q (Or.inr hq))
    _ (verticalAxis R c e I) (vertical_cycle R c e I) (vertical_at_zero.{a,u,r,v} R c e D)
      (vertical_off_zero.{a,u,r,v} R c D hF)
  have he : verticalTotal R c e I = f := HomologicalComplex.hom_ext _ _ (fun n => (verticalTotal_f R c e I n).trans (h n).symm)
  exact he ▸ hf

private lemma abutment_eq {M : AmbientSheaves.{a} R} (I : InjectiveResolution M)
    (D : NaturalityData.{u,r,a,v} R c) (n : ℕ) :
    D.abutment I n = abutmentIso.{u,r,a,v} R c I n := by
  have hα : D.augmentation I = totalAugmentationMap.{u,r,a,v} R c I := by
    apply HomologicalComplex.hom_ext
    intro m
    exact (D.augmentation_formula I m).trans (totalAugmentationMap_f R c I m).symm
  apply Iso.ext
  let α := totalAugmentationMap.{u,r,a,v} R c I
  let _ : IsIso (homologyMap α (n : ℤ)) := inferInstance
  have hD : homologyMap α (n : ℤ) ≫ (D.abutment I n).hom =
      liftedSectionModelMap.{u,r,a,v} R c I n := by
    change homologyMap (totalAugmentationMap.{u,r,a,v} R c I) (n : ℤ) ≫ _ = _
    rw [← hα, D.abutment_formula]
  apply (cancel_epi (homologyMap α (n : ℤ))).1
  rw [hD]
  simp only [α, abutmentIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
    IsIso.hom_inv_id_assoc]

private def comparisonAt {F : SheafOfModules.{a} R}
    (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)) (n : ℕ) :
    (sourceCohomology.{a,u,r,v} R c n).obj F ⟶ (originalSectionCohomology.{a,u,r,v} R c n).obj F :=
  (sourceModel.{a,u,r,v} R c F n).inv ≫ homologyMap (verticalTotal R c e I) (n : ℤ) ≫
    (abutmentIso.{u,r,a,v} R c I n).hom

private lemma comparisonAt_naturality {F G : SheafOfModules.{a} R} (f : F ⟶ G)
    {I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)}
    {J : InjectiveResolution (nativeCoefficient.{u,r,a} R G)}
    (φ : I.cocomplex ⟶ J.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = (liftSheafCoefficients.{max u r,u,r,a} R).map f ≫ J.ι.f 0)
    (n : ℕ) :
    (sourceCohomology.{a,u,r,v} R c n).map f ≫ comparisonAt R c e J n =
      comparisonAt R c e I n ≫ (originalSectionCohomology.{a,u,r,v} R c n).map f := by
  have h := abutmentIso_naturality.{u,r,a,v} R c I J φ
    ((liftSheafCoefficients.{max u r,u,r,a} R).map f) comm n
  have hv := congrArg (fun k => homologyMap k (n : ℤ))
    (verticalNaturality R c e f φ comm)
  simp only [homologyMap_comp] at hv
  apply (cancel_epi (sourceModel.{a,u,r,v} R c F n).hom).1
  simp only [comparisonAt, assoc, Iso.hom_inv_id_assoc]
  erw [← reassoc_of% (sourceModel_naturality R c f n), Iso.hom_inv_id_assoc, reassoc_of% hv, h]
  rfl

private lemma comparisonAt_independent {F : SheafOfModules.{a} R}
    (I J : InjectiveResolution (nativeCoefficient.{u,r,a} R F)) (n : ℕ) :
    comparisonAt R c e I n = comparisonAt R c e J n := by
  let f := (liftSheafCoefficients.{max u r,u,r,a} R).map (𝟙 F)
  simpa using (comparisonAt_naturality R c e (𝟙 F)
    (InjectiveResolution.desc f J I) (InjectiveResolution.desc_commutes_zero f J I) n).symm

private lemma comparisonAt_edge {F : SheafOfModules.{a} R}
    (I : InjectiveResolution (nativeCoefficient.{u,r,a} R F))
    (D : NaturalityData.{u,r,a,v} R c)
    (E : EdgeData (D.data I).filtration (D.data I).pages) (n : ℕ) :
    let P := D.data I
    let K := liftedRawCochainComplex.{a,u,r,v} R c F
    (sourceModel.{a,u,r,v} R c F n).inv ≫
      (K.extendHomologyIso embedding (embed_nat n)).hom ≫
      homologyMap (degreeZeroMap R c e F) n ≫
      (secondPageComparison.{u,r,a,v} R c I P (D.vertical I) n 0).inv ≫
      eqToHom (congrArg (PageCohomology.object P.filtration P.pages 2 (n : ℤ)) (add_zero _)) ≫
      E.row (n : ℤ) (by omega) ≫ (D.abutment I n).hom = comparisonAt R c e I n := by
  dsimp only
  let g := degreeZeroMap R c e F
  have hedge := row_edge_augmentation (D.data I).firstPages E (verticalTotal R c e I)
    (verticalClassMap R c e (I := I) D) (verticalAxis R c e I).f
    (fun p => vertical_cycle R c e I p 1 (by simp))
    (verticalTotal_f R c e I) (verticalClassMap_f R c e D) (n : ℤ) (by omega)
  rw [secondPageComparison, Iso.trans_inv, Iso.trans_inv]
  simp only [Int.natCast_zero, assoc]
  have hg := extendHomologyIso_hom_naturality g embedding (embed_nat n)
  erw [← reassoc_of% hg, Iso.hom_inv_id_assoc, homologyMapIso_inv, ← homologyMap_comp_assoc]
  change (sourceModel.{a,u,r,v} R c F n).inv ≫
    homologyMap (verticalClassMap R c e (I := I) D) (n : ℤ) ≫
    ((D.data I).firstPages.secondIso (n : ℤ) 0).inv ≫ _ = _
  rw [reassoc_of% hedge, abutment_eq R c I D n]
  rfl

omit [EnoughInjectives (AmbientSheaves.{a} R)] in
/-- The original Čech comparison on an acyclic cover is the normalized bottom edge. -/
theorem acyclic_cover_comparison :
    Specs.AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients.comparisonType.{a,u,r,v} := by
  intro X R U T c
  let h := SheafCohomologyOriginalCoefficients.enoughInjectives.{a,u,r} R
  let _ := h
  obtain ⟨ε, hε, _⟩ := coefficient_carrier_comparison.{u,r,a,v} R c
  let e : CoefficientComparison.{a,u,r,v} R c := ⟨ε, hε⟩
  let D := coefficientNaturalityData.{u,r,a,v} R c
  let I (F : SheafOfModules.{a} R) := injectiveResolution (nativeCoefficient.{u,r,a} R F)
  let η (n : ℕ) : sourceCohomology.{a,u,r,v} R c n ⟶
        originalSectionCohomology.{a,u,r,v} R c n :=
    { app F := comparisonAt R c e (I F) n
      naturality {F G} f := comparisonAt_naturality R c e f
        (InjectiveResolution.desc ((liftSheafCoefficients.{max u r,u,r,a} R).map f)
          (I G) (I F))
        (InjectiveResolution.desc_commutes_zero _ _ _) n }
  refine ⟨h, ⟨D⟩, e, η, ?_, ?_, ?_⟩
  · intro F n hF
    let _ := vertical_quasiIso R c e (I F) D hF
    let _ : IsIso (homologyMap (verticalTotal R c e (I F)) (n : ℤ)) :=
      (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
    let _ : IsIso ((η n).app F) := by
      change IsIso (comparisonAt R c e (I F) n)
      unfold comparisonAt
      infer_instance
    let i := (asIso ((η n).app F)).toLinearEquiv
    exact ((ULift.moduleEquiv (R := sectionRing R U)).symm.trans
      (i.trans ULift.moduleEquiv)).bijective
  · intro F G f n x
    exact congrArg (fun g => (g (ULift.up x)).down) ((η n).naturality f)
  · intro D' F J
    let P := D'.data J
    refine ⟨verticalTotal R c e J, verticalTotal_normalized R c e J,
      ?_, ⟨edgeData P.filtration P.pages P.converges.finite ?_⟩, ?_⟩
    · intro n
      let _ := D'.augmentation_quasiIso J
      let _ : IsIso (homologyMap (D'.augmentation J) (n : ℤ)) := inferInstance
      have he : (D'.abutment J n).hom = inv (homologyMap (D'.augmentation J) (n : ℤ)) ≫
          liftedSectionModelMap.{u,r,a,v} R c J n := by
        apply (cancel_epi (homologyMap (D'.augmentation J) (n : ℤ))).1
        rw [D'.abutment_formula, IsIso.hom_inv_id_assoc]
      change comparisonAt R c e (I F) n = _
      rw [comparisonAt_independent R c e (I F) J n, comparisonAt, ← abutment_eq R c J D' n, he]
    · intro p n hn
      have hz := D'.firstQuadrant J 2 p (n - p) (by omega)
      simpa only [DoubleComplexFirstPages.page, show p + (n - p) = n by omega] using hz
    · intro E n
      change _ = comparisonAt R c e (I F) n
      rw [comparisonAt_independent R c e (I F) J n]
      exact comparisonAt_edge R c e J D' E n

open private compareExtendedHomology transportedHomology_natural
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

private lemma abutment_hom_formula {M : AmbientSheaves.{a} R}
    (D : NaturalityData.{u,r,a,v} R c) (I : InjectiveResolution M) (n : ℕ) :
    letI := D.augmentation_quasiIso I
    letI : IsIso (homologyMap (D.augmentation I) (n : ℤ)) := inferInstance
    (D.abutment I n).hom = inv (homologyMap (D.augmentation I) (n : ℤ)) ≫
      liftedSectionModelMap.{u,r,a,v} R c I n := by
  let _ := D.augmentation_quasiIso I
  apply (cancel_epi (homologyMap (D.augmentation I) (n : ℤ))).1
  rw [D.abutment_formula, IsIso.hom_inv_id_assoc]

omit [EnoughInjectives (AmbientSheaves.{a} R)] in
private lemma ambientVertical_f {M : AmbientSheaves.{a} R} (I : InjectiveResolution M) (p : ℕ) :
    let K := cochainComplex.{u,r,a,v} R c M.val
    (verticalTotalAugmentationMap.{u,r,a,v} R c I).f (p : ℤ) =
      (K.extendXIso embedding (embed_nat p)).hom ≫
        (verticalAugmentation.{u,r,a,v} R c I).f p ≫
        (intBicomplexTermIso (doubleComplex.{u,r,a,v} R c I.cocomplex) p 0).inv ≫
        sumInjection (doubleComplexInt.{u,r,a,v} R c I.cocomplex) (p : ℤ) 0 (p : ℤ)
          (add_zero _) := by
  dsimp only [verticalTotalAugmentationMap]
  rw [zeroRowTotalMap_f, extendZeroRowAugmentation_f]
  simp only [assoc]

private lemma ambientComparison_naturality {M N : AmbientSheaves.{a} R}
    (D : NaturalityData.{u,r,a,v} R c) (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (n : ℕ) :
    homologyMap (extendMap (cochainMap.{u,r,a,v} R c f.val) embedding) (n : ℤ) ≫
      homologyMap (verticalTotalAugmentationMap.{u,r,a,v} R c J) (n : ℤ) ≫ (D.abutment J n).hom =
    homologyMap (verticalTotalAugmentationMap.{u,r,a,v} R c I) (n : ℤ) ≫ (D.abutment I n).hom ≫
      (sectionLift.{u,r,a,v} R c).map ((cohomologyValue.{a,u,r} R U n).map f) := by
  let φ := InjectiveResolution.desc f J I
  have hφ := InjectiveResolution.desc_commutes_zero f J I
  have h := zeroRowTotal_naturality (cochainMap.{u,r,a,v} R c f.val)
    (doubleComplexMap.{u,r,a,v} R c φ) (verticalAugmentation.{u,r,a,v} R c I)
    (verticalAugmentation.{u,r,a,v} R c J) (verticalAugmentation_closed.{u,r,a,v} R c I)
    (verticalAugmentation_closed.{u,r,a,v} R c J)
    (verticalAugmentation_naturality.{u,r,a,v} R c I J φ f hφ)
  have hv := congrArg (fun g => homologyMap g (n : ℤ)) h
  simp only [homologyMap_comp] at hv
  erw [← assoc, hv, assoc, abutment_eq R c I D n, abutment_eq R c J D n]
  erw [abutmentIso_naturality.{u,r,a,v} R c I J φ f hφ n]
  rfl

section CarrierComparison

set_option quotPrecheck false in
set_option hygiene false in
local notation "L" => sheafCarrierLift.{u,r,a,b} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "P" => presheafCarrierLift.{u,r,a,b} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => cochainCarrierLift.{u,r,a,v,b} R c

variable [EnoughInjectives (AmbientSheaves.{max a b} R)]
  [(L).PreservesInjectiveObjects] [(L).PreservesHomology] [(P).PreservesHomology]
  {D : NaturalityData.{u,r,a,v} R c} {E : NaturalityData.{u,r,max a b,v} R c}
  {F : SheafOfModules.{a} R} {I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)}
  (A : CarrierModelComparison.{u,r,a,v,b} R c D E I)

private def commonIntCochainIso :
    (cochainComplex.{u,r,max a b,v} R c ((L).obj (nativeCoefficient.{u,r,a} R F)).val).extend
      embedding ≅ ((S).mapHomologicalComplex (.up ℤ)).obj (sourceComplex R c F) :=
  (embedding.extendFunctor _).mapIso (commonCochainIso.{a,u,r,v,b} R c (F := F) A e) ≪≫
    (mapExtendIso (S) (liftedRawCochainComplex.{a,u,r,v} R c F) embedding).symm

private lemma commonIntCochainIso_f (p : ℕ) :
    let K := cochainComplex.{u,r,max a b,v} R c ((L).obj (nativeCoefficient.{u,r,a} R F)).val
    let K₀ := liftedRawCochainComplex.{a,u,r,v} R c F
    (commonIntCochainIso R c e A).hom.f (p : ℤ) ≫ (S).map (K₀.extendXIso embedding (embed_nat p)).hom =
      (K.extendXIso embedding (embed_nat p)).hom ≫ (commonCochainIso.{a,u,r,v,b} R c (F := F) A e).hom.f p := by
  let K := liftedRawCochainComplex.{a,u,r,v} R c F
  let H := (S).mapHomologicalComplex (.up ℕ)
  let i := mapExtendIso (S) K embedding
  have hi : i.inv.f (p : ℤ) ≫ (S).map (K.extendXIso embedding (embed_nat p)).hom =
      ((H.obj K).extendXIso embedding (embed_nat p)).hom := by
    have h := HomologicalComplex.congr_hom i.inv_hom_id (p : ℤ)
    simp only [comp_f, id_f] at h
    rw [← mapExtendIso_hom_f (S) K embedding (embed_nat p), ← assoc, h, id_comp]
  simp only [commonIntCochainIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, comp_f, assoc]
  change (extendMap (commonCochainIso.{a,u,r,v,b} R c (F := F) A e).hom embedding).f (p : ℤ) ≫ _ ≫ _ = _
  rw [hi, extendMap_f _ _ (embed_nat p)]
  simp only [assoc]
  let z := (H.obj K).extendXIso embedding (embed_nat p)
  change _ ≫ _ ≫ z.inv ≫ z.hom = _
  rw [Iso.inv_hom_id, comp_id]

private lemma commonCochainIso_hom_map :
    (commonCochainIso.{a,u,r,v,b} R c (F := F) A e).hom ≫
      ((S).mapHomologicalComplex (.up ℕ)).map (e.iso.app F.val).hom =
    (A.localTuples (nativeCoefficient.{u,r,a} R F).val).hom := by
  simp only [commonCochainIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id]
  rw [CategoryTheory.Functor.map_id, comp_id]

private lemma commonCochainIso_coordinate (p : ℕ) (s : Cochains R F.val c p) :
    (commonCochainIso.{a,u,r,v,b} R c (F := F) A e).hom.f p (fun t ↦ ULift.up (ULift.up (s t))) =
      ULift.up (ULift.up s) := by
  let j := ((S).mapHomologicalComplex (.up ℕ)).map (e.iso.app F.val).hom
  have hj : IsIso (j.f p) := inferInstanceAs
    (IsIso ((eval (CochainModules.{u,r,max a b,v} R (U := U)) (.up ℕ) p).map j))
  apply (ModuleCat.mono_iff_injective (j.f p)).1 inferInstance
  let x : Cochains R ((L).obj (nativeCoefficient.{u,r,a} R F)).val c p :=
    fun t ↦ ULift.up (ULift.up (s t))
  have h : (commonCochainIso.{a,u,r,v,b} R c (F := F) A e).hom.f p ≫ j.f p =
      (A.localTuples (nativeCoefficient.{u,r,a} R F).val).hom.f p :=
    HomologicalComplex.congr_hom (commonCochainIso_hom_map R c e A) p
  change j.f p ((commonCochainIso.{a,u,r,v,b} R c (F := F) A e).hom.f p x) = j.f p (ULift.up (ULift.up s))
  refine (congrArg (fun f => f x) h).trans ((A.localTuples_formula _ p x).trans ?_)
  change ULift.up (fun t ↦ ULift.up (s t)) = ULift.up ((e.iso.hom.app F.val).f p (ULift.up s))
  exact congrArg ULift.up (funext fun t ↦ (e.coordinate F.val p s t).symm)

private lemma verticalTotal_carrier {β : sourceComplex R c F ⟶
      sumTotal (doubleComplexInt.{u,r,a,v} R c I.cocomplex)}
    (hβ : IsVerticalAugmentation R c e F I β) :
    let I' := carrierLiftResolution.{u,r,a,b} R I
    verticalTotalAugmentationMap.{u,r,max a b,v} R c I' ≫ A.total.hom =
      (commonIntCochainIso R c e A).hom ≫ ((S).mapHomologicalComplex (.up ℤ)).map β := by
  let I' := carrierLiftResolution.{u,r,a,b} R I
  let K := liftedRawCochainComplex.{a,u,r,v} R c F
  let K' := cochainComplex.{u,r,max a b,v} R c ((L).obj (nativeCoefficient.{u,r,a} R F)).val
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : 0 ≤ n
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    let d := intBicomplexTermIso (doubleComplex.{u,r,a,v} R c I.cocomplex) p 0
    let d' := intBicomplexTermIso (doubleComplex.{u,r,max a b,v} R c I'.cocomplex) p 0
    let t := (A.double.hom.f (p : ℤ)).f 0
    let j := sumInjection (doubleComplexInt.{u,r,a,v} R c I.cocomplex) (p : ℤ) 0 (p : ℤ) (add_zero _)
    let g := (verticalAugmentation.{u,r,a,v} R c I).f p
    let g' := (verticalAugmentation.{u,r,max a b,v} R c I').f p
    let z := (A.localTuples (nativeCoefficient.{u,r,a} R F).val).hom.f p
    have hnat : g' ≫ d'.inv ≫ t ≫ (S).map d.hom = z ≫ (S).map g := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      change (d'.inv ≫ t ≫ (S).map d.hom) (g' s) = (S).map g (z s)
      refine (A.double_formula p 0 (g' s)).trans ?_
      have hz : z s = ULift.up (fun k ↦ (s k).down) :=
        A.localTuples_formula (nativeCoefficient.{u,r,a} R F).val p s
      change ULift.up (fun k ↦ (g' s k).down) = (S).map g (z s)
      rw [hz]
      change ULift.up (fun k ↦ (g' s k).down) = ULift.up (g (fun k ↦ (s k).down))
      rfl
    have hterm : g' ≫ d'.inv ≫ t = z ≫ (S).map g ≫ (S).map d.inv := by
      apply (cancel_mono ((S).map d.hom)).1
      simp only [assoc, hnat, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, comp_id]
    have hsource : (commonCochainIso.{a,u,r,v,b} R c (F := F) A e).hom.f p ≫ (S).map ((e.iso.hom.app F.val).f p) = z :=
      HomologicalComplex.congr_hom (commonCochainIso_hom_map R c e A) p
    simp only [comp_f, Functor.mapHomologicalComplex_map_f]
    erw [ambientVertical_f.{max a b,u,r,v} R c I' p]
    simp only [assoc]
    erw [A.total_formula (p : ℤ) 0 (p : ℤ) (add_zero _)]
    rw [hβ p]
    change (K'.extendXIso embedding (embed_nat p)).hom ≫ g' ≫ d'.inv ≫ t ≫ (S).map j =
      (commonIntCochainIso R c e A).hom.f (p : ℤ) ≫
        (S).map ((K.extendXIso embedding (embed_nat p)).hom ≫
          (e.iso.hom.app F.val).f p ≫ g ≫ d.inv ≫ j)
    simp only [CategoryTheory.Functor.map_comp, assoc]
    erw [reassoc_of% (commonIntCochainIso_f R c e A p), reassoc_of% hsource, reassoc_of% hterm]
  · exact (K'.isZero_extend_X embedding n (fun m hm => by rw [embed_nat] at hm; omega)).eq_of_src _ _

private lemma commonSourceIso_hom (n : ℕ) :
    (commonSourceIso.{a,u,r,v,b} R c (F := F) A e n).hom =
      (transportedHomology (S) (commonIntCochainIso R c e A) (n : ℤ)).hom ≫
        (S).map (sourceModel.{a,u,r,v} R c F n).hom := by
  let K := liftedRawCochainComplex.{a,u,r,v} R c F
  let K' := cochainComplex.{u,r,max a b,v} R c ((L).obj (nativeCoefficient.{u,r,a} R F)).val
  let k := commonCochainIso.{a,u,r,v,b} R c (F := F) A e
  let i := commonIntCochainIso R c e A
  have hi : i.hom ≫ ((S).mapHomologicalComplex (.up ℤ)).map (𝟙 _) ≫
        (mapExtendIso (S) K embedding).hom = 𝟙 _ ≫ extendMap k.hom embedding := by
    rw [CategoryTheory.Functor.map_id]
    simp only [commonIntCochainIso, i, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      id_comp, assoc]
    let j := mapExtendIso (S) K embedding
    change extendMap k.hom embedding ≫ j.inv ≫ j.hom = extendMap k.hom embedding
    rw [Iso.inv_hom_id, comp_id]
  have h := compareExtendedHomology (S) (Iso.refl (K'.extend embedding))
    (Iso.refl (K.extend embedding)) k.hom i.hom hi n
  simp only [Iso.refl_hom, homologyMap_id, id_comp,
    CategoryTheory.Functor.map_comp] at h
  erw [(S).map_id, id_comp] at h
  simp only [commonSourceIso, transportedHomology, sourceModel, Iso.trans_hom, Functor.mapIso_hom,
    homologyMapIso_hom, CategoryTheory.Functor.map_comp, assoc]
  erw [reassoc_of% h]

private lemma comparison_carrier (η : ∀ n,
    sourceCohomology.{a,u,r,v} R c n ⟶ originalSectionCohomology.{a,u,r,v} R c n)
    {β} (hβ : IsVerticalAugmentation R c e F I β) (hη : AgreesWithModel R c D e η F I β)
    (n : ℕ) :
    let I' := carrierLiftResolution.{u,r,a,b} R I
    homologyMap (verticalTotalAugmentationMap.{u,r,max a b,v} R c I') (n : ℤ) ≫
      (E.abutment I' n).hom ≫ (A.target n).hom =
      (commonSourceIso.{a,u,r,v,b} R c (F := F) A e n).hom ≫ (S).map ((η n).app F) := by
  let I' := carrierLiftResolution.{u,r,a,b} R I
  have h₁ := transportedHomology_natural (S) (commonIntCochainIso R c e A) A.total
    (verticalTotalAugmentationMap.{u,r,max a b,v} R c I') β (verticalTotal_carrier R c e A hβ)
    (n : ℤ)
  have h₂ := A.target_formula n
  have h₃ : (η n).app F = (sourceModel.{a,u,r,v} R c F n).inv ≫ homologyMap β (n : ℤ) ≫
      (D.abutment I n).hom := by
    rw [abutment_hom_formula R c D I n]
    exact hη.1 n
  dsimp only
  erw [← h₂, ← assoc, h₁, commonSourceIso_hom R c e A, h₃]
  simp only [assoc, ← (S).map_comp, Iso.hom_inv_id_assoc]

private lemma comparison_agreesAfterEnlargement (η : ∀ n,
    sourceCohomology.{a,u,r,v} R c n ⟶ originalSectionCohomology.{a,u,r,v} R c n)
    {β} (hβ : IsVerticalAugmentation R c e F I β) (hη : AgreesWithModel R c D e η F I β) :
    AgreesAfterEnlargement.{a,u,r,v,b} R c (F := F) A e η := by
  let I' := carrierLiftResolution.{u,r,a,b} R I
  refine ⟨verticalTotalAugmentationMap.{u,r,max a b,v} R c I',
    ambientVertical_f.{max a b,u,r,v} R c I', ?_⟩
  intro n
  have h := comparison_carrier R c e A η hβ hη n
  dsimp only at h
  erw [abutment_hom_formula.{max a b,u,r,v} R c E I' n] at h
  simpa only [assoc] using h

end CarrierComparison

section SectionComparisons

open Specs.AdvancedHomologicalAlgebra.SheafCohomology (resolutionModelMap)
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
  (sectionsValue mapAugmentation modelComparison)
open AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
  (ambientComparisonExact individualCohomologyIso individualCohomologyIso_normalized)

open private extendHomology_mapComparison
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients
open private ambientCohomologyIso individualCohomologyIso_hom_app flattenCoefficientLift
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients

open private sectionExtendComponent
  from MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

omit [EnoughInjectives (AmbientSheaves.{a} R)] in
private lemma sectionExtendIso_hom_eq (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    (sectionExtendIso.{u,r,a} R U K).hom =
      (mapExtendIso (sectionsValue.{a} R U) K ComplexShape.embeddingUpNat).hom := by
  let d := ComplexShape.embeddingUpNat
  apply HomologicalComplex.hom_ext
  intro q
  change (sectionExtendComponent.{u,r,a} R U K (d.r q)).hom =
    (mapExtendXIso (sectionsValue.{a} R U) K (d.r q)).hom
  cases d.r q <;> rfl

set_option quotPrecheck false in
set_option hygiene false in
local notation "L" => sheafCarrierLift.{u,r,a,b} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "H" => ModuleCat.uliftFunctor.{b,max a u r} (sectionRing R U)

variable [(L).PreservesHomology] [(L).PreservesInjectiveObjects]
  [EnoughInjectives (AmbientSheaves.{max a b} R)]

private lemma liftedAugmentation_extend {M : AmbientSheaves.{a} R} (I : InjectiveResolution M) :
    let I' := carrierLiftResolution.{u,r,a,b} R I
    mapAugmentation (L) I.ι' ≫ (mapExtendIso (L) I.cocomplex ComplexShape.embeddingUpNat).hom =
      I'.ι' := by
  let I' := carrierLiftResolution.{u,r,a,b} R I
  let d := ComplexShape.embeddingUpNat
  let j := mapExtendIso (L) I.cocomplex d
  let x := I.cochainComplexXIso 0 0 rfl
  let y := I'.cochainComplexXIso 0 0 rfl
  have hj : j.hom.f 0 ≫ y.hom = (L).map x.hom :=
    mapExtendIso_hom_f (L) I.cocomplex d (i := 0) (i' := 0) rfl
  apply from_single_hom_ext
  simp only [mapAugmentation, comp_f, Functor.mapHomologicalComplex_map_f, InjectiveResolution.ι'_f_zero]
  change ((singleMapHomologicalComplex (L) (.up ℤ) 0).inv.app M).f 0 ≫
      (L).map ((singleObjXSelf (.up ℤ) 0 M).hom ≫ I.ι.f 0 ≫ x.inv) ≫ j.hom.f 0 =
    (singleObjXSelf (.up ℤ) 0 ((L).obj M)).hom ≫ I'.ι.f 0 ≫ y.inv
  apply (cancel_mono y.hom).1
  simp only [singleMapHomologicalComplex_inv_app_self, assoc, hj, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, comp_id, Iso.inv_hom_id_assoc, I', carrierLiftResolution_ι_zero]

private lemma mapExtendIso_comp_hom
    {C B B' : Type*} [Category* C] [Category* B] [Category* B']
    [Abelian C] [Abelian B] [Abelian B'] (F : C ⥤ B) (G : B ⥤ B')
    [F.Additive] [G.Additive] (K : CochainComplex C ℕ) :
    let d := ComplexShape.embeddingUpNat
    (G.mapHomologicalComplex (.up ℤ)).map (mapExtendIso F K d).hom ≫
      (mapExtendIso G ((F.mapHomologicalComplex (.up ℕ)).obj K) d).hom =
      (mapExtendIso (F ⋙ G) K d).hom := by
  let d := ComplexShape.embeddingUpNat
  let K' := (F.mapHomologicalComplex (.up ℕ)).obj K
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : 0 ≤ n
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hp : d.f p = (p : ℤ) := rfl
    apply (cancel_mono ((((F ⋙ G).mapHomologicalComplex (.up ℕ)).obj K).extendXIso d hp).hom).1
    simp only [comp_f, Functor.mapHomologicalComplex_map_f, assoc]
    change G.map ((mapExtendIso F K d).hom.f (p : ℤ)) ≫
        (mapExtendIso G K' d).hom.f (p : ℤ) ≫
          (((G.mapHomologicalComplex (.up ℕ)).obj K').extendXIso d hp).hom =
      (mapExtendIso (F ⋙ G) K d).hom.f (p : ℤ) ≫
        ((((F ⋙ G).mapHomologicalComplex (.up ℕ)).obj K).extendXIso d hp).hom
    rw [mapExtendIso_hom_f G K' d hp, mapExtendIso_hom_f (F ⋙ G) K d hp,
      ← G.map_comp, mapExtendIso_hom_f F K d hp]
    rfl
  · exact (((F ⋙ G).mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X d n
      (fun p hp => by change (p : ℤ) = n at hp; omega) |>.eq_of_tgt _ _

/-- The section comparison in the spectral sequence uses the same augmented
models as the individually adequate derived section comparison. -/
private lemma sectionModelMap_carrier_normalized {M : AmbientSheaves.{a} R}
    (I : InjectiveResolution M) (n : ℕ) :
    let I' := carrierLiftResolution.{u,r,a,b} R I
    sectionModelMap.{u,r,max a b} R U I' n ≫
      (ambientCohomologyIso.{a,u,r,b} R U n).inv.app M =
      (((sectionComplex.{u,r,a} R U I.cocomplex).sc n).mapHomologyIso (H)).hom ≫
        (H).map (sectionModelMap.{u,r,a} R U I n) := by
  let F := sectionsValue.{a} R U
  let G := sectionsValue.{max a b} R U
  let I' := carrierLiftResolution.{u,r,a,b} R I
  let K := sectionComplex.{u,r,a} R U I.cocomplex
  let K' := sectionComplex.{u,r,max a b} R U I'.cocomplex
  let d := ComplexShape.embeddingUpNat
  let l := sectionExtendIso.{u,r,a} R U I.cocomplex
  let k := sectionExtendIso.{u,r,max a b} R U I'.cocomplex
  let j := mapExtendIso (L) I.cocomplex d
  let i := (G.mapHomologicalComplex (.up ℤ)).mapIso j.symm
  let C := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let θ := (C.sc (n : ℤ)).mapHomologyIso (H)
  let δ := (ambientCohomologyIso.{a,u,r,b} R U n).app M
  obtain ⟨hi, hmodel⟩ := (ambientComparisonExact.{a,u,r,b} R U).choose_spec.1
    M I.cochainComplex I.ι' inferInstance (fun q => inferInstance)
  have hn := hmodel n
  have hcomp : (modelComparison F G (L) (H)
      (Iso.refl (F ⋙ (H))) I.cochainComplex n).hom = θ.inv := by
    simp only [modelComparison, Iso.trans_hom, Iso.symm_hom,
      NatIso.mapHomologicalComplex, Iso.app_hom, Iso.refl_hom, NatTrans.mapHomologicalComplex_id,
      NatTrans.id_app, Functor.mapIso_hom, CategoryTheory.Functor.map_id]
    rfl
  change (H).map (resolutionModelMap F I.ι' inferInstance n) ≫ δ.hom =
    (modelComparison F G (L) (H) (Iso.refl (F ⋙ (H))) I.cochainComplex n).hom ≫
      resolutionModelMap G (mapAugmentation (L) I.ι') hi n at hn
  have hj := SheafCohomology.resolutionModelMap_naturality G
    (mapAugmentation (L) I.ι') hi I'.ι' inferInstance (𝟙 ((L).obj M)) j.hom (by
      rw [CategoryTheory.Functor.map_id, id_comp, liftedAugmentation_extend.{a,u,r,b} R I]) n
  rw [CategoryTheory.Functor.map_id, comp_id] at hj
  rw [hcomp, hj] at hn
  have hf : resolutionModelMap G I'.ι' inferInstance n ≫ δ.inv =
      (transportedHomology (H) i (n : ℤ)).hom ≫
        (H).map (resolutionModelMap F I.ι' inferInstance n) := by
    have hji : i.hom ≫ (G.mapHomologicalComplex (.up ℤ)).map j.hom = 𝟙 _ := by
      change (G.mapHomologicalComplex (.up ℤ)).map j.inv ≫
        (G.mapHomologicalComplex (.up ℤ)).map j.hom = _
      rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
    apply (cancel_mono δ.hom).1
    simp only [assoc, Iso.inv_hom_id, comp_id]
    erw [hn]
    change resolutionModelMap G I'.ι' inferInstance n =
      homologyMap i.hom (n : ℤ) ≫ θ.hom ≫ θ.inv ≫
        homologyMap ((G.mapHomologicalComplex (.up ℤ)).map j.hom) (n : ℤ) ≫
          resolutionModelMap G I'.ι' inferInstance n
    rw [Iso.hom_inv_id_assoc, ← homologyMap_comp_assoc, hji, homologyMap_id, id_comp]
  have hs : i.hom ≫ ((H).mapHomologicalComplex (.up ℤ)).map l.hom ≫
      (mapExtendIso (H) K d).hom = k.hom := by
    have h₁ := mapExtendIso_comp_hom F (H) I.cocomplex
    have h₂ := mapExtendIso_comp_hom (L) G I.cocomplex
    have hl : l.hom = (mapExtendIso F I.cocomplex d).hom :=
      sectionExtendIso_hom_eq.{a,u,r} R (U := U) I.cocomplex
    have hk : k.hom = (mapExtendIso G I'.cocomplex d).hom :=
      sectionExtendIso_hom_eq.{max a b,u,r} R (U := U) I'.cocomplex
    rw [hl, h₁]
    change i.hom ≫ (mapExtendIso (L ⋙ G) I.cocomplex d).hom = k.hom
    erw [← h₂, ← hk]
    change ((G.mapHomologicalComplex (.up ℤ)).map j.inv) ≫
      ((G.mapHomologicalComplex (.up ℤ)).map j.hom) ≫ k.hom = _
    rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, id_comp]
  let q := homologyMap l.hom (n : ℤ) ≫ (K.extendHomologyIso d (j := n) (j' := (n : ℤ)) rfl).hom
  let q' := homologyMap k.hom (n : ℤ) ≫ (K'.extendHomologyIso d (j := n) (j' := (n : ℤ)) rfl).hom
  have hq : (transportedHomology (H) i (n : ℤ)).hom ≫ (H).map q =
      q' ≫ ((K.sc n).mapHomologyIso (H)).hom := by
    have hh := congrArg (fun z => homologyMap z (n : ℤ)) hs
    simp only [homologyMap_comp] at hh
    have hnat := ShortComplex.mapHomologyIso_hom_naturality
      ((shortComplexFunctor _ (.up ℤ) (n : ℤ)).map l.hom) (H)
    change homologyMap (((H).mapHomologicalComplex (.up ℤ)).map l.hom) (n : ℤ) ≫
      (((K.extend d).sc (n : ℤ)).mapHomologyIso (H)).hom =
      θ.hom ≫ (H).map (homologyMap l.hom (n : ℤ)) at hnat
    simp only [transportedHomology, Iso.trans_hom, homologyMapIso_hom, q, q', CategoryTheory.Functor.map_comp, assoc]
    erw [← reassoc_of% hnat, ← extendHomology_mapComparison (H) K n,
      ← reassoc_of% hh]
    rfl
  have hk : q' ≫ sectionModelMap.{u,r,max a b} R U I' n =
      resolutionModelMap G I'.ι' inferInstance n := by
    let j' := K'.extendHomologyIso d (j := n) (j' := (n : ℤ)) rfl
    change (homologyMap k.hom (n : ℤ) ≫ j'.hom) ≫ j'.inv ≫
      homologyMap k.inv (n : ℤ) ≫ resolutionModelMap G I'.ι' inferInstance n = _
    simp only [assoc, Iso.hom_inv_id_assoc, ← homologyMap_comp_assoc, Iso.hom_inv_id,
      homologyMap_id, id_comp]
  have hl : q ≫ sectionModelMap.{u,r,a} R U I n =
      resolutionModelMap F I.ι' inferInstance n := by
    let jne := K.extendHomologyIso d (j := n) (j' := (n : ℤ)) rfl
    change (homologyMap l.hom (n : ℤ) ≫ jne.hom) ≫ jne.inv ≫
      homologyMap l.inv (n : ℤ) ≫ resolutionModelMap F I.ι' inferInstance n = _
    simp only [assoc, Iso.hom_inv_id_assoc, ← homologyMap_comp_assoc, Iso.hom_inv_id,
      homologyMap_id, id_comp]
  apply (cancel_epi q').1
  change q' ≫ sectionModelMap.{u,r,max a b} R U I' n ≫ δ.inv = _
  rw [← assoc, hk, hf, ← hl, CategoryTheory.Functor.map_comp, ← reassoc_of% hq]

set_option quotPrecheck false in
set_option hygiene false in
local notation "P" => presheafCarrierLift.{u,r,a,b} R

private lemma sectionComparison_individual [(P).PreservesHomology]
    {D : NaturalityData.{u,r,a,v} R c} {E : NaturalityData.{u,r,max a b,v} R c}
    {F : SheafOfModules.{a} R} {I : InjectiveResolution (nativeCoefficient.{u,r,a} R F)}
    (A : CarrierModelComparison.{u,r,a,v,b} R c D E I) (n : ℕ) :
    (A.sectionComparison U n).inv ≫
      (cohomologyValue.{max a b,u,r} R U n).map (flattenNativeCoefficient.{u,r,a,b} R F).hom =
      (individualCohomologyIso.{b,u,r,a} X R U n).hom.app F := by
  let I' := carrierLiftResolution.{u,r,a,b} R I
  let M := nativeCoefficient.{u,r,a} R F
  let Q := cohomologyValue.{max a b,u,r} R U n
  let t := sectionModelMap.{u,r,max a b} R U I' n
  let _ : IsIso t := inferInstanceAs (IsIso (sectionModelMap.{u,r,max a b} R U I' n))
  have h : (A.sectionComparison U n).hom =
      (ambientCohomologyIso.{a,u,r,b} R U n).inv.app M := by
    apply (cancel_epi t).1
    exact (A.section_model U n).trans (sectionModelMap_carrier_normalized.{a,u,r,b} R I n).symm
  have hi : (A.sectionComparison U n).inv = (ambientCohomologyIso.{a,u,r,b} R U n).hom.app M := by
    have he : A.sectionComparison U n = ((ambientCohomologyIso.{a,u,r,b} R U n).app M).symm := Iso.ext h
    exact congrArg Iso.inv he
  let fl := (flattenNativeCoefficient.{u,r,a,b} R F).hom
  let fl' := (flattenCoefficientLift.{u,r,b,a,max u r} R).hom.app F
  have hfl : fl = fl' := by
    apply SheafOfModules.hom_ext
    ext V x
    rfl
  calc
    _ = (ambientCohomologyIso.{a,u,r,b} R U n).hom.app M ≫ Q.map fl :=
      congrArg (fun g => g ≫ Q.map fl) hi
    _ = (ambientCohomologyIso.{a,u,r,b} R U n).hom.app M ≫ Q.map fl' :=
      congrArg (fun g => (ambientCohomologyIso.{a,u,r,b} R U n).hom.app M ≫ Q.map g) hfl
    _ = _ := (individualCohomologyIso_hom_app.{b,u,r,a} R U F n).symm

end SectionComparisons

section MixedNaturality

open AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
  (individualCohomologyIso individualCohomologyIso_normalized)
open private sheafCarrierPreservesInjectives conjugate_comm
  from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

private def unliftTwice {K : Type*} [Ring K] {M N : Type*}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : ULift.{w₁} (ULift.{w₂} M) →ₗ[K] ULift.{w₃} (ULift.{w₄} N)) : M →ₗ[K] N :=
  (ULift.moduleEquiv.toLinearMap.comp ULift.moduleEquiv.toLinearMap).comp
    (f.comp (ULift.moduleEquiv.symm.toLinearMap.comp ULift.moduleEquiv.symm.toLinearMap))

set_option maxHeartbeats 5000000 in
/-- The native Čech comparison is natural for the given sectionwise maps
even when the coefficient carriers lie in different universes. -/
theorem acyclic_cover_comparison_mixed :
    Specs.AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients.mixedComparisonType.{a,u,r,v,b} := by
  intro X R U T c _ _ _
  refine ⟨sheafCarrierPreservesInjectives.{u,r,a,b} R, sheafCarrierPreservesInjectives.{u,r,b,a} R,
    inferInstance, inferInstance, inferInstance, inferInstance,
    coefficientNaturalityData.{u,r,a,v} R c, coefficientNaturalityData.{u,r,b,v} R c,
    coefficientNaturalityData.{u,r,max a b,v} R c, ?_⟩
  intro F G f I J e₁ e₂ η₁ η₂ β₁ β₂ hβ₁ hη₁ hβ₂ hη₂
  let A₁ := carrierModelComparison.{u,r,a,v,b} R c I
  let A₂ := carrierModelComparison.{u,r,b,v,a} R c J
  let I' := carrierLiftResolution.{u,r,a,b} R I
  let J' := carrierLiftResolution.{u,r,b,a} R J
  let f' := mixedCoefficientMap.{u,r,a,b} R f
  let k := cochainMap.{u,r,max a b,v} R c f'.val
  let S₁ := cochainCarrierLift.{u,r,a,v,b} R c
  let S₂ := cochainCarrierLift.{u,r,b,v,a} R c
  let j₁ := individualCohomologyIso.{b,u,r,a} X R U
  let j₂ := individualCohomologyIso.{a,u,r,b} X R U
  let i₁ := commonCochainIso.{a,u,r,v,b} R c (F := F) A₁ e₁
  let i₂ := commonCochainIso.{b,u,r,v,a} R c (F := G) A₂ e₂
  let Q₁ := commonSourceIso.{a,u,r,v,b} R c (F := F) A₁ e₁
  let Q₂ := commonSourceIso.{b,u,r,v,a} R c (F := G) A₂ e₂
  let H n := cohomologyValue.{max a b,u,r} R U n
  let d n := (sectionLift.{u,r,max a b,v} R c).map ((H n).map f')
  let source n := (Q₁ n).inv ≫ homologyMap (extendMap k embedding) (n : ℤ) ≫ (Q₂ n).hom
  let target n := (A₁.target n).inv ≫ d n ≫ (A₂.target n).hom
  let g (n : ℕ) : ((rawComplexFunctor.{a,u,r,v} R c).obj F).homology n →ₗ[sectionRing R U]
      ((rawComplexFunctor.{b,u,r,v} R c).obj G).homology n := unliftTwice (source n).hom
  let h (n : ℕ) : (coefficientCohomologyValue.{a,u,r} X R U n).obj F →ₗ[sectionRing R U]
      (coefficientCohomologyValue.{b,u,r} X R U n).obj G := unliftTwice (target n).hom
  refine ⟨A₁, A₂, j₁, j₂, g, h,
    comparison_agreesAfterEnlargement.{a,u,r,v,b} R c e₁ (F := F) A₁ η₁ hβ₁ hη₁,
    comparison_agreesAfterEnlargement.{b,u,r,v,a} R c e₂ (F := G) A₂ η₂ hβ₂ hη₂,
    individualCohomologyIso_normalized.{b,u,r,a} X R U,
    individualCohomologyIso_normalized.{a,u,r,b} X R U, ?_, ?_, ?_, ?_, ?_⟩
  · intro p s
    let s' : Cochains R ((sheafCarrierLift.{u,r,a,b} R).obj (nativeCoefficient.{u,r,a} R F)).val c p :=
      fun t => ULift.up (ULift.up (s t))
    have hi : i₁.hom.f p s' = ULift.up (ULift.up s) :=
      commonCochainIso_coordinate.{a,u,r,v,b} R c e₁ (F := F) A₁ p s
    have he : i₁.hom.f p ≫ i₁.inv.f p = 𝟙 _ := HomologicalComplex.congr_hom i₁.hom_inv_id p
    have hi' : i₁.inv.f p (ULift.up (ULift.up s)) = s' :=
      (congrArg (fun x => i₁.inv.f p x) hi.symm).trans (congrArg (fun m => m s') he)
    change i₂.hom.f p (k.f p (i₁.inv.f p (ULift.up (ULift.up s)))) = _
    rw [hi']
    exact commonCochainIso_coordinate.{b,u,r,v,a} R c e₂ (F := G) A₂ p
      (fun t ↦ f.app (op (tupleOpen c t)) (s t))
  · intro n x
    rfl
  · intro n x
    let x' := (A₁.sectionComparison U n).inv (ULift.up x)
    let y' := (H n).map f' x'
    let fl₁ := (flattenNativeCoefficient.{u,r,a,b} R F).hom
    let fl₂ := (flattenNativeCoefficient.{u,r,b,a} R G).hom
    have h₁ := sectionComparison_individual.{a,u,r,v,b} R c (F := F) A₁ n
    have h₂ := sectionComparison_individual.{b,u,r,v,a} R c (F := G) A₂ n
    have hx : (A₁.target n).inv (ULift.up (ULift.up x)) = ULift.up x' := by
      apply (ModuleCat.mono_iff_injective (A₁.target n).hom).1 inferInstance
      have hx' : (A₁.sectionComparison U n).hom x' = ULift.up x :=
        congrArg (fun m => m (ULift.up x)) (A₁.sectionComparison U n).inv_hom_id
      exact (congrArg (fun m => m (ULift.up (ULift.up x))) (A₁.target n).inv_hom_id).trans
        (((A₁.target_sections n x').trans
          (congrArg (fun y => ULift.up (ULift.up y.down)) hx')).symm)
    have hy : ULift.up (h n x) = (A₂.sectionComparison U n).hom y' := by
      have ht : target n (ULift.up (ULift.up x)) = (A₂.target n).hom (ULift.up y') :=
        congrArg (fun y => (A₂.target n).hom (d n y)) hx
      exact (congrArg (fun z => ULift.up z.down.down) ht).trans
        (congrArg (fun z => ULift.up z.down.down) (A₂.target_sections n y'))
    have hf : fl₁ ≫ f.lift.{max u r} = f' ≫ fl₂ := by
      simp only [f', mixedCoefficientMap, fl₁, fl₂, assoc, Iso.inv_hom_id, comp_id]
    have hx₁ : (j₁ n).hom.app F (ULift.up x) = (H n).map fl₁ x' :=
      congrArg (fun m => m (ULift.up x)) h₁.symm
    have hy₂ : (j₂ n).hom.app G (ULift.up (h n x)) = (H n).map fl₂ y' := by
      calc
        _ = (j₂ n).hom.app G ((A₂.sectionComparison U n).hom y') :=
          congrArg ((j₂ n).hom.app G) hy
        _ = (H n).map fl₂ y' := by
          have hi := (A₂.sectionComparison U n).hom_inv_id
          have he : (A₂.sectionComparison U n).inv ((A₂.sectionComparison U n).hom y') = y' :=
            congrArg (fun m => m y') hi
          exact (congrArg (fun m => m ((A₂.sectionComparison U n).hom y')) h₂.symm).trans
            (congrArg ((H n).map fl₂) he)
    change (H n).map f.lift.{max u r} ((j₁ n).hom.app F (ULift.up x)) =
      (j₂ n).hom.app G (ULift.up (h n x))
    rw [hx₁, hy₂]
    have hmap := congrArg (H n).map hf
    simp only [CategoryTheory.Functor.map_comp] at hmap
    exact congrArg (fun m => m x') hmap
  · intro n x
    rfl
  · intro n x
    have h₁ := comparison_carrier.{a,u,r,v,b} R c e₁ (F := F) A₁ η₁ hβ₁ hη₁ n
    have h₂ := comparison_carrier.{b,u,r,v,a} R c e₂ (F := G) A₂ η₂ hβ₂ hη₂ n
    have hn := ambientComparison_naturality.{max a b,u,r,v} R c
      (coefficientNaturalityData.{u,r,max a b,v} R c) f' I' J' n
    let E := coefficientNaturalityData.{u,r,max a b,v} R c
    have hsq : source n ≫ S₂.map ((η₂ n).app G) = S₁.map ((η₁ n).app F) ≫ target n :=
      conjugate_comm (Q₁ n) (Q₂ n) (A₁.target n) (A₂.target n)
        (homologyMap (extendMap k embedding) (n : ℤ)) (d n)
        (homologyMap (verticalTotalAugmentationMap.{u,r,max a b,v} R c I') (n : ℤ) ≫ (E.abutment I' n).hom)
        (homologyMap (verticalTotalAugmentationMap.{u,r,max a b,v} R c J') (n : ℤ) ≫ (E.abutment J' n).hom)
        (S₁.map ((η₁ n).app F)) (S₂.map ((η₂ n).app G))
        (by simpa only [assoc] using h₁.symm) (by simpa only [assoc] using h₂.symm)
        (by simpa only [assoc] using hn)
    exact congrArg (fun m => (m (ULift.up (ULift.up x))).down.down) hsq

end MixedNaturality

end AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients
