import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.LeftGrothendieckSpectralSequence
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ClassicalDerivedValues
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AcyclicTermComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.GrothendieckEdges
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.CategoryTheory.Localization.Opposite
import Batteries.Tactic.OpenPrivate

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open Specs.AdvancedHomologicalAlgebra.BoundedDerivedModels
open Specs.AdvancedHomologicalAlgebra.TotalDerivedUniversalProperty
open Specs.AdvancedHomologicalAlgebra.TotalLeftDerivedFunctor
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison
open CategoryTheory.Abelian

namespace AdvancedHomologicalAlgebra.LeftGrothendieckSpectralSequence

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

section Duality
universe u v w
variable (A : Type u) [Category.{v} A] [Abelian A]

abbrev cochainDual : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex Aᵒᵖ ℤ :=
  (CochainComplex.opEquivalence A).functor

/-- Reversal of cochain degrees and arrows, before imposing bounds. -/
def homotopyDual :
    (HomotopyCategory A (.up ℤ))ᵒᵖ ⥤ HomotopyCategory Aᵒᵖ (.up ℤ) where
  obj X := (HomotopyCategory.quotient _ _).obj ((cochainDual A).obj (op X.unop.as))
  map f := (HomotopyCategory.quotient _ _).map ((cochainDual A).map f.unop.out.op)
  map_id X := by
    change (HomotopyCategory.quotient _ _).map ((cochainDual A).map (Quot.out (𝟙 X.unop)).op) = _
    rw [← (HomotopyCategory.quotient _ _).map_id, ← (cochainDual A).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply CochainComplex.homotopyOp
    apply HomotopyCategory.homotopyOfEq
    rw [HomotopyCategory.quotient_map_out]
    exact ((HomotopyCategory.quotient A (.up ℤ)).map_id X.unop.as).symm
  map_comp f g := by
    change (HomotopyCategory.quotient _ _).map
        ((cochainDual A).map (Quot.out (g.unop ≫ f.unop)).op) = _
    rw [← (HomotopyCategory.quotient _ _).map_comp, ← (cochainDual A).map_comp, ← op_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply CochainComplex.homotopyOp
    apply HomotopyCategory.homotopyOfEq
    simp

lemma homotopyDual_map_quotient {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    (homotopyDual A).map ((HomotopyCategory.quotient _ _).map f).op =
      (HomotopyCategory.quotient _ _).map ((cochainDual A).map f.op) := by
  apply HomotopyCategory.eq_of_homotopy
  exact CochainComplex.homotopyOp (HomotopyCategory.homotopyOutMap f)

/-- The source bound b becomes the lower bound -b in the dual. -/
def boundedHomotopyDual : (KMinus A)ᵒᵖ ⥤ HomotopyCategory.Plus Aᵒᵖ :=
  (HomotopyCategory.plus Aᵒᵖ).lift ((minusInclusion A).op ⋙ homotopyDual A) (by
    intro (X : (KMinus A)ᵒᵖ)
    obtain ⟨b, hb⟩ := X.unop.property
    change HomotopyCategory.plus Aᵒᵖ
      ((HomotopyCategory.quotient _ _).obj ((cochainDual A).obj (op X.unop.obj.as)))
    apply (HomotopyCategory.plus_quotient_obj_iff _).mpr
    change ∃ n : ℤ, ((cochainDual A).obj (op X.unop.obj.as)).IsStrictlyGE n
    refine ⟨-b, ?_⟩
    refine (CochainComplex.isStrictlyGE_iff _ _).mpr fun j hj => ?_
    have hz := (CochainComplex.isStrictlyLE_iff _ _).mp hb (-j) (by omega)
    exact hz.op)

private abbrev revShape : (ComplexShape.up ℤ).Embedding (ComplexShape.up ℤ).symm := ComplexShape.embeddingUpIntDownInt

private def reindexedHomology (K : HomologicalComplex A (ComplexShape.up ℤ).symm) (n : ℤ) :
    (K.restriction revShape).homology n ≅ K.homology (-n) :=
  K.restrictionHomologyIso revShape
    (n-1) n (n+1) (by simp) (by simp) rfl rfl rfl
    (ComplexShape.prev_eq' _ (by change -n + 1 = -(n-1); omega))
    (ComplexShape.next_eq' _ (by change -(n+1) + 1 = -n; omega))

private def reindexedHomologyNatIso (n : ℤ) :
    revShape.restrictionFunctor A ⋙ HomologicalComplex.homologyFunctor A (.up ℤ) n ≅
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ).symm (-n) := by
  refine NatIso.ofComponents (fun K => reindexedHomology A K n) ?_
  intro K L f
  change HomologicalComplex.homologyMap (HomologicalComplex.restrictionMap f revShape) n ≫
      (reindexedHomology A L n).hom =
    (reindexedHomology A K n).hom ≫ HomologicalComplex.homologyMap f (-n)
  rw [← cancel_epi ((K.restriction revShape).homologyπ n)]
  simp only [reindexedHomology, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_restrictionHomologyIso_hom_assoc,
    HomologicalComplex.homologyπ_restrictionHomologyIso_hom]
  let Lc := (L.restrictionCyclesIso revShape n (n+1) (by simp)
    (show revShape.f n = -n from rfl) (show revShape.f (n+1) = -(n+1) from rfl)
    (ComplexShape.next_eq' _ (by change -(n+1) + 1 = -n; omega))).hom
  let Kc := (K.restrictionCyclesIso revShape n (n+1) (by simp)
    (show revShape.f n = -n from rfl) (show revShape.f (n+1) = -(n+1) from rfl)
    (ComplexShape.next_eq' _ (by change -(n+1) + 1 = -n; omega))).hom
  change HomologicalComplex.cyclesMap (HomologicalComplex.restrictionMap f revShape) n ≫
      Lc ≫ L.homologyπ (-n) = Kc ≫ K.homologyπ (-n) ≫ HomologicalComplex.homologyMap f (-n)
  rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc, ← Category.assoc]
  apply congrArg (fun t => t ≫ L.homologyπ (-n))
  rw [← cancel_mono (L.iCycles (-n))]
  simp only [Lc, Kc, Category.assoc, HomologicalComplex.restrictionCyclesIso_hom_iCycles,
    HomologicalComplex.restrictionCyclesIso_hom_iCycles_assoc,
    HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i_assoc]
  simp [HomologicalComplex.restrictionMap, HomologicalComplex.restrictionXIso, revShape]


def cochainHomologyDual (n : ℤ) :
    cochainDual A ⋙ HomologicalComplex.homologyFunctor Aᵒᵖ (.up ℤ) n ≅
      (HomologicalComplex.homologyFunctor A (.up ℤ) (-n)).op :=
  associator _ _ _ ≪≫
    isoWhiskerLeft (HomologicalComplex.opFunctor A (.up ℤ)) (reindexedHomologyNatIso Aᵒᵖ n) ≪≫
    HomologicalComplex.homologyOpNatIso A (.up ℤ) (-n)

abbrev minusHomotopyHomology (n : ℤ) : KMinus A ⥤ A :=
  minusInclusion A ⋙ HomotopyCategory.homologyFunctor A (.up ℤ) n

def boundedHomotopyHomologyDual (n : ℤ) :
    boundedHomotopyDual A ⋙ HomotopyCategory.Plus.ι Aᵒᵖ ⋙
      HomotopyCategory.homologyFunctor Aᵒᵖ (.up ℤ) n ≅
      (minusHomotopyHomology A (-n)).op := by
  let e := cochainHomologyDual A n
  let e₁ := HomotopyCategory.homologyFunctorFactors A (.up ℤ) (-n)
  let e₂ := HomotopyCategory.homologyFunctorFactors Aᵒᵖ (.up ℤ) n
  refine NatIso.ofComponents
    (fun K => e₂.app ((cochainDual A).obj (op K.unop.obj.as)) ≪≫
      e.app (op K.unop.obj.as) ≪≫ (e₁.app K.unop.obj.as).op) ?_
  intro K L f
  let g := f.unop.hom.out
  have hg : (HomotopyCategory.quotient A (.up ℤ)).map g = f.unop.hom :=
    HomotopyCategory.quotient_map_out _
  change (HomotopyCategory.homologyFunctor Aᵒᵖ (.up ℤ) n).map
      ((HomotopyCategory.quotient _ _).map ((cochainDual A).map g.op)) ≫ _ =
      _ ≫ ((HomotopyCategory.homologyFunctor A (.up ℤ) (-n)).map f.unop.hom).op
  rw [← hg]
  simp only [Iso.trans_hom, Iso.op_hom, Category.assoc]
  erw [e₂.hom.naturality_assoc, e.hom.naturality_assoc]
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  have h₁ := e₁.hom.naturality g
  dsimp only [Functor.comp_map] at h₁
  erw [← h₁]
  rfl

lemma boundedHomotopyDual_quasiIso {X Y : (KMinus A)ᵒᵖ} (f : X ⟶ Y) (hf : WMinus A f.unop) :
    HomotopyCategory.Plus.quasiIso Aᵒᵖ ((boundedHomotopyDual A).map f) := by
  intro n
  have h : IsIso (((minusHomotopyHomology A (-n)).op).map f) := by
    haveI : IsIso ((minusHomotopyHomology A (-n)).map f.unop) := hf (-n)
    exact isIso_op (((minusHomotopyHomology A (-n)).map f.unop))
  exact (NatIso.isIso_map_iff (boundedHomotopyHomologyDual A n) f).mpr h

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{max u v} Aᵒᵖ]

lemma derivedDual_inverts :
    (WMinus A).op.IsInvertedBy (boundedHomotopyDual A ⋙ DerivedCategory.Plus.Qh) :=
  fun _ _ f hf => Localization.inverts (DerivedCategory.Plus.Qh (C := Aᵒᵖ)) (HomotopyCategory.Plus.quasiIso Aᵒᵖ) _
    (boundedHomotopyDual_quasiIso A f hf)

variable [(QMinus A).IsLocalization (WMinus A)]

/-- Duality on the bounded derived category, obtained by localization. -/
def derivedDual : (DerivedCategory.Minus A)ᵒᵖ ⥤ DerivedCategory.Plus Aᵒᵖ :=
  Localization.lift _ (derivedDual_inverts A) (QMinus A).op

def derivedDualFactors :
    (QMinus A).op ⋙ derivedDual A ≅ boundedHomotopyDual A ⋙ DerivedCategory.Plus.Qh :=
  Localization.fac _ (derivedDual_inverts A) (QMinus A).op

def derivedHomologyDual (n : ℤ) :
    derivedDual A ⋙ DerivedCategory.Plus.homologyFunctor Aᵒᵖ n ≅
      (DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor A (-n)).op := by
  let Q := (QMinus A).op
  let W := (WMinus A).op
  let H₁ := derivedDual A ⋙ DerivedCategory.Plus.homologyFunctor Aᵒᵖ n
  let H₂ := (DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor A (-n)).op
  refine Localization.liftNatIso Q W (Q ⋙ H₁) (Q ⋙ H₂) H₁ H₂ ?_
  exact (associator _ _ _).symm ≪≫
    isoWhiskerRight (derivedDualFactors A) _ ≪≫ (associator _ _ _ ) ≪≫
    isoWhiskerLeft (boundedHomotopyDual A)
      (isoWhiskerRight (DerivedCategory.Plus.QhCompιIsoιCompQh Aᵒᵖ) _ ≪≫
        (associator _ _ _) ≪≫
        isoWhiskerLeft (HomotopyCategory.Plus.ι Aᵒᵖ) (DerivedCategory.homologyFunctorFactorsh Aᵒᵖ n)) ≪≫
    boundedHomotopyHomologyDual A n ≪≫
    NatIso.op (isoWhiskerLeft (minusInclusion A) (DerivedCategory.homologyFunctorFactorsh A (-n)))

private lemma homologyOp_via_sc'
    (K : CochainComplex A ℤ) (i j k : ℤ)
    (hi : (ComplexShape.up ℤ).prev j = i) (hk : (ComplexShape.up ℤ).next j = k) :
    (K.homologyOp j).hom =
      (K.op.homologyIsoSc' k j i hk hi).hom ≫
      (K.sc' i j k).homologyOpIso.hom ≫
      (K.homologyIsoSc' i j k hi hk).hom.op := by
  subst i k
  have he : ((K.op).homologyIsoSc' ((ComplexShape.up ℤ).next j) j
      ((ComplexShape.up ℤ).prev j) rfl rfl).hom = 𝟙 _ := by
    change ShortComplex.homologyMap (𝟙 (K.op.sc j)) = _
    exact ShortComplex.homologyMap_id _
  simp [HomologicalComplex.homologyOp, he]
  rfl

private lemma cochainHomologyDual_eq (K : CochainComplex A ℤ) (n : ℤ) :
    (cochainHomologyDual A n).hom.app (op K) = (reversedHomology A K n).hom := by
  have hi : (ComplexShape.up ℤ).prev (-n) = -(n + 1) := by simp; omega
  have hk : (ComplexShape.up ℤ).next (-n) = -(n - 1) := by simp; omega
  simp only [cochainHomologyDual, Iso.trans_hom, NatTrans.comp_app, associator_hom_app,
    Category.id_comp, isoWhiskerLeft_hom, whiskerLeft_app]
  erw [Category.id_comp]
  change (reindexedHomology Aᵒᵖ K.op n).hom ≫ (K.homologyOp (-n)).hom = _
  rw [homologyOp_via_sc' A K (-(n + 1)) (-n) (-(n - 1)) hi hk]
  simp only [reindexedHomology, HomologicalComplex.restrictionHomologyIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  unfold reversedHomology
  simp only [Iso.trans_hom, Iso.op_hom, Category.assoc]
  rfl

/-- The localization comparison on the reversed cochain complex. -/
def derivedDualLocalized (K : KMinus A) :
    (derivedDual A).obj (op ((QMinus A).obj K)) ≅
      DerivedCategory.Plus.Q.obj (reversedBounded A K) :=
  (derivedDualFactors A).app (op K) ≪≫
    (DerivedCategory.Plus.quotientCompQhIso Aᵒᵖ).app (reversedBounded A K)

lemma derivedDualLocalized_naturality (K L : KMinus A) (f : K.obj.as ⟶ L.obj.as) :
    let m : K ⟶ L := ObjectProperty.homMk ((HomotopyCategory.quotient A (.up ℤ)).map f)
    let fm : reversedBounded A L ⟶ reversedBounded A K :=
      ObjectProperty.homMk ((cochainDual A).map f.op)
    (derivedDual A).map ((QMinus A).map m).op ≫ (derivedDualLocalized A K).hom =
      (derivedDualLocalized A L).hom ≫ DerivedCategory.Plus.Q.map fm := by
  dsimp only
  rw [derivedDualLocalized, derivedDualLocalized, Iso.trans_hom, Iso.trans_hom,
    ← Category.assoc]
  let m : K ⟶ L := ObjectProperty.homMk ((HomotopyCategory.quotient A (.up ℤ)).map f)
  erw [show (derivedDual A).map ((QMinus A).map m).op ≫
        (derivedDualFactors A).hom.app (op K) = _ from
      (derivedDualFactors A).hom.naturality m.op, Category.assoc]
  have h : (boundedHomotopyDual A).map m.op =
      (HomotopyCategory.Plus.quotient Aᵒᵖ).map
        (show reversedBounded A L ⟶ reversedBounded A K from
          ObjectProperty.homMk ((cochainDual A).map f.op)) := by
    ext : 1
    exact homotopyDual_map_quotient A f
  change (derivedDualFactors A).hom.app (op L) ≫
      DerivedCategory.Plus.Qh.map ((boundedHomotopyDual A).map m.op) ≫ _ = _
  rw [h, Category.assoc]
  exact congrArg (fun t => (derivedDualFactors A).hom.app (op L) ≫ t)
    ((DerivedCategory.Plus.quotientCompQhIso Aᵒᵖ).hom.naturality
      (show reversedBounded A L ⟶ reversedBounded A K from
        ObjectProperty.homMk ((cochainDual A).map f.op)))

private lemma derivedDualHomology_normalized (K : KMinus A) (n : ℤ) :
    (derivedHomologyDual A n).hom.app (op ((QMinus A).obj K)) =
      (DerivedCategory.Plus.homologyFunctor Aᵒᵖ n).map (derivedDualLocalized A K).hom ≫
      (DerivedCategory.homologyFunctorFactors Aᵒᵖ n).hom.app (reversedBounded A K).obj ≫
      (reversedHomology A K.obj.as n).hom ≫
      (derivedHomologyOnModel A K n).hom.op := by
  dsimp only [derivedHomologyDual, Localization.liftNatIso_hom]
  erw [Localization.liftNatTrans_app]
  dsimp only [Localization.Lifting.compLeft, Localization.Lifting.iso, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Iso.trans_hom, NatTrans.comp_app, associator_hom_app, associator_inv_app,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Iso.symm_hom, boundedHomotopyHomologyDual, NatIso.ofComponents_hom_app, Iso.app_hom]
  simp only [Category.comp_id, Category.id_comp, Category.assoc, NatIso.op_hom, NatTrans.op_app,
    isoWhiskerLeft_inv, whiskerLeft_app, Iso.op_hom]
  rw [cochainHomologyDual_eq]
  simp only [derivedDualLocalized, derivedHomologyOnModel, Iso.trans_hom, Functor.map_comp,
    NatIso.op_hom, NatTrans.op_app, Iso.op_hom, op_comp, Category.assoc]
  let J := reversedComplex A K.obj.as
  have hleft :
      (DerivedCategory.homologyFunctor Aᵒᵖ n).map
        ((DerivedCategory.Plus.QhCompιIsoιCompQh Aᵒᵖ).hom.app
          ((boundedHomotopyDual A).obj (op K))) ≫
        (DerivedCategory.homologyFunctorFactorsh Aᵒᵖ n).hom.app
          ((HomotopyCategory.Plus.ι Aᵒᵖ).obj ((boundedHomotopyDual A).obj (op K))) ≫
        (HomotopyCategory.homologyFunctorFactors Aᵒᵖ (.up ℤ) n).hom.app J =
      (DerivedCategory.Plus.homologyFunctor Aᵒᵖ n).map
        ((DerivedCategory.Plus.quotientCompQhIso Aᵒᵖ).app (reversedBounded A K)).hom ≫
        (DerivedCategory.homologyFunctorFactors Aᵒᵖ n).hom.app J := by
    change (DerivedCategory.homologyFunctor Aᵒᵖ n).map (𝟙 _) ≫
        (DerivedCategory.homologyFunctorFactorsh Aᵒᵖ n).hom.app
          ((HomotopyCategory.quotient _ _).obj J) ≫ _ =
      (DerivedCategory.homologyFunctor Aᵒᵖ n).map
        ((DerivedCategory.quotientCompQhIso Aᵒᵖ).hom.app J) ≫ _
    simp [DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj, Category.assoc]
  have hright :
      ((HomotopyCategory.homologyFunctorFactors A (.up ℤ) (-n)).app K.obj.as).hom.op ≫
        (((minusInclusion A).isoWhiskerLeft
          (DerivedCategory.homologyFunctorFactorsh A (-n))).hom.app K).op =
      ((DerivedCategory.homologyFunctorFactors A (-n)).app K.obj.as).hom.op ≫
        ((DerivedCategory.homologyFunctor A (-n)).mapIso
          ((DerivedCategory.quotientCompQhIso A).symm.app K.obj.as)).hom.op := by
    apply Quiver.Hom.unop_inj
    change (DerivedCategory.homologyFunctorFactorsh A (-n)).hom.app K.obj ≫
        (HomotopyCategory.homologyFunctorFactors A (.up ℤ) (-n)).hom.app K.obj.as =
      (DerivedCategory.homologyFunctor A (-n)).map
        ((DerivedCategory.quotientCompQhIso A).inv.app K.obj.as) ≫
        (DerivedCategory.homologyFunctorFactors A (-n)).hom.app K.obj.as
    have he : (DerivedCategory.quotientCompQhIso A).inv.app K.obj.as =
        (DerivedCategory.quotientCompQhIso A).hom.app K.obj.as := rfl
    erw [DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj A K.obj.as (-n), he]
    simp
  rw [hright]
  have h := congrArg (fun f => f ≫ (reversedHomology A K.obj.as n).hom ≫
      ((DerivedCategory.homologyFunctorFactors A (-n)).app K.obj.as).hom.op ≫
        ((DerivedCategory.homologyFunctor A (-n)).mapIso
          ((DerivedCategory.quotientCompQhIso A).symm.app K.obj.as)).hom.op) hleft
  have h' := congrArg (fun f => (DerivedCategory.Plus.homologyFunctor Aᵒᵖ n).map
      ((derivedDualFactors A).hom.app (op K)) ≫ f) h
  simp only [Iso.app_hom, Category.assoc] at h'
  exact h'
end Duality
section LeftDerivedDual
universe u₁ v₁ u₂ v₂ w₁ w₂
variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]

/-- Termwise application and reversal commute on complexes and on homotopy classes. -/
def termwiseDual (F : A ⥤ B) [F.Additive] :
    (termwiseMinusValue F).op ⋙ boundedHomotopyDual B ≅
      boundedHomotopyDual A ⋙ F.op.mapHomotopyCategoryPlus := by
  refine NatIso.ofComponents (fun X => eqToIso ?_) ?_
  · apply ObjectProperty.FullSubcategory.ext
    rfl
  · intro X Y f
    let g := f.unop.hom.out
    have hg : (HomotopyCategory.quotient A (.up ℤ)).map g = f.unop.hom :=
      HomotopyCategory.quotient_map_out _
    have hh : (minus A).homMk ((HomotopyCategory.quotient A (.up ℤ)).map g) = f.unop := by
      ext : 1
      exact hg
    rw [← Quiver.Hom.op_unop f, ← hh]
    ext : 1
    simp only [eqToIso.hom, eqToHom_refl, Category.comp_id, Category.id_comp]
    change
      (homotopyDual B).map ((F.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient A (.up ℤ)).map g)).op =
      (F.op.mapHomotopyCategory (.up ℤ)).map
        ((homotopyDual A).map ((HomotopyCategory.quotient A (.up ℤ)).map g).op)
    rw [Functor.mapHomotopyCategory_map, homotopyDual_map_quotient, homotopyDual_map_quotient,
      Functor.mapHomotopyCategory_map]
    rfl

variable [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{max u₁ v₁} Aᵒᵖ] [HasDerivedCategory.{max u₂ v₂} Bᵒᵖ]
  [(QMinus A).IsLocalization (WMinus A)] [(QMinus B).IsLocalization (WMinus B)]

/-- Commutation of duality with the termwise functor followed by localization. -/
def mappedDual (F : A ⥤ B) [F.Additive] :
    (minusUValue F).op ⋙ derivedDual B ≅ boundedHomotopyDual A ⋙
      (F.op.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) := by
  change ((termwiseMinusValue F).op ⋙ (QMinus B).op) ⋙ derivedDual B ≅ _
  exact (associator _ _ _) ≪≫ isoWhiskerLeft (termwiseMinusValue F).op (derivedDualFactors B) ≪≫
    (associator _ _ _).symm ≪≫ isoWhiskerRight (termwiseDual F) _ ≪≫ associator _ _ _

variable [(minus A).IsTriangulated] [(minus B).IsTriangulated]
  [EnoughProjectives A]

private def projectiveObjects : ObjectProperty (KMinus A) :=
  fun X => ∀ n : ℤ, Projective (X.obj.as.X n)

private abbrev projectiveQuotient :
    (projectiveObjects (A := A)).FullSubcategory ⥤ DerivedCategory.Minus A :=
  (projectiveObjects (A := A)).ι ⋙ QMinus A

private instance projectiveQuotientFull : (projectiveQuotient (A := A)).Full where
  map_surjective {X Y} f := by
    let M : TotalLeftDerivedFunctor.Models A :=
      ⟨X.obj, TotalLeftDerivedFunctor.projective_mem A X.obj X.property⟩
    obtain ⟨g, hg⟩ := (TotalLeftDerivedFunctor.model_map_bijective A M Y.obj).surjective f
    exact ⟨(projectiveObjects (A := A)).homMk g, hg⟩

private instance projectiveQuotientFaithful : (projectiveQuotient (A := A)).Faithful where
  map_injective {X Y} f g h := by
    let M : TotalLeftDerivedFunctor.Models A :=
      ⟨X.obj, TotalLeftDerivedFunctor.projective_mem A X.obj X.property⟩
    ext : 1
    exact (TotalLeftDerivedFunctor.model_map_bijective A M Y.obj).injective h

private instance projectiveQuotientEssSurj : (projectiveQuotient (A := A)).EssSurj where
  mem_essImage X := by
    obtain ⟨b, P, hb, hP, ⟨e⟩⟩ := ProjectiveComplexReplacement.derivedRepresentative A X
    let M : KMinus A := ⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, b, hb⟩
    exact ⟨⟨M, hP⟩, ⟨DerivedCategory.Minus.ι.preimageIso
      ((DerivedCategory.quotientCompQhIso A).symm.app P ≪≫ e.symm)⟩⟩

private instance projectiveQuotientEquivalence : (projectiveQuotient (A := A)).IsEquivalence := {}

/-- Right derivation in the opposite category agrees naturally with
left derivation on D⁻. The comparison is constructed on projective
models, where both comparison maps are invertible. -/
private def deriveDualOnProjectives (F : A ⥤ B) [F.Additive] (LF : ExactLeftData F) :
    (projectiveQuotient (A := A)).op ⋙ (LF.functor.op ⋙ derivedDual B) ≅
      (projectiveQuotient (A := A)).op ⋙ (derivedDual A ⋙ F.op.rightDerivedFunctorPlus) := by
  let J := (projectiveObjects (A := A)).ι.op
  let Q := (projectiveQuotient (A := A)).op
  let α : J ⋙ (minusUValue F).op ⟶ J ⋙ ((QMinus A).op ⋙ LF.functor.op) :=
    whiskerLeft J (NatTrans.op LF.counit)
  have hα (M : (projectiveObjects (A := A)).FullSubcategoryᵒᵖ) :
      IsIso (α.app M) := by
    haveI := LF.model_iso M.unop.obj M.unop.property
    exact inferInstanceAs (IsIso (LF.counit.app M.unop.obj).op)
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  let η := whiskerLeft (J ⋙ boundedHomotopyDual A) F.op.rightDerivedFunctorPlusUnith
  have hη (M : (projectiveObjects (A := A)).FullSubcategoryᵒᵖ) :
      IsIso (η.app M) := by
    apply TotalRightDerivedFunctor.modelComparison Aᵒᵖ Bᵒᵖ F.op
    intro n
    exact Injective.projective_iff_injective_op.mp (M.unop.property (-n))
  haveI : IsIso η := NatIso.isIso_of_isIso_app η
  let H := LF.functor.op ⋙ derivedDual B
  let K := derivedDual A ⋙ F.op.rightDerivedFunctorPlus
  exact
    (associator _ _ _).symm ≪≫
      isoWhiskerRight ((associator _ _ _) ≪≫ (asIso α).symm) _ ≪≫
      (associator _ _ _) ≪≫ isoWhiskerLeft J (mappedDual F) ≪≫
      (associator _ _ _).symm ≪≫ asIso η ≪≫
      isoWhiskerRight ((associator _ _ _) ≪≫
        isoWhiskerLeft J (derivedDualFactors A).symm ≪≫ (associator _ _ _).symm) _ ≪≫
      associator _ _ _


def deriveDual (F : A ⥤ B) [F.Additive] (LF : ExactLeftData F) :
    LF.functor.op ⋙ derivedDual B ≅ derivedDual A ⋙ F.op.rightDerivedFunctorPlus :=
  (FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ (DerivedCategory.Plus Bᵒᵖ)).obj
      (projectiveQuotient (A := A)).op)).preimageIso (deriveDualOnProjectives F LF)

private lemma deriveDual_on_projective (F : A ⥤ B) [F.Additive] (LF : ExactLeftData F)
    (K : KMinus A) (hK : projectiveObjects K) :
    (derivedDual B).map (LF.counit.app K).op ≫
        (deriveDual F LF).hom.app (op ((QMinus A).obj K)) ≫
        F.op.rightDerivedFunctorPlus.map ((derivedDualFactors A).hom.app (op K)) =
      (mappedDual F).hom.app (op K) ≫
        F.op.rightDerivedFunctorPlusUnith.app ((boundedHomotopyDual A).obj (op K)) := by
  let FF := FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ (DerivedCategory.Plus Bᵒᵖ)).obj (projectiveQuotient (A := A)).op)
  let M : (projectiveObjects (A := A)).FullSubcategory := ⟨K, hK⟩
  have he : (deriveDual F LF).hom.app (op ((QMinus A).obj K)) =
      (deriveDualOnProjectives F LF).hom.app (op M) :=
    NatTrans.congr_app (FF.map_preimage (deriveDualOnProjectives F LF).hom) (op M)
  rw [he]
  dsimp only [deriveDualOnProjectives, Iso.trans_hom, NatTrans.comp_app, associator_inv_app,
    associator_hom_app, isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_hom,
    whiskerLeft_app, Iso.symm_hom, asIso_inv, asIso_hom, NatTrans.op_app]
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Functor.map_id, Category.assoc]
  let α : (projectiveObjects (A := A)).ι.op ⋙ (minusUValue F).op ⟶
      (projectiveObjects (A := A)).ι.op ⋙ ((QMinus A).op ⋙ LF.functor.op) :=
    whiskerLeft _ (NatTrans.op LF.counit)
  have hα (N : (projectiveObjects (A := A)).FullSubcategoryᵒᵖ) :
      IsIso (α.app N) := by
    haveI := LF.model_iso N.unop.obj N.unop.property
    exact inferInstanceAs (IsIso (LF.counit.app N.unop.obj).op)
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  have hc : (LF.counit.app K).op ≫ (inv α).app (op M) = 𝟙 _ :=
    (asIso α).hom_inv_id_app (op M)
  change (derivedDual B).map (LF.counit.app K).op ≫
      (derivedDual B).map ((inv α).app (op M)) ≫
      (mappedDual F).hom.app (op K) ≫
      F.op.rightDerivedFunctorPlusUnith.app ((boundedHomotopyDual A).obj (op K)) ≫
      F.op.rightDerivedFunctorPlus.map ((derivedDualFactors A).inv.app (op K)) ≫
      F.op.rightDerivedFunctorPlus.map ((derivedDualFactors A).hom.app (op K)) = _
  erw [← Category.assoc ((derivedDual B).map _), ← Functor.map_comp, hc,
    (derivedDual B).map_id, Category.id_comp]
  erw [← F.op.rightDerivedFunctorPlus.map_comp, Iso.inv_hom_id_app,
    F.op.rightDerivedFunctorPlus.map_id]
  simp

private lemma deriveDual_unith (F : A ⥤ B) [F.Additive] (LF : ExactLeftData F)
    (K : KMinus A) :
    (derivedDual B).map (LF.counit.app K).op ≫
        (deriveDual F LF).hom.app (op ((QMinus A).obj K)) ≫
        F.op.rightDerivedFunctorPlus.map ((derivedDualFactors A).hom.app (op K)) =
      (mappedDual F).hom.app (op K) ≫
        F.op.rightDerivedFunctorPlusUnith.app ((boundedHomotopyDual A).obj (op K)) := by
  let J := (minusUValue F).op ⋙ derivedDual B
  let L := boundedHomotopyDual A ⋙ (DerivedCategory.Plus.Qh ⋙ F.op.rightDerivedFunctorPlus)
  let lhs : J ⟶ L :=
    whiskerRight (NatTrans.op LF.counit) _ ≫ (isoWhiskerRight (opComp _ _) _).hom ≫
      (associator _ _ _).hom ≫
      whiskerLeft (QMinus A).op (deriveDual F LF).hom ≫ (associator _ _ _).inv ≫
      whiskerRight (derivedDualFactors A).hom _ ≫ (associator _ _ _).hom
  let rhs : J ⟶ L :=
    (mappedDual F).hom ≫ whiskerLeft (boundedHomotopyDual A) F.op.rightDerivedFunctorPlusUnith
  have lhs_app (M : KMinus A) : lhs.app (op M) =
      (derivedDual B).map (LF.counit.app M).op ≫
        (deriveDual F LF).hom.app (op ((QMinus A).obj M)) ≫
        F.op.rightDerivedFunctorPlus.map ((derivedDualFactors A).hom.app (op M)) := by
    simp [lhs, Category.assoc]
  have rhs_app (M : KMinus A) : rhs.app (op M) =
      (mappedDual F).hom.app (op M) ≫
        F.op.rightDerivedFunctorPlusUnith.app ((boundedHomotopyDual A).obj (op M)) := rfl
  obtain ⟨b, hb⟩ := K.property
  obtain ⟨P, π, hbP, hP, _, hπ⟩ := ProjectiveComplexReplacement.replacement A K.obj.as b hb
  let M : KMinus A := ⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, b, hbP⟩
  let m : M ⟶ K := ObjectProperty.homMk ((HomotopyCategory.quotient A (.up ℤ)).map π)
  have hm : WMinus A m := by
    change HomotopyCategory.quasiIso A (.up ℤ) ((HomotopyCategory.quotient A (.up ℤ)).map π)
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff π).2 hπ
  have hi : IsIso (L.map m.op) :=
    inferInstanceAs (IsIso (F.op.rightDerivedFunctorPlus.map
      (Localization.isoOfHom DerivedCategory.Plus.Qh _
        ((boundedHomotopyDual A).map m.op) (boundedHomotopyDual_quasiIso A m.op hm)).hom))
  rw [← lhs_app, ← rhs_app, ← cancel_mono (L.map m.op), ← lhs.naturality, ← rhs.naturality]
  rw [lhs_app, rhs_app, deriveDual_on_projective F LF M hP]

end LeftDerivedDual
section Stalk
universe u₁ v₁ w₁
variable (A : Type u₁) [Category.{v₁} A] [Abelian A]

private def singleDualComplex : (CochainComplex.singleFunctor A 0).op ⋙ cochainDual A ≅
    CochainComplex.singleFunctor Aᵒᵖ 0 := by
  refine NatIso.ofComponents (fun X => reversedStalk A X.unop) ?_
  intro X Y f
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = 0
  · subst i
    change (((CochainComplex.singleFunctor A 0).map f.unop).f 0).op ≫
      ((reversedStalk A Y.unop).hom.f 0) =
      ((reversedStalk A X.unop).hom.f 0) ≫ ((CochainComplex.singleFunctor Aᵒᵖ 0).map f).f 0
    change (((HomologicalComplex.single A (.up ℤ) 0).map f.unop).f 0).op ≫ _ =
      _ ≫ ((HomologicalComplex.single Aᵒᵖ (.up ℤ) 0).map f).f 0
    simp [reversedStalk, HomologicalComplex.single_map_f_self, Category.assoc]
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 Y i hi).eq_of_tgt _ _

variable [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{max u₁ v₁} Aᵒᵖ]
  [(QMinus A).IsLocalization (WMinus A)]

private def minusStalkFunctor : A ⥤ KMinus A :=
  (minus A).lift (HomotopyCategory.singleFunctor A 0)
    (fun X => (minusPointModel A 0 X).property)

private def minusStalkFunctorIso : minusSingle A ≅ minusStalkFunctor A ⋙ QMinus A :=
  ((FullyFaithful.ofFullyFaithful DerivedCategory.Minus.ι).whiskeringRight A).preimageIso
    (DerivedCategory.singleFunctorIsoCompQh A 0)

private lemma minusStalkFunctorIso_app (X : A) :
    (minusStalkFunctorIso A).app X = minusStalkModelIso A X := by
  ext : 1
  apply DerivedCategory.Minus.ι.map_injective
  rfl

private def reversedStalkToPlusIso (X : A) :
    DerivedCategory.Plus.Q.obj (reversedBounded A (minusPointModel A 0 X)) ≅
      (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X) := by
  let K : CochainComplex.Plus Aᵒᵖ :=
    ⟨(CochainComplex.singleFunctor Aᵒᵖ 0).obj (op X), ⟨0, inferInstance⟩⟩
  change _ ≅ DerivedCategory.Plus.Q.obj K
  exact DerivedCategory.Plus.Q.mapIso (ObjectProperty.isoMk _ (reversedStalk A X))

private lemma reversedStalkToPlusIso_naturality {X Y : Aᵒᵖ} (f : X ⟶ Y) :
    let fm : reversedBounded A (minusPointModel A 0 X.unop) ⟶
        reversedBounded A (minusPointModel A 0 Y.unop) :=
      ObjectProperty.homMk ((cochainDual A).map ((CochainComplex.singleFunctor A 0).map f.unop).op)
    DerivedCategory.Plus.Q.map fm ≫ (reversedStalkToPlusIso A Y.unop).hom =
      (reversedStalkToPlusIso A X.unop).hom ≫ (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).map f := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp]
  change DerivedCategory.Q.map ((cochainDual A).map
      ((CochainComplex.singleFunctor A 0).map f.unop).op) ≫
      DerivedCategory.Q.map ((reversedStalk A Y.unop).hom) =
    DerivedCategory.Q.map ((reversedStalk A X.unop).hom) ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor Aᵒᵖ 0).map f)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg DerivedCategory.Q.map ((singleDualComplex A).hom.naturality f)

private def derivedStalkOnModel :
    (minusStalkFunctor A ⋙ QMinus A).op ⋙ derivedDual A ≅
      DerivedCategory.Plus.singleFunctor Aᵒᵖ 0 := by
  refine NatIso.ofComponents (fun X => derivedDualLocalized A (minusPointModel A 0 X.unop) ≪≫
    reversedStalkToPlusIso A X.unop) ?_
  intro X Y f
  let g := (CochainComplex.singleFunctor A 0).map f.unop
  simp only [Functor.comp_map, Functor.op_map, Iso.trans_hom]
  rw [← Category.assoc]
  erw [derivedDualLocalized_naturality A (minusPointModel A 0 Y.unop)
    (minusPointModel A 0 X.unop) g, Category.assoc, reversedStalkToPlusIso_naturality A f]
  cat_disch

/-- Opposite-category passage carries the degree-zero stalk to the
same degree-zero stalk, also on every morphism of the source. -/
def derivedStalkDual :
    (minusSingle A).op ⋙ derivedDual A ≅ DerivedCategory.Plus.singleFunctor Aᵒᵖ 0 :=
  isoWhiskerRight (NatIso.op (minusStalkFunctorIso A).symm) _ ≪≫ derivedStalkOnModel A

def derivedReversal : DerivedReversal A where
  functor := derivedDual A
  localized := derivedDualLocalized A
  localized_naturality := derivedDualLocalized_naturality A
  homology := derivedHomologyDual A
  homology_eq := derivedDualHomology_normalized A
  stalk X := (derivedStalkDual A).app (op X)
  stalk_eq X := by
    change (derivedDual A).map ((minusStalkFunctorIso A).app X).inv.op ≫
        ((derivedDualLocalized A (minusPointModel A 0 X)).hom ≫ (reversedStalkToPlusIso A X).hom) =
      (derivedDual A).map (minusStalkModelIso A X).inv.op ≫
        (derivedDualLocalized A (minusPointModel A 0 X)).hom ≫ reversedStalkToPlus A X
    rw [minusStalkFunctorIso_app]
    rfl
end Stalk
section ClassicalDual
universe u₁ v₁ u₂ v₂ w₁ w₂
variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{max u₁ v₁} Aᵒᵖ] [HasDerivedCategory.{max u₂ v₂} Bᵒᵖ]
  [(QMinus A).IsLocalization (WMinus A)] [(QMinus B).IsLocalization (WMinus B)]
  [(minus A).IsTriangulated] [(minus B).IsTriangulated]
  [EnoughProjectives A]
  (F : A ⥤ B) [F.Additive] (LF : ExactLeftData F)

def classicalDual (n : ℕ) : rightValue F.op n ≅ (leftValue F LF n).op := calc
  _ ≅ ((minusSingle A).op ⋙ derivedDual A) ⋙
      F.op.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor Bᵒᵖ n :=
    isoWhiskerRight (derivedStalkDual A).symm _
  _ ≅ (minusSingle A).op ⋙ (LF.functor.op ⋙ derivedDual B) ⋙
      DerivedCategory.Plus.homologyFunctor Bᵒᵖ n :=
    associator _ _ _ ≪≫ isoWhiskerLeft _ ((associator _ _ _).symm ≪≫
      isoWhiskerRight (deriveDual F LF).symm _)
  _ ≅ (leftValue F LF n).op :=
    isoWhiskerLeft _ (associator _ _ _ ≪≫ isoWhiskerLeft _ (derivedHomologyDual B n))

end ClassicalDual
section ReversedDerivation
universe u₁ v₁ u₂ v₂ w₁ w₂
variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{max u₁ v₁} Aᵒᵖ] [HasDerivedCategory.{max u₂ v₂} Bᵒᵖ]
  [(QMinus A).IsLocalization (WMinus A)] [(QMinus B).IsLocalization (WMinus B)]
  [(minus A).IsTriangulated] [(minus B).IsTriangulated]
  [EnoughProjectives A]
  (F : A ⥤ B) [F.Additive] (LF : ExactLeftData F)

lemma termwiseDual_hom_app (K : KMinus A) :
    (termwiseDual F).hom.app (op K) = 𝟙 _ := by
  apply (HomotopyCategory.Plus.ι Bᵒᵖ).map_injective
  simp [termwiseDual]

lemma reversedTermwise_hom (K : KMinus A) :
    (reversedTermwise F K).hom = 𝟙 _ := rfl

lemma derivedDual_unit_counit (K : KMinus A) :
    (derivedDual B).map (LF.counit.app K).op ≫
        (deriveDual F LF).hom.app (op ((QMinus A).obj K)) ≫
        F.op.rightDerivedFunctorPlus.map (derivedDualLocalized A K).hom =
      (derivedDualLocalized B ((termwiseMinusValue F).obj K)).hom ≫
        DerivedCategory.Plus.Q.map (reversedTermwise F K).hom ≫
        F.op.rightDerivedFunctorPlusUnit.app (reversedBounded A K) := by
  simp only [derivedDualLocalized, Iso.trans_hom, Functor.map_comp, Iso.app_hom]
  erw [← Category.assoc _ _ ((F.op.rightDerivedFunctorPlus).map _),
    ← Category.assoc _ _ ((F.op.rightDerivedFunctorPlus).map _), deriveDual_unith F LF K]
  dsimp only [mappedDual, id_eq, Iso.trans_hom, NatTrans.comp_app, associator_hom_app,
    Iso.symm_hom, associator_inv_app, isoWhiskerLeft_hom, whiskerLeft_app,
    isoWhiskerRight_hom, whiskerRight_app]
  simp only [termwiseDual_hom_app, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.id_comp, Category.assoc, reversedTermwise_hom, Functor.rightDerivedFunctorPlusUnit_app,
    Functor.quotientCompMapHomotopyCategoryPlusIso, Iso.refl_inv, NatTrans.id_app]
  erw [DerivedCategory.Plus.Qh.map_id, Iso.hom_inv_id_app_assoc]
  simp
  erw [Category.id_comp]
  rfl

def reversedDerivedFunctor : ReversedDerivedFunctor F LF (derivedReversal A) (derivedReversal B) where
  iso := deriveDual F LF
  unit_counit := derivedDual_unit_counit F LF

lemma classicalDual_app (n : ℕ) (X : A) :
    (classicalDual F LF n).app (op X) =
      ReversedDerivedFunctor.classical F LF (derivedReversal A) (derivedReversal B)
        (reversedDerivedFunctor F LF) n X := by
  ext : 1
  dsimp only [classicalDual, ReversedDerivedFunctor.classical, reversedDerivedFunctor,
    derivedReversal, Iso.app_hom, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv,
    NatTrans.comp_app, associator_hom_app, associator_inv_app, isoWhiskerRight_hom,
    whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app, Functor.comp_map]
  simp [Category.assoc, Functor.map_comp]

end ReversedDerivation
section ComplexStalkReversal
open HomologicalComplex
universe u v
variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Duality on an arbitrary stalk, normalized on its only nonzero term. -/
def reversedSingle (n : ℤ) (X : A) :
    reversedComplex A ((CochainComplex.singleFunctor A (-n)).obj X) ≅
      (CochainComplex.singleFunctor Aᵒᵖ n).obj (op X) := by
  let e : ∀ j : ℤ, (reversedComplex A ((CochainComplex.singleFunctor A (-n)).obj X)).X j ≅
      ((CochainComplex.singleFunctor Aᵒᵖ n).obj (op X)).X j := fun j => by
    by_cases h : j = n
    · subst j
      exact (singleObjXSelf (.up ℤ) (-n) X).symm.op ≪≫
        (singleObjXSelf (.up ℤ) n (op X)).symm
    · have h' : -j ≠ -n := by omega
      exact (isZero_single_obj_X (.up ℤ) (-n) X (-j) h').op.iso
        (isZero_single_obj_X (.up ℤ) n (op X) j h)
  refine HomologicalComplex.Hom.isoOfComponents e ?_
  intro i j _
  rw [HomologicalComplex.single_obj_d, comp_zero]
  change 0 = (((CochainComplex.singleFunctor A (-n)).obj X).d (-j) (-i)).op ≫ _
  simp

lemma reversedSingle_hom_f_self (n : ℤ) (X : A) :
    (reversedSingle A n X).hom.f n =
      (singleObjXSelf (.up ℤ) (-n) X).inv.op ≫ (singleObjXSelf (.up ℤ) n (op X)).inv := by
  simp [reversedSingle]

variable {A} in
private lemma opHomologyProjection (S : ShortComplex A) :
    S.op.homologyπ ≫ S.homologyOpIso.hom = S.cyclesOpIso.hom ≫ S.homologyι.op := by
  simp only [ShortComplex.homologyOpIso, Iso.trans_hom, Iso.symm_hom, Iso.op_hom,
    Category.assoc, ShortComplex.homologyπ_comp_leftHomologyIso_inv_assoc]
  change S.op.leftHomologyπ ≫ S.rightHomologyData.op.leftHomologyIso.hom ≫
      S.rightHomologyIso.inv.op = _
  rw [S.rightHomologyData.op.leftHomologyπ_comp_leftHomologyIso_hom_assoc]
  rfl

set_option maxHeartbeats 1000000 in
lemma reversedSingle_homology (n : ℤ) (X : A) :
    homologyMap (reversedSingle A n X).hom n ≫
      (singleObjHomologySelfIso (.up ℤ) n (op X)).hom =
    (reversedHomology A ((CochainComplex.singleFunctor A (-n)).obj X) n).hom ≫
      (singleObjHomologySelfIso (.up ℤ) (-n) X).inv.op := by
  let K := (CochainComplex.singleFunctor A (-n)).obj X
  let J := reversedComplex A K
  let S := K.sc' (-(n+1)) (-n) (-(n-1))
  let T := J.sc' (n-1) n (n+1)
  let e : T ≅ S.op := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by
    change 𝟙 (op (K.X (-(n-1)))) ≫ (K.d (-n) (-(n-1))).op =
      (K.d (-n) (-(n-1))).op ≫ 𝟙 (op (K.X (-n)))
    simp) (by
      change 𝟙 (op (K.X (-n))) ≫ (K.d (-(n+1)) (-n)).op =
        (K.d (-(n+1)) (-n)).op ≫ 𝟙 (op (K.X (-(n+1))))
      simp)
  let hT := J.homologyIsoSc' (n-1) n (n+1) (by simp) (by simp)
  let hS := K.homologyIsoSc' (-(n+1)) (-n) (-(n-1)) (by simp; omega) (by simp; omega)
  let cT := J.cyclesIsoSc' (n-1) n (n+1) (by simp) (by simp)
  let cS := K.opcyclesIsoSc' (-(n+1)) (-n) (-(n-1)) (by simp; omega) (by simp; omega)
  have hLeft : J.homologyπ n ≫ homologyMap (reversedSingle A n X).hom n ≫
      (singleObjHomologySelfIso (.up ℤ) n (op X)).hom =
      J.iCycles n ≫ (singleObjXSelf (.up ℤ) (-n) X).inv.op := by
    rw [homologyπ_naturality_assoc, homologyπ_singleObjHomologySelfIso_hom,
      singleObjCyclesSelfIso_hom, cyclesMap_i_assoc, reversedSingle_hom_f_self]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hRight : J.homologyπ n ≫ (reversedHomology A K n).hom ≫
      (singleObjHomologySelfIso (.up ℤ) (-n) X).inv.op =
      J.iCycles n ≫ (singleObjXSelf (.up ℤ) (-n) X).inv.op := by
    change J.homologyπ n ≫ (hT.hom ≫ ShortComplex.homologyMap e.hom ≫
      S.homologyOpIso.hom ≫ hS.hom.op) ≫ _ = _
    simp only [Category.assoc]
    rw [show ∀ (Z : Aᵒᵖ) (b : T.homology ⟶ Z),
      J.homologyπ n ≫ hT.hom ≫ b = cT.hom ≫ T.homologyπ ≫ b by
      intro Z b
      simp only [hT, cT, π_homologyIsoSc'_hom_assoc]
      rfl]
    simp only [Category.assoc, ShortComplex.homologyπ_naturality_assoc,
      reassoc_of% (opHomologyProjection S)]
    have hs : (singleObjHomologySelfIso (.up ℤ) (-n) X).inv ≫
        hS.hom ≫ S.homologyι = (singleObjXSelf (.up ℤ) (-n) X).inv ≫ S.pOpcycles := by
      rw [show hS.hom ≫ S.homologyι = K.homologyι (-n) ≫ cS.hom from
        homologyIsoSc'_hom_ι _ _ _ _ _ _]
      rw [singleObjHomologySelfIso_inv_homologyι_assoc, singleObjOpcyclesSelfIso_hom,
        Category.assoc, pOpcycles_opcyclesIsoSc'_hom]
    rw [← op_comp, ← op_comp, Category.assoc, hs, op_comp]
    have hCy : S.cyclesOpIso.hom ≫ S.pOpcycles.op = S.op.iCycles := by
      rw [← cancel_epi S.cyclesOpIso.inv, Iso.inv_hom_id_assoc]
      exact S.cyclesOpIso_inv_op_iCycles.symm
    rw [reassoc_of% hCy, ShortComplex.cyclesMap_i_assoc]
    change cT.hom ≫ T.iCycles ≫ (𝟙 _) ≫ _ = _
    rw [Category.id_comp]
    have hc : cT.hom ≫ T.iCycles = J.iCycles n :=
      cyclesIsoSc'_hom_iCycles _ _ _ _ _ _
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ (singleObjXSelf (.up ℤ) (-n) X).inv.op) hc
  exact (cancel_epi (J.homologyπ n)).1 (hLeft.trans hRight.symm)

end ComplexStalkReversal

section ShiftedStalkReversal
open HomologicalComplex
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

def minusPointIso (k : ℤ) (X : A) :
    (minusPoint A k).obj X ≅ (QMinus A).obj (minusPointModel A k X) :=
  DerivedCategory.Minus.ι.preimageIso ((DerivedCategory.singleFunctorIsoCompQh A k).app X)

private lemma minusPointIso_hom_ι (k : ℤ) (X : A) :
    DerivedCategory.Minus.ι.map (minusPointIso k X).hom =
      (DerivedCategory.quotientCompQhIso A).inv.app ((CochainComplex.singleFunctor A k).obj X) := by
  simp only [minusPointIso, Functor.preimageIso_hom, Functor.map_preimage]
  change (DerivedCategory.singleFunctorIsoCompQh A k).hom.app X = _
  change (DerivedCategory.quotientCompQhIso A).inv.app ((CochainComplex.singleFunctor A k).obj X) ≫
    𝟙 _ = _
  exact Category.comp_id _

private lemma minusPointHomology (n : ℤ) (X : A) :
    (homologicalHomology (C := A) n).map (minusPointIso (-n) X).hom ≫
      (derivedHomologyOnModel A (minusPointModel A (-n) X) n).hom ≫
      (singleObjHomologySelfIso (.up ℤ) (-n) X).hom =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso A (-n)).hom.app X := by
  let K := (CochainComplex.singleFunctor A (-n)).obj X
  let H := DerivedCategory.homologyFunctor A (-n)
  simp only [Functor.comp_map, minusPointIso_hom_ι, derivedHomologyOnModel,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Category.assoc]
  change H.map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫
    H.map ((DerivedCategory.quotientCompQhIso A).inv.app K) ≫ _ = _
  have hid : (DerivedCategory.quotientCompQhIso A).inv.app K = 𝟙 _ := rfl
  erw [hid, H.map_id, Category.id_comp, Category.id_comp]
  symm
  simp only [DerivedCategory.singleFunctorCompHomologyFunctorIso, Iso.trans_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom, associator_hom_app,
    whiskerRight_app, whiskerLeft_app, DerivedCategory.singleFunctorsPostcompQIso,
    Functor.mapIso_refl, Iso.refl_hom, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

variable [HasDerivedCategory.{max u v} Aᵒᵖ]

private abbrev plusPointModel (n : ℤ) (Y : Aᵒᵖ) : CochainComplex.Plus Aᵒᵖ :=
  ⟨(CochainComplex.singleFunctor Aᵒᵖ n).obj Y, ⟨n, inferInstance⟩⟩

def reversedPoint (OA : DerivedReversal A) (n : ℤ) (X : A) :
    OA.functor.obj (op ((minusPoint A (-n)).obj X)) ≅
      (DerivedCategory.Plus.singleFunctor Aᵒᵖ n).obj (op X) :=
  OA.functor.mapIso (minusPointIso (-n) X).symm.op ≪≫
    OA.localized (minusPointModel A (-n) X) ≪≫
    DerivedCategory.Plus.Q.mapIso (show reversedBounded A (minusPointModel A (-n) X) ≅
      plusPointModel n (op X) from ObjectProperty.isoMk _ (reversedSingle A n X))

lemma reversedPoint_zero (OA : DerivedReversal A) (X : A) :
    reversedPoint OA 0 X = OA.stalk X := by
  apply Iso.ext
  rw [OA.stalk_eq]
  simp only [reversedPoint, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    Iso.symm_hom, Category.assoc]
  rfl

lemma reversedPoint_homology (OA : DerivedReversal A) (n : ℤ) (X : A) :
    (DerivedCategory.Plus.homologyFunctor Aᵒᵖ n).map (reversedPoint OA n X).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso Aᵒᵖ n).hom.app (op X) =
    (OA.homology n).hom.app (op ((minusPoint A (-n)).obj X)) ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso A (-n)).inv.app X).op := by
  let M := minusPointModel A (-n) X
  let i := minusPointIso (-n) X
  let J := reversedBounded A M
  let L := plusPointModel n (op X)
  let e : J ≅ L := ObjectProperty.isoMk _ (reversedSingle A n X)
  let H := DerivedCategory.Plus.homologyFunctor Aᵒᵖ n
  let ε := (DerivedCategory.singleFunctorCompHomologyFunctorIso A (-n)).app X
  have hApp : (DerivedCategory.singleFunctorCompHomologyFunctorIso Aᵒᵖ n).hom.app (op X) =
      (DerivedCategory.homologyFunctorFactors Aᵒᵖ n).hom.app L.obj ≫
        (singleObjHomologySelfIso (.up ℤ) n (op X)).hom := by
    simp only [DerivedCategory.singleFunctorCompHomologyFunctorIso, Iso.trans_hom,
      NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom, associator_hom_app,
      whiskerRight_app, whiskerLeft_app, DerivedCategory.singleFunctorsPostcompQIso,
      Functor.mapIso_refl, Iso.refl_hom, NatTrans.id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
    rfl
  have hNat := (OA.homology n).hom.naturality i.inv.op
  change H.map (OA.functor.map i.inv.op) ≫ (OA.homology n).hom.app (op ((QMinus A).obj M)) =
    (OA.homology n).hom.app (op ((minusPoint A (-n)).obj X)) ≫
      ((homologicalHomology (C := A) n).map i.inv).op at hNat
  have hE := (DerivedCategory.homologyFunctorFactors Aᵒᵖ n).hom.naturality e.hom.hom
  change H.map (DerivedCategory.Plus.Q.map e.hom) ≫
    (DerivedCategory.homologyFunctorFactors Aᵒᵖ n).hom.app L.obj =
    (DerivedCategory.homologyFunctorFactors Aᵒᵖ n).hom.app J.obj ≫
      homologyMap (reversedSingle A n X).hom n at hE
  have hModel := minusPointHomology n X
  change (homologicalHomology (C := A) n).map i.hom ≫
    (derivedHomologyOnModel A M n).hom ≫ (singleObjHomologySelfIso (.up ℤ) (-n) X).hom =
    ε.hom at hModel
  have hModelInv : (singleObjHomologySelfIso (.up ℤ) (-n) X).inv ≫
      (derivedHomologyOnModel A M n).inv ≫ (homologicalHomology (C := A) n).map i.inv =
      ε.inv := by
    let m := (homologicalHomology (C := A) n).mapIso i ≪≫
      derivedHomologyOnModel A M n ≪≫ singleObjHomologySelfIso (.up ℤ) (-n) X
    have hm : m = ε := Iso.ext hModel
    simpa only [m, Iso.trans_inv, Functor.mapIso_inv, Category.assoc] using congrArg Iso.inv hm
  have hComp : (derivedHomologyOnModel A M n).hom.op ≫
      ((homologicalHomology (C := A) n).map i.hom).op ≫ ε.inv.op =
    (singleObjHomologySelfIso (.up ℤ) (-n) X).inv.op := by
    apply Quiver.Hom.unop_inj
    rw [unop_comp, unop_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op, Quiver.Hom.unop_op,
      ← hModelInv]
    simp only [Category.assoc]
    erw [← CategoryTheory.Functor.map_comp_assoc, i.inv_hom_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
    rfl
  simp only [reversedPoint, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom]
  change H.map (OA.functor.map i.inv.op ≫ (OA.localized M).hom ≫
      DerivedCategory.Plus.Q.map e.hom) ≫ _ = _
  rw [Functor.map_comp, Functor.map_comp, hApp]
  simp only [Category.assoc]
  erw [reassoc_of% hE, reversedSingle_homology A n X, ← hComp]
  erw [← reassoc_of% (OA.homology_eq M n), reassoc_of% hNat]
  have hi : ((homologicalHomology (C := A) n).map i.inv).op ≫
      ((homologicalHomology (C := A) n).map i.hom).op = 𝟙 _ := by
    rw [← op_comp, ← CategoryTheory.Functor.map_comp, i.hom_inv_id,
      CategoryTheory.Functor.map_id, op_id]
  erw [reassoc_of% hi]
  rfl

end ShiftedStalkReversal

section ReversedStalkUnit
open HomologicalComplex
universe u v w u' v' w'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  [(minus A).IsTriangulated] [(minus B).IsTriangulated]
  [HasDerivedCategory.{max u v} Aᵒᵖ] [HasDerivedCategory.{max u' v'} Bᵒᵖ]
  [EnoughInjectives Aᵒᵖ]
  (F : A ⥤ B) [F.Additive] (LF : ExactLeftData F)

private abbrev mappedPointHom (k : ℤ) (X : A) :
    (termwiseMinusValue F).obj (minusPointModel A k X) ⟶ minusPointModel B k (F.obj X) :=
  ObjectProperty.homMk ((HomotopyCategory.quotient B (.up ℤ)).map
    ((singleMapHomologicalComplex F (.up ℤ) k).hom.app X))

lemma stalkCounit_model (k : ℤ) (X : A) :
    stalkCounit F LF k X ≫ (minusPointIso k (F.obj X)).hom =
    LF.functor.map (minusPointIso k X).hom ≫ LF.counit.app (minusPointModel A k X) ≫
      (QMinus B).map (mappedPointHom F k X) := by
  let K := (CochainComplex.singleFunctor A k).obj X
  let L := (CochainComplex.singleFunctor B k).obj (F.obj X)
  let M := (F.mapHomologicalComplex (.up ℤ)).obj K
  let f := (singleMapHomologicalComplex F (.up ℤ) k).hom.app X
  unfold stalkCounit
  simp only [Category.assoc]
  congr 2
  apply DerivedCategory.Minus.ι.map_injective
  simp only [CategoryTheory.Functor.map_comp, minusPointIso_hom_ι, Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc]
  have hi : (HomotopyCategory.singleFunctorPostcompQuotientIso A k).hom.app X = 𝟙 _ := rfl
  erw [hi, CategoryTheory.Functor.map_id, Functor.mapHomotopyCategoryFactors_hom_app,
    Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp]
  have hM : (DerivedCategory.quotientCompQhIso B).inv.app M = 𝟙 _ := rfl
  change DerivedCategory.Q.map f ≫ (DerivedCategory.quotientCompQhIso B).inv.app L =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map f)
  have hn := DerivedCategory.quotientCompQhIso_inv_naturality f
  change _ = (DerivedCategory.quotientCompQhIso B).inv.app M ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map f) at hn
  erw [hM, Category.id_comp] at hn
  exact hn

private abbrev plusMappedPointHom (n : ℤ) (X : A) :
    plusPointModel n (op (F.obj X)) ⟶ F.op.mapCochainComplexPlus.obj (plusPointModel n (op X)) :=
  ObjectProperty.homMk ((singleMapHomologicalComplex F.op (.up ℤ) n).inv.app (op X))

def shiftedStalkUnit (n : ℤ) (X : A) :
    (DerivedCategory.Plus.singleFunctor Bᵒᵖ n).obj (op (F.obj X)) ⟶
      F.op.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor Aᵒᵖ n).obj (op X)) :=
  DerivedCategory.Plus.Q.map (plusMappedPointHom F n X) ≫
    F.op.rightDerivedFunctorPlusUnit.app (plusPointModel n (op X))

private abbrev reversedMappedPointHom (n : ℤ) (X : A) :
    reversedBounded B (minusPointModel B (-n) (F.obj X)) ⟶
      reversedBounded B ((termwiseMinusValue F).obj (minusPointModel A (-n) X)) :=
  ObjectProperty.homMk ((CochainComplex.opEquivalence B).functor.map
    ((singleMapHomologicalComplex F (.up ℤ) (-n)).hom.app X).op)

private lemma reversedMappedPoint (n : ℤ) (X : A) :
    (ObjectProperty.isoMk _ (reversedSingle B n (F.obj X)) :
      reversedBounded B (minusPointModel B (-n) (F.obj X)) ≅ plusPointModel n (op (F.obj X))).hom ≫
        plusMappedPointHom F n X =
    reversedMappedPointHom F n X ≫ (reversedTermwise F (minusPointModel A (-n) X)).hom ≫
      F.op.mapCochainComplexPlus.map
        (ObjectProperty.isoMk _ (reversedSingle A n X) :
          reversedBounded A (minusPointModel A (-n) X) ≅ plusPointModel n (op X)).hom := by
  apply (CochainComplex.Plus.ι Bᵒᵖ).map_injective
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = n
  · subst i
    change (reversedSingle B n (F.obj X)).hom.f n ≫
          ((singleMapHomologicalComplex F.op (.up ℤ) n).inv.app (op X)).f n =
        (((singleMapHomologicalComplex F (.up ℤ) (-n)).hom.app X).f (-n)).op ≫
          𝟙 _ ≫ F.op.map ((reversedSingle A n X).hom.f n)
    simp only [reversedSingle_hom_f_self, singleMapHomologicalComplex_hom_app_self,
      singleMapHomologicalComplex_inv_app_self, Category.id_comp, Category.assoc,
      Iso.inv_hom_id_assoc, op_comp, CategoryTheory.Functor.map_comp]
    let a := singleObjXSelf (.up ℤ) (-n) X
    let b := singleObjXSelf (.up ℤ) (-n) (F.obj X)
    let c := singleObjXSelf (.up ℤ) n (op X)
    let d := singleObjXSelf (.up ℤ) n (op (F.obj X))
    change b.inv.op ≫ d.inv ≫ d.hom ≫ F.op.map c.inv =
      b.inv.op ≫ F.op.map a.hom.op ≫ F.op.map a.inv.op ≫ F.op.map c.inv
    rw [Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp_assoc, ← op_comp,
      a.inv_hom_id, op_id, CategoryTheory.Functor.map_id, Category.id_comp]
  · have hi' : -i ≠ -n := by omega
    exact (isZero_single_obj_X (.up ℤ) (-n) (F.obj X) (-i) hi').op.eq_of_src _ _

variable (OA : DerivedReversal A) (OB : DerivedReversal B)
  (OF : ReversedDerivedFunctor F LF OA OB)

/-- The reversed left counit agrees with the right unit on every literal stalk. -/
lemma reversedStalkCounit (n : ℤ) (X : A) :
    OB.functor.map (stalkCounit F LF (-n) X).op ≫
      OF.iso.hom.app (op ((minusPoint A (-n)).obj X)) ≫
      F.op.rightDerivedFunctorPlus.map (reversedPoint OA n X).hom =
    (reversedPoint OB n (F.obj X)).hom ≫ shiftedStalkUnit F n X := by
  let M := minusPointModel A (-n) X
  let N := minusPointModel B (-n) (F.obj X)
  let K := (termwiseMinusValue F).obj M
  let α := minusPointIso (-n) X
  let β := minusPointIso (-n) (F.obj X)
  let i : reversedBounded A M ≅ plusPointModel n (op X) :=
    ObjectProperty.isoMk _ (reversedSingle A n X)
  let j : reversedBounded B N ≅ plusPointModel n (op (F.obj X)) :=
    ObjectProperty.isoMk _ (reversedSingle B n (F.obj X))
  let U := F.op.rightDerivedFunctorPlus
  let QA := DerivedCategory.Plus.Q (C := Aᵒᵖ)
  let QB := DerivedCategory.Plus.Q (C := Bᵒᵖ)
  let τ := F.op.rightDerivedFunctorPlusUnit
  let f := mappedPointHom F (-n) X
  let g := reversedMappedPointHom F n X
  let s := stalkCounit F LF (-n) X
  have hs : s = LF.functor.map α.hom ≫ LF.counit.app M ≫ (QMinus B).map f ≫ β.inv := by
    apply (cancel_mono β.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      stalkCounit_model F LF (-n) X
  have hα := OF.iso.hom.naturality α.hom.op
  change OB.functor.map (LF.functor.map α.hom).op ≫
      OF.iso.hom.app (op ((minusPoint A (-n)).obj X)) =
    OF.iso.hom.app (op ((QMinus A).obj M)) ≫ U.map (OA.functor.map α.hom.op) at hα
  have hloc := OB.localized_naturality K N
    ((singleMapHomologicalComplex F (.up ℤ) (-n)).hom.app X)
  change OB.functor.map ((QMinus B).map f).op ≫ (OB.localized K).hom =
    (OB.localized N).hom ≫ QB.map g at hloc
  have hMap := reversedMappedPoint F n X
  change j.hom ≫ plusMappedPointHom F n X =
    g ≫ (reversedTermwise F M).hom ≫ F.op.mapCochainComplexPlus.map i.hom at hMap
  have hτ := τ.naturality i.hom
  change QB.map (F.op.mapCochainComplexPlus.map i.hom) ≫ τ.app (plusPointModel n (op X)) =
    τ.app (reversedBounded A M) ≫ U.map (QA.map i.hom) at hτ
  simp only [reversedPoint, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom,
    Category.assoc]
  change OB.functor.map s.op ≫ OF.iso.hom.app (op ((minusPoint A (-n)).obj X)) ≫
    U.map (OA.functor.map α.inv.op ≫ (OA.localized M).hom ≫ QA.map i.hom) =
    OB.functor.map β.inv.op ≫ (OB.localized N).hom ≫ QB.map j.hom ≫
      QB.map (plusMappedPointHom F n X) ≫ τ.app (plusPointModel n (op X))
  have hcancel : U.map (OA.functor.map α.hom.op) ≫
      U.map (OA.functor.map α.inv.op) = 𝟙 _ :=
    (U.mapIso (OA.functor.mapIso α.symm.op)).inv_hom_id
  have hsop : s.op = β.inv.op ≫ ((QMinus B).map f).op ≫
      (LF.counit.app M).op ≫ (LF.functor.map α.hom).op := by
    rw [hs]
    simp only [op_comp, Category.assoc]
  rw [hsop]
  erw [OB.functor.map_comp, OB.functor.map_comp, OB.functor.map_comp,
    U.map_comp, U.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hα, reassoc_of% hcancel]
  erw [reassoc_of% (OF.unit_counit M), reassoc_of% hloc, ← hτ]
  have hMap' := congrArg QB.map hMap
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hMap'
  erw [← reassoc_of% hMap']

lemma reversedStalkCounit_inv (n : ℤ) (X : A) :
    shiftedStalkUnit F n X ≫
        F.op.rightDerivedFunctorPlus.map (reversedPoint OA n X).inv ≫
        OF.iso.inv.app (op ((minusPoint A (-n)).obj X)) =
      (reversedPoint OB n (F.obj X)).inv ≫
        OB.functor.map (stalkCounit F LF (-n) X).op := by
  let U := F.op.rightDerivedFunctorPlus
  let e := reversedPoint OA n X
  let d := reversedPoint OB n (F.obj X)
  let i := OF.iso.app (op ((minusPoint A (-n)).obj X))
  let s := stalkCounit F LF (-n) X
  let q := shiftedStalkUnit F n X
  have hu := reversedStalkCounit F LF OA OB OF n X
  change OB.functor.map s.op ≫ i.hom ≫ U.map e.hom = d.hom ≫ q at hu
  change q ≫ U.map e.inv ≫ i.inv = d.inv ≫ OB.functor.map s.op
  apply (cancel_epi d.hom).1
  have he : U.map e.hom ≫ U.map e.inv = 𝟙 _ := (U.mapIso e).hom_inv_id
  erw [← Category.assoc, ← Category.assoc, ← hu]
  simp only [Category.assoc]
  erw [reassoc_of% he, i.hom_inv_id, Category.comp_id, d.hom_inv_id_assoc]

/-- Canonical comparison on the homology of opposite shifted stalks. -/
def reversedPointValue (n : ℤ) (X : A) :
    (DerivedCategory.Plus.homologyFunctor Bᵒᵖ n).obj
      (F.op.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor Aᵒᵖ n).obj (op X))) ≅
      op ((homologicalHomology (C := B) n).obj (LF.functor.obj ((minusPoint A (-n)).obj X))) :=
  (DerivedCategory.Plus.homologyFunctor Bᵒᵖ n).mapIso
    (F.op.rightDerivedFunctorPlus.mapIso (reversedPoint OA n X).symm ≪≫
      (OF.iso.app (op ((minusPoint A (-n)).obj X))).symm) ≪≫
    (OB.homology n).app (op (LF.functor.obj ((minusPoint A (-n)).obj X)))

lemma reversedPointValue_normalization (n : ℤ) (X : A) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso Bᵒᵖ n).inv.app (op (F.obj X)) ≫
      (DerivedCategory.Plus.homologyFunctor Bᵒᵖ n).map (shiftedStalkUnit F n X) ≫
      (reversedPointValue F LF OA OB OF n X).hom =
    (pointComparison F LF (-n) X).op := by
  let H := DerivedCategory.Plus.homologyFunctor Bᵒᵖ n
  let U := F.op.rightDerivedFunctorPlus
  let e := reversedPoint OA n X
  let d := reversedPoint OB n (F.obj X)
  let i := OF.iso.app (op ((minusPoint A (-n)).obj X))
  let a := (OB.homology n).app (op (LF.functor.obj ((minusPoint A (-n)).obj X)))
  let b := (OB.homology n).app (op ((minusPoint B (-n)).obj (F.obj X)))
  let s := stalkCounit F LF (-n) X
  let q := shiftedStalkUnit F n X
  let ε := (DerivedCategory.singleFunctorCompHomologyFunctorIso Bᵒᵖ n).app (op (F.obj X))
  let η := (DerivedCategory.singleFunctorCompHomologyFunctorIso B (-n)).app (F.obj X)
  have hq : q ≫ U.map e.inv ≫ i.inv = d.inv ≫ OB.functor.map s.op :=
    reversedStalkCounit_inv F LF OA OB OF n X
  have hε := reversedPoint_homology OB n (F.obj X)
  change H.map d.hom ≫ ε.hom = b.hom ≫ η.inv.op at hε
  have hε' : ε.inv ≫ H.map d.inv ≫ b.hom = η.hom.op := by
    apply (cancel_epi ε.hom).1
    erw [Iso.hom_inv_id_assoc]
    apply (cancel_epi (H.map d.hom)).1
    have hd : H.map d.hom ≫ H.map d.inv = 𝟙 _ := (H.mapIso d).hom_inv_id
    have hη : η.inv.op ≫ η.hom.op = 𝟙 _ := (η.symm.op).hom_inv_id
    erw [reassoc_of% hd, ← Category.assoc, hε, Category.assoc, hη,
      Category.comp_id]
  have hn := (OB.homology n).hom.naturality s.op
  change H.map (OB.functor.map s.op) ≫ a.hom =
    b.hom ≫ ((homologicalHomology (C := B) n).map s).op at hn
  change ε.inv ≫ H.map q ≫ (H.map (U.map e.inv ≫ i.inv) ≫ a.hom) =
    (((homologicalHomology (C := B) n).map s) ≫ η.hom).op
  erw [op_comp, H.map_comp (U.map e.inv) i.inv]
  simp only [Category.assoc]
  have hh := congrArg H.map hq
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at hh
  erw [reassoc_of% hh, hn]
  erw [reassoc_of% hε']

lemma reversedPointValue_zero (X : A) :
    reversedPointValue F LF OA OB OF 0 X =
      ReversedDerivedFunctor.classical F LF OA OB OF 0 X := by
  unfold reversedPointValue ReversedDerivedFunctor.classical
  rw [reversedPoint_zero]
  rfl

end ReversedStalkUnit


section RightStalkCoordinates
universe u v w u' v' w'
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  [(minus A).IsTriangulated] [(minus B).IsTriangulated]
  [HasDerivedCategory.{max u v} Aᵒᵖ] [HasDerivedCategory.{max u' v'} Bᵒᵖ]
  [EnoughInjectives Aᵒᵖ]
  (F : A ⥤ B) [F.Additive] (LF : ExactLeftData F)
  (OA : DerivedReversal A) (OB : DerivedReversal B)
  (OF : ReversedDerivedFunctor F LF OA OB)

lemma shiftedStalkUnit_zero (X : A) :
    shiftedStalkUnit F 0 X = (GrothendieckEdges.stalkToDerived F.op).app (op X) := by
  rw [GrothendieckEdges.stalkToDerived_app_literal]
  rfl

lemma reversedStalkCounit_zero (X : A) :
    (GrothendieckEdges.stalkToDerived F.op).app (op X) ≫
        F.op.rightDerivedFunctorPlus.map (OA.stalk X).inv ≫
        OF.iso.inv.app (op ((minusSingle A).obj X)) =
      (OB.stalk (F.obj X)).inv ≫ OB.functor.map (stalkCounit F LF 0 X).op := by
  have h := reversedStalkCounit_inv F LF OA OB OF 0 X
  rw [shiftedStalkUnit_zero, reversedPoint_zero, reversedPoint_zero] at h
  exact h

lemma reversedPointValue_rightStalk [PreservesFiniteLimits F.op] (n : ℤ) (X : A) :
    (GrothendieckEdges.rightDerivedStalkHomologyIso F.op n).inv.app (op X) ≫
      (reversedPointValue F LF OA OB OF n X).hom = (pointComparison F LF (-n) X).op := by
  let H := DerivedCategory.Plus.homologyFunctor Bᵒᵖ n
  let ε := (DerivedCategory.singleFunctorCompHomologyFunctorIso Bᵒᵖ n).app (op (F.obj X))
  let t := (GrothendieckEdges.shiftedStalkValueIso F.op n).app (op X)
  let e := (GrothendieckEdges.canonicalRightZeroIso F.op).app (op X)
  let q := shiftedStalkUnit F n X
  have h := GrothendieckEdges.shiftedStalkUnit_normalization F.op n (op X)
  change H.map q ≫ t.hom = ε.hom ≫ e.inv at h
  have he : ε.inv ≫ H.map q = e.inv ≫ t.inv := by
    apply (cancel_mono t.hom).1
    erw [Category.assoc, h, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  change (e.inv ≫ t.inv) ≫ _ = _
  erw [← he, Category.assoc]
  exact reversedPointValue_normalization F LF OA OB OF n X

lemma reversedClassicalZero [PreservesFiniteLimits F.op] (X : A) :
    (GrothendieckEdges.degreeZeroUnit F.op).app (op X) ≫
      (ReversedDerivedFunctor.classical F LF OA OB OF 0 X).hom =
      (degreeZeroComparison F LF X).op := by
  have h := reversedPointValue_rightStalk F LF OA OB OF 0 X
  rw [reversedPointValue_zero] at h
  unfold GrothendieckEdges.rightDerivedStalkHomologyIso
    GrothendieckEdges.shiftedStalkValueIso at h
  simp only [dite_eq_left, id_eq, Iso.trans_inv, Iso.refl_inv, NatTrans.comp_app,
    NatTrans.id_app] at h
  erw [Category.comp_id] at h
  exact h

end RightStalkCoordinates
section Diagrams
open HypercohomologyDerivedNaturality GrothendieckSpectralSequence
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

def homologicalNext (D : HomologicalDiagram C) (r : ℕ) (p n : ℤ) :
    (homologicalPage (r+1) (p+((r:ℤ)+2)) (n+1)).obj D ≅
      (pageComplex D r p n).homology :=
  (D.unop.nextIso r p n).unop.symm ≪≫
    ((D.unop.pageComplex r p n).unop.homologyOpIso).unop.symm

theorem incoming_square_zero (D : HomologicalDiagram C) (r : ℕ) (p n : ℤ) :
    incoming D r (p+((r:ℤ)+2)) (n+1) ≫ incoming D r p n = 0 := by
  simpa only [unop_comp, unop_zero] using congrArg Quiver.Hom.unop (D.unop.square_zero r p n)

theorem incoming_naturality {D D' : HomologicalDiagram C} (f : D ⟶ D')
    (r : ℕ) (p n : ℤ) :
    (homologicalPage r (p+((r:ℤ)+2)) (n+1)).map f ≫ incoming D' r p n =
      incoming D r p n ≫ (homologicalPage r p n).map f := by
  change (f.unop.page r (p+((r:ℤ)+2)) (n+1)).unop ≫ (D'.unop.differential r p n).unop =
    (D.unop.differential r p n).unop ≫ (f.unop.page r p n).unop
  simpa only [unop_comp] using (congrArg Quiver.Hom.unop (f.unop.differential_comm r p n)).symm

theorem first_quadrant_all_pages (D : HomologicalDiagram C)
    (h : ∀ p n : ℤ, p < 0 ∨ n < p → IsZero ((homologicalPage 0 p n).obj D)) :
    ∀ r : ℕ, ∀ p n : ℤ, p < 0 ∨ n < p → IsZero ((homologicalPage r p n).obj D) := by
  intro r
  induction r with
  | zero => exact h
  | succ r ih =>
    intro p n hpn
    let s := (r : ℤ) + 2
    have hp : p-s+s = p := by omega
    have hn : n-1+1 = n := by omega
    let E := homologicalNext D r (p-s) (n-1)
    have hz : IsZero ((pageComplex D r (p-s) (n-1)).X₂) := by
      change IsZero ((homologicalPage r (p-s+s) (n-1+1)).obj D)
      rw [hp, hn]
      exact ih p n hpn
    have he : IsZero ((homologicalPage (r+1) (p-s+s) (n-1+1)).obj D) :=
      ((pageComplex D r (p-s) (n-1)).isZero_homology_of_isZero_X₂ hz).of_iso E
    rwa [hp, hn] at he

lemma differential_zero_of (D : HomologicalDiagram C) (r : ℕ) (p n : ℤ)
    (h : D.unop.differential r (p - ((r : ℤ) + 2)) (n - 1) = 0) :
    differential D r p n = 0 := by
  simp [differential, incoming, h]

private def gradesOfEpis {T X Y : C} (f : T ⟶ X) (g : X ⟶ Y) [Epi f]
    (h : kernelSubobject f ≤ kernelSubobject (f ≫ g)) :
    graded _ _ h ≅ kernel g := by
  let k := (kernelSubobject (f ≫ g)).arrow
  let b : (kernelSubobject (f ≫ g) : C) ⟶ kernel g :=
    kernel.lift g (k ≫ f) (by simp [k, Category.assoc])
  let a := Subobject.ofLE _ _ h
  have hab : a ≫ b = 0 := by
    rw [← cancel_mono (kernel.ι g)]
    simp [a, b, k]
  let S := ShortComplex.mk a b hab
  have hk : IsLimit (KernelFork.ofι a hab) := by
    apply KernelFork.IsLimit.ofι'
    intro Z t ht
    have ht' : (t ≫ k) ≫ f = 0 := by
      have := congrArg (fun i => i ≫ kernel.ι g) ht
      simpa [b, Category.assoc] using this
    let l := factorThruKernelSubobject f (t ≫ k) ht'
    refine ⟨l, ?_⟩
    rw [← cancel_mono k]
    simp [l, a, k, Category.assoc]
  haveI : Epi b := by
    apply (epi_iff_surjective_up_to_refinements b).mpr
    intro Z z
    obtain ⟨Z', e, he, w, hw⟩ := surjective_up_to_refinements_of_epi f (z ≫ kernel.ι g)
    have hw' : w ≫ (f ≫ g) = 0 := by rw [← Category.assoc, ← hw]; simp
    let l := factorThruKernelSubobject (f ≫ g) w hw'
    refine ⟨Z', e, he, l, ?_⟩
    rw [← cancel_mono (kernel.ι g)]
    simp only [b, Category.assoc, kernel.lift_ι]
    rw [← Category.assoc l k f]
    have hl : l ≫ k = w := factorThruKernelSubobject_comp_arrow _ _ _
    rw [hl]
    simpa only [Category.assoc] using hw
  have hS : S.Exact := S.exact_of_f_is_kernel hk
  exact (colimit.isColimit _).coconePointUniqueUpToIso hS.gIsCokernel

/-- The quotient of adjacent increasing steps is the dual graded piece. -/
def dualGraded (D : HomologicalDiagram C) (p n : ℤ)
    (h : D.unop.down p n ≫ D.unop.inclusion p n = D.unop.inclusion (p+1) n)
    [Mono (D.unop.inclusion p n)]
    (hle : filtration D (p-1) n ≤ filtration D p n) :
    (cokernel (D.unop.down p n)).unop ≅ graded _ _ hle := by
  have hp : p - 1 + 1 = p := by omega
  let f := (D.unop.inclusion (p+1) n).unop
  let g := (D.unop.down p n).unop
  let i := (D.unop.inclusion p n).unop
  let c := cokernel.π (D.unop.down p n)
  have hi : i ≫ g = f := by simpa only [unop_comp] using congrArg Quiver.Hom.unop h
  haveI : Epi i := inferInstanceAs (Epi (D.unop.inclusion p n).unop)
  have hz : c.unop ≫ g = 0 := by
    simpa only [unop_comp, unop_zero] using
      congrArg Quiver.Hom.unop (cokernel.condition (D.unop.down p n))
  have h₀ : IsLimit (KernelFork.ofι c.unop hz) :=
    CokernelCofork.IsColimit.ofπUnop c (cokernel.condition _) (cokernelIsCokernel _)
  refine h₀.conePointUniqueUpToIso (kernelIsKernel g) ≪≫ ?_
  -- Generalizing both indices of the adjacent quotients makes the transport explicit.
  have hleft : filtration D (p-1) n = kernelSubobject i :=
    congrArg (fun t : ℤ => kernelSubobject (D.unop.inclusion t n).unop) hp
  have hright : filtration D p n = kernelSubobject (i ≫ g) :=
    congrArg (fun m => kernelSubobject m) hi.symm
  have grade_eq {T : C} {S U S' U' : Subobject T} (eS : S = S') (eU : U = U')
      (h : S ≤ U) (h' : S' ≤ U') : graded S U h = graded S' U' h' := by subst S'; subst U'; rfl
  exact (gradesOfEpis i g (kernelSubobject_comp_le i g)).symm ≪≫
    eqToIso (grade_eq hleft.symm hright.symm _ _)

theorem reverse_filtration (D : HomologicalDiagram C)
    (hm : ∀ p n, Mono (D.unop.inclusion p n))
    (hd : ∀ p n, D.unop.down p n ≫ D.unop.inclusion p n = D.unop.inclusion (p+1) n)
    (hf : ∀ n, ∃ a b : ℤ,
      (∀ p, p ≤ a → IsIso (D.unop.inclusion p n)) ∧
      (∀ p, b ≤ p → IsZero (D.unop.step p n)))
    (hc : Converges D.unop) : FiniteConvergence D := by
  have inc (p n : ℤ) : filtration D (p-1) n ≤ filtration D p n := by
    have hl : filtration D (p-1) n = kernelSubobject (D.unop.inclusion p n).unop :=
      congrArg (fun t : ℤ => kernelSubobject (D.unop.inclusion t n).unop) (by omega)
    have hr : filtration D p n = kernelSubobject
        ((D.unop.inclusion p n).unop ≫ (D.unop.down p n).unop) :=
      congrArg (fun m => kernelSubobject m) (by rw [← unop_comp, hd])
    rw [hl, hr]
    apply kernelSubobject_comp_le
  refine ⟨inc, ?_, ?_, ?_⟩
  · intro D' f p n
    refine kernelSubobject_factors _ _ ?_
    rw [Category.assoc]
    have h := congrArg Quiver.Hom.unop (f.unop.inclusion_comm (p+1) n)
    simp only [unop_comp] at h
    change (D.unop.inclusion (p+1) n).unop ≫ (f.unop.step (p+1) n).unop =
      (homologicalTarget n).map f ≫ (D'.unop.inclusion (p+1) n).unop at h
    rw [← h]
    change (kernelSubobject (D.unop.inclusion (p+1) n).unop).arrow ≫
      (D.unop.inclusion (p+1) n).unop ≫ (f.unop.step (p+1) n).unop = 0
    rw [kernelSubobject_arrow_comp_assoc, zero_comp]
  · intro n
    obtain ⟨a, b, ha, hb⟩ := hf n
    refine ⟨a-1, b-1, ?_, ?_⟩
    · intro p hp
      haveI := ha (p+1) (by omega)
      haveI : Mono (D.unop.inclusion (p+1) n).unop := inferInstance
      exact Subobject.mk_eq_bot_iff_zero.mpr (by rw [← cancel_mono (D.unop.inclusion (p+1) n).unop]; simp)
    · intro p hp
      have hzero := (hb (p+1) (by omega)).unop.eq_of_tgt (D.unop.inclusion (p+1) n).unop 0
      exact congrArg (fun m => kernelSubobject m) hzero |>.trans kernelSubobject_zero
  · intro n
    obtain ⟨N, hN⟩ := hc (n-1)
    obtain ⟨M, hM⟩ := hc n
    refine ⟨max N M, ?_⟩
    intro r hr p
    have hNr : N ≤ r := le_trans (le_max_left _ _) hr
    have hMr : M ≤ r := le_trans (le_max_right _ _) hr
    haveI := hm p n
    obtain ⟨e⟩ := (hM r hMr p).2
    exact ⟨differential_zero_of D r p n (hN r hNr _).1,
      ⟨e.unop.symm ≪≫ dualGraded D p n (hd p n) (inc p n)⟩⟩

end Diagrams

section Composition
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
  [(minus A).IsTriangulated] [(minus B).IsTriangulated] [(minus C).IsTriangulated]
  [EnoughProjectives A] [EnoughProjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  (LF : ExactLeftData F) (LG : ExactLeftData G) (LFG : ExactLeftData (F ⋙ G))

theorem canonical_comparison_exists
    (hacyc : ∀ (P : A), Projective P → leftAcyclicValue G LG (F.obj P)) :
    ∃ e : LF.functor ⋙ LG.functor ≅ LFG.functor,
      whiskerLeft (QMinus A) e.hom ≫ LFG.counit = composedCounit F G LF LG := by
  obtain ⟨α, hα⟩ := (LFG.universal _).2 (composedCounit F G LF LG)
  have inst (X : DerivedCategory.Minus A) : IsIso (α.app X) := by
    obtain ⟨b, P, hb, hP, ⟨e⟩⟩ := ProjectiveComplexReplacement.derivedRepresentative A X
    let M : KMinus A := ⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, b, hb⟩
    let i : (QMinus A).obj M ≅ X := DerivedCategory.Minus.ι.preimageIso
      ((DerivedCategory.quotientCompQhIso A).symm.app P ≪≫ e.symm)
    have h : IsIso (α.app ((QMinus A).obj M)) := by
      haveI := LF.model_iso M hP
      haveI := LFG.model_iso M hP
      haveI : IsIso (LG.counit.app ((termwiseMinusValue F).obj M)) :=
        AcyclicTermComparison.leftComparison B C inferInstance inferInstance G LG _
          (fun n => hacyc _ (hP n))
      have h := congr_app hα M
      change α.app ((QMinus A).obj M) ≫ LFG.counit.app M =
        (composedCounit F G LF LG).app M at h
      haveI : IsIso ((composedCounit F G LF LG).app M) := by
        dsimp only [composedCounit, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
        infer_instance
      haveI : IsIso (α.app ((QMinus A).obj M) ≫ LFG.counit.app M) := h ▸ inferInstance
      exact IsIso.of_isIso_comp_right _ (LFG.counit.app M)
    have he := α.naturality i.hom
    have hEq : α.app X = (LF.functor ⋙ LG.functor).map i.inv ≫
        α.app ((QMinus A).obj M) ≫ LFG.functor.map i.hom := by
      simp only [← he, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
      simp
    rw [hEq]
    infer_instance
  haveI : IsIso α := NatIso.isIso_of_isIso_app α
  exact ⟨asIso α, hα⟩

end Composition


section DegreeZero

open private mappedStalkIso
  from MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

universe u₁ v₁ u₂ v₂ w₁ w₂
variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
  [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [(minus A).IsTriangulated] [(minus B).IsTriangulated]
variable (F : A ⥤ B) [F.Additive] (LF : ExactLeftData F)

private theorem canonicalZeroComponents (X : A) :
    degreeZeroComparison F LF X = (leftDegreeZeroCounit F LF).app X := by
  dsimp only [degreeZeroComparison, pointComparison, stalkCounit, leftDegreeZeroCounit]
  simp only [Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
    Functor.comp_map, Iso.symm_hom, associator_hom_app, associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  unfold mappedStalkIso
  simp
  let H := DerivedCategory.homologyFunctor B 0
  have hm {Y Z : DerivedCategory.Minus B} (f : Y.obj ⟶ Z.obj) :
      (DerivedCategory.Minus.ι.preimage f : Y ⟶ Z).hom = f :=
    DerivedCategory.Minus.ι.map_preimage f
  have hq : (DerivedCategory.singleFunctorIsoCompQ B 0).inv.app (F.obj X) = 𝟙 _ := rfl
  erw [hm, hq]
  repeat erw [H.map_comp]
  repeat erw [H.map_id]
  repeat erw [Category.id_comp]
  repeat erw [Category.assoc]
  rfl

private def degreeZeroIso [EnoughProjectives A] [PreservesFiniteColimits F] :
    leftValue F LF 0 ≅ F := by
  letI := ClassicalDerivedValues.leftZero A B inferInstance inferInstance F LF
  exact asIso (leftDegreeZeroCounit F LF)

private theorem degreeZeroIso_hom [EnoughProjectives A] [PreservesFiniteColimits F] (X : A) :
    (degreeZeroIso F LF).hom.app X = degreeZeroComparison F LF X :=
  (canonicalZeroComponents F LF X).symm

end DegreeZero


section Abutment

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
  [(minus A).IsTriangulated] [(minus B).IsTriangulated] [(minus C).IsTriangulated]
  {F : A ⥤ B} {G : B ⥤ C} [F.Additive] [G.Additive]
  {LF : ExactLeftData F} {LG : ExactLeftData G} {LFG : ExactLeftData (F ⋙ G)}
  (P : Package F G LF LG LFG)

private def mappedStepIso {X Y : C} (e : X ≅ Y) (S : Subobject X) :
    (S : C) ≅ ((Subobject.map e.hom).obj S : C) :=
  Subobject.isoOfMkEq (S.arrow ≫ e.hom) _
    (by rw [← Subobject.map_mk, Subobject.mk_arrow])

@[reassoc]
private lemma mappedStepIso_arrow {X Y : C} (e : X ≅ Y) (S : Subobject X) :
    (mappedStepIso e S).hom ≫ ((Subobject.map e.hom).obj S).arrow = S.arrow ≫ e.hom :=
  Subobject.ofMkLE_arrow _

private abbrev abutmentTargetApp (X : DerivedCategory.Minus A) (n : ℤ) :=
  (targetIso F G LF LG LFG P n).app X

private theorem abutmentFiltration_increasing (X : DerivedCategory.Minus A) (p n : ℤ) :
    abutmentFiltration F G LF LG LFG P X (p-1) n ≤ abutmentFiltration F G LF LG LFG P X p n :=
  (Subobject.mapIsoToOrderIso (abutmentTargetApp P X n)).monotone
    ((P.convergence X).increasing p n)

private theorem abutmentFiltration_monotone (X : DerivedCategory.Minus A) (n : ℤ) :
    Monotone (fun p => abutmentFiltration F G LF LG LFG P X p n) := by
  apply monotone_int_of_le_succ
  intro p
  simpa only [Int.add_sub_cancel] using abutmentFiltration_increasing P X (p+1) n

private theorem abutmentFiltration_finite (X : DerivedCategory.Minus A) (n : ℤ) :
    ∃ a b : ℤ, (∀ p, p ≤ a → abutmentFiltration F G LF LG LFG P X p n = ⊥) ∧
      (∀ p, b ≤ p → abutmentFiltration F G LF LG LFG P X p n = ⊤) := by
  obtain ⟨a, b, ha, hb⟩ := (P.convergence X).finite n
  let e := Subobject.mapIsoToOrderIso (abutmentTargetApp P X n)
  exact ⟨a, b,
    fun p h => (congrArg e (ha p h)).trans e.map_bot,
    fun p h => (congrArg e (hb p h)).trans e.map_top⟩

private theorem abutmentFiltration_natural {X Y : DerivedCategory.Minus A} (f : X ⟶ Y) (p n : ℤ) :
    (abutmentFiltration F G LF LG LFG P Y p n).Factors
      ((abutmentFiltration F G LF LG LFG P X p n).arrow ≫ (abutment F G LFG n).map f) := by
  let S := filtration (P.sequence.obj X) p n
  let T := filtration (P.sequence.obj Y) p n
  let eX := abutmentTargetApp P X n
  let eY := abutmentTargetApp P Y n
  let i := mappedStepIso eX S
  let j := mappedStepIso eY T
  have hT : T.Factors (S.arrow ≫ (homologicalTarget n).map (P.sequence.map f)) :=
    (P.convergence X).natural_filtration _ (P.sequence.map f) p n
  let h := T.factorThru _ hT
  have hh : h ≫ T.arrow = S.arrow ≫ (homologicalTarget n).map (P.sequence.map f) :=
    Subobject.factorThru_arrow T _ hT
  have hn : (homologicalTarget n).map (P.sequence.map f) ≫ eY.hom =
      eX.hom ≫ (abutment F G LFG n).map f :=
    (targetIso F G LF LG LFG P n).hom.naturality f
  have hs : i.inv ≫ S.arrow ≫ eX.hom =
      (abutmentFiltration F G LF LG LFG P X p n).arrow := by
    rw [← mappedStepIso_arrow eX S, i.inv_hom_id_assoc]
    rfl
  change ((Subobject.map eY.hom).obj T).Factors
    (((Subobject.map eX.hom).obj S).arrow ≫ (abutment F G LFG n).map f)
  apply (Subobject.factors_iff _ _).mpr
  refine ⟨i.inv ≫ h ≫ j.hom, ?_⟩
  change (i.inv ≫ h ≫ j.hom) ≫ ((Subobject.map eY.hom).obj T).arrow = _
  simp only [Category.assoc, j, mappedStepIso_arrow]
  rw [← Category.assoc h T.arrow, hh, Category.assoc S.arrow, hn,
    ← Category.assoc S.arrow, ← Category.assoc i.inv, hs]
  rfl

private theorem abutmentFiltration_stable (X : DerivedCategory.Minus A) (n : ℤ) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → ∀ p : ℤ,
      differential (P.sequence.obj X) r p n = 0 ∧
      Nonempty ((homologicalPage r p n).obj (P.sequence.obj X) ≅
        graded _ _ (abutmentFiltration_increasing P X p n)) := by
  let e := abutmentTargetApp P X n
  obtain ⟨N, hN⟩ := (P.convergence X).stable n
  refine ⟨N, fun r hr p => ?_⟩
  obtain ⟨hz, ⟨ep⟩⟩ := hN r hr p
  let S := filtration (P.sequence.obj X) (p-1) n
  let T := filtration (P.sequence.obj X) p n
  let i := mappedStepIso e S
  let j := mappedStepIso e T
  let a := Subobject.ofLE S T ((P.convergence X).increasing p n)
  let b := Subobject.ofLE ((Subobject.map e.hom).obj S) ((Subobject.map e.hom).obj T)
    (abutmentFiltration_increasing P X p n)
  have hc : a ≫ j.hom = i.hom ≫ b := by
    apply (cancel_mono ((Subobject.map e.hom).obj T).arrow).1
    simp only [Category.assoc, i, j, a, b, mappedStepIso_arrow, Subobject.ofLE_arrow]
    rw [Subobject.ofLE_arrow_assoc]
  exact ⟨hz, ⟨ep ≪≫ cokernel.mapIso a b i j hc⟩⟩

theorem abutmentConverges : AbutmentConvergence F G LF LG LFG P where
  monotone := abutmentFiltration_monotone P
  natural_filtration := abutmentFiltration_natural P
  finite := abutmentFiltration_finite P
  stable := abutmentFiltration_stable P

end Abutment

section LeftTruncation

variable {B : Type u₂} {C : Type u₃} [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]

private abbrev minusHomology (k : ℤ) : DerivedCategory.Minus B ⥤ B :=
  DerivedCategory.Minus.ι ⋙ DerivedCategory.homologyFunctor B k

private abbrev minusT (B : Type*) [Category* B] [Abelian B] [HasDerivedCategory B] :=
  DerivedCategory.TStructure.t.onMinus (C := DerivedCategory B)

private lemma leftDerived_preserves_isLE [(minus B).IsTriangulated] [(minus C).IsTriangulated]
    [EnoughProjectives B] (G : B ⥤ C) [G.Additive] (LG : ExactLeftData G)
    (Y : DerivedCategory.Minus B) (k : ℤ) [ (minusT B).IsLE Y k ] :
    (LG.functor.obj Y).obj.IsLE k := by
  have hY : Y.obj.IsLE k :=
    (ObjectProperty.tStructure_isLE_iff _ _ Y k).1 inferInstance
  obtain ⟨K, hb, ⟨e⟩⟩ := Y.obj.exists_iso_Q_obj_of_isLE k
  let M : KMinus B := ⟨(HomotopyCategory.quotient B (.up ℤ)).obj K, k, hb⟩
  let e' : Y ≅ (QMinus B).obj M :=
    DerivedCategory.Minus.ι.preimageIso (e ≪≫ (DerivedCategory.quotientCompQhIso B).app K)
  have hM : CochainComplex.IsStrictlyLE M.obj.as k := hb
  have : (DerivedCategory.Minus.ι.obj (LG.functor.obj ((QMinus B).obj M))).IsLE k :=
    AcyclicTermComparison.leftDerived_isLE G LG M k
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (DerivedCategory.Minus.ι.mapIso (LG.functor.mapIso e').symm) k

private lemma minus_homology_map_truncGEπ_isIso
    (G : DerivedCategory.Minus B ⥤ DerivedCategory.Minus C)
    [G.CommShift ℤ] [G.IsTriangulated]
    (a q : ℤ) (hq : a ≤ q) (Y : DerivedCategory.Minus B)
    (h : (G.obj (((minusT B).truncLE (a-1)).obj Y)).obj.IsLE (a-1)) :
    IsIso ((minusHomology (B := C) q).map
      (G.map (((minusT B).truncGEπ a).app Y))) := by
  let t := minusT B
  let R := G ⋙ DerivedCategory.Minus.ι
  let T := (t.triangleLEGE (a-1) a (by omega)).obj Y
  have hT : R.mapTriangle.obj T ∈ distTriang (DerivedCategory C) :=
    R.map_distinguished _ (t.triangleLEGE_distinguished (a-1) a (by omega) Y)
  let H := DerivedCategory.homologyFunctor C 0
  have : (R.mapTriangle.obj T).obj₁.IsLE (a-1) := h
  have hz := DerivedCategory.isZero_of_isLE (R.mapTriangle.obj T).obj₁ (a-1) q (by omega)
  have hz' := DerivedCategory.isZero_of_isLE (R.mapTriangle.obj T).obj₁ (a-1) (q+1) (by omega)
  have : Mono ((H.shift q).map (R.mapTriangle.obj T).mor₂) :=
    (H.homologySequence_mono_shift_map_mor₂_iff _ hT q).2 (hz.eq_of_src _ _)
  have : Epi ((H.shift q).map (R.mapTriangle.obj T).mor₂) :=
    (H.homologySequence_epi_shift_map_mor₂_iff _ hT q (q+1) rfl).2 (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((H.shift q).map (R.mapTriangle.obj T).mor₂)

private lemma minus_homology_truncGEπ_isIso
    (Y : DerivedCategory.Minus B) (a q : ℤ) (hq : a ≤ q) :
    IsIso ((minusHomology (B := B) q).map (((minusT B).truncGEπ a).app Y)) :=
  minus_homology_map_truncGEπ_isIso (𝟭 _) a q hq Y
    (by
      change (((minusT B).truncLE (a-1)).obj Y).obj.IsLE (a-1)
      exact (ObjectProperty.tStructure_isLE_iff _ _ _ _).1 inferInstance)

private lemma minus_homology_truncLEι_isIso
    (Y : DerivedCategory.Minus B) (a q : ℤ) (hq : q ≤ a) :
    IsIso ((minusHomology (B := B) q).map (((minusT B).truncLEι a).app Y)) := by
  let t := minusT B
  let R := DerivedCategory.Minus.ι (C := B)
  let T := (t.triangleLEGE a (a+1) rfl).obj Y
  have hT : R.mapTriangle.obj T ∈ distTriang (DerivedCategory B) :=
    R.map_distinguished _ (t.triangleLEGE_distinguished a (a+1) rfl Y)
  let H := DerivedCategory.homologyFunctor B 0
  have : (R.mapTriangle.obj T).obj₃.IsGE (a+1) :=
    by
      change (((minusT B).truncGE (a+1)).obj Y).obj.IsGE (a+1)
      exact (ObjectProperty.tStructure_isGE_iff _ _ _ _).1 inferInstance
  have hz := DerivedCategory.isZero_of_isGE (R.mapTriangle.obj T).obj₃ (a+1) q (by omega)
  have hz' := DerivedCategory.isZero_of_isGE (R.mapTriangle.obj T).obj₃ (a+1) (q-1) (by omega)
  have : Epi ((H.shift q).map (R.mapTriangle.obj T).mor₁) :=
    (H.homologySequence_epi_shift_map_mor₁_iff _ hT q).2 (hz.eq_of_tgt _ _)
  have : Mono ((H.shift q).map (R.mapTriangle.obj T).mor₁) :=
    (H.homologySequence_mono_shift_map_mor₁_iff _ hT (q-1) q (by omega)).2 (hz'.eq_of_src _ _)
  exact isIso_of_mono_of_epi ((H.shift q).map (R.mapTriangle.obj T).mor₁)

private abbrev minusPointTruncation (k : ℤ) : DerivedCategory.Minus B ⥤ DerivedCategory.Minus B :=
  (minusT B).truncGE k ⋙ (minusT B).truncLE k

private instance minusPointTruncation_isGE (k : ℤ) (Y : DerivedCategory.Minus B) :
    ((minusPointTruncation k).obj Y).obj.IsGE k :=
  (ObjectProperty.tStructure_isGE_iff _ _ _ _).1 (by
    let t := minusT B
    change t.IsGE ((t.truncLE k).obj ((t.truncGE k).obj Y)) k
    infer_instance)

private instance minusPointTruncation_isLE (k : ℤ) (Y : DerivedCategory.Minus B) :
    ((minusPointTruncation k).obj Y).obj.IsLE k :=
  (ObjectProperty.tStructure_isLE_iff _ _ _ _).1 (by
    let t := minusT B
    change t.IsLE ((t.truncLE k).obj ((t.truncGE k).obj Y)) k
    infer_instance)

private def minusPointPureComponent (k : ℤ) (X : DerivedCategory.Minus B)
    [X.obj.IsGE k] [X.obj.IsLE k] :
    X ≅ (minusPoint B k).obj ((minusHomology k).obj X) := by
  let h := X.obj.exists_iso_singleFunctor_obj_of_isGE_of_isLE k
  let U := Classical.choose h
  let S := minusPoint B k
  let H := minusHomology (B := B) k
  let ε : S ⋙ H ≅ 𝟭 B := DerivedCategory.singleFunctorCompHomologyFunctorIso B k
  let a : X ≅ S.obj U := DerivedCategory.Minus.ι.preimageIso
    (Classical.choice (Classical.choose_spec h))
  let d : H.obj X ≅ U := H.mapIso a ≪≫ ε.app U
  exact a ≪≫ S.mapIso d.symm

private lemma minusPointPureComponent_normalization (k : ℤ) (X : DerivedCategory.Minus B)
    [X.obj.IsGE k] [X.obj.IsLE k] :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B k).inv.app ((minusHomology k).obj X) ≫
      (minusHomology k).map (minusPointPureComponent k X).inv = 𝟙 _ := by
  let h := X.obj.exists_iso_singleFunctor_obj_of_isGE_of_isLE k
  let U := Classical.choose h
  let S := minusPoint B k
  let H := minusHomology (B := B) k
  let ε : S ⋙ H ≅ 𝟭 B := DerivedCategory.singleFunctorCompHomologyFunctorIso B k
  let a : X ≅ S.obj U := DerivedCategory.Minus.ι.preimageIso
    (Classical.choice (Classical.choose_spec h))
  let d : H.obj X ≅ U := H.mapIso a ≪≫ ε.app U
  change ε.inv.app (H.obj X) ≫ H.map (S.map d.hom ≫ a.inv) = 𝟙 (H.obj X)
  rw [H.map_comp, ← Category.assoc]
  change (ε.inv.app (H.obj X) ≫ (S ⋙ H).map d.hom) ≫ H.map a.inv = _
  rw [← ε.inv.naturality, Functor.id_map]
  have e : H.map a.hom ≫ H.map a.inv = 𝟙 _ := (H.mapIso a).hom_inv_id
  change ( (H.map a.hom ≫ ε.hom.app U) ≫ ε.inv.app U) ≫ H.map a.inv = _
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact e

private lemma minusHomology_map_injective_from_point (k : ℤ)
    {X : DerivedCategory.Minus B} {U V : B} (e : X ≅ (minusPoint B k).obj V)
    {f g : (minusPoint B k).obj U ⟶ X}
    (h : (minusHomology k).map f = (minusHomology k).map g) : f = g := by
  let S := minusPoint B k
  let H := minusHomology (B := B) k
  let ε : S ⋙ H ≅ 𝟭 B := DerivedCategory.singleFunctorCompHomologyFunctorIso B k
  have : (S ⋙ DerivedCategory.Minus.ι).Full :=
    inferInstanceAs (DerivedCategory.singleFunctor B k).Full
  have : S.Full := Functor.Full.of_comp_faithful S DerivedCategory.Minus.ι
  have : (S ⋙ H).Faithful := Functor.Faithful.of_iso ε.symm
  obtain ⟨f', hf⟩ := S.map_surjective (f ≫ e.hom)
  obtain ⟨g', hg⟩ := S.map_surjective (g ≫ e.hom)
  have heq : (S ⋙ H).map f' = (S ⋙ H).map g' := by
    change H.map (S.map f') = H.map (S.map g')
    rw [hf, hg, H.map_comp, H.map_comp, h]
  exact (cancel_mono e.hom).1 (hf.symm.trans ((congrArg S.map ((S ⋙ H).map_injective heq)).trans hg))

private def minusPointTruncationPureIso (k : ℤ) :
    minusPointTruncation (B := B) k ≅ minusPointTruncation k ⋙ minusHomology k ⋙ minusPoint B k := by
  let T := minusPointTruncation (B := B) k
  let H := minusHomology (B := B) k
  let S := minusPoint B k
  let ε : S ⋙ H ≅ 𝟭 B := DerivedCategory.singleFunctorCompHomologyFunctorIso B k
  let e (Y : DerivedCategory.Minus B) := minusPointPureComponent k (T.obj Y)
  refine (NatIso.ofComponents (fun Y => (e Y).symm) ?_).symm
  intro X Y f
  apply minusHomology_map_injective_from_point k (e Y)
  apply (cancel_epi (ε.inv.app (H.obj (T.obj X)))).1
  have hX : ε.inv.app (H.obj (T.obj X)) ≫ H.map (e X).inv = 𝟙 _ :=
    minusPointPureComponent_normalization k (T.obj X)
  have hY : ε.inv.app (H.obj (T.obj Y)) ≫ H.map (e Y).inv = 𝟙 _ :=
    minusPointPureComponent_normalization k (T.obj Y)
  change ε.inv.app (H.obj (T.obj X)) ≫ H.map (S.map (H.map (T.map f)) ≫ (e Y).inv) =
    ε.inv.app (H.obj (T.obj X)) ≫ H.map ((e X).inv ≫ T.map f)
  simp only [H.map_comp, ← Category.assoc]
  change ((ε.inv.app (H.obj (T.obj X)) ≫ (S ⋙ H).map (H.map (T.map f))) ≫ H.map (e Y).inv) =
    (ε.inv.app (H.obj (T.obj X)) ≫ H.map (e X).inv) ≫ H.map (T.map f)
  rw [← ε.inv.naturality, Functor.id_map, Category.assoc, hX, hY,
    Category.comp_id, Category.id_comp]

private lemma minusPointTruncationPureIso_normalization (k : ℤ) (Y : DerivedCategory.Minus B) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B k).inv.app
      ((minusHomology k).obj ((minusPointTruncation k).obj Y)) ≫
    (minusHomology k).map ((minusPointTruncationPureIso k).inv.app Y) = 𝟙 _ :=
  minusPointPureComponent_normalization k ((minusPointTruncation k).obj Y)

private def minusPointTruncationHomologyIso (k : ℤ) :
    minusPointTruncation (B := B) k ⋙ minusHomology k ≅ minusHomology k := by
  let t := minusT B
  let H := minusHomology (B := B) k
  let α := whiskerRight (t.truncGEπ k) H
  let β := whiskerRight (whiskerLeft (t.truncGE k) (t.truncLEι k)) H
  have (Y : DerivedCategory.Minus B) : IsIso (α.app Y) :=
    minus_homology_truncGEπ_isIso Y k k le_rfl
  have (Y : DerivedCategory.Minus B) : IsIso (β.app Y) :=
    minus_homology_truncLEι_isIso ((t.truncGE k).obj Y) k k le_rfl
  have : IsIso α := NatIso.isIso_of_isIso_app _
  have : IsIso β := NatIso.isIso_of_isIso_app _
  exact asIso β ≪≫ (asIso α).symm

private def minusPointTruncationIso (k : ℤ) :
    minusPointTruncation (B := B) k ≅ minusHomology k ⋙ minusPoint B k :=
  minusPointTruncationPureIso k ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight (minusPointTruncationHomologyIso k) (minusPoint B k)

private lemma minusPointTruncationIso_normalization (k : ℤ) (Y : DerivedCategory.Minus B) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso B k).inv.app
      ((minusHomology k).obj Y) ≫
    (minusHomology k).map ((minusPointTruncationIso k).inv.app Y ≫
        ((minusT B).truncLEι k).app (((minusT B).truncGE k).obj Y)) =
    (minusHomology k).map (((minusT B).truncGEπ k).app Y) := by
  let H := minusHomology (B := B) k
  let S := minusPoint B k
  let ε : S ⋙ H ≅ 𝟭 B := DerivedCategory.singleFunctorCompHomologyFunctorIso B k
  let θ := (minusPointTruncationPureIso (B := B) k).app Y
  let h := (minusPointTruncationHomologyIso (B := B) k).app Y
  let α := H.map (((minusT B).truncGEπ k).app Y)
  let β := H.map (((minusT B).truncLEι k).app (((minusT B).truncGE k).obj Y))
  have hθ : ε.inv.app ((minusPointTruncation k ⋙ minusHomology k).obj Y) ≫
      H.map θ.inv = 𝟙 _ :=
    minusPointTruncationPureIso_normalization k Y
  simp only [minusPointTruncationIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    isoWhiskerRight_inv, whiskerRight_app, associator_hom_app, Category.comp_id]
  change ε.inv.app (H.obj Y) ≫ H.map ((S.map h.inv ≫ θ.inv) ≫ _) = α
  simp only [Functor.map_comp, Category.assoc]
  change ε.inv.app (H.obj Y) ≫ (S ⋙ H).map h.inv ≫ H.map θ.inv ≫ β = α
  rw [← Category.assoc, ← ε.inv.naturality h.inv, Functor.id_map, Category.assoc,
    ← Category.assoc (ε.inv.app _), hθ, Category.id_comp]
  have : IsIso α := minus_homology_truncGEπ_isIso Y k k le_rfl
  have : IsIso β :=
    minus_homology_truncLEι_isIso (((minusT B).truncGE k).obj Y) k k le_rfl
  change (minusPointTruncationHomologyIso (B := B) k).inv.app Y ≫ β = α
  simp only [minusPointTruncationHomologyIso, Iso.trans_inv, Iso.symm_inv,
    asIso_hom, asIso_inv, NatTrans.comp_app, NatIso.isIso_inv_app,
    whiskerRight_app, whiskerLeft_app]
  change (α ≫ inv β) ≫ β = α
  simp

section

variable [(minus B).IsTriangulated] [(minus C).IsTriangulated] [EnoughProjectives B]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteColimits G] (LG : ExactLeftData G)

lemma pointComparison_isIso (k : ℤ) (Z : B) : IsIso (pointComparison G LG k Z) := by
  let M := minusPointModel B k Z
  have : CochainComplex.IsStrictlyLE M.obj.as k := by
    change ((CochainComplex.singleFunctor B k).obj Z).IsStrictlyLE k
    infer_instance
  have : IsIso ((minusHomology (B := C) k).map (LG.counit.app M)) :=
    AcyclicTermComparison.leftComparison_highest_degree G LG M k
  unfold pointComparison stalkCounit
  simp only [Functor.map_comp]
  infer_instance

def dualTruncation (k : ℤ) : DualTruncation (G := G) (LG := LG) k := by
  let α := whiskerRight ((minusT B).truncGEπ k) (LG.functor ⋙ minusHomology (B := C) k)
  letI := LG.commShift
  letI := LG.triangulated
  have (Y : DerivedCategory.Minus B) : IsIso (α.app Y) :=
    minus_homology_map_truncGEπ_isIso LG.functor k k le_rfl Y
      (leftDerived_preserves_isLE G LG _ _)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact
    { upper := asIso α
      upper_hom := rfl
      point := minusPointTruncationIso k
      point_normalization := minusPointTruncationIso_normalization k
      stalk Z := by
        have := pointComparison_isIso G LG k Z
        exact asIso (pointComparison G LG k Z)
      stalk_hom _ := rfl }

end
end LeftTruncation

section ReverseTruncation

variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{max u₂ v₂} Bᵒᵖ]
  (OB : DerivedReversal B)

private abbrev plusT (B : Type*) [Category* B] [Abelian B] [HasDerivedCategory B] :=
  DerivedCategory.Plus.TStructure.t (C := B)

lemma reverse_isLE (Y : DerivedCategory.Minus B) (n : ℤ) [(minusT B).IsGE Y (-n)] :
    (OB.functor.obj (op Y)).IsLE n := by
  have hY : Y.obj.IsGE (-n) :=
    (ObjectProperty.tStructure_isGE_iff _ _ _ _).1 inferInstance
  apply (DerivedCategory.Plus.isLE_ι_obj_iff _ _).1
  apply (DerivedCategory.isLE_iff _ _).2
  intro j hj
  have hz := DerivedCategory.isZero_of_isGE Y.obj (-n) (-j) (by omega)
  exact hz.op.of_iso ((OB.homology j).app (op Y))

lemma reverse_isGE (Y : DerivedCategory.Minus B) (n : ℤ) [(minusT B).IsLE Y (-n)] :
    (OB.functor.obj (op Y)).IsGE n := by
  have hY : Y.obj.IsLE (-n) :=
    (ObjectProperty.tStructure_isLE_iff _ _ _ _).1 inferInstance
  apply (DerivedCategory.Plus.isGE_ι_obj_iff _ _).1
  apply (DerivedCategory.isGE_iff _ _).2
  intro j hj
  have hz := DerivedCategory.isZero_of_isLE Y.obj (-n) (-j) (by omega)
  exact hz.op.of_iso ((OB.homology j).app (op Y))

private def reverseTruncGEMap (n : ℤ) (Y : DerivedCategory.Minus B) :
    OB.functor.obj (op (((minusT B).truncGE (-n)).obj Y)) ⟶
      ((plusT Bᵒᵖ).truncLE n).obj (OB.functor.obj (op Y)) := by
  have := reverse_isLE OB (((minusT B).truncGE (-n)).obj Y) n
  exact (plusT Bᵒᵖ).liftTruncLT (OB.functor.map (((minusT B).truncGEπ (-n)).app Y).op)
    n (n+1) rfl

private lemma reverseTruncGEMap_ι (n : ℤ) (Y : DerivedCategory.Minus B) :
    reverseTruncGEMap OB n Y ≫
      ((plusT Bᵒᵖ).truncLEι n).app (OB.functor.obj (op Y)) =
    OB.functor.map (((minusT B).truncGEπ (-n)).app Y).op := by
  have := reverse_isLE OB (((minusT B).truncGE (-n)).obj Y) n
  exact (plusT Bᵒᵖ).liftTruncLT_ι (OB.functor.map (((minusT B).truncGEπ (-n)).app Y).op)
    n (n+1) rfl

variable [EnoughInjectives Bᵒᵖ]

def reverseTruncGE (n : ℤ) (Y : DerivedCategory.Minus B) :
    OB.functor.obj (op (((minusT B).truncGE (-n)).obj Y)) ≅
      ((plusT Bᵒᵖ).truncLE n).obj (OB.functor.obj (op Y)) := by
  let H (j : ℤ) := DerivedCategory.Plus.homologyFunctor Bᵒᵖ j
  have : IsIso (reverseTruncGEMap OB n Y) := by
    rw [DerivedCategory.Plus.isIso_iff]
    intro j
    by_cases hj : j ≤ n
    · have : IsIso ((H j).map (((plusT Bᵒᵖ).truncLEι n).app (OB.functor.obj (op Y)))) :=
        GrothendieckEdges.homology_truncLEι_isIso _ n j hj
      have : IsIso ((H j).map (OB.functor.map (((minusT B).truncGEπ (-n)).app Y).op)) := by
        apply (NatIso.isIso_map_iff (OB.homology j) _).2
        change IsIso (((minusHomology (-j)).map (((minusT B).truncGEπ (-n)).app Y)).op)
        have := minus_homology_truncGEπ_isIso Y (-n) (-j) (by omega)
        infer_instance
      have : IsIso ((H j).map (reverseTruncGEMap OB n Y) ≫
          (H j).map (((plusT Bᵒᵖ).truncLEι n).app (OB.functor.obj (op Y)))) := by
        rw [← Functor.map_comp, reverseTruncGEMap_ι]
        infer_instance
      exact IsIso.of_isIso_comp_right _ ((H j).map (((plusT Bᵒᵖ).truncLEι n).app (OB.functor.obj (op Y))))
    · have := reverse_isLE OB (((minusT B).truncGE (-n)).obj Y) n
      exact IsZero.isIso (DerivedCategory.Plus.isZero_homology_of_isLE _ n j (by omega))
        (DerivedCategory.Plus.isZero_homology_of_isLE _ n j (by omega)) _
  exact asIso (reverseTruncGEMap OB n Y)

@[reassoc] lemma reverseTruncGE_hom_ι (n : ℤ) (Y : DerivedCategory.Minus B) :
    (reverseTruncGE OB n Y).hom ≫ ((plusT Bᵒᵖ).truncLEι n).app (OB.functor.obj (op Y)) =
    OB.functor.map (((minusT B).truncGEπ (-n)).app Y).op :=
  reverseTruncGEMap_ι OB n Y

end ReverseTruncation

section ReversePointSpan

variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B] [EnoughInjectives B]

private lemma plus_homology_map_to_point_injective
    (n : ℤ) {X : DerivedCategory.Plus B} [X.IsLE n] {U : B}
    {f g : X ⟶ (DerivedCategory.Plus.singleFunctor B n).obj U}
    (h : (DerivedCategory.Plus.homologyFunctor B n).map f =
      (DerivedCategory.Plus.homologyFunctor B n).map g) : f = g := by
  let t := plusT B
  let S := DerivedCategory.Plus.singleFunctor B n
  let H := DerivedCategory.Plus.homologyFunctor B n
  let f' := t.descTruncGE f n
  let g' := t.descTruncGE g n
  have e₁ : (t.truncGEπ n).app X ≫ f' = f := t.π_descTruncGE f n
  have e₂ : (t.truncGEπ n).app X ≫ g' = g := t.π_descTruncGE g n
  suffices f' = g' by rw [← e₁, ← e₂, this]
  let X' := (t.truncGE n).obj X
  have : X'.IsLE n := by dsimp only [X']; infer_instance
  have : X'.IsGE n := by dsimp only [X']; infer_instance
  apply DerivedCategory.Plus.ι.map_injective
  apply GrothendieckEdges.pure_homology_map_injective n
  change H.map f' = H.map g'
  have : IsIso (H.map ((t.truncGEπ n).app X)) := GrothendieckEdges.homology_truncGEπ_isIso X n n le_rfl
  apply (cancel_epi (H.map ((t.truncGEπ n).app X))).1
  rw [← H.map_comp, ← H.map_comp, e₁, e₂]
  exact h

omit [EnoughInjectives B] in
lemma reverseTruncationToSingle [HasDerivedCategory.{max u₂ v₂} Bᵒᵖ] [EnoughInjectives Bᵒᵖ] (OB : DerivedReversal B) (n : ℤ) (Y : DerivedCategory.Minus B)
    (p : (minusPoint B (-n)).obj ((minusHomology (-n)).obj Y) ⟶ ((minusT B).truncGE (-n)).obj Y)
    (hp : (DerivedCategory.singleFunctorCompHomologyFunctorIso B (-n)).inv.app
        ((minusHomology (-n)).obj Y) ≫ (minusHomology (-n)).map p =
      (minusHomology (-n)).map (((minusT B).truncGEπ (-n)).app Y))
    (s : OB.functor.obj (op ((minusPoint B (-n)).obj ((minusHomology (-n)).obj Y))) ≅
      (DerivedCategory.Plus.singleFunctor Bᵒᵖ n).obj (op ((minusHomology (-n)).obj Y)))
    (hs : (DerivedCategory.Plus.homologyFunctor Bᵒᵖ n).map s.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso Bᵒᵖ n).hom.app
        (op ((minusHomology (-n)).obj Y)) =
      (OB.homology n).hom.app (op ((minusPoint B (-n)).obj ((minusHomology (-n)).obj Y))) ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso B (-n)).inv.app
          ((minusHomology (-n)).obj Y)).op) :
    (reverseTruncGE OB n Y).inv ≫ OB.functor.map p.op ≫ s.hom ≫
      (DerivedCategory.Plus.singleFunctor Bᵒᵖ n).map ((OB.homology n).inv.app (op Y)) =
      (GrothendieckEdges.truncationToSingle (B := Bᵒᵖ) n).app (OB.functor.obj (op Y)) := by
  let J := DerivedCategory.Plus.homologyFunctor Bᵒᵖ n
  let H := minusHomology (B := B) (-n)
  let S := DerivedCategory.Plus.singleFunctor Bᵒᵖ n
  let D := OB.functor
  let ζ := OB.homology n
  let e := reverseTruncGE OB n Y
  let εR : S ⋙ J ≅ 𝟭 Bᵒᵖ := GrothendieckEdges.singlePlusHomologyIso n
  let εL := DerivedCategory.singleFunctorCompHomologyFunctorIso B (-n)
  let q := ((minusT B).truncGEπ (-n)).app Y
  let i := ((plusT Bᵒᵖ).truncLEι n).app (D.obj (op Y))
  apply plus_homology_map_to_point_injective n
  apply (cancel_mono (εR.hom.app (J.obj (D.obj (op Y))))).1
  have hr : J.map ((GrothendieckEdges.truncationToSingle n).app (D.obj (op Y))) ≫
      εR.hom.app (J.obj (D.obj (op Y))) = J.map i :=
    GrothendieckEdges.truncationToSingle_normalization n (D.obj (op Y))
  rw [hr]
  change J.map (e.inv ≫ D.map p.op ≫ s.hom ≫ S.map (ζ.inv.app (op Y))) ≫
    εR.hom.app (J.obj (D.obj (op Y))) = J.map i
  simp only [Functor.map_comp, Category.assoc]
  have hn := εR.hom.naturality (ζ.inv.app (op Y))
  change J.map (S.map (ζ.inv.app (op Y))) ≫ εR.hom.app (J.obj (D.obj (op Y))) =
    εR.hom.app (op (H.obj Y)) ≫ ζ.inv.app (op Y) at hn
  have hnp := ζ.hom.naturality p.op
  change J.map (D.map p.op) ≫ ζ.hom.app (op ((minusPoint B (-n)).obj (H.obj Y))) =
    ζ.hom.app (op (((minusT B).truncGE (-n)).obj Y)) ≫ (H.map p).op at hnp
  have hq := ζ.hom.naturality q.op
  change J.map (D.map q.op) ≫ ζ.hom.app (op Y) =
    ζ.hom.app (op (((minusT B).truncGE (-n)).obj Y)) ≫ (H.map q).op at hq
  change J.map s.hom ≫ εR.hom.app (op (H.obj Y)) =
      ζ.hom.app (op ((minusPoint B (-n)).obj (H.obj Y))) ≫
        (εL.inv.app (H.obj Y)).op at hs
  change εL.inv.app (H.obj Y) ≫ H.map p = H.map q at hp
  have hmap : J.map (D.map p.op) ≫ J.map s.hom ≫ εR.hom.app (op (H.obj Y)) =
      ζ.hom.app (op (((minusT B).truncGE (-n)).obj Y)) ≫ (H.map q).op := by
    rw [hs, ← Category.assoc, hnp, Category.assoc, ← op_comp, hp]
  rw [hn, ← Category.assoc (J.map s.hom), ← Category.assoc (J.map (D.map p.op)), hmap, ← hq]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id, ← J.map_comp]
  have hi : D.map q.op = e.hom ≫ i := (reverseTruncGE_hom_ι OB n Y).symm
  rw [hi, e.inv_hom_id_assoc]

end ReversePointSpan

section ReverseColumnSpan

open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {B : Type u₂} {C : Type u₃} [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
  [HasDerivedCategory.{max u₂ v₂} Bᵒᵖ] [HasDerivedCategory.{max u₃ v₃} Cᵒᵖ]
  [(minus B).IsTriangulated] [(minus C).IsTriangulated] [EnoughInjectives Bᵒᵖ]

omit [HasDerivedCategory B] [HasDerivedCategory C] [(minus B).IsTriangulated]
  [(minus C).IsTriangulated] in
private lemma columnPoint_eq {G : Bᵒᵖ ⥤ Cᵒᵖ} [G.Additive] {n : ℤ}
    (T : GrothendieckEdges.ColumnTruncation G n) (Y : DerivedCategory.Plus Bᵒᵖ) :
    ((plusT Bᵒᵖ).truncGEπ n).app (((plusT Bᵒᵖ).truncLE n).obj Y) ≫ T.point.hom.app Y =
      (GrothendieckEdges.truncationToSingle n).app Y := by
  apply plus_homology_map_to_point_injective n (X := ((plusT Bᵒᵖ).truncLE n).obj Y)
  let H := DerivedCategory.Plus.homologyFunctor Bᵒᵖ n
  apply (cancel_mono ((GrothendieckEdges.singlePlusHomologyIso n).hom.app (H.obj Y))).1
  exact (T.point_normalization Y).trans (GrothendieckEdges.truncationToSingle_normalization n Y).symm

lemma reverseColumnEdge {G : B ⥤ C} [G.Additive] {LG : ExactLeftData G}
    (OB : DerivedReversal B) (n : ℤ) (T : DualTruncation (G := G) (LG := LG) (-n))
    (R : GrothendieckEdges.ColumnTruncation G.op n) (e₀ : rightValue G.op 0 ≅ G.op)
    (Ω : OB.functor ⋙ (G.op.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor Cᵒᵖ n) ≅ (LG.functor ⋙ minusHomology (-n)).op)
    (Y : DerivedCategory.Minus B)
    (s : OB.functor.obj (op ((minusPoint B (-n)).obj ((minusHomology (-n)).obj Y))) ≅
      (DerivedCategory.Plus.singleFunctor Bᵒᵖ n).obj (op ((minusHomology (-n)).obj Y)))
    (hs : (DerivedCategory.Plus.homologyFunctor Bᵒᵖ n).map s.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso Bᵒᵖ n).hom.app
        (op ((minusHomology (-n)).obj Y)) =
      (OB.homology n).hom.app (op ((minusPoint B (-n)).obj ((minusHomology (-n)).obj Y))) ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso B (-n)).inv.app
          ((minusHomology (-n)).obj Y)).op)
    (hsG : (G.op.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor Cᵒᵖ n).map s.hom ≫
        (GrothendieckEdges.shiftedStalkValueIso G.op n ≪≫ e₀).hom.app (op ((minusHomology (-n)).obj Y)) =
      Ω.hom.app (op ((minusPoint B (-n)).obj ((minusHomology (-n)).obj Y))) ≫
        (T.stalk ((minusHomology (-n)).obj Y)).inv.op)
    {Y' : DerivedCategory.Plus Bᵒᵖ} (f : Y' ⟶ OB.functor.obj (op Y)) :
    (R.edge G.op e₀).app Y' ≫ G.op.map
      ((DerivedCategory.Plus.homologyFunctor Bᵒᵖ n).map f ≫ (OB.homology n).hom.app (op Y)) =
    (G.op.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor Cᵒᵖ n).map f ≫
      Ω.hom.app (op Y) ≫
        (T.upper.inv.app Y).op ≫
        ((LG.functor ⋙ minusHomology (-n)).map
          (T.point.inv.app Y ≫ ((minusT B).truncLEι (-n)).app (((minusT B).truncGE (-n)).obj Y))).op ≫
        (T.stalk ((minusHomology (-n)).obj Y)).inv.op := by
  let D := OB.functor
  let ζ := OB.homology n
  let Z := D.obj (op Y)
  let H := minusHomology (B := B) (-n)
  let J := DerivedCategory.Plus.homologyFunctor Bᵒᵖ n
  let K := G.op.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor Cᵒᵖ n
  let L := LG.functor ⋙ minusHomology (B := C) (-n)
  let S := DerivedCategory.Plus.singleFunctor Bᵒᵖ n
  let X := ((minusT B).truncGE (-n)).obj Y
  let V := (minusPoint B (-n)).obj (H.obj Y)
  let b := R.lower.app Z
  let c := T.upper.app Y
  let e := reverseTruncGE OB n Y
  let q := ((minusT B).truncGEπ (-n)).app Y
  let i := ((plusT Bᵒᵖ).truncLEι n).app Z
  let p : V ⟶ X := T.point.inv.app Y ≫ ((minusT B).truncLEι (-n)).app X
  let w := GrothendieckEdges.shiftedStalkValueIso G.op n ≪≫ e₀
  let ρ := (GrothendieckEdges.truncationToSingle n).app Z
  let t := (T.stalk (H.obj Y)).inv.op
  have h := ((R.edge G.op e₀).naturality_assoc f (G.op.map (ζ.hom.app (op Y)))).symm
  change (R.edge G.op e₀).app Y' ≫ G.op.map (J.map f) ≫ G.op.map (ζ.hom.app (op Y)) =
      K.map f ≫ (R.edge G.op e₀).app Z ≫ G.op.map (ζ.hom.app (op Y)) at h
  rw [Functor.map_comp, h]
  apply congrArg (K.map f ≫ ·)
  have hρ : (R.edge G.op e₀).app Z = b.inv ≫ K.map ρ ≫ w.hom.app (J.obj Z) := by
    unfold GrothendieckEdges.ColumnTruncation.edge
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      associator_hom_app, Category.id_comp]
    rw [columnPoint_eq R Z]
    rfl
  change (R.edge G.op e₀).app Z ≫ G.op.map (ζ.hom.app (op Y)) =
    Ω.hom.app (op Y) ≫ c.inv.op ≫ (L.map p).op ≫ t
  rw [hρ]
  have hb : b.hom = K.map i := by
    change R.lower.hom.app Z = _
    rw [R.lower_hom]
    rfl
  have hc : c.hom = L.map q := by
    change T.upper.hom.app Y = _
    rw [T.upper_hom]
    rfl
  have hw := w.hom.naturality_assoc (ζ.inv.app (op Y)) (G.op.map (ζ.hom.app (op Y)))
  change K.map (S.map (ζ.inv.app (op Y))) ≫ w.hom.app (J.obj Z) ≫
      G.op.map (ζ.hom.app (op Y)) =
    w.hom.app (op (H.obj Y)) ≫ G.op.map (ζ.inv.app (op Y)) ≫ G.op.map (ζ.hom.app (op Y)) at hw
  rw [← G.op.map_comp, ζ.inv_hom_id_app] at hw
  erw [G.op.map_id, Category.comp_id] at hw
  have hmap : K.map e.hom ≫ b.hom = K.map (D.map q.op) := by
    rw [hb, ← Functor.map_comp]
    exact congrArg K.map (reverseTruncGE_hom_ι OB n Y)
  have hΩp := Ω.hom.naturality_assoc p.op t
  change K.map (D.map p.op) ≫ Ω.hom.app (op V) ≫ t =
    Ω.hom.app (op X) ≫ (L.map p).op ≫ t at hΩp
  have hΩq := Ω.hom.naturality_assoc q.op (c.inv.op ≫ (L.map p).op ≫ t)
  change K.map (D.map q.op) ≫ Ω.hom.app (op Y) ≫ c.inv.op ≫ (L.map p).op ≫ t =
    Ω.hom.app (op X) ≫ (L.map q).op ≫ c.inv.op ≫ (L.map p).op ≫ t at hΩq
  have hρ' : e.inv ≫ D.map p.op ≫ s.hom ≫ S.map (ζ.inv.app (op Y)) = ρ :=
    reverseTruncationToSingle OB n Y p (T.point_normalization Y) s hs
  have hρe : e.hom ≫ ρ = D.map p.op ≫ s.hom ≫ S.map (ζ.inv.app (op Y)) := by
    rw [← hρ', e.hom_inv_id_assoc]
  have ht : K.map s.hom ≫ w.hom.app (op (H.obj Y)) = Ω.hom.app (op V) ≫ t := hsG
  apply (cancel_epi (K.map e.hom ≫ b.hom)).1
  simp only [Category.assoc, b.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, hρe]
  simp only [Functor.map_comp, Category.assoc]
  rw [hw, ht, hΩp]
  rw [← Category.assoc (K.map e.hom) b.hom, hmap, hΩq, ← hc]
  have hc' : c.hom.op ≫ c.inv.op = 𝟙 _ := by rw [← op_comp, c.inv_hom_id]; rfl
  rw [reassoc_of% hc']

end ReverseColumnSpan

section DerivedHomologyReversal

open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

variable {B : Type u₂} {C : Type u₃} [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
  [HasDerivedCategory.{max u₂ v₂} Bᵒᵖ] [HasDerivedCategory.{max u₃ v₃} Cᵒᵖ]
  [(minus B).IsTriangulated] [(minus C).IsTriangulated] [EnoughInjectives Bᵒᵖ]
  (G : B ⥤ C) [G.Additive] (LG : ExactLeftData G)
  (OB : DerivedReversal B) (OC : DerivedReversal C)
  (OG : ReversedDerivedFunctor G LG OB OC)

def reversedDerivedHomology (n : ℤ) :
    OB.functor ⋙ G.op.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor Cᵒᵖ n ≅
      (LG.functor ⋙ minusHomology (B := C) (-n)).op :=
  (associator _ _ _).symm ≪≫
    isoWhiskerRight OG.iso.symm _ ≪≫ (associator _ _ _) ≪≫
    isoWhiskerLeft LG.functor.op (OC.homology n)

@[simp] lemma reversedDerivedHomology_hom_app (n : ℤ) (Y : DerivedCategory.Minus B) :
    (reversedDerivedHomology G LG OB OC OG n).hom.app (op Y) =
      (DerivedCategory.Plus.homologyFunctor Cᵒᵖ n).map (OG.iso.inv.app (op Y)) ≫
        (OC.homology n).hom.app (op (LG.functor.obj Y)) := by
  simp [reversedDerivedHomology]

lemma reversedColumnStalk [PreservesFiniteLimits G.op] (n : ℤ)
    (T : DualTruncation (G := G) (LG := LG) (-n)) (e₀ : rightValue G.op 0 ≅ G.op)
    (he₀ : e₀.inv = GrothendieckEdges.degreeZeroUnit G.op) (X : B) :
    (G.op.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor Cᵒᵖ n).map
      (reversedPoint OB n X).hom ≫ (GrothendieckEdges.shiftedStalkValueIso G.op n ≪≫ e₀).hom.app (op X) =
    (reversedDerivedHomology G LG OB OC OG n).hom.app (op ((minusPoint B (-n)).obj X)) ≫
      (T.stalk X).inv.op := by
  let K := G.op.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor Cᵒᵖ n
  let S := (minusPoint B (-n)).obj X
  let s := reversedPoint OB n X
  let a := (reversedDerivedHomology G LG OB OC OG n).app (op S)
  let v := reversedPointValue G LG OB OC OG n X
  let w := GrothendieckEdges.rightDerivedStalkHomologyIso G.op n
  let t := T.stalk X
  have hv : w.inv.app (op X) ≫ v.hom = t.hom.op := by
    rw [T.stalk_hom]
    exact reversedPointValue_rightStalk G LG OB OC OG n X
  have hz : e₀ = GrothendieckEdges.canonicalRightZeroIso G.op := by
    apply Iso.symm_eq_iff.mp
    apply Iso.ext
    exact he₀
  have hw : w.hom.app (op X) = v.hom ≫ t.inv.op := by
    apply (cancel_epi (w.inv.app (op X))).1
    erw [w.inv_hom_id_app, ← Category.assoc, hv, ← op_comp, t.inv_hom_id]
    rfl
  have hs : K.map s.hom ≫ v.hom = a.hom := by
    let H := DerivedCategory.Plus.homologyFunctor Cᵒᵖ n
    let U := G.op.rightDerivedFunctorPlus
    change K.map s.hom ≫ (reversedPointValue G LG OB OC OG n X).hom =
      (reversedDerivedHomology G LG OB OC OG n).hom.app (op S)
    rw [reversedDerivedHomology_hom_app]
    change H.map (U.map s.hom) ≫ H.map (U.map s.inv ≫ OG.iso.inv.app (op S)) ≫
        (OC.homology n).hom.app (op (LG.functor.obj S)) = _
    have h : H.map (U.map s.hom) ≫ H.map (U.map s.inv) = 𝟙 _ := ((U ⋙ H).mapIso s).hom_inv_id
    rw [H.map_comp, Category.assoc, reassoc_of% h]
  rw [hz]
  change K.map s.hom ≫ w.hom.app (op X) = a.hom ≫ t.inv.op
  rw [hw, ← Category.assoc, hs]

end DerivedHomologyReversal
section Assembly
open GrothendieckSpectralSequence HypercohomologyDerivedNaturality G05FilteredEdges

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Abelian A] [Category.{v₂} B] [Abelian B]
  [Category.{v₃} C] [Abelian C]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
  [HasDerivedCategory.{max u₁ v₁} Aᵒᵖ] [HasDerivedCategory.{max u₂ v₂} Bᵒᵖ] [HasDerivedCategory.{max u₃ v₃} Cᵒᵖ]
  [(minus A).IsTriangulated] [(minus B).IsTriangulated] [(minus C).IsTriangulated]
  [(QMinus A).IsLocalization (WMinus A)] [(QMinus B).IsLocalization (WMinus B)]
  [(QMinus C).IsLocalization (WMinus C)]
  [EnoughProjectives A] [EnoughProjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  (LF : ExactLeftData F) (LG : ExactLeftData G) (LFG : ExactLeftData (F ⋙ G))

variable (R : GrothendieckSpectralSequence.Package F.op G.op)

private abbrev rightSequence :=
  GrothendieckSpectralSequence.sequence F.op G.op R.row

private abbrev dualSequence : DerivedCategory.Minus A ⥤ HomologicalDiagram C :=
  (derivedDual A ⋙ rightSequence F G R).rightOp

private def dualRowPresentationIso :
    (dualSequence F G R).leftOp ≅ LF.functor.op ⋙ derivedDual B ⋙ R.row.derived :=
  Functor.rightOpLeftOpIso _ ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight (deriveDual F LF).symm _ ≪≫ associator _ _ _

private def dualSecondIso (p : ℕ) (q : ℤ) :
    dualSequence F G R ⋙ homologicalPage 0 p ((p : ℤ)+q) ≅
      LF.functor ⋙ homologicalHomology q ⋙ leftValue G LG p := by
  let H := DerivedCategory.Plus.homologyFunctor Bᵒᵖ q
  let V := rightValue G.op p
  let J := LF.functor.op ⋙ derivedDual B
  have e : (dualSequence F G R).leftOp ⋙ pageEval 0 p ((p : ℤ)+q) ≅
      (LF.functor ⋙ homologicalHomology q ⋙ leftValue G LG p).op := calc
    _ ≅ (J ⋙ R.row.derived) ⋙ pageEval 0 p ((p : ℤ)+q) :=
      isoWhiskerRight (dualRowPresentationIso F G LF R ≪≫ (associator _ _ _).symm) _
    _ ≅ J ⋙ H ⋙ V := associator _ _ _ ≪≫ isoWhiskerLeft J (R.coordinates.second p q)
    _ ≅ LF.functor.op ⋙ (homologicalHomology (C := B) q).op ⋙ V :=
      associator _ _ _ ≪≫ isoWhiskerLeft _
        ((associator _ _ _).symm ≪≫ isoWhiskerRight (derivedHomologyDual B q) V)
    _ ≅ LF.functor.op ⋙ (homologicalHomology (C := B) q).op ⋙ (leftValue G LG p).op :=
      isoWhiskerLeft _ (isoWhiskerLeft _ (classicalDual G LG p))
    _ ≅ _ := (isoWhiskerLeft _ (opComp _ _).symm) ≪≫ (opComp _ _).symm
  exact (NatIso.unop e).symm ≪≫ opUnopIso _

private def dualIteratedIso (n : ℤ) :
    dualSequence F G R ⋙ homologicalTarget n ≅
      (LF.functor ⋙ LG.functor) ⋙ homologicalHomology n := by
  let H := DerivedCategory.Plus.homologyFunctor Cᵒᵖ n
  let J := LF.functor.op ⋙ derivedDual B
  have e : (dualSequence F G R).leftOp ⋙ targetEval n ≅
      ((LF.functor ⋙ LG.functor) ⋙ homologicalHomology n).op := calc
    _ ≅ (J ⋙ R.row.derived) ⋙ targetEval n :=
      isoWhiskerRight (dualRowPresentationIso F G LF R ≪≫ (associator _ _ _).symm) _
    _ ≅ J ⋙ G.op.rightDerivedFunctorPlus ⋙ H :=
      associator _ _ _ ≪≫ isoWhiskerLeft J (R.coordinates.target n)
    _ ≅ LF.functor.op ⋙ (LG.functor.op ⋙ derivedDual C) ⋙ H :=
      associator _ _ _ ≪≫ isoWhiskerLeft _
        ((associator _ _ _).symm ≪≫ isoWhiskerRight (deriveDual G LG).symm _)
    _ ≅ LF.functor.op ⋙ LG.functor.op ⋙ (homologicalHomology (C := C) n).op :=
      isoWhiskerLeft _ (associator _ _ _ ≪≫ isoWhiskerLeft _ (derivedHomologyDual C n))
    _ ≅ _ := (associator _ _ _).symm ≪≫ isoWhiskerRight (opComp _ _).symm _ ≪≫ (opComp _ _).symm
  exact (NatIso.unop e).symm ≪≫ opUnopIso _

private theorem dualRowSecond_app (X : DerivedCategory.Minus A) (p : ℕ) (q : ℤ) :
    ((dualSecondIso F G LF LG R p q).inv.app X).op =
      ((dualRowPresentationIso F G LF R).hom.app (op X)).page 0 p ((p : ℤ) + q) ≫
      (R.coordinates.second p q).hom.app ((derivedDual B).obj (op (LF.functor.obj X))) ≫
      (rightValue G.op p).map
        ((derivedHomologyDual B q).hom.app (op (LF.functor.obj X))) ≫
      (classicalDual G LG p).hom.app
        (op ((homologicalHomology (C := B) q).obj (LF.functor.obj X))) := by
  simp [dualSecondIso, pageEval, Category.assoc]
  erw [Category.id_comp]

private theorem dualRowTarget_app (X : DerivedCategory.Minus A) (n : ℤ) :
    ((dualIteratedIso F G LF LG R n).inv.app X).op =
      ((dualRowPresentationIso F G LF R).hom.app (op X)).target n ≫
      (R.coordinates.target n).hom.app ((derivedDual B).obj (op (LF.functor.obj X))) ≫
      (DerivedCategory.Plus.homologyFunctor Cᵒᵖ n).map
        ((deriveDual G LG).inv.app (op (LF.functor.obj X))) ≫
      (derivedHomologyDual C n).hom.app (op (LG.functor.obj (LF.functor.obj X))) := by
  simp [dualIteratedIso, targetEval, Category.assoc]
  erw [Category.id_comp]

private abbrev RightOnStalk := GrothendieckEdges.objectSequence F.op G.op R

private abbrev DualOnStalk := (minusSingle A).op ⋙ derivedDual A ⋙ rightSequence F G R

private def dualOnStalkIso : DualOnStalk F G R ≅ RightOnStalk F G R :=
  (associator _ _ _).symm ≪≫ isoWhiskerRight (derivedStalkDual A) _

private def dualStalkSecond (p q : ℕ) :
    (minusSingle A ⋙ dualSequence F G R) ⋙ homologicalPage 0 p ((p : ℤ)+q) ≅
      objectSecond F G LF LG p q :=
  associator _ _ _ ≪≫ isoWhiskerLeft (minusSingle A) (dualSecondIso F G LF LG R p q) ≪≫
    (associator (minusSingle A) (LF.functor ⋙ homologicalHomology (q : ℤ))
      (leftValue G LG p)).symm

private def rightStalkInputIso (X : A) :
    F.op.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)) ≅
      (derivedDual B).obj (op (LF.functor.obj ((minusSingle A).obj X))) :=
  F.op.rightDerivedFunctorPlus.mapIso ((derivedStalkDual A).app (op X)).symm ≪≫
    ((deriveDual F LF).app (op ((minusSingle A).obj X))).symm

private theorem dualRowPresentation_stalk (X : A) :
    (dualRowPresentationIso F G LF R).hom.app (op ((minusSingle A).obj X)) =
      (dualOnStalkIso F G R).hom.app (op X) ≫ R.row.derived.map
        (rightStalkInputIso F LF X).hom := by
  let a := (F.op.rightDerivedFunctorPlus.mapIso ((derivedStalkDual A).app (op X)))
  change _ = _ ≫ R.row.derived.map
    (a.inv ≫ (deriveDual F LF).inv.app (op ((minusSingle A).obj X)))
  dsimp [dualRowPresentationIso, dualOnStalkIso, Functor.rightOpLeftOpIso]
  simp only [Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id]
  change R.row.derived.map ((deriveDual F LF).inv.app (op ((minusSingle A).obj X))) =
    R.row.derived.map a.hom ≫ R.row.derived.map a.inv ≫
      R.row.derived.map ((deriveDual F LF).inv.app (op ((minusSingle A).obj X)))
  exact ((R.row.derived.mapIso a).hom_inv_id_assoc _).symm

private theorem dualSecond_on_stalk (p q : ℕ) (X : A) :
    ((dualSecondIso F G LF LG R p q).inv.app ((minusSingle A).obj X)).op =
      ((dualOnStalkIso F G R).hom.app (op X)).page 0 p ((p : ℤ) + q) ≫
      (R.secondIso p q).hom.app ((DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)) ≫
      (rightValue G.op p).map ((classicalDual F LF q).hom.app (op X)) ≫
      (classicalDual G LG p).hom.app (op ((leftValue F LF q).obj X)) := by
  rw [dualRowSecond_app, dualRowPresentation_stalk, R.second_eq]
  let Z := (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)
  let Y := LF.functor.obj ((minusSingle A).obj X)
  let V := rightValue G.op p
  let H := DerivedCategory.Plus.homologyFunctor Bᵒᵖ (q : ℤ)
  let f := (rightStalkInputIso F LF X).hom
  have h := (R.coordinates.second p q).hom.naturality f
  change (R.row.derived.map f).page 0 p ((p : ℤ) + q) ≫
      (R.coordinates.second p q).hom.app ((derivedDual B).obj (op Y)) =
    (R.coordinates.second p q).hom.app (F.op.rightDerivedFunctorPlus.obj Z) ≫ V.map (H.map f) at h
  have hc : (classicalDual F LF q).hom.app (op X) =
      H.map f ≫ (derivedHomologyDual B (q : ℤ)).hom.app (op Y) := by
    simp [classicalDual, rightStalkInputIso, Category.assoc, f, H, Y]
  rw [hc, Functor.map_comp]
  simp only [Iso.trans_hom, NatTrans.comp_app, associator_hom_app, Iso.symm_hom,
    associator_inv_app, isoWhiskerLeft_hom, whiskerLeft_app, Category.comp_id, Category.id_comp]
  let u := ((dualOnStalkIso F G R).hom.app (op X)).page 0 p ((p : ℤ) + q)
  let t := V.map ((derivedHomologyDual B (q : ℤ)).hom.app (op Y)) ≫
    (classicalDual G LG p).hom.app (op ((leftValue F LF q).obj X))
  change (u ≫ (R.row.derived.map f).page 0 p ((p : ℤ) + q)) ≫
      (R.coordinates.second p q).hom.app ((derivedDual B).obj (op Y)) ≫ t =
    u ≫ (R.coordinates.second p q).hom.app (F.op.rightDerivedFunctorPlus.obj Z) ≫
      (V.map (H.map f) ≫ V.map ((derivedHomologyDual B (q : ℤ)).hom.app (op Y))) ≫
      (classicalDual G LG p).hom.app (op ((leftValue F LF q).obj X))
  simpa only [Category.assoc] using congrArg (fun k => u ≫ k ≫ t) h

private def rightIteratedStalkIso (X : A) :
    G.op.rightDerivedFunctorPlus.obj (F.op.rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X))) ≅
      (derivedDual C).obj (op (LG.functor.obj (LF.functor.obj ((minusSingle A).obj X)))) :=
  G.op.rightDerivedFunctorPlus.mapIso (rightStalkInputIso F LF X) ≪≫
    ((deriveDual G LG).app (op (LF.functor.obj ((minusSingle A).obj X)))).symm

private theorem dualIterated_on_stalk (X : A) (n : ℤ) :
    ((dualIteratedIso F G LF LG R n).inv.app ((minusSingle A).obj X)).op =
      ((dualOnStalkIso F G R).hom.app (op X)).target n ≫
      (R.iteratedIso n).hom.app ((DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)) ≫
      (DerivedCategory.Plus.homologyFunctor Cᵒᵖ n).map ((rightIteratedStalkIso F G LF LG X).hom) ≫
      (derivedHomologyDual C n).hom.app (op (LG.functor.obj (LF.functor.obj ((minusSingle A).obj X)))) := by
  rw [dualRowTarget_app, dualRowPresentation_stalk, R.iterated_eq]
  let Z := (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)
  let Y := LF.functor.obj ((minusSingle A).obj X)
  let H := DerivedCategory.Plus.homologyFunctor Cᵒᵖ n
  let f := (rightStalkInputIso F LF X).hom
  have h := (R.coordinates.target n).hom.naturality f
  change (R.row.derived.map f).target n ≫
      (R.coordinates.target n).hom.app ((derivedDual B).obj (op Y)) =
    (R.coordinates.target n).hom.app (F.op.rightDerivedFunctorPlus.obj Z) ≫
      H.map (G.op.rightDerivedFunctorPlus.map f) at h
  simp only [rightIteratedStalkIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Functor.map_comp, NatTrans.comp_app, associator_hom_app, associator_inv_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Category.comp_id, Category.id_comp]
  let a := ((dualOnStalkIso F G R).hom.app (op X)).target n
  let t := H.map ((deriveDual G LG).inv.app (op Y)) ≫
    (derivedHomologyDual C n).hom.app (op (LG.functor.obj Y))
  change (a ≫ (R.row.derived.map f).target n) ≫
      (R.coordinates.target n).hom.app ((derivedDual B).obj (op Y)) ≫ t =
    a ≫ (R.coordinates.target n).hom.app (F.op.rightDerivedFunctorPlus.obj Z) ≫
      (H.map (G.op.rightDerivedFunctorPlus.map f) ≫ H.map ((deriveDual G LG).inv.app (op Y))) ≫
      (derivedHomologyDual C n).hom.app (op (LG.functor.obj Y))
  simpa only [Category.assoc] using congrArg (fun k => a ≫ k ≫ t) h

private def rightRowAxis (n : ℕ) :
    rightSequence F G R ⋙ pageEval 0 n n ≅ GrothendieckSpectralSequence.secondValue F.op G.op n 0 :=
  eqToIso (by rw [add_zero]) ≪≫ R.secondIso n 0

private def rightColumnAxis (n : ℕ) :
    rightSequence F G R ⋙ pageEval 0 0 n ≅ GrothendieckSpectralSequence.secondValue F.op G.op 0 n :=
  eqToIso (by simp only [Int.natCast_zero, zero_add]) ≪≫ R.secondIso 0 n

private theorem rightRowAxis_at_stalk (O : GrothendieckEdges.ObjectEdges F.op G.op R)
    (n : ℕ) (X : A) :
    (rightRowAxis F G R n).hom.app ((DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)) =
      (O.rowPage n).hom.app (op X) ≫
        (rightValue G.op n).map (O.degreeZeroF.hom.app (op X)) := by
  have h := congrArg (fun e => e.hom.app (op X)) (O.row_identification n)
  have h' := congrArg (fun e => e.hom.app (op X)) (O.objectCase.secondIso_eq n 0)
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, associator_hom_app,
    associator_inv_app, Iso.symm_hom, Category.assoc, Category.comp_id, Category.id_comp] at h h'
  change (O.objectCase.secondIso n 0).hom.app (op X) =
    (GrothendieckEdges.rowIndexIso F.op G.op R n).hom.app (op X) ≫ _ at h
  rw [h'] at h
  erw [Category.comp_id] at h
  unfold rightRowAxis
  simp only [Iso.trans_hom, NatTrans.comp_app]
  erw [h]
  have hh := ((GrothendieckEdges.rowIndexIso F.op G.op R n).app (op X)).inv_hom_id_assoc
    ((O.rowPage n).hom.app (op X) ≫
      (rightValue G.op n).map (O.degreeZeroF.hom.app (op X)))
  simp only [GrothendieckEdges.rowIndexIso, Iso.app_inv, Iso.app_hom,
    eqToIso.inv, eqToIso.hom, eqToHom_app] at hh ⊢
  exact hh

private theorem rightColumnAxis_at_stalk (O : GrothendieckEdges.ObjectEdges F.op G.op R)
    (n : ℕ) (X : A) :
    (rightColumnAxis F G R n).hom.app ((DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)) =
      (O.columnPage n).hom.app (op X) ≫ O.degreeZero.inv.app ((rightValue F.op n).obj (op X)) := by
  have h := congrArg (fun e => e.hom.app (op X)) (O.column_identification n)
  have h' := congrArg (fun e => e.hom.app (op X)) (O.objectCase.secondIso_eq 0 n)
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, associator_hom_app,
    associator_inv_app, Iso.symm_hom, Category.assoc, Category.comp_id, Category.id_comp] at h h'
  change (O.objectCase.secondIso 0 n).hom.app (op X) =
    (GrothendieckEdges.columnIndexIso F.op G.op R n).hom.app (op X) ≫ _ at h
  rw [h'] at h
  erw [Category.comp_id] at h
  unfold rightColumnAxis
  simp only [Iso.trans_hom, NatTrans.comp_app]
  erw [h]
  have hh := ((GrothendieckEdges.columnIndexIso F.op G.op R n).app (op X)).inv_hom_id_assoc
    ((O.columnPage n).hom.app (op X) ≫ O.degreeZero.inv.app ((rightValue F.op n).obj (op X)))
  simp only [GrothendieckEdges.columnIndexIso, Iso.app_inv, Iso.app_hom,
    eqToIso.inv, eqToIso.hom, eqToHom_app] at hh ⊢
  exact hh

private theorem reindexed_dualSecond_on_stalk
    (p q : ℕ) (m : ℤ) (h : m = (p : ℤ) + q) (X : A) :
    let fm := fun k => (minusSingle A ⋙ dualSequence F G R) ⋙ homologicalPage 0 (p : ℤ) k
    let gm := fun k => rightSequence F G R ⋙ pageEval 0 (p : ℤ) k
    let Z := (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)
    (((eqToIso (congrArg fm h) ≪≫ dualStalkSecond F G LF LG R p q).inv.app X)).op =
      ((dualOnStalkIso F G R).hom.app (op X)).page 0 p m ≫
      ((eqToIso (congrArg gm h) ≪≫ R.secondIso p q).hom.app Z) ≫
      (rightValue G.op p).map ((classicalDual F LF q).hom.app (op X)) ≫
      (classicalDual G LG p).hom.app (op ((leftValue F LF q).obj X)) := by
  subst m
  simp [dualStalkSecond, Category.assoc]
  erw [Category.comp_id]
  simpa [Category.assoc] using dualSecond_on_stalk F G LF LG R p q X

private theorem dualQuadrant (O : GrothendieckEdges.ObjectCase F.op G.op R)
    (X : A) (p n : ℤ) (h : p < 0 ∨ n < p) :
    IsZero (((DualOnStalk F G R).obj (op X)).page 0 p n) :=
  (O.quadrant (op X) p n h).of_iso ((pageEval 0 p n).mapIso ((dualOnStalkIso F G R).app (op X)))

private def rightDerivedAtStalk (X : A) : DerivedCategory.Plus Bᵒᵖ :=
  F.op.rightDerivedFunctorPlus.obj ((derivedDual A).obj (op ((minusSingle A).obj X)))

private def dualFilteredEdges (O : GrothendieckEdges.ObjectCase F.op G.op R) (X : A) :
    EdgeData ((DualOnStalk F G R).obj (op X)) :=
  derivedEdges G.op R.row (rightDerivedAtStalk F X) (fun p n h => dualQuadrant F G R O X p n h)

private theorem dualFilteredEdges_natural (O : GrothendieckEdges.ObjectCase F.op G.op R)
    {X Y : A} (f : X ⟶ Y) :
    EdgeMap ((DualOnStalk F G R).map f.op) (dualFilteredEdges F G R O Y) (dualFilteredEdges F G R O X) :=
  derived_edges_naturality G.op R.row
    (((minusSingle A).op ⋙ derivedDual A ⋙ F.op.rightDerivedFunctorPlus).map f.op) _ _

private def dualColumn (O : GrothendieckEdges.ObjectCase F.op G.op R) (n : ℕ) :
    (minusSingle A ⋙ dualSequence F G R) ⋙ homologicalPage 0 0 n ⟶
      (minusSingle A ⋙ dualSequence F G R) ⋙ homologicalTarget n where
  app X := ((dualFilteredEdges F G R O X).column n).unop
  naturality := by
    intro X Y f
    change (((DualOnStalk F G R).map f.op).page 0 0 n).unop ≫
        ((dualFilteredEdges F G R O Y).column n).unop =
      ((dualFilteredEdges F G R O X).column n).unop ≫
        (((DualOnStalk F G R).map f.op).target n).unop
    simpa only [unop_comp] using
      (congrArg Quiver.Hom.unop ((dualFilteredEdges_natural F G R O f).column n)).symm

private def dualRow (O : GrothendieckEdges.ObjectCase F.op G.op R) (n : ℕ) :
    (minusSingle A ⋙ dualSequence F G R) ⋙ homologicalTarget n ⟶
      (minusSingle A ⋙ dualSequence F G R) ⋙ homologicalPage 0 n n where
  app X := ((dualFilteredEdges F G R O X).row n).unop
  naturality := by
    intro X Y f
    change (((DualOnStalk F G R).map f.op).target n).unop ≫
        ((dualFilteredEdges F G R O Y).row n).unop =
      ((dualFilteredEdges F G R O X).row n).unop ≫
        (((DualOnStalk F G R).map f.op).page 0 n n).unop
    simpa only [unop_comp] using
      (congrArg Quiver.Hom.unop ((dualFilteredEdges_natural F G R O f).row n)).symm

private theorem dualEdgeFormulas (O : GrothendieckEdges.ObjectCase F.op G.op R) (X : A) :
    FilteredEdgeFormulas G ((minusSingle A ⋙ dualSequence F G R).obj X)
      (dualFilteredEdges F G R O X) := by
  let Y := rightDerivedAtStalk F X
  let M := GrothendieckEdges.modelData G.op R.row Y
  let e := GrothendieckEdges.modelIso G.op R.row Y
  let hQ := fun p n h => dualQuadrant F G R O X p n h
  refine ⟨inferInstance, inferInstance, inferInstance, R.row, Y, rfl, ?_⟩
  exact ⟨realized_row_formula G.op M e hQ, realized_column_formula G.op M e hQ⟩

private theorem reverse_fiveTerms {D : RowDiagram Cᵒᵖ} (E : EdgeData D) (h : FiveTermData E) :
    FiveTerms (E.row 2).unop (differential (op D) 0 2 2) (E.column 1).unop (E.row 1).unop := by
  have hd : differential (op D) 0 2 2 = (transgression D).unop := by
    simp [differential]
  rw [hd]
  have hf : (E.row 2).unop ≫ (transgression D).unop = 0 := by
    simpa only [unop_zero, unop_comp] using congrArg Quiver.Hom.unop h.d_row
  have hg : (transgression D).unop ≫ (E.column 1).unop = 0 := by
    simpa only [unop_zero, unop_comp] using congrArg Quiver.Hom.unop h.column_d
  have hh : (E.column 1).unop ≫ (E.row 1).unop = 0 := by
    simpa only [unop_zero, unop_comp] using congrArg Quiver.Hom.unop h.row_column
  haveI := h.row_mono
  exact ⟨inferInstance, hf, hg, hh,
    (ShortComplex.exact_unop_iff _).mpr h.exact_E20,
    (ShortComplex.exact_unop_iff _).mpr h.exact_E01,
    (ShortComplex.exact_unop_iff _).mpr h.exact_H1⟩

private theorem rightRow_at_stalk [PreservesFiniteLimits F.op] [PreservesFiniteLimits G.op]
    (O : GrothendieckEdges.ObjectEdges F.op G.op R) (n : ℕ) (X : A) :
    let Z := (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)
    let H := G.op.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor Cᵒᵖ (n : ℤ)
    (O.rowPage n).hom.app (op X) ≫ H.map ((GrothendieckEdges.stalkToDerived F.op).app (op X)) =
      (O.filtered (op X)).row n ≫ (R.iteratedIso (n : ℤ)).hom.app Z := by
  dsimp only
  letI := R.comparison_isIso
  let cmp := _root_.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F.op G.op
  letI : IsIso cmp := NatIso.isIso_of_isIso_app _
  let H := DerivedCategory.Plus.homologyFunctor Cᵒᵖ (n : ℤ)
  let Z := (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)
  have h := O.first_comparison n (op X)
  rw [O.target_identification, R.canonical] at h
  change (O.rowPage n).hom.app (op X) ≫
      ((G.op.rightDerivedFunctorPlus ⋙ H).map ((GrothendieckEdges.stalkToDerived F.op).app (op X)) ≫
        H.map ((asIso cmp).inv.app Z)) =
    (O.filtered (op X)).row n ≫ (R.iteratedIso (n : ℤ)).hom.app Z ≫
      H.map ((asIso cmp).inv.app Z) at h
  exact (cancel_mono (H.map ((asIso cmp).inv.app Z))).mp (by simpa only [Category.assoc] using h)

private theorem rightColumn_at_stalk [PreservesFiniteLimits F.op] [PreservesFiniteLimits G.op]
    (O : GrothendieckEdges.ObjectEdges F.op G.op R) (n : ℕ) (X : A) :
    let Z := (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)
    (O.filtered (op X)).column n ≫ (O.columnPage n).hom.app (op X) =
      (R.iteratedIso (n : ℤ)).hom.app Z ≫
        ((O.truncation n).edge G.op O.degreeZero).app (F.op.rightDerivedFunctorPlus.obj Z) := by
  dsimp only
  letI := R.comparison_isIso
  let cmp := _root_.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F.op G.op
  letI : IsIso cmp := NatIso.isIso_of_isIso_app _
  let H := DerivedCategory.Plus.homologyFunctor Cᵒᵖ (n : ℤ)
  let Z := (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)
  have h := O.second_comparison n (op X)
  rw [O.target_identification, R.canonical] at h
  change ((R.iteratedIso (n : ℤ)).hom.app Z ≫ H.map ((asIso cmp).inv.app Z)) ≫
    H.map ((asIso cmp).hom.app Z) ≫
      ((O.truncation n).edge G.op O.degreeZero).app (F.op.rightDerivedFunctorPlus.obj Z) =
    (O.filtered (op X)).column n ≫ (O.columnPage n).hom.app (op X) at h
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app] at h
  erw [H.map_id, Category.id_comp] at h
  exact h.symm

open FiniteFiltrationConvergence in
private theorem objectFiltered_eq (O : GrothendieckEdges.ObjectEdges F.op G.op R) (X : A) :
    let Y := F.op.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X))
    O.filtered (op X) = derivedEdges G.op R.row Y (O.objectCase.quadrant (op X)) := by
  dsimp only
  let Y := F.op.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X))
  let M := GrothendieckEdges.modelData G.op R.row Y
  let e := GrothendieckEdges.modelIso G.op R.row Y
  let h := O.objectCase.quadrant (op X)
  let hQ := realizedQuadrant G.op M e h
  have hmodel : derivedEdges G.op R.row Y h = realizedEdges G.op M e h := rfl
  change O.filtered (op X) = derivedEdges G.op R.row Y h
  rw [hmodel]
  apply EdgeData.ext
  · funext n
    let ep := (pageEval 0 n n).mapIso e
    let a := closedToPage M.filtration M.pages 2 n n
    haveI : Epi a :=
      EdgesAndFiveTerms.row_closedToPage_epi M.filtration M.pages M.convergence.finite hQ n
    exact (cancel_epi (a ≫ ep.inv)).mp
      (((O.filtered_formulas (op X)).row n).trans (realized_row_formula G.op M e h n).symm)
  · funext n
    let et := (targetEval n).mapIso e
    let a := EdgesAndFiveTerms.ambientClass M.filtration 0 n
    haveI : IsIso (cohomologyPiece M.filtration 0 (n : ℤ)).arrow :=
      (Subobject.isIso_arrow_iff_eq_top _).2
        (EdgesAndFiveTerms.cohomologyPiece_zero_eq_top M.filtration M.pages M.convergence.finite hQ n)
    haveI : Epi a := by
      change Epi (closedClass M.filtration 0 n ≫ (cohomologyPiece M.filtration 0 n).arrow)
      infer_instance
    exact (cancel_epi ((a ≫ (M.targetIso n).hom) ≫ et.inv)).mp
      (((O.filtered_formulas (op X)).column n).trans (realized_column_formula G.op M e h n).symm)

private theorem dualFilteredEdges_to_right
    (O : GrothendieckEdges.ObjectEdges F.op G.op R) (X : A) :
    EdgeMap ((dualOnStalkIso F G R).hom.app (op X)) (dualFilteredEdges F G R O.objectCase X)
      (O.filtered (op X)) := by
  rw [objectFiltered_eq F G R O X]
  let a := F.op.rightDerivedFunctorPlus.map ((derivedStalkDual A).hom.app (op X))
  have h := derived_edges_naturality G.op R.row a (dualQuadrant F G R O.objectCase X)
    (O.objectCase.quadrant (op X))
  have e : (dualOnStalkIso F G R).hom.app (op X) = R.row.derived.map a := by
    change 𝟙 _ ≫ R.row.derived.map a = _
    erw [Category.id_comp]
  rw [e]
  exact h

private def dualPackage
    (cmp : LF.functor ⋙ LG.functor ≅ LFG.functor)
    (hcmp : whiskerLeft (QMinus A) cmp.hom ≫ LFG.counit = composedCounit F G LF LG) :
    Package F G LF LG LFG where
  sequence := dualSequence F G R
  secondIso := dualSecondIso F G LF LG R
  negative := by
    intro X p n hp
    change IsZero ((((rightSequence F G R).obj ((derivedDual A).obj (op X))).page 0 p n).unop)
    have h := (R.negative ((derivedDual A).obj (op X)) p (n-p) hp).unop
    rwa [show p + (n-p) = n by omega] at h
  comparison := cmp
  comparison_counit := hcmp
  iteratedIso := dualIteratedIso F G LF LG R
  convergence := fun X => reverse_filtration _ (R.inclusion_mono _) (R.down_inclusion _)
    (R.finite _) (R.convergence _)
  rowPresentation := by
    refine ⟨inferInstance, inferInstance, inferInstance, derivedReversal B, derivedReversal C,
      reversedDerivedFunctor G LG, R.row, R.coordinates, dualRowPresentationIso F G LF R, ?_, ?_⟩
    · intro X p q
      let Y := LF.functor.obj X
      let H := (homologicalHomology (C := B) q).obj Y
      have h := dualRowSecond_app F G LF LG R X p q
      have hc := classicalDual_app G LG p H
      exact h.trans (congrArg (fun t =>
        ((dualRowPresentationIso F G LF R).hom.app (op X)).page 0 p ((p : ℤ) + q) ≫
        (R.coordinates.second p q).hom.app ((derivedDual B).obj (op Y)) ≫
        (rightValue G.op p).map ((derivedHomologyDual B q).hom.app (op Y)) ≫ t.hom) hc)
    · intro X n
      exact dualRowTarget_app F G LF LG R X n

variable (cmp : LF.functor ⋙ LG.functor ≅ LFG.functor)
  (hcmp : whiskerLeft (QMinus A) cmp.hom ≫ LFG.counit = composedCounit F G LF LG)

private def dualObjectCase [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (Q : GrothendieckEdges.ObjectCase F.op G.op R) :
    ObjectCase F G LF LG LFG (dualPackage F G LF LG LFG R cmp hcmp) where
  secondIso := dualStalkSecond F G LF LG R
  secondIso_eq := fun _ _ => rfl
  quadrant := fun X => first_quadrant_all_pages _ (fun p n h => (dualQuadrant F G R Q X p n h).unop)
  degreeZeroF := degreeZeroIso F LF
  degreeZeroG := degreeZeroIso G LG
  degreeZeroF_hom := degreeZeroIso_hom F LF
  degreeZeroG_hom := degreeZeroIso_hom G LG
  column := dualColumn F G R Q
  row := dualRow F G R Q
  filtered := fun X => dualEdgeFormulas F G R Q X
  fiveTerms := fun X => reverse_fiveTerms (dualFilteredEdges F G R Q X)
    (derived_fiveTerms G.op R.row (rightDerivedAtStalk F X) _)

private theorem leftRow_on_stalk
    [PreservesFiniteLimits F.op]
    (O : ObjectCase F G LF LG LFG (dualPackage F G LF LG LFG R cmp hcmp))
    (Q : GrothendieckEdges.ObjectEdges F.op G.op R)
    (n : ℕ) (X : A) :
    ((rowValueIso O n).inv.app X).op =
      (((dualOnStalkIso F G R).hom.app (op X)).page 0 n n ≫
        (Q.rowPage n).hom.app (op X) ≫ (classicalDual G LG n).hom.app (op (F.obj X))) := by
  have hS : O.secondIso n 0 = dualStalkSecond F G LF LG R n 0 := O.secondIso_eq n 0
  have h₀ := reversedClassicalZero F LF (derivedReversal A) (derivedReversal B)
    (reversedDerivedFunctor F LF) X
  rw [← classicalDual_app F LF] at h₀
  have h₀' := congrArg (fun k => k.app (op X)) Q.degreeZeroF_hom
  simp only [rowValueIso, hS, Iso.trans_inv, NatTrans.comp_app, isoWhiskerRight_inv,
    whiskerRight_app, op_comp]
  have h := reindexed_dualSecond_on_stalk F G LF LG R n 0 n (by simp) X
  simp only [Iso.trans_inv, NatTrans.comp_app, op_comp] at h
  rw [← Category.assoc, h]
  erw [rightRowAxis_at_stalk F G R Q n X]
  simp only [Category.assoc]
  have hNat := (classicalDual G LG n).hom.naturality ((O.degreeZeroF.inv.app X).op)
  change (rightValue G.op n).map ((O.degreeZeroF.inv.app X).op) ≫
      (classicalDual G LG n).hom.app (op (F.obj X)) =
    (classicalDual G LG n).hom.app (op ((leftValue F LF 0).obj X)) ≫
      ((leftValue G LG n).map (O.degreeZeroF.inv.app X)).op at hNat
  have hId : (O.degreeZeroF.hom.app X).op ≫ (O.degreeZeroF.inv.app X).op = 𝟙 _ :=
    ((O.degreeZeroF.app X).op).hom_inv_id
  erw [← hNat, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, h₀', h₀,
    ← O.degreeZeroF_hom X, hId, (rightValue G.op n).map_id, Category.id_comp]

private theorem leftColumn_on_stalk
    [PreservesFiniteLimits G.op]
    (O : ObjectCase F G LF LG LFG (dualPackage F G LF LG LFG R cmp hcmp))
    (Q : GrothendieckEdges.ObjectEdges F.op G.op R)
    (n : ℕ) (X : A) :
    ((columnValueIso O n).inv.app X).op =
      (((dualOnStalkIso F G R).hom.app (op X)).page 0 0 n ≫
        (Q.columnPage n).hom.app (op X) ≫
        G.op.map ((classicalDual F LF n).hom.app (op X))) := by
  have hS : O.secondIso 0 n = dualStalkSecond F G LF LG R 0 n := O.secondIso_eq 0 n
  have h₀ := reversedClassicalZero G LG (derivedReversal B) (derivedReversal C)
    (reversedDerivedFunctor G LG) ((leftValue F LF n).obj X)
  rw [← classicalDual_app G LG] at h₀
  have h₀' := congrArg (fun k => k.app (op ((leftValue F LF n).obj X))) Q.degreeZero_hom
  simp only [columnValueIso, hS, Iso.trans_inv, NatTrans.comp_app, isoWhiskerLeft_inv,
    whiskerLeft_app, op_comp]
  have h := reindexed_dualSecond_on_stalk F G LF LG R 0 n n (by simp) X
  simp only [Iso.trans_inv, NatTrans.comp_app, op_comp] at h
  rw [← Category.assoc, h]
  erw [rightColumnAxis_at_stalk F G R Q n X]
  simp only [Category.assoc]
  let a := (classicalDual F LF n).hom.app (op X)
  have hNat := Q.degreeZero.inv.naturality a
  let U := (leftValue F LF n).obj X
  have hId : (O.degreeZeroG.hom.app U).op ≫ (O.degreeZeroG.inv.app U).op = 𝟙 _ :=
    ((O.degreeZeroG.app U).op).hom_inv_id
  erw [← reassoc_of% hNat, h₀']
  erw [← Category.assoc ((GrothendieckEdges.degreeZeroUnit G.op).app (op U)),
    h₀, ← O.degreeZeroG_hom, hId, Category.comp_id]
  rfl

private theorem rightRowCounit_on_stalk (n : ℕ) (X : A) :
    let Z := (minusSingle A).obj X
    let H := DerivedCategory.Plus.homologyFunctor Cᵒᵖ (n : ℤ)
    (classicalDual G LG n).hom.app (op (F.obj X)) ≫
        ((LG.functor ⋙ homologicalHomology (C := C) (n : ℤ)).map (stalkCounit F LF 0 X)).op =
      H.map (G.op.rightDerivedFunctorPlus.map ((GrothendieckEdges.stalkToDerived F.op).app (op X))) ≫
        H.map ((rightIteratedStalkIso F G LF LG X).hom) ≫
        (derivedHomologyDual C n).hom.app (op (LG.functor.obj (LF.functor.obj Z))) := by
  dsimp only
  let Z := (minusSingle A).obj X
  let Y := LF.functor.obj Z
  let U := (minusSingle B).obj (F.obj X)
  let s : Y ⟶ U := stalkCounit F LF 0 X
  let H := DerivedCategory.Plus.homologyFunctor Cᵒᵖ (n : ℤ)
  let K := G.op.rightDerivedFunctorPlus
  let d := (derivedStalkDual B).inv.app (op (F.obj X))
  let hk := (deriveDual G LG).inv
  let ch := (derivedHomologyDual C (n : ℤ)).hom
  have hv := ch.naturality (LG.functor.map s).op
  change H.map ((derivedDual C).map (LG.functor.map s).op) ≫ ch.app (op (LG.functor.obj Y)) =
    ch.app (op (LG.functor.obj U)) ≫
      ((homologicalHomology (C := C) (n : ℤ)).map (LG.functor.map s)).op at hv
  have hx := hk.naturality s.op
  change K.map ((derivedDual B).map s.op) ≫ hk.app (op Y) =
    hk.app (op U) ≫ (derivedDual C).map (LG.functor.map s).op at hx
  have hu := reversedStalkCounit_zero F LF (derivedReversal A) (derivedReversal B)
    (reversedDerivedFunctor F LF) X
  have hU : (GrothendieckEdges.stalkToDerived F.op).app (op X) ≫
      (rightStalkInputIso F LF X).hom = d ≫ (derivedDual B).map s.op := by
    simpa [rightStalkInputIso, derivedReversal, reversedDerivedFunctor, d, s, Category.assoc] using hu
  have hclass : (classicalDual G LG n).hom.app (op (F.obj X)) =
      H.map (K.map d) ≫ H.map (hk.app (op U)) ≫ ch.app (op (LG.functor.obj U)) := by
    simp [classicalDual, d, hk, ch, H, K, U]
  rw [hclass]
  simp only [rightIteratedStalkIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc]
  change H.map (K.map d) ≫ H.map (hk.app (op U)) ≫
      ch.app (op (LG.functor.obj U)) ≫
      ((homologicalHomology (C := C) (n : ℤ)).map (LG.functor.map s)).op =
    H.map (K.map ((GrothendieckEdges.stalkToDerived F.op).app (op X))) ≫
      H.map (K.map (rightStalkInputIso F LF X).hom) ≫
      H.map (hk.app (op Y)) ≫ ch.app (op (LG.functor.obj Y))
  have hpath : K.map d ≫ hk.app (op U) ≫ (derivedDual C).map (LG.functor.map s).op =
      K.map ((GrothendieckEdges.stalkToDerived F.op).app (op X)) ≫
        K.map (rightStalkInputIso F LF X).hom ≫ hk.app (op Y) := by
    erw [← hx, ← K.map_comp_assoc, ← hU, K.map_comp_assoc]
  erw [← hv, ← H.map_comp_assoc (hk.app (op U)), ← H.map_comp_assoc (K.map d), hpath]
  simp only [Functor.map_comp, Category.assoc]

private theorem canonicalRow_on_stalk
    [PreservesFiniteLimits F.op] [PreservesFiniteLimits G.op]
    [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (Q : GrothendieckEdges.ObjectEdges F.op G.op R)
    (n : ℕ) (X : A) :
    let P := dualPackage F G LF LG LFG R cmp hcmp
    let O := dualObjectCase F G LF LG LFG R cmp hcmp Q.objectCase
    (P.iteratedIso n).inv.app ((minusSingle A).obj X) ≫ (O.row n).app X ≫
        (rowValueIso O n).hom.app X =
      (homologicalHomology (C := C) (n : ℤ)).map (LG.functor.map (stalkCounit F LF 0 X)) := by
  dsimp only
  let O := dualObjectCase F G LF LG LFG R cmp hcmp Q.objectCase
  have hAxis := leftRow_on_stalk F G LF LG LFG R cmp hcmp O Q n X
  let Z := (minusSingle A).obj X
  let Y := LF.functor.obj Z
  let E := dualFilteredEdges F G R Q.objectCase X
  let E' := Q.filtered (op X)
  let a := (dualOnStalkIso F G R).hom.app (op X)
  let H := DerivedCategory.Plus.homologyFunctor Cᵒᵖ (n : ℤ)
  let t := (dualIteratedIso F G LF LG R n).app Z
  let u := (rowValueIso O n).app X
  let v := (classicalDual G LG n).hom.app (op (F.obj X))
  let h := (homologicalHomology (C := C) (n : ℤ)).map (LG.functor.map (stalkCounit F LF 0 X))
  let c := H.map ((rightIteratedStalkIso F G LF LG X).hom) ≫
    (derivedHomologyDual C n).hom.app (op (LG.functor.obj Y))
  let Zr := (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)
  let b := (Q.rowPage n).hom.app (op X)
  let t' := (R.iteratedIso (n : ℤ)).hom.app Zr
  let k := H.map (G.op.rightDerivedFunctorPlus.map
    ((GrothendieckEdges.stalkToDerived F.op).app (op X)))
  have he : a.page 0 n n ≫ E'.row n = E.row n ≫ a.target n :=
    (dualFilteredEdges_to_right F G R Q X).row n
  have hr : b ≫ k = E'.row n ≫ t' := rightRow_at_stalk F G R Q n X
  have hc : v ≫ h.op = k ≫ c := rightRowCounit_on_stalk F G LF LG n X
  have ht : t.inv.op = a.target n ≫ t' ≫ c :=
    dualIterated_on_stalk F G LF LG R X n
  have ha : u.inv.op = a.page 0 n n ≫ b ≫ v := hAxis
  have hh : E.row n ≫ t.inv.op = u.inv.op ≫ h.op := calc
    _ = (E.row n ≫ a.target n) ≫ t' ≫ c := by rw [ht, Category.assoc]
    _ = a.page 0 n n ≫ E'.row n ≫ t' ≫ c := by rw [← he, Category.assoc]
    _ = a.page 0 n n ≫ b ≫ k ≫ c := by rw [← reassoc_of% hr]
    _ = u.inv.op ≫ h.op := by rw [← hc, ha]; simp only [Category.assoc]
  apply Quiver.Hom.op_inj
  simp only [op_comp]
  change (u.hom.op ≫ (E.row n)) ≫ t.inv.op = h.op
  rw [Category.assoc, hh]
  exact (u.op).hom_inv_id_assoc _

private theorem canonicalColumn_on_stalk
    [PreservesFiniteLimits F.op] [PreservesFiniteLimits G.op] [PreservesFiniteColimits F] [PreservesFiniteColimits G]
    (Q : GrothendieckEdges.ObjectEdges F.op G.op R)
    (n : ℕ) (X : A) :
    let P := dualPackage F G LF LG LFG R cmp hcmp
    let O := dualObjectCase F G LF LG LFG R cmp hcmp Q.objectCase
    let T := dualTruncation G LG (-(n : ℤ))
    let Z := (minusSingle A).obj X
    let Y := LF.functor.obj Z
    let H := homologicalHomology (C := C) (n : ℤ)
    (columnValueIso O n).inv.app X ≫ (O.column n).app X ≫ (P.iteratedIso n).hom.app Z =
      (T.stalk ((homologicalHomology (C := B) (n : ℤ)).obj Y)).inv ≫
        H.map (LG.functor.map
          (T.point.inv.app Y ≫
            (DerivedCategory.TStructure.t.onMinus.truncLEι (-(n : ℤ))).app
              ((DerivedCategory.TStructure.t.onMinus.truncGE (-(n : ℤ))).obj Y))) ≫
        T.upper.inv.app Y := by
  dsimp only
  let O := dualObjectCase F G LF LG LFG R cmp hcmp Q.objectCase
  let T := dualTruncation G LG (-(n : ℤ))
  let Z := (minusSingle A).obj X
  let Y := LF.functor.obj Z
  let W := (homologicalHomology (C := B) (n : ℤ)).obj Y
  let J := DerivedCategory.Plus.homologyFunctor Cᵒᵖ (n : ℤ)
  let K := G.op.rightDerivedFunctorPlus ⋙ J
  let OB := derivedReversal B
  let OC := derivedReversal C
  let OG := reversedDerivedFunctor G LG
  let Ω := reversedDerivedHomology G LG OB OC OG (n : ℤ)
  let f := (rightStalkInputIso F LF X).hom
  let E := dualFilteredEdges F G R Q.objectCase X
  let E' := Q.filtered (op X)
  let a := (dualOnStalkIso F G R).hom.app (op X)
  let u := (columnValueIso O n).app X
  let t := (dualIteratedIso F G LF LG R n).app Z
  let Zr := (DerivedCategory.Plus.singleFunctor Aᵒᵖ 0).obj (op X)
  let b := (Q.columnPage n).hom.app (op X)
  let t' := (R.iteratedIso (n : ℤ)).hom.app Zr
  let c := (classicalDual F LF n).hom.app (op X)
  let col := ((Q.truncation n).edge G.op Q.degreeZero).app (F.op.rightDerivedFunctorPlus.obj Zr)
  let H := homologicalHomology (C := C) (n : ℤ)
  let l := (T.stalk W).inv ≫ H.map (LG.functor.map
    (T.point.inv.app Y ≫ ((minusT B).truncLEι (-(n : ℤ))).app
      (((minusT B).truncGE (-(n : ℤ))).obj Y))) ≫ T.upper.inv.app Y
  have hAxis : u.inv.op = a.page 0 0 n ≫ b ≫ G.op.map c :=
    leftColumn_on_stalk F G LF LG LFG R cmp hcmp O Q n X
  have hCo := reverseColumnEdge OB (n : ℤ) T (Q.truncation n) Q.degreeZero Ω Y
    (reversedPoint OB (n : ℤ) W) (reversedPoint_homology OB (n : ℤ) W)
    (reversedColumnStalk G LG OB OC OG (n : ℤ) T Q.degreeZero Q.degreeZero_hom W) f
  have hCl : c = (DerivedCategory.Plus.homologyFunctor Bᵒᵖ (n : ℤ)).map f ≫
      (OB.homology (n : ℤ)).hom.app (op Y) := by
    simp [c, classicalDual, rightStalkInputIso, f, OB, derivedReversal, Y, Z, Category.assoc]
  have hCo' : col ≫ G.op.map c = K.map f ≫ Ω.hom.app (op Y) ≫ l.op := by
    rw [hCl]
    simp only [l, op_comp, Category.assoc]
    exact hCo
  have hT : t.inv.op = a.target n ≫ t' ≫ K.map f ≫ Ω.hom.app (op Y) := by
    have h := dualIterated_on_stalk F G LF LG R X n
    simp only [rightIteratedStalkIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Iso.app_inv, Functor.map_comp, Category.assoc] at h
    rw [reversedDerivedHomology_hom_app]
    exact h
  have hE : a.target n ≫ E'.column n = E.column n ≫ a.page 0 0 n :=
    (dualFilteredEdges_to_right F G R Q X).column n
  have hQ : E'.column n ≫ b = t' ≫ col := rightColumn_at_stalk F G R Q n X
  have hFinal : E.column n ≫ u.inv.op = t.inv.op ≫ l.op := calc
    _ = (E.column n ≫ a.page 0 0 n) ≫ b ≫ G.op.map c := by rw [hAxis, Category.assoc]
    _ = a.target n ≫ E'.column n ≫ b ≫ G.op.map c := by rw [← hE, Category.assoc]
    _ = a.target n ≫ t' ≫ col ≫ G.op.map c := by rw [reassoc_of% hQ]
    _ = t.inv.op ≫ l.op := by rw [hCo', hT]; simp only [Category.assoc]
  apply Quiver.Hom.op_inj
  simp only [op_comp]
  change (t.hom.op ≫ E.column n) ≫ u.inv.op = l.op
  rw [Category.assoc, hFinal]
  exact (t.op).hom_inv_id_assoc _

private theorem canonicalEdges_of_iterated
    {P : Package F G LF LG LFG} (O : ObjectCase F G LF LG LFG P)
    (T : ∀ n : ℕ, DualTruncation (G := G) (LG := LG) (-(n : ℤ)))
    (hColumn : ∀ (n : ℕ) (X : A),
      let Z := (minusSingle A).obj X
      let Y := LF.functor.obj Z
      let H := homologicalHomology (C := C) (n : ℤ)
      (columnValueIso O n).inv.app X ≫ (O.column n).app X ≫ (P.iteratedIso n).hom.app Z =
        ((T n).stalk ((homologicalHomology (C := B) (n : ℤ)).obj Y)).inv ≫
          H.map (LG.functor.map
            ((T n).point.inv.app Y ≫
              (DerivedCategory.TStructure.t.onMinus.truncLEι (-(n : ℤ))).app
                ((DerivedCategory.TStructure.t.onMinus.truncGE (-(n : ℤ))).obj Y))) ≫
          (T n).upper.inv.app Y)
    (hRow : ∀ (n : ℕ) (X : A),
      let Z := (minusSingle A).obj X
      let H := homologicalHomology (C := C) (n : ℤ)
      (P.iteratedIso n).inv.app Z ≫ (O.row n).app X ≫ (rowValueIso O n).hom.app X =
        H.map (LG.functor.map (stalkCounit F LF 0 X))) :
    CanonicalEdges O := by
  refine ⟨T, fun n X => ⟨?_, ?_⟩⟩
  · simp only [firstEdge, objectTargetIso, targetIso, Iso.trans_hom, NatTrans.comp_app,
      associator_hom_app, Category.id_comp, isoWhiskerLeft_hom, isoWhiskerRight_hom,
      whiskerRight_app, whiskerLeft_app]
    simpa only [Category.assoc] using congrArg
      (fun f => f ≫ (homologicalHomology (C := C) (n : ℤ)).map
        (P.comparison.hom.app ((minusSingle A).obj X))) (hColumn n X)
  · simp only [secondEdge, objectTargetIso, targetIso, Iso.trans_inv, NatTrans.comp_app,
      associator_inv_app, Category.comp_id, isoWhiskerLeft_inv, isoWhiskerRight_inv,
      whiskerRight_app, whiskerLeft_app]
    simpa only [Category.assoc] using congrArg
      (fun f => (homologicalHomology (C := C) (n : ℤ)).map
        (P.comparison.inv.app ((minusSingle A).obj X)) ≫ f) (hRow n X)

theorem grothendieck : Specs.FullStatement.{u₁,v₁,u₂,v₂,u₃,v₃,w₁,w₂,w₃} := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro F G _ _ _ _ LF LG LFG hvan
  letI : HasDerivedCategory.{max u₁ v₁} Aᵒᵖ := HasDerivedCategory.standard Aᵒᵖ
  letI : HasDerivedCategory.{max u₂ v₂} Bᵒᵖ := HasDerivedCategory.standard Bᵒᵖ
  letI : HasDerivedCategory.{max u₃ v₃} Cᵒᵖ := HasDerivedCategory.standard Cᵒᵖ
  letI := preservesFiniteLimits_op F
  letI := preservesFiniteLimits_op G
  have hacyc (P : A) (hp : Projective P) : leftAcyclicValue G LG (F.obj P) :=
    (AcyclicTermComparison.leftVanishing B C inferInstance inferInstance G LG _).mpr
      (fun i => hvan P hp (i+1) (by omega))
  have hopen (I : Aᵒᵖ) (hi : Injective I) : rightAcyclicValue G.op (F.op.obj I) := by
    apply (AcyclicTermComparison.rightVanishing Bᵒᵖ Cᵒᵖ G.op _).mpr
    intro i
    have hp : Projective I.unop := by letI := hi; infer_instance
    exact ((hvan I.unop hp (i+1) (by omega)).op).of_iso
      ((classicalDual G LG (i+1)).app (F.op.obj I))
  obtain ⟨R, ⟨O⟩⟩ := GrothendieckEdges.grothendieck_edges Aᵒᵖ Bᵒᵖ Cᵒᵖ F.op G.op hopen
  obtain ⟨cmp, hcmp⟩ := canonical_comparison_exists F G LF LG LFG hacyc
  let P := dualPackage F G LF LG LFG R cmp hcmp
  let OL := dualObjectCase F G LF LG LFG R cmp hcmp O.objectCase
  refine ⟨P, abutmentConverges P, OL, ?_⟩
  apply canonicalEdges_of_iterated F G LF LG LFG OL (fun n => dualTruncation G LG (-(n : ℤ)))
  · exact canonicalColumn_on_stalk F G LF LG LFG R cmp hcmp O
  · exact canonicalRow_on_stalk F G LF LG LFG R cmp hcmp O

end Assembly
section Applicability
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃

theorem applicable : Specs.ExistsApplicable.{u₁,v₁,u₂,v₂,u₃,v₃,w₁,w₂,w₃} := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ F G _ _ _ _
  obtain ⟨hA, hB, ⟨LF⟩⟩ := TotalLeftDerivedFunctor.existence A B F
  obtain ⟨_, hC, ⟨LG⟩⟩ := TotalLeftDerivedFunctor.existence B C G
  obtain ⟨_, _, ⟨LFG⟩⟩ := TotalLeftDerivedFunctor.existence A C (F ⋙ G)
  obtain ⟨_, _, _, h⟩ := grothendieck A B C
  exact ⟨hA, hB, hC, ⟨LF⟩, ⟨LG⟩, ⟨LFG⟩, h F G⟩

end Applicability

section ClassicalExactness
open CategoryTheory.Category G05FilteredEdges
universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃

theorem classical_exactness : Specs.ClassicalExactness.{u₁,v₁,u₂,v₂,u₃,v₃,w₁,w₂,w₃} := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ F G _ _ LF LG LFG P O X
  let D := (objectSequence F G LF LG LFG P).obj X
  let f := (O.row 2).app X
  let d := differential D 0 2 2
  let g := (O.column 1).app X
  let h := (O.row 1).app X
  let i := (objectTargetIso (P := P) 2).app X
  let j := (rowValueIso O 2).app X
  let k := (columnValueIso O 1).app X
  let l := (objectTargetIso (P := P) 1).app X
  let m := (rowValueIso O 1).app X
  change FiveTerms (i.inv ≫ f ≫ j.hom) (j.inv ≫ d ≫ k.hom)
    (k.inv ≫ g ≫ l.hom) (l.inv ≫ h ≫ m.hom)
  have E := O.fiveTerms X
  haveI : Epi h := E.epi
  have hfd : (i.inv ≫ f ≫ j.hom) ≫ (j.inv ≫ d ≫ k.hom) = 0 := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc f d, E.fd, zero_comp, comp_zero]
  have hdg : (j.inv ≫ d ≫ k.hom) ≫ (k.inv ≫ g ≫ l.hom) = 0 := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc d g, E.dg, zero_comp, comp_zero]
  have hgh : (k.inv ≫ g ≫ l.hom) ≫ (l.inv ≫ h ≫ m.hom) = 0 := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc g h, E.gh, zero_comp, comp_zero]
  exact ⟨inferInstance, hfd, hdg, hgh,
    exact_conjugate i.symm j.symm k.symm f d E.fd E.exact_f_d hfd,
    exact_conjugate j.symm k.symm l.symm d g E.dg E.exact_d_g hdg,
    exact_conjugate k.symm l.symm m.symm g h E.gh E.exact_g_h hgh⟩

end ClassicalExactness

end AdvancedHomologicalAlgebra.LeftGrothendieckSpectralSequence
