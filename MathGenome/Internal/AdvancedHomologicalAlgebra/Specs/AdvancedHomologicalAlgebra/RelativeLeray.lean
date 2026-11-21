import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.HigherDirectImageLocalDescription
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GrothendieckEdges

/-! HA-H07, relative Leray (3790–3792, 3803–3814).
The target category is that of modules over the actual sheaf of rings on Z.
The row diagram starts at E₂ and is indexed by (p,p+q).
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 150000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace
open AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.HigherDirectImageLocalTheory
open AdvancedHomologicalAlgebra.GrothendieckSpectralSequence
open AdvancedHomologicalAlgebra.GrothendieckEdges
open AdvancedHomologicalAlgebra.HypercohomologyDerivedNaturality

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AdvancedHomologicalAlgebra.RelativeLeray

variable {X Y Z : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (T : RingSheaf Z)
  (f : X ⟶ Y) (g : Y ⟶ Z)
  (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R)
  (ψ : T ⟶ (TopCat.Sheaf.pushforward RingCat.{u} g).obj S)

/-- Pushforward along the composite, using the composite map of structure sheaves. -/
abbrev compositeDirectImage : Modules R ⥤ Modules T :=
  directImage R T (f ≫ g) (ψ ≫ (TopCat.Sheaf.pushforward RingCat.{u} g).map φ)

local notation "F₀" => directImage R S f φ
local notation "G₀" => directImage S T g ψ
local notation "FG₀" => compositeDirectImage R S T f g φ ψ

/-- Composition of pushforwards, using the actual restriction of scalars on opens. -/
def underivedCompositionIso : F₀ ⋙ G₀ ≅ FG₀ :=
  SheafOfModules.pushforwardComp (F := Opens.map g) (G := Opens.map f) ψ φ

/-- Applying bounded right derivation to the actual underived composite. -/
def derivedPushforwardIso : (F₀ ⋙ G₀).rightDerivedFunctorPlus ≅ (FG₀).rightDerivedFunctorPlus where
  hom := (underivedCompositionIso R S T f g φ ψ).hom.rightDerivedFunctorPlus
  inv := (underivedCompositionIso R S T f g φ ψ).inv.rightDerivedFunctorPlus
  hom_inv_id := by rw [← NatTrans.rightDerivedFunctorPlus_comp, Iso.hom_inv_id,
    NatTrans.rightDerivedFunctorPlus_id]
  inv_hom_id := by rw [← NatTrans.rightDerivedFunctorPlus_comp, Iso.inv_hom_id,
    NatTrans.rightDerivedFunctorPlus_id]

/-- The direct-image composition comparison is the HA-R12 comparison after
identifying the underived composite. -/
def compositionMap : (FG₀).rightDerivedFunctorPlus ⟶
    (F₀).rightDerivedFunctorPlus ⋙ (G₀).rightDerivedFunctorPlus :=
  (derivedPushforwardIso R S T f g φ ψ).inv ≫
    _root_.Specs.AdvancedHomologicalAlgebra.RightDerivedComposition.comparisonValue F₀ G₀

/-- One natural sequence on D⁺, whose restriction to sheaves is first quadrant. -/
structure Data where
  package : Package F₀ G₀
  edges : ObjectEdges F₀ G₀ package
  composition_isIso : IsIso (compositionMap R S T f g φ ψ)
  sheaf_quadrant : ∀ (M : Modules R) (r : ℕ) (p n : ℤ), p < 0 ∨ n < p →
    IsZero (((sequence F₀ G₀ package.row).obj
      ((DerivedCategory.Plus.singleFunctor (Modules R) 0).obj M)).page r p n)

variable {R S T f g φ ψ} (L : Data R S T f g φ ψ)

/-- The natural E₂ identification on bounded-below derived objects. -/
def Data.secondIso (p : ℕ) (q : ℤ) :
    sequence F₀ G₀ L.package.row ⋙ pageEval 0 (p : ℤ) ((p : ℤ) + q) ≅
      (F₀).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor (Modules S) q ⋙
        higherDirectImage S T g ψ p :=
  L.package.secondIso p q

variable (R S T f g φ ψ) in
/-- The HA-G04 abutment uses HA-R12 to identify the iterated derived functor
with the derived underived composite. This last factor identifies that
composite with pushforward along the composite map of ringed spaces. -/
def pushforwardComparison (n : ℤ) : compositeValue F₀ G₀ n ≅
    (FG₀).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor (Modules T) n :=
  isoWhiskerRight (derivedPushforwardIso R S T f g φ ψ)
    (DerivedCategory.Plus.homologyFunctor (Modules T) n)

def Data.targetIso (n : ℤ) :
    sequence F₀ G₀ L.package.row ⋙ targetEval n ≅
      (FG₀).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor (Modules T) n :=
  L.package.targetIso n ≪≫ pushforwardComparison R S T f g φ ψ n

/-- For sheaf inputs the same sequence has E₂^{p,q} = R^p g_* (R^q f_* M). -/
def Data.sheafSecondIso (p q : ℕ) :
    objectSequence F₀ G₀ L.package ⋙ pageEval 0 (p : ℤ) ((p : ℤ) + (q : ℤ)) ≅
      higherDirectImage R S f φ q ⋙ higherDirectImage S T g ψ p :=
  L.edges.objectCase.secondIso p q

variable (R S T f g φ ψ) in
/-- The sheaf abutment is R^n(gf)_* M. -/
def sheafPushforwardComparison (n : ℕ) :
    _root_.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightValue (F₀ ⋙ G₀) n ≅
      higherDirectImage R T (f ≫ g) (ψ ≫ (TopCat.Sheaf.pushforward RingCat.{u} g).map φ) n :=
  isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (Modules R) 0)
    (pushforwardComparison R S T f g φ ψ n)

def Data.sheafTargetIso (n : ℕ) :
    objectSequence F₀ G₀ L.package ⋙ targetEval (n : ℤ) ≅
      higherDirectImage R T (f ≫ g) (ψ ≫ (TopCat.Sheaf.pushforward RingCat.{u} g).map φ) n :=
  L.edges.objectCase.targetIso n ≪≫ sheafPushforwardComparison R S T f g φ ψ n

theorem Data.sheafTargetIso_eq (n : ℕ) :
    L.sheafTargetIso n =
      isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (Modules R) 0) (L.targetIso n) := by
  rw [Data.sheafTargetIso, L.edges.objectCase.targetIso_eq, Data.targetIso,
    isoWhiskerLeft_trans]
  rfl

/-- The natural bottom-row edge, in the actual relative abutment coordinates. -/
def Data.rowEdge (n : ℕ) :
    F₀ ⋙ higherDirectImage S T g ψ n ⟶
      higherDirectImage R T (f ≫ g) (ψ ≫ (TopCat.Sheaf.pushforward RingCat.{u} g).map φ) n :=
  derivedFirstEdge F₀ G₀ L.package n ≫ (sheafPushforwardComparison R S T f g φ ψ n).hom

/-- The natural left-column edge, in the actual relative abutment coordinates. -/
def Data.columnEdge (n : ℕ) :
    higherDirectImage R T (f ≫ g) (ψ ≫ (TopCat.Sheaf.pushforward RingCat.{u} g).map φ) n ⟶
      higherDirectImage R S f φ n ⋙ G₀ :=
  (sheafPushforwardComparison R S T f g φ ψ n).inv ≫
    classicalColumn F₀ G₀ (L.edges.truncation n) L.edges.degreeZero

theorem Data.row_comparison (n : ℕ) (M : Modules R) :
    (L.edges.rowPage n).hom.app M ≫ (L.rowEdge n).app M =
      (L.edges.filtered M).row n ≫ (L.sheafTargetIso n).hom.app M := by
  simp only [Data.rowEdge, Data.sheafTargetIso, NatTrans.comp_app, Iso.trans_hom]
  rw [← Category.assoc, ← Category.assoc, L.edges.first_comparison n M]

theorem Data.column_comparison (n : ℕ) (M : Modules R) :
    (L.sheafTargetIso n).hom.app M ≫ (L.columnEdge n).app M =
      (L.edges.filtered M).column n ≫ (L.edges.columnPage n).hom.app M := by
  simpa only [Data.columnEdge, Data.sheafTargetIso, NatTrans.comp_app, Iso.trans_hom,
    Category.assoc, Iso.hom_inv_id_app_assoc] using L.edges.second_comparison n M

/-- The filtration on H^n(R(gf)_* K) is formed from the actual diagram inclusions. -/
def Data.filtration (K : DerivedCategory.Plus (Modules R)) (p n : ℤ) :
    Subobject (((FG₀).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor (Modules T) n).obj K) := by
  letI := L.package.inclusion_mono K p n
  exact Subobject.mk ((((sequence F₀ G₀ L.package.row).obj K).inclusion p n) ≫
    (L.targetIso n).hom.app K)

end AdvancedHomologicalAlgebra.RelativeLeray

namespace Specs.AdvancedHomologicalAlgebra.RelativeLeray

open _root_.AdvancedHomologicalAlgebra.RelativeLeray
open _root_.Specs.AdvancedHomologicalAlgebra.AcyclicTermComparison

def Acyclicity : Prop :=
  ∀ {X Y Z : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (T : RingSheaf Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R)
    (ψ : T ⟶ (TopCat.Sheaf.pushforward RingCat.{u} g).obj S)
    (I : Modules R), Injective I →
      rightAcyclicValue (directImage S T g ψ) ((directImage R S f φ).obj I)

def CanonicalComposition : Prop :=
  ∀ {X Y Z : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (T : RingSheaf Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R)
    (ψ : T ⟶ (TopCat.Sheaf.pushforward RingCat.{u} g).obj S),
    IsIso (compositionMap R S T f g φ ψ)

def SpectralSequence : Prop :=
  ∀ {X Y Z : TopCat.{u}} (R : RingSheaf X) (S : RingSheaf Y) (T : RingSheaf Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{u} f).obj R)
    (ψ : T ⟶ (TopCat.Sheaf.pushforward RingCat.{u} g).obj S),
    letI (M : Modules T) : OrderBot (Subobject M) := Subobject.orderBot (C := Modules T)
    ∃ L : Data R S T f g φ ψ,
      (∀ K p n, L.filtration K (p + 1) n ≤ L.filtration K p n) ∧
      (∀ K n, ∃ a b : ℤ,
        (∀ p, p ≤ a → L.filtration K p n = ⊤) ∧
        (∀ p, b ≤ p → L.filtration K p n = ⊥))

end Specs.AdvancedHomologicalAlgebra.RelativeLeray
