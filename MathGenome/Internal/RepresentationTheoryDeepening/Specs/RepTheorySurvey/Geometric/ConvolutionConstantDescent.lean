import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.IntersectionComplexes
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedLocalSheaves
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace RepTheorySurvey.Geometric.ConvolutionConstantDescentSpec

open Analytic LocalSheaf

abbrev scalars : Coeff.{u} := ModuleCat.of ℚ (ULift.{u} ℚ)

def constantAdj (X : TopCat.{u}) :
    constantSheaf (Opens.grothendieckTopology X) Coeff.{u} ⊣ globalSections X :=
  constantSheafAdj _ _ (isTerminalTop (α := Opens X))

/-- Global sections of a direct image identify with global sections on its source. -/
def directGlobalSections {Y X : TopCat.{u}} (m : Y ⟶ X) :
    directImage m ⋙ globalSections X ≅ globalSections Y :=
  NatIso.ofComponents (fun F => F.obj.mapIso (eqToIso (congrArg op (Opens.map_top m))))
    (fun f => f.hom.naturality _ |>.symm)

def ConstantPullbackType :=
  ∀ {Y X : TopCat.{u}} (m : Y ⟶ X), (inverseImage m).obj (rational X) ≅ rational Y

/-- Canonical pullback of the rational constant sheaf from the two adjunctions. -/
def constantPullback : ConstantPullbackType.{u} :=
  fun {Y X} m =>
    (((constantAdj X).comp (inverseDirectAdjunction m)).leftAdjointUniq
      ((constantAdj Y).ofNatIsoRight (directGlobalSections m).symm)).app scalars

def ShiftedConstantPullbackType :=
  ∀ {Y X : TopCat.{u}} (m : Y ⟶ X) (d : ℕ),
    (derivedInverseImage m).obj (IntersectionComplex.shiftedConstant X d).obj ≅
      (IntersectionComplex.shiftedConstant Y d).obj

/-- The same comparison on a constant sheaf in degree zero, shifted by `d`. -/
def shiftedConstantPullback : ShiftedConstantPullbackType.{u} :=
  fun {Y X} m d => by
    let F := inverseImage m
    let e := (F.mapDerivedCategorySingleFunctor 0).app (rational X) ≪≫
      (DerivedCategory.singleFunctor (Sheaves Y) 0).mapIso (constantPullback m)
    exact (F.mapDerivedCategory.commShiftIso (d : ℤ)).app _ ≪≫
      (shiftFunctor (Derived Y) (d : ℤ)).mapIso e

/-- The inverse image of the identity is compared with the identity via
uniqueness of the left adjoint to the identity direct image. -/
def inverseImageIdentity (X : TopCat.{u}) :
    inverseImage (𝟙 X) ≅ 𝟭 (Sheaves X) :=
  (inverseDirectAdjunction (𝟙 X)).leftAdjointUniq (Adjunction.id (C := Sheaves X))

/-- The identity comparison induced by localization of the sheaf-level one. -/
def derivedInverseImageIdentity (X : TopCat.{u}) :
    derivedInverseImage (𝟙 X) ≅ 𝟭 (Derived X) := by
  let F := inverseImage (𝟙 X)
  let I := 𝟭 (Sheaves X)
  have e : F.mapDerivedCategory ≅ I.mapDerivedCategory :=
    Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso (Sheaves X) (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      (I.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
      F.mapDerivedCategory I.mapDerivedCategory
      (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex (inverseImageIdentity X) _)
        (DerivedCategory.Q (C := Sheaves X)))
  exact e ≪≫ Functor.mapDerivedCategoryIdIso (Sheaves X)

def TensorPresheafType := ∀ {Z : TopCat.{0}}, Sheaves Z → Sheaves Z → Z.Presheaf Coeff.{0}

/-- The sectionwise tensor before sheafification. -/
def tensorPresheaf : TensorPresheafType :=
  fun F G =>
    { obj U := F.obj.obj U ⊗ G.obj.obj U
      map i := F.obj.map i ⊗ₘ G.obj.map i
      map_id U := by simp
      map_comp i j := by simp }

def CoefficientTensorType := ∀ {Z : TopCat.{0}}, Sheaves Z → Sheaves Z → Sheaves Z

/-- The tensor of the two rational sheaves is the sheafified sectionwise tensor. -/
def coefficientTensor : CoefficientTensorType :=
  fun {Z} F G =>
    (presheafToSheaf (Opens.grothendieckTopology Z) Coeff.{0}).obj (tensorPresheaf F G)

def constantSections (Z : TopCat.{0}) (U : (Opens Z)ᵒᵖ) :
    scalars ⟶ (rational Z).obj.obj U :=
  ((sheafificationAdjunction (Opens.grothendieckTopology Z) Coeff.{0}).unit.app
    ((Functor.const (Opens Z)ᵒᵖ).obj scalars)).app U

def scalarProduct : (scalars : Coeff.{0}) ⊗ scalars ⟶ scalars :=
  ModuleCat.ofHom (TensorProduct.lift (LinearMap.mul ℚ (ULift.{0} ℚ)))

abbrev pulledBackTensor {Z X Y : TopCat.{0}} (a : Z ⟶ X) (b : Z ⟶ Y) : Sheaves Z :=
  coefficientTensor ((inverseImage a).obj (rational X)) ((inverseImage b).obj (rational Y))

/-- On each open, the two pulled-back constant sections multiply in the specified
order via the unit into the sheafified tensor. -/
def MultipliesCoefficients {Z X Y : TopCat.{0}} (a : Z ⟶ X) (b : Z ⟶ Y)
    (e : pulledBackTensor a b ≅ rational Z) : Prop :=
  let F := (inverseImage a).obj (rational X)
  let G := (inverseImage b).obj (rational Y)
  let η := (sheafificationAdjunction (Opens.grothendieckTopology Z) Coeff.{0}).unit
  ∀ U : (Opens Z)ᵒᵖ,
    ((constantSections Z U ≫ (constantPullback a).inv.hom.app U) ⊗ₘ
      (constantSections Z U ≫ (constantPullback b).inv.hom.app U)) ≫
      (η.app (tensorPresheaf F G)).app U ≫ e.hom.hom.app U =
        scalarProduct ≫ constantSections Z U

/-- The two singly shifted factors contribute total shift `1 + 1`. -/
abbrev shiftedTensor {Z X Y : TopCat.{0}} (a : Z ⟶ X) (b : Z ⟶ Y) : Derived Z :=
  ((DerivedCategory.singleFunctor (Sheaves Z) 0).obj (pulledBackTensor a b))⟦(2 : ℤ)⟧

/-- The comparison of the two pullbacks is specified by the constant
coefficient identifications for the action and projection. -/
def NormalizedCoefficients {H : AnalyticGroup.{0}} {Z : TopCat.{0}}
    (A : AnalyticAction H Z) (d : ℕ) : Prop :=
  ∃ e : A.Equivariance (IntersectionComplex.shiftedConstant Z d).obj,
    e.iso = shiftedConstantPullback A.act d ≪≫
      (shiftedConstantPullback (AnalyticAction.projection H Z) d).symm

namespace Expected

def TensorMultiplication : Prop :=
  ∀ {Z X Y : TopCat.{0}} (a : Z ⟶ X) (b : Z ⟶ Y),
    ∃ μ : pulledBackTensor a b ≅ rational Z, MultipliesCoefficients a b μ

def ShiftedPullbackComposition : Prop :=
  ∀ {W Z X : TopCat.{0}} (k : W ⟶ Z) (q : Z ⟶ X) (d : ℕ),
    (derivedInverseImageComposition k q).hom.app
        (IntersectionComplex.shiftedConstant X d).obj ≫
      (derivedInverseImage k).map (shiftedConstantPullback q d).hom ≫
      (shiftedConstantPullback k d).hom =
    (shiftedConstantPullback (k ≫ q) d).hom

def ShiftedPullbackIdentity : Prop :=
  ∀ (X : TopCat.{0}) (d : ℕ),
    shiftedConstantPullback (𝟙 X) d =
      (derivedInverseImageIdentity X).app (IntersectionComplex.shiftedConstant X d).obj

def NormalizedEquivariance : Prop :=
  ∀ {H : AnalyticGroup.{0}} {Z : TopCat.{0}} (A : AnalyticAction H Z) (d : ℕ),
    NormalizedCoefficients A d

/-- The shifted multiplication identifies the representative-space tensor with the
pullback of the descended coefficient model. Its comparison agrees on further
pullback, in particular for maps from the overlaps of the frame quotient. -/
def ShiftedDescent : Prop :=
  ∀ {Z X Y S : TopCat.{0}} (a : Z ⟶ X) (b : Z ⟶ Y) (q : Z ⟶ S),
    ∃ (μ : pulledBackTensor a b ≅ rational Z)
      (e : (derivedInverseImage q).obj (IntersectionComplex.shiftedConstant S 2).obj ≅
        shiftedTensor a b),
      let μ₂ : shiftedTensor a b ≅ (IntersectionComplex.shiftedConstant Z 2).obj :=
        (shiftFunctor (Derived Z) (2 : ℤ)).mapIso
          ((DerivedCategory.singleFunctor (Sheaves Z) 0).mapIso μ)
      MultipliesCoefficients a b μ ∧ e ≪≫ μ₂ = shiftedConstantPullback q 2 ∧
      ∀ (W : TopCat.{0}) (k : W ⟶ Z),
        (derivedInverseImageComposition k q).hom.app
            (IntersectionComplex.shiftedConstant S 2).obj ≫
          (derivedInverseImage k).map (e.hom ≫ μ₂.hom) ≫
          (shiftedConstantPullback k 2).hom =
        (shiftedConstantPullback (k ≫ q) 2).hom

end Expected

end RepTheorySurvey.Geometric.ConvolutionConstantDescentSpec
