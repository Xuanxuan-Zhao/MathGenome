import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.Pairs
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularChains
import Mathlib.Algebra.Homology.Functor
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
import Mathlib.Topology.Sheaves.Flasque

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open P202Specs.CohomologyPairs P202Specs.SingularChains

universe u

namespace RepTheorySurvey.Geometric.Analytic.SingularCochains

abbrev Values := ULift.{u} ℚ

private def complexOfPresheaves {X : TopCat.{u}}
    (F : (Opens X)ᵒᵖ ⥤ CochainComplex Coeff.{u} ℤ) :
    CochainComplex ((Opens X)ᵒᵖ ⥤ Coeff.{u}) ℤ where
  X i := F ⋙ HomologicalComplex.eval _ _ i
  d i j :=
    { app U := (F.obj U).d i j
      naturality _ _ f := (F.map f).comm i j }
  shape i j h := by
    apply NatTrans.ext
    funext U
    exact (F.obj U).shape i j h
  d_comp_d' i j k _ _ := by
    apply NatTrans.ext
    funext U
    exact (F.obj U).d_comp_d i j k

/-- The presheaf complex of ordinary rational singular cochains. -/
def presheafComplex (X : TopCat.{u}) : CochainComplex ((Opens X)ᵒᵖ ⥤ Coeff.{u}) ℤ :=
  complexOfPresheaves ((Opens.toTopCat X).op ⋙ ordinaryCochainFunctor ℚ Values.{u})

/-- The presheaf complex of augmented singular cochains, with the dual of the
chain augmentation in degrees `-1` and `0`. -/
def augmentedPresheafComplex (X : TopCat.{u}) : CochainComplex ((Opens X)ᵒᵖ ⥤ Coeff.{u}) ℤ :=
  complexOfPresheaves ((Opens.toTopCat X).op ⋙ (reducedFunctor ℚ ℚ).op ⋙
    dualComplexFunctor ℚ Values.{u} (ComplexShape.down ℤ))

/-- Degreewise sheafification of the ordinary complex. -/
def sheafComplex (X : TopCat.{u}) : CochainComplex (Sheaves X) ℤ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}).mapHomologicalComplex _).obj
    (presheafComplex X)

/-- Degreewise sheafification of the augmented complex. -/
def augmentedSheafComplex (X : TopCat.{u}) : CochainComplex (Sheaves X) ℤ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}).mapHomologicalComplex _).obj
    (augmentedPresheafComplex X)

abbrev unit (X : TopCat.{u}) (q : ℤ) :
    (presheafComplex X).X q ⟶ ((sheafComplex X).X q).obj :=
  toSheafify (Opens.grothendieckTopology X) _

/-- The sheafification unit as a cochain map, in every degree. -/
def complexUnit (X : TopCat.{u}) :
    presheafComplex X ⟶ ((TopCat.Sheaf.forget Coeff.{u} X).mapHomologicalComplex _).obj
      (sheafComplex X) :=
  (NatTrans.mapHomologicalComplex
    (toSheafification (Opens.grothendieckTopology X) Coeff.{u}) _).app
      (presheafComplex X)

abbrev SimplexIn {X : TopCat.{u}} (U : Opens X) (q : ℕ) :=
  C(Convexity.StdSimplex ℝ (Fin (q + 1)), U)

/-- Coordinates on ordinary cochains, given by evaluation on basis simplices. -/
def coordinates {X : TopCat.{u}} (U : Opens X) (q : ℕ) :
    ((presheafComplex X).X (q : ℤ)).obj (op U) ≃ₗ[ℚ] (SimplexIn U q → Values.{u}) :=
  (ordinaryCochainsEquiv ℚ Values.{u} (TopCat.of U) q).trans
    ((Finsupp.llift Values.{u} ℚ ℚ _).symm.trans
      (LinearEquiv.funCongrLeft ℚ Values.{u} (simplexEquiv (TopCat.of U) q).symm))

/-- Postcomposition with an inclusion of open sets on singular simplices. -/
def includeSimplex {X : TopCat.{u}} {V U : Opens X} (i : V ⟶ U) {q : ℕ}
    (s : SimplexIn V q) : SimplexIn U q :=
  ((Opens.toTopCat X).map i).hom.comp s

private abbrev coefficient := ModuleCat.of ℚ Values.{u}

private def augmentationAtZero (Y : TopCat.{u}) :
    (ordinaryComplex ℚ ℚ Y).X 0 ⟶ coefficient.{u} :=
  (ordinaryNonnegativeIso ℚ ℚ Y 0).hom ≫ P202Specs.SingularChains.augmentation ℚ ℚ Y

private theorem augmentationAtZero_natural {Y Z : TopCat.{u}} (f : Y ⟶ Z) :
    ((ordinaryFunctor ℚ ℚ).map f).f 0 ≫ augmentationAtZero Z = augmentationAtZero Y := by
  change (HomologicalComplex.extendMap (chainMap ℚ ℚ f) (degreeEmbedding 0)).f 0 ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (show (degreeEmbedding 0).f 0 = 0 from rfl)]
  change ((ordinaryNonnegativeIso ℚ ℚ Y 0).hom ≫ (chainMap ℚ ℚ f).f 0 ≫
    (ordinaryNonnegativeIso ℚ ℚ Z 0).inv) ≫
      ((ordinaryNonnegativeIso ℚ ℚ Z 0).hom ≫ P202Specs.SingularChains.augmentation ℚ ℚ Z) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, augmentation_naturality]
  rfl

private theorem augmentationAtZero_d (Y : TopCat.{u}) :
    (ordinaryComplex ℚ ℚ Y).d 1 0 ≫ augmentationAtZero Y = 0 := by
  rw [← cancel_epi (ordinaryNonnegativeIso ℚ ℚ Y 1).inv, comp_zero]
  change (ordinaryNonnegativeIso ℚ ℚ Y 1).inv ≫ (ordinaryComplex ℚ ℚ Y).d 1 0 ≫
    (ordinaryNonnegativeIso ℚ ℚ Y 0).hom ≫ P202Specs.SingularChains.augmentation ℚ ℚ Y = 0
  rw [← Category.assoc, ← Category.assoc, Category.assoc
    (ordinaryNonnegativeIso ℚ ℚ Y 1).inv,
    show (ordinaryNonnegativeIso ℚ ℚ Y 1).inv ≫
      (ordinaryComplex ℚ ℚ Y).d 1 0 ≫ (ordinaryNonnegativeIso ℚ ℚ Y 0).hom =
      (complex ℚ ℚ Y).d 1 0 from P202.SingularChains.ordinary_boundary ℚ ℚ Y 0,
    augmentation_boundary]

private def dualCoefficientIso :
    coefficient.{u} ≅ (dualFunctor ℚ Values.{u}).obj (op coefficient.{u}) :=
  ((LinearMap.ringLmapEquivSelf ℚ ℚ Values.{u}).symm.trans
    (LinearEquiv.arrowCongr
      (ULift.moduleEquiv.symm : ℚ ≃ₗ[ℚ] Values.{u}) (LinearEquiv.refl ℚ Values.{u}))).toModuleIso

/-- The presheaf coaugmentation sends a scalar to the constant singular
zero-cochain with that value. -/
def presheafAugmentation (X : TopCat.{u}) :
    (Functor.const ((Opens X)ᵒᵖ)).obj coefficient.{u} ⟶ (presheafComplex X).X 0 where
  app U := dualCoefficientIso.hom ≫
    (dualFunctor ℚ Values.{u}).map (augmentationAtZero (TopCat.of U.unop)).op
  naturality U V f := by
    let D := dualFunctor ℚ Values.{u}
    let g := (Opens.toTopCat X).map f.unop
    change 𝟙 _ ≫ (_ ≫ D.map (augmentationAtZero ((Opens.toTopCat X).obj V.unop)).op) =
      (_ ≫ D.map (augmentationAtZero ((Opens.toTopCat X).obj U.unop)).op) ≫
        D.map (((ordinaryFunctor ℚ ℚ).map g).f 0).op
    rw [Category.id_comp, Category.assoc, ← Functor.map_comp, ← op_comp,
      augmentationAtZero_natural]

/-- The coaugmentation of the degreewise sheafification by the constant
rational sheaf. -/
def augmentationArrow (X : TopCat.{u}) : rational X ⟶ (sheafComplex X).X 0 :=
  (presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}).map (presheafAugmentation X)

theorem augmentationArrow_d (X : TopCat.{u}) :
    augmentationArrow X ≫ (sheafComplex X).d 0 1 = 0 := by
  let sh := presheafToSheaf (Opens.grothendieckTopology X) Coeff.{u}
  change sh.map (presheafAugmentation X) ≫ sh.map ((presheafComplex X).d 0 1) = 0
  rw [← Functor.map_comp, ← Functor.map_zero (F := sh)]
  congr 1
  apply NatTrans.ext
  funext U
  let D := dualFunctor ℚ Values.{u}
  let Y := TopCat.of U.unop
  change (dualCoefficientIso.hom ≫ D.map (augmentationAtZero Y).op) ≫
    D.map ((ordinaryComplex ℚ ℚ Y).d 1 0).op = 0
  rw [Category.assoc, ← Functor.map_comp, ← op_comp, augmentationAtZero_d, op_zero,
    Functor.map_zero, comp_zero]

/-- The canonical map from the degree-zero constant rational sheaf to the
singular cochain sheaf complex. -/
def augmentation (X : TopCat.{u}) :
    (CochainComplex.singleFunctor (Sheaves X) 0).obj (rational X) ⟶ sheafComplex X :=
  HomologicalComplex.mkHomFromSingle (augmentationArrow X) (by
    intro j hj
    change 0 + 1 = j at hj
    rw [← hj, zero_add]
    exact augmentationArrow_d X)

/-- The cochain complex of sections of the sheafified singular cochains. -/
abbrev evaluatedComplex {X : TopCat.{u}} (U : Opens X) :=
  ((sectionsOn U).mapHomologicalComplex (.up ℤ)).obj (sheafComplex X)

/-- The map from ordinary cochains on an open to the sections of their
sheafification, obtained by evaluation of the unit cochain map. -/
def sectionMap {X : TopCat.{u}} (U : Opens X) :
    ordinaryCochains ℚ Values.{u} (TopCat.of U) ⟶ evaluatedComplex U :=
  (((evaluation (Opens X)ᵒᵖ Coeff.{u}).obj (op U)).mapHomologicalComplex _).map
    (complexUnit X)

/-- Every open neighborhood admits a contractible open refinement at the point. -/
def HasContractibleOpenBasis (X : TopCat.{u}) : Prop :=
  ∀ (x : X) (U : Opens X), x ∈ U → ∃ V : Opens X,
    x ∈ V ∧ V ≤ U ∧ ContractibleSpace V

namespace Expected

def PresheafComplexType := ∀ X : TopCat.{u}, CochainComplex ((Opens X)ᵒᵖ ⥤ Coeff.{u}) ℤ

def SheafComplexType := ∀ X : TopCat.{u}, CochainComplex (Sheaves X) ℤ

def ComplexUnitType := ∀ X : TopCat.{u},
  presheafComplex X ⟶ ((TopCat.Sheaf.forget Coeff.{u} X).mapHomologicalComplex _).obj
    (sheafComplex X)

def SectionMapType := ∀ {X : TopCat.{u}} (U : Opens X),
  ordinaryCochains ℚ Values.{u} (TopCat.of U) ⟶ evaluatedComplex U

def CoordinatesType := ∀ {X : TopCat.{u}} (U : Opens X) (q : ℕ),
  ((presheafComplex X).X (q : ℤ)).obj (op U) ≃ₗ[ℚ] (SimplexIn U q → Values.{u})

def CoordinatesRestriction : Prop :=
  ∀ {X : TopCat.{u}} {V U : Opens X} (q : ℕ) (i : V ⟶ U)
    (c : ((presheafComplex X).X (q : ℤ)).obj (op U)) (s : SimplexIn V q),
      coordinates V q (((presheafComplex X).X (q : ℤ)).map i.op c) s =
        coordinates U q c (includeSimplex i s)

def AugmentationType := ∀ X : TopCat.{u},
  (CochainComplex.singleFunctor (Sheaves X) 0).obj (rational X) ⟶ sheafComplex X

def Resolution : Prop :=
  ∀ (X : TopCat.{u}), HasContractibleOpenBasis X → QuasiIso (augmentation X)

def NonnegativeSupport : Prop :=
  ∀ (X : TopCat.{u}), (sheafComplex X).IsStrictlyGE 0

def SectionSurjectivity : Prop :=
  ∀ (X : TopCat.{u}) [SecondCountableTopology X] [LocallyCompactSpace X] [T2Space X]
    (U : Opens X) (q : ℕ), Function.Surjective ((unit X (q : ℤ)).app (op U))

def Flabbiness : Prop :=
  ∀ (X : TopCat.{u}) [SecondCountableTopology X] [LocallyCompactSpace X] [T2Space X]
    (q : ℕ), TopCat.Sheaf.IsFlasque ((sheafComplex X).X (q : ℤ))

def AugmentedExactness : Prop :=
  ∀ (X : TopCat.{u}), HasContractibleOpenBasis X → (augmentedSheafComplex X).Acyclic

open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues in
def FlasqueAcyclicity : Prop :=
  letI := HasDerivedCategory.standard Coeff.{u}
  ∀ (X : TopCat.{u}) (F : Sheaves X), TopCat.Sheaf.IsFlasque F →
    ∀ (U : Opens X) (n : ℕ), IsZero ((rightValue (sectionsOn U) (n + 1)).obj F)

end Expected
end RepTheorySurvey.Geometric.Analytic.SingularCochains
