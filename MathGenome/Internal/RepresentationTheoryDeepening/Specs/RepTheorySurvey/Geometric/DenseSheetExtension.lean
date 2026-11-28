import Mathlib.Analysis.Complex.Basic
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

noncomputable section

open CategoryTheory

namespace RepTheorySurvey.Geometric.DenseSheetExtensionSpecs

open Analytic

abbrev MarkedPlane := ℂ × ℂ

/-- Inclusion of one labelled sheet of the two-point parameter space. -/
def sheetInclusion {J : Type} [TopologicalSpace J] (l : J) :
    TopCat.of MarkedPlane ⟶ TopCat.of (MarkedPlane × J) :=
  TopCat.ofHom ⟨fun p ↦ (p, l), continuous_id.prodMk continuous_const⟩

/-- The germ along one sheet, starting in the stalk of the pulled-back direct image. -/
def pullbackSheetGerm {J : Type} [TopologicalSpace J] {Y Y' : TopCat.{0}}
    (f : TopCat.of (MarkedPlane × J) ⟶ Y) (k : Y' ≅ Y)
    (F : Sheaves (TopCat.of (MarkedPlane × J))) (p : MarkedPlane) (l : J)
    (y' : Y') (hy : k.hom y' = f (p, l)) :
    (stalk y').obj ((inverseImage k.hom).obj ((directImage f).obj F)) ⟶
      (stalk (X := TopCat.of (MarkedPlane × J)) (p, l)).obj F :=
  (inverseImageStalkIso k.hom ((directImage f).obj F) y').inv ≫
    eqToHom (congrArg (fun y ↦ (stalk y).obj ((directImage f).obj F)) hy) ≫
    TopCat.Presheaf.stalkPushforward Coeff.{0} f F.obj (p, l)

/-- Morphisms to the pulled-back direct image agree if their germs on each
constant sheet agree at every pair of distinct marks. -/
def DenseSheetExtension : Prop :=
  ∀ (J : Type) [TopologicalSpace J] [DiscreteTopology J]
    (Y Y' : TopCat.{0}) (f : TopCat.of (MarkedPlane × J) ⟶ Y) (k : Y' ≅ Y)
    (F : Sheaves (TopCat.of (MarkedPlane × J))) (G : Sheaves Y')
    (M : J → Coeff.{0}),
    (∀ l : J, (inverseImage (sheetInclusion l)).obj F ≅ constant (TopCat.of MarkedPlane) (M l)) →
    ∀ (u v : G ⟶ (inverseImage k.hom).obj ((directImage f).obj F)),
      (∀ (p : MarkedPlane), p.1 ≠ p.2 → ∀ (l : J) (y' : Y')
        (hy : k.hom y' = f (p, l)),
          (stalk y').map u ≫ pullbackSheetGerm f k F p l y' hy =
            (stalk y').map v ≫ pullbackSheetGerm f k F p l y' hy) →
      u = v

end RepTheorySurvey.Geometric.DenseSheetExtensionSpecs
