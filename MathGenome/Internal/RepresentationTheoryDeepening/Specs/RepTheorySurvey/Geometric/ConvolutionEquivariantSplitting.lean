import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionActionComparisons
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionPointCoefficients
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionSplitting

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.ConvolutionEquivariantSplittingSpecs

open Analytic AnalyticAction ConvolutionUnitConeSpecs ConvolutionBundleSpecs
open ConvolutionActionComparisonsSpecs ConvolutionSplittingSpecs
open ConvolutionPointCoefficientsSpecs (TrivialPointEquivariance productPoint productPoint_closed)
open IntersectionComplex (shiftedConstant)
open LatticeModelSpecs BoundedLatticeSpecs

/-- All surviving jet groups are actual quotients by positive powers of the parameter. -/
abbrev higherJet {n : ℕ} (hn : 2 ≤ n) := GLJets 2 n (le_trans (by decide : 1 ≤ 2) hn)

def truncateToTwo {n : ℕ} (hn : 2 ≤ n) : higherJet hn →* Jets :=
  Matrix.GeneralLinearGroup.map (truncateJet hn)

def higherGroup {n : ℕ} {hn : 2 ≤ n} (h : IsTopologicalGroup (higherJet hn)) :
    AnalyticGroup where
  space := TopCat.of (higherJet hn)
  topologicalGroup := h

/-- The map between two sheaves intertwines their analytic descent data. -/
def Intertwines {H : AnalyticGroup.{0}} {Z : TopCat.{0}} {A : AnalyticAction H Z}
    {F G : Derived Z} (α : A.Equivariance F) (β : A.Equivariance G) (f : F ⟶ G) : Prop :=
  (derivedInverseImage A.act).map f ≫ β.iso.hom =
    α.iso.hom ≫ (derivedInverseImage (projection H Z)).map f

/-- Normalization of the equivariance on a pushforward by the actual two base-change mates. -/
def UsesConvolutionMates {H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {B : AnalyticAction H ordered} (commutes : Commutes A B)
    (α : A.Equivariance convolution.obj) : Prop :=
  ∃ (a : DerivedAdjunction (ConvolutionActionComparisonsSpecs.productMap H.space))
    (b : DerivedAdjunction convolutionMap),
    IsDerivedDirectAdjunction _ a ∧ IsDerivedDirectAdjunction _ b ∧
    IsIso (projectionMate H.space a b) ∧ IsIso (actionMate commutes a b) ∧
    α.iso.hom ≫ projectionComparison H.space a b = actionComparison commutes a b

/-- At higher jet levels the chosen equivariance is pulled back by actual truncation. -/
def PullsBackToHigherJets {H : AnalyticGroup.{0}}
    {Z : TopCat.{0}} {A : AnalyticAction H Z} {F : Derived Z} (α : A.Equivariance F)
    (φ : ∀ {n : ℕ} (hn : 2 ≤ n), higherJet hn →* H.space) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n),
    ∃ (h : IsTopologicalGroup (higherJet hn)) (hc : Continuous (φ hn)),
      let K := higherGroup h
      let A' := restrictAction (K := K) (φ hn) hc A
      ∃ β : A'.Equivariance F,
        pullbackMorphism (parameterMap (K := K) (φ hn) hc Z) rfl
          (TopCat.ext (fun _ => rfl)) α.iso.hom = β.iso.hom

/-- The unshifted costalk complex on the closed product has cohomology only in degree four. -/
def ProductCostalkConcentrated (H : AnalyticGroup.{0}) {x : surface}
    (hx : IsClosed ({x} : Set surface)) : Prop :=
  let F := (derivedExtraordinaryInverseImage (productPoint_closed H hx)).obj
    (LocalSheaf.sheafInDegreeZero (rational (Parameters H surface)))
  ∀ n : ℤ, n ≠ 4 → IsZero ((DerivedCategory.Plus.homologyFunctor _ n).obj F)

/-- The two vanishing Hom groups used for the splitting after projection pullback. -/
def ProductHomVanishing (H : AnalyticGroup.{0}) {x : surface}
    (hx : IsClosed ({x} : Set surface)) : Prop :=
  let p := derivedInverseImage (projection H surface)
  ∀ d : ℕ, (d = 2 ∨ d = 3) →
    Subsingleton (p.obj (pointSkyscraper x hx) ⟶ p.obj (shiftedConstant surface d).obj)

/-- The fixed splitting exists on the actual jet action and its inverse-image comparisons.
Its maps use the explicit normalization on the constant and closed-point summands. -/
structure SplittingData where
  topologicalGroup : IsTopologicalGroup Jets
  firstAction : AnalyticAction (jetGroup topologicalGroup) minuscule
  orderedAction : AnalyticAction (jetGroup topologicalGroup) ordered
  terminalAction : AnalyticAction (jetGroup topologicalGroup) surface
  first_action : ∀ g : Jets, ∀ p : minuscule,
    firstPlane (firstAction.act (g, p)) = (firstPlane p).map (constantJetLinear g)
  firstStage_equivariant : ∀ g : Jets, ∀ p : ordered,
    firstStageMap (orderedAction.act (g, p)) = firstAction.act (g, firstStageMap p)
  terminal_action : ∀ g : Jets, ∀ p : surface,
    secondPlane (terminalAction.act (g, p)) = (secondPlane p).map (twoTermJetLinear g)
  commutes : Commutes terminalAction orderedAction
  point : surface
  closed : IsClosed ({point} : Set surface)
  scalar : ConvolutionSurfaceSpecs.ScalarTerminalPoint point
  fixes : ∀ g : Jets, terminalAction.act (g, point) = point
  firstEq : firstAction.Equivariance minusculeFactor.obj
  orderedEq : orderedAction.Equivariance orderedFactor.obj
  constantEq : terminalAction.Equivariance (shiftedConstant surface 2).obj
  pointEq : terminalAction.Equivariance (pointSkyscraper point closed)
  convolutionEq : terminalAction.Equivariance convolution.obj
  first_normalized : firstEq.iso = shiftedConstantPullback firstAction.act 1 ≪≫
    (shiftedConstantPullback (projection _ minuscule) 1).symm
  ordered_normalized : orderedEq.iso = shiftedConstantPullback orderedAction.act 2 ≪≫
    (shiftedConstantPullback (projection _ ordered) 2).symm
  constant_normalized : constantEq.iso = shiftedConstantPullback terminalAction.act 2 ≪≫
    (shiftedConstantPullback (projection _ surface) 2).symm
  point_normalized : TrivialPointEquivariance fixes pointEq
  convolution_normalized : UsesConvolutionMates commutes convolutionEq
  unit_equivariant : Intertwines constantEq convolutionEq unit
  coneIso : unitCone ≅ pointSkyscraper point closed
  quotient_equivariant : Intertwines convolutionEq pointEq (quotientMap coneIso)
  sectionMap : pointSkyscraper point closed ⟶ convolution.obj
  section_identity : sectionMap ≫ quotientMap coneIso = 𝟙 _
  section_unique : ∀ s : pointSkyscraper point closed ⟶ convolution.obj,
    s ≫ quotientMap coneIso = 𝟙 _ → s = sectionMap
  section_equivariant : Intertwines pointEq convolutionEq sectionMap
  splitIso : ((shiftedConstant surface 2).obj ⊞ pointSkyscraper point closed) ≅ convolution.obj
  split_constant : biprod.inl ≫ splitIso.hom = unit
  split_point : biprod.inr ≫ splitIso.hom = sectionMap
  constant_perverse : IsMiddlePerverse (orbitStratification point closed) (shiftedConstant surface 2).obj
  point_perverse : IsMiddlePerverse (orbitStratification point closed) (pointSkyscraper point closed)
  convolution_perverse : IsMiddlePerverse (orbitStratification point closed) convolution.obj
  product_costalk : ProductCostalkConcentrated (jetGroup topologicalGroup) closed
  product_hom_vanishing : ProductHomVanishing (jetGroup topologicalGroup) closed
  higher_first : PullsBackToHigherJets firstEq truncateToTwo
  higher_ordered : PullsBackToHigherJets orderedEq truncateToTwo
  higher_constant : PullsBackToHigherJets constantEq truncateToTwo
  higher_point : PullsBackToHigherJets pointEq truncateToTwo
  higher_convolution : PullsBackToHigherJets convolutionEq truncateToTwo

namespace Expected

/-- The fixed unit and its unique section give the normalized equivariant splitting. -/
def ConvolutionEquivariantSplitting : Prop := Nonempty SplittingData

end Expected
end RepTheorySurvey.Geometric.ConvolutionEquivariantSplittingSpecs
