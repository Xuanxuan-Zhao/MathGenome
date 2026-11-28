import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.FiniteStageClosedExtensions
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TwoStepICNormalization

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace RepTheorySurvey.Geometric.MinusculeLocalSquareSpecs

open Analytic Analytic.IntersectionComplex LocalSheaf
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open ConvolutionAnalyticChartsSpecs (surface)
open ConvolutionEquivariantSplittingSpecs (SplittingData)
open ConvolutionUnitConeSpecs (convolution pointSkyscraper unit)
open EquivariantIntersectionComplexesSpecs (ContinuousJets jetSystem SchubertJetAction
  Intertwines IntertwinesPullback NormalizedICDatum)
open FiniteStageClosedExtensionSpecs (AgreesWithMates MatesAreIso)
open LatticeModelSpecs (BoundedLattice boundedSubspace OrbitBound)
open MinusculeAndTwoStepSpecs (scalarPair scalarPoint twoStepPair)
open RankTwoSchubertStrataSpecs (schubertPointSubspace)
open SchubertIntersectionConstructibilitySpecs (SchubertSpace IsNormalizedOrbitIC)
open TwoStepICNormalizationSpecs (TerminalComparison)

/-- The local comparisons for the fixed splitting and the normalized terminal IC.
The closed point is compared with the supplied scalar Schubert model, and its
skyscraper uses the same equivariance in the exact and derived mate equations. -/
structure LocalComparison (c : ContinuousJets) (a : DerivedAdjunctions.{0}) (d : SplittingData)
    {terminalBound : OrbitBound twoStepPair 2}
    {B : SchubertJetAction c twoStepPair 2 terminalBound}
    {D : DimensionFiltration (SchubertSpace twoStepPair 2 terminalBound) 0}
    {β : B.action.Equivariance (complex D).obj}
    (T : TerminalComparison c (@a) d B D β)
    (b : boundedBelowInverseImage (closedInclusion ({d.point} : Set surface)) ⊣
      closedExtensionPlus d.closed)
    {scalarBound : OrbitBound scalarPair 2}
    (C : SchubertJetAction c scalarPair 2 scalarBound)
    {E : DimensionFiltration (SchubertSpace scalarPair 2 scalarBound) 0}
    (γ : C.action.Equivariance (complex E).obj) where
  pointAction : JetAction (jetSystem c) (TopCat.of ({d.point} : Set surface))
  pointCutoff : pointAction.cutoff = 1
  pointActs : ∀ (k : ℕ) (hk : pointAction.cutoff ≤ k),
    (pointAction.action k hk).act =
      AnalyticAction.projection ((jetSystem c).group k) (TopCat.of ({d.point} : Set surface))
  pointDatum : pointAction.Equivariance (point d.point).obj
  /-- On the degree-zero rational complex, the two pullbacks are identified by
  the equality of the action and projection maps. -/
  pointCoefficients : ∀ (k : ℕ) (hk : pointAction.cutoff ≤ k),
    (pointDatum.datum k hk).iso.hom =
      eqToHom (congrArg (fun f => (derivedInverseImage f).obj (point d.point).obj)
        (pointActs k hk))
  model : TopCat.of ({d.point} : Set surface) ≅ SchubertSpace scalarPair 2 scalarBound
  lattice : TopCat.of ({d.point} : Set surface) → BoundedLattice 2 2
  latticeScalar : ∀ p, (lattice p).val = scalarPoint
  modelCoordinates : ∀ p, schubertPointSubspace (model.hom p) = boundedSubspace (lattice p)
  modelAction : Intertwines pointAction C.action model.hom
  modelIdentification : (point d.point).obj ≅ (derivedInverseImage model.hom).obj (complex E).obj
  modelIntertwines : IntertwinesPullback modelAction pointDatum γ modelIdentification.hom
  convolutionDatum : T.action.Equivariance convolution.obj
  convolutionAtTwo : (convolutionDatum.datum 1 T.cutoff.le).iso.hom =
    eqToHom (congrArg (fun f => (derivedInverseImage f).obj convolution.obj) T.actsAtTwo) ≫
      d.convolutionEq.iso.hom
  skyscraperDatum : T.action.Equivariance (pointSkyscraper d.point d.closed)
  skyscraperAtTwo : (skyscraperDatum.datum 1 T.cutoff.le).iso.hom =
    eqToHom (congrArg (fun f => (derivedInverseImage f).obj (pointSkyscraper d.point d.closed))
      T.actsAtTwo) ≫ d.pointEq.iso.hom
  pointInclusionAction : Intertwines pointAction T.action (closedInclusion ({d.point} : Set surface))
  exactExtensionMates : ∀ (k : ℕ) (hp : pointAction.cutoff ≤ k) (ht : T.action.cutoff ≤ k),
    let H := (jetSystem c).group k
    let i := closedInclusion ({d.point} : Set surface)
    let iH := parameterInclusion H i
    let F := point d.point
    let actionMate := adjointSquareMap (pullbackSquare (pointInclusionAction k hp ht)) (a iH) b F
    let projMate := adjointSquareMap (pullbackSquare (projectionSquare H i)) (a iH) b F
    (skyscraperDatum.datum k ht).iso.hom ≫ projMate.hom =
      actionMate.hom ≫ ((derivedDirectImage iH).map
        (ObjectProperty.homMk (pointDatum.datum k hp).iso.hom)).hom
  directImageMatesAreIso : MatesAreIso pointInclusionAction (@a) (point d.point)
  directImageMates :
    let i := closedInclusion ({d.point} : Set surface)
    let F := point d.point
    AgreesWithMates pointInclusionAction (@a) pointDatum skyscraperDatum
      (((a i).rightAdjointUniq b).inv.app F).hom
  sectionIntertwines : ∀ (k : ℕ) (hk : T.action.cutoff ≤ k),
    ConvolutionEquivariantSplittingSpecs.Intertwines (skyscraperDatum.datum k hk)
      (convolutionDatum.datum k hk) d.sectionMap
  unitIntertwines : ∀ (k : ℕ) (hk : T.action.cutoff ≤ k),
    ConvolutionEquivariantSplittingSpecs.Intertwines (T.intersectionDatum.datum k hk)
      (convolutionDatum.datum k hk) (T.constantIdentification.inv ≫ unit)

namespace Expected

/-- Construct the local point, skyscraper and convolution data for the supplied
terminal comparison and normalized scalar Schubert IC. -/
def MinusculeLocalSquare : Prop :=
  ∀ (c : ContinuousJets) (a : DerivedAdjunctions.{0}) (d : SplittingData)
    (terminalBound : OrbitBound twoStepPair 2)
    (B : SchubertJetAction c twoStepPair 2 terminalBound)
    (D : DimensionFiltration (SchubertSpace twoStepPair 2 terminalBound) 0)
    (β : B.action.Equivariance (complex D).obj)
    (T : TerminalComparison c (@a) d B D β)
    (b : boundedBelowInverseImage (closedInclusion ({d.point} : Set surface)) ⊣
      closedExtensionPlus d.closed)
    (scalarBound : OrbitBound scalarPair 2)
    (C : SchubertJetAction c scalarPair 2 scalarBound)
    (P : Stratification (SchubertSpace scalarPair 2 scalarBound))
    (E : DimensionFiltration (SchubertSpace scalarPair 2 scalarBound) 0),
    IsNormalizedOrbitIC scalarPair 2 scalarBound (𝟙 _) 0 P E →
    ∀ (γ : C.action.Equivariance (complex E).obj), NormalizedICDatum (@a) C.action E γ →
      Nonempty (LocalComparison c (@a) d T b C γ)

end Expected
end RepTheorySurvey.Geometric.MinusculeLocalSquareSpecs
