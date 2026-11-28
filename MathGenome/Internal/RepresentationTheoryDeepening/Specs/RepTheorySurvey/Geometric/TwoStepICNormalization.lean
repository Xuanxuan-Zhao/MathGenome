import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionEquivariantSplitting
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TwoStepIntersectionComplex

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory TopologicalSpace Topology

namespace RepTheorySurvey.Geometric.TwoStepICNormalizationSpecs

open Analytic
open Analytic.IntersectionComplex (DimensionFiltration FiltrationIso attachmentι complex
  shiftedConstant surfaceFiltration)
open ConvolutionAnalyticChartsSpecs (surface)
open ConvolutionBundleSpecs (secondPlane)
open ConvolutionConstantDescentSpec (shiftedConstantPullback)
open ConvolutionEquivariantSplittingSpecs (SplittingData)
open EquivariantIntersectionComplexesSpecs
open LatticeModelSpecs MinusculeAndTwoStepSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs

/-- The normalization of the GS10 map on the terminal surface. The chart
identifies the open complements of the distinguished points, and the adjunct
equation fixes the constant-coefficient identification on that open stratum. -/
def IsGS10Identification (a : DerivedAdjunctions.{0}) (d : SplittingData)
    (e : (shiftedConstant surface 2).obj ≅
      (IntersectionComplex.surface d.point d.closed).obj) : Prop :=
  let U := complementOpen {d.point} d.closed
  let j := openInclusion U
  let K := shiftedConstant surface 2
  let F := shiftedConstant (TopCat.of U) 2
  e.hom ≫ attachmentι j U.isOpenEmbedding 0 F =
    ((a j).homEquiv K F (ObjectProperty.homMk (shiftedConstantPullback j 2).hom)).hom

/-- The terminal surface and the occupied Schubert model carry the same
lattices and the same normalized rational intersection complex. -/
structure TerminalComparison (c : ContinuousJets) (a : DerivedAdjunctions.{0})
    (d : SplittingData) {bound : OrbitBound twoStepPair 2}
    (B : SchubertJetAction c twoStepPair 2 bound)
    (D : DimensionFiltration (SchubertSpace twoStepPair 2 bound) 0)
    (β : B.action.Equivariance (complex D).obj) where
  latticeChart : surface ≅ TwoStepIntersectionComplexSpecs.X
  chartScalar : (latticeChart.hom d.point).val = scalarPoint
  model : surface ≅ SchubertSpace twoStepPair 2 bound
  lattice : surface → BoundedLattice 2 2
  chartCoordinates : ∀ p, (latticeChart.hom p).val = (lattice p).val
  terminalCoordinates : ∀ p,
    secondPlane p = (latticeSubspace 0 2 (lattice p).val).map twoStepCoordinates.toLinearMap
  modelCoordinates : ∀ p, schubertPointSubspace (model.hom p) = boundedSubspace (lattice p)
  modelFiltration : FiltrationIso model (surfaceFiltration d.point d.closed) D
  /-- Level one is reduction modulo `t^2`. Higher actions factor through
  this action by the truncations of `jetSystem c`. -/
  action : JetAction (jetSystem c) surface
  cutoff : action.cutoff = 1
  actsAtTwo : (action.action 1 cutoff.le).act = d.terminalAction.act
  modelAction : Intertwines action B.action model.hom
  constantDatum : action.Equivariance (shiftedConstant surface 2).obj
  constantCoefficients : ∀ k hk, (constantDatum.datum k hk).iso =
    shiftedConstantPullback (action.action k hk).act 2 ≪≫
      (shiftedConstantPullback (AnalyticAction.projection ((jetSystem c).group k) surface) 2).symm
  constantAtTwo : (constantDatum.datum 1 cutoff.le).iso.hom =
    eqToHom (congrArg (fun f => (derivedInverseImage f).obj (shiftedConstant surface 2).obj)
      actsAtTwo) ≫ d.constantEq.iso.hom
  intersectionDatum : action.Equivariance (IntersectionComplex.surface d.point d.closed).obj
  normalized : NormalizedICDatum (@a) action (surfaceFiltration d.point d.closed) intersectionDatum
  constantIdentification :
    (shiftedConstant surface 2).obj ≅ (IntersectionComplex.surface d.point d.closed).obj
  isGS10Identification : IsGS10Identification (@a) d constantIdentification
  constantIntertwines : ∀ k hk,
    ConvolutionEquivariantSplittingSpecs.Intertwines
      (constantDatum.datum k hk) (intersectionDatum.datum k hk) constantIdentification.hom
  modelIdentification : (IntersectionComplex.surface d.point d.closed).obj ≅
    (derivedInverseImage model.hom).obj (complex D).obj
  modelIntertwines : IntertwinesPullback modelAction intersectionDatum β modelIdentification.hom

namespace Expected

/-- For the supplied splitting and the normalized orbit IC data at the chosen
jet system, identify the terminal constant summand with that orbit IC. -/
def TerminalICNormalization : Prop :=
  ∀ (c : ContinuousJets) (a : DerivedAdjunctions.{0}) (d : SplittingData)
    (bound : OrbitBound twoStepPair 2) (B : SchubertJetAction c twoStepPair 2 bound)
    (P : Stratification (SchubertSpace twoStepPair 2 bound))
    (D : DimensionFiltration (SchubertSpace twoStepPair 2 bound) 0),
    IsNormalizedOrbitIC twoStepPair 2 bound (𝟙 _) 1 P D →
    ∀ (β : B.action.Equivariance (complex D).obj), NormalizedICDatum (@a) B.action D β →
      Nonempty (TerminalComparison c (@a) d B D β)

end Expected
end RepTheorySurvey.Geometric.TwoStepICNormalizationSpecs
