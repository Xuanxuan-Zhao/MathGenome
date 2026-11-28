import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionSurface
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SingularCochainSheaves

namespace RepTheorySurvey.Geometric.ConvolutionAnalyticChartsSpecs

noncomputable section

open CategoryTheory
open LinearAlgebraicGroups (Points)
open LatticeModelSpecs MinusculeAndTwoStepSpecs ConvolutionBundleSpecs ConvolutionSurfaceSpecs

/-- The analytic topology of the terminal Schubert scheme is induced by its
inclusion in the Grassmannian of two-planes. -/
abbrev surfacePointTopology : TopologicalSpace (Points twoStepScheme complexAlgebra) :=
  TopologicalSpace.induced (fun p => p ≫ twoStepSchemeInGrassmannian)
    (grassmannianAnalyticTopology twoStepBasis twoStepRank)

attribute [local instance] surfacePointTopology

abbrev surface : TopCat :=
  @TopCat.of (Points twoStepScheme complexAlgebra) surfacePointTopology

/-- The ordered space with the shared topology induced by both Grassmannian
coordinates. -/
abbrev ordered : TopCat :=
  @TopCat.of (Points incidenceScheme complexAlgebra) incidenceAnalyticTopology

/-- The complement of the scalar terminal point in the analytic Schubert space. -/
def terminalComplement (x : surface) : Set surface :=
  ({x} : Set surface)ᶜ

/-- The inverse image of the scalar complement under the terminal projection. -/
def orderedComplement (x : surface) : Set ordered :=
  (fun q : ordered => q ≫ terminalProjection) ⁻¹' terminalComplement x

namespace Expected

/-- The four topological hypotheses for the singular cochain comparison on
the analytic ordered convolution surface. -/
def OrderedTopology : Prop :=
  SecondCountableTopology ordered ∧ LocallyCompactSpace ordered ∧ T2Space ordered ∧
    Analytic.SingularCochains.HasContractibleOpenBasis ordered

/-- The terminal projection is a homeomorphism away from the scalar point.
The inverse uses the first-coordinate image of the terminal plane. -/
def OpenOrbitHomeomorphism : Prop :=
  ∀ (x : surface), ScalarTerminalPoint x →
    ∃ e : orderedComplement x ≃ₜ terminalComplement x,
      (∀ q, (e q).val = q.val ≫ terminalProjection) ∧
      ∀ p, firstPlane ((e.symm p).val ≫ firstProjection) =
        (secondPlane p.val).map (LinearMap.fst ℂ V V)

end Expected
end

end RepTheorySurvey.Geometric.ConvolutionAnalyticChartsSpecs
