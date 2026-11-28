import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionUnitCone
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MiddleExtension

noncomputable section

open CategoryTheory

namespace RepTheorySurvey.Geometric.ConvolutionProjectionBaseChangeSpecs

open Analytic
open Analytic.IntersectionComplex (directImageComparison)
open Analytic.SingularCochains (HasContractibleOpenBasis)
open ConvolutionUnitConeSpecs (ordered surface convolutionMap orderedFactor)

/-- Projection to the second factor, with the product topology on the domain. -/
def productProjection (T X : TopCat.{0}) : TopCat.of (T × X) ⟶ X :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

/-- The product of the identity on the parameter space with a continuous map. -/
def productMap (T : TopCat.{0}) {Y X : TopCat.{0}} (m : Y ⟶ X) :
    TopCat.of (T × Y) ⟶ TopCat.of (T × X) :=
  TopCat.ofHom ⟨fun z => (z.1, m z.2),
    continuous_fst.prodMk (m.hom.continuous.comp continuous_snd)⟩

theorem productSquare (T : TopCat.{0}) {Y X : TopCat.{0}} (m : Y ⟶ X) :
    productMap T m ≫ productProjection T X = productProjection T Y ≫ m :=
  TopCat.ext (fun _ => rfl)

namespace Expected

def ProductProjectionType := ∀ T X : TopCat.{0}, TopCat.of (T × X) ⟶ X

def ProductMapType :=
  ∀ (T : TopCat.{0}) {Y X : TopCat.{0}}, (Y ⟶ X) → (TopCat.of (T × Y) ⟶ TopCat.of (T × X))

/-- The mate for projection along a parameter space is invertible on the shifted
rational coefficient complex of the actual ordered incidence space. -/
def ProjectionBaseChange : Prop :=
  ∀ (T : TopCat.{0}) [SecondCountableTopology T] [LocallyCompactSpace T] [T2Space T],
    HasContractibleOpenBasis T →
    ∀ (a : boundedBelowInverseImage (productMap T convolutionMap) ⊣
        derivedDirectImage (productMap T convolutionMap))
      (b : boundedBelowInverseImage convolutionMap ⊣ derivedDirectImage convolutionMap),
      IsIso (directImageComparison (productSquare T convolutionMap) a b orderedFactor)

end Expected
end RepTheorySurvey.Geometric.ConvolutionProjectionBaseChangeSpecs
