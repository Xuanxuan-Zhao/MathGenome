import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionBundle
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Category.TopCat.Basic

namespace RepTheorySurvey.Geometric.ConvolutionFrameQuotientSpecs

noncomputable section

open CategoryTheory Topology
open LinearAlgebraicGroups (Points)
open LatticeModelSpecs BoundedLatticeSpecs MinusculeAndTwoStepSpecs
open ConvolutionBundleSpecs

abbrev FrameRepresentative := Representatives (PositiveGL 2) firstStage (colength 1)

def representedSecondStage (p : FrameRepresentative) : Colength 1 :=
  ⟨p.val.2, p.property.2⟩

/-- The first frame is measured by its constant and linear coefficients.
The second modification uses the subspace topology of the lattice stage. -/
def representativeCoordinates (p : FrameRepresentative) :
    (Fin 2 → Fin 2 → Fin 2 → ℂ) × Colength 1 :=
  (fun i j k ↦ (p.val.1.val i j).coeff (k.val : ℤ), representedSecondStage p)

instance representativeTopology : TopologicalSpace FrameRepresentative :=
  TopologicalSpace.induced representativeCoordinates inferInstance

abbrev representativeSpace : TopCat := TopCat.of FrameRepresentative

abbrev minuscule : TopCat := TopCat.of ProjectivePoints

abbrev ordered : TopCat := TopCat.of (Points incidenceScheme complexAlgebra)

/-- The continuous maps from representatives realize the twisted quotient on
the analytic incidence space and record the second modification in the chosen frame. -/
def FrameQuotient : Prop :=
  ∃ (h : StableStage (PositiveGL 2) (colength 1))
    (e : OrderedProduct h ≃ ordered)
    (b : representativeSpace ⟶ minuscule)
    (q : representativeSpace ⟶ ordered),
    IsQuotientMap q ∧
    ∀ p : FrameRepresentative,
      q p = e (Quotient.mk (twistRel (PositiveGL 2) firstStage (colength 1)) p) ∧
      firstPlane (q p ≫ ConvolutionBundleSpecs.firstProjection) =
        (latticeSubspace 0 1 (p.val.1 • standardLattice 2)).map constantCoordinates.toLinearMap ∧
      firstPlane (b p) =
        (latticeSubspace 0 1 p.val.2).map constantCoordinates.toLinearMap ∧
      secondPlane (q p ≫ terminalProjection) =
        (latticeSubspace 0 2 (p.val.1 • p.val.2)).map twoStepCoordinates.toLinearMap

abbrev Jets := GLJets 2 2 (by decide)

/-- Action on the first window by the constant term of the jet. -/
def constantJetLinear (g : Jets) : V →ₗ[ℂ] V :=
  Matrix.toLin' (fun i j ↦ jetCoefficients 2 (g.val i j) 0)

/-- Action on the terminal window in constant and linear coordinates. -/
def twoTermJetLinear (g : Jets) : (V × V) →ₗ[ℂ] (V × V) :=
  twoStepCoordinates.toLinearMap.comp
    ((windowJetLinear 0 (le_refl 2) g.val).comp twoStepCoordinates.symm.toLinearMap)

/-- The group of two-term jets has continuous group operations and acts
jointly continuously on the first-stage lines and on the incidence space. -/
def JetActions : Prop :=
  IsTopologicalGroup Jets ∧
  ∃ (A₁ : MulAction Jets ProjectivePoints) (A₂ : MulAction Jets ordered),
    Continuous (fun x : Jets × ProjectivePoints ↦ A₁.smul x.1 x.2) ∧
    Continuous (fun x : Jets × ordered ↦ A₂.smul x.1 x.2) ∧
    (∀ (g : Jets) (p : ProjectivePoints),
      firstPlane (A₁.smul g p) = (firstPlane p).map (constantJetLinear g)) ∧
    (∀ (g : Jets) (p : ordered),
      A₂.smul g p ≫ ConvolutionBundleSpecs.firstProjection =
        A₁.smul g (p ≫ ConvolutionBundleSpecs.firstProjection) ∧
      secondPlane (A₂.smul g p ≫ terminalProjection) =
        (secondPlane (p ≫ terminalProjection)).map (twoTermJetLinear g))

end

end RepTheorySurvey.Geometric.ConvolutionFrameQuotientSpecs
