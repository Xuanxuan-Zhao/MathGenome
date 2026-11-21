import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.SimplyConnectedOneFormPotential
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.RadialFluxObstruction

/-! Statements for paper.tex, Example d04:11:punctured-three.
The punctured domain and radial two-form are the shared Chapter 15 objects.
Both contraction conventions quantify over arbitrary continuous paths. -/
noncomputable section
open Set
namespace Specs.D04.C11.PuncturedThreeSpaceSimplyConnected
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C11.SimplyConnectedOneFormPotential.Model
open Specs.D04.C15.RadialFluxObstruction.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model

def punctured_openType : Prop := IsOpen puncturedSpace
def punctured_connectedType : Prop := Connected puncturedSpace
def punctured_pathConnectedType : Prop := PathConnected puncturedSpace
def punctured_free_contractionsType : Prop := FreeLoopContractions puncturedSpace
def punctured_simplyConnectedType : Prop := SimplyConnected puncturedSpace
def punctured_contraction_conventionsType : Prop :=
  SimplyConnected puncturedSpace ↔ PathConnected puncturedSpace ∧ FreeLoopContractions puncturedSpace

open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C11.PotentialPathIndependencePeriods.Model

def punctured_oneform_potentialType : Prop := ∀ F : E 3 → E 3,
  CrOn 1 puncturedSpace F →
  (∀ x ∈ puncturedSpace, (jacobian F x).IsSymm) → HasPotential puncturedSpace F

def radial_counterexampleType : Prop :=
  IsOpen puncturedSpace ∧ Connected puncturedSpace ∧ SimplyConnected puncturedSpace ∧
  IsCrForm (some 1) puncturedSpace radialForm ∧
  (∀ x ∈ puncturedSpace, exteriorDerivative radialForm x = 0) ∧
  ¬ ∃ eta : FormField 3 1, IsCrForm (some 1) puncturedSpace eta ∧
    ∀ x ∈ puncturedSpace, exteriorDerivative eta x = radialForm x

end Specs.D04.C11.PuncturedThreeSpaceSimplyConnected
