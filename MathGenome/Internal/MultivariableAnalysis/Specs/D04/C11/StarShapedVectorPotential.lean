import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.EuclideanPoincareLemma
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.OrientedEuclideanDictionary
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C15.RadialFluxObstruction

/-! Independent statements for chapters/11.tex, d04:11:vector-potential.
The displayed integral is componentwise the shared proper Riemann integral.
The order F × (x-a) uses the standard orientation of three-space. -/
noncomputable section
open Set
namespace Specs.D04.C11.StarShapedVectorPotential
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C13.HomotopyOperatorRegularity.Model

namespace Model

def radialVectorPotential (a : E 3) (F : E 3 → E 3) (x : E 3) : E 3 :=
  WithLp.toLp 2 (fun i => scalarIntegral
    (fun t => t * (euclideanCross (F (a + t • (x-a))) (x-a)) i))

end Model
open Model

abbrev radialVectorPotentialType := E 3 → (E 3 → E 3) → E 3 → E 3
def radialVectorPotentialValue : radialVectorPotentialType := radialVectorPotential

/-- Identification with the explicit degree-two radial primitive, including sign. -/
def alpha_radialVectorPotentialType : Prop :=
  ∀ (a : E 3) (F : E 3 → E 3),
    alpha (radialVectorPotential a F) = homotopyOperator a (beta F)

def starShaped_vector_potentialType : Prop :=
  ∀ (U : Set (E 3)) (a : E 3) (F : E 3 → E 3),
    IsOpen U → a ∈ U → StarConvex ℝ a U → CrOn 1 U F →
    (∀ x ∈ U, divergence F x = 0) →
    (∀ x ∈ U, ∀ i : Fin 3, ScalarIntegrable
      (fun t => t * (euclideanCross (F (a + t • (x-a))) (x-a)) i)) ∧
    CrOn 1 U (radialVectorPotential a F) ∧
    (∀ x ∈ U, curl (radialVectorPotential a F) x = F x)

def divergence_curl_C2Type : Prop :=
  ∀ (U : Set (E 3)) (A : E 3 → E 3),
    IsOpen U → CrOn 2 U A → ∀ x ∈ U, divergence (curl A) x = 0

/-- The specified punctured-space field excludes potentials of both regularities. -/
def radial_obstructionType : Prop :=
  let U := Specs.D04.C15.RadialFluxObstruction.Model.puncturedSpace
  let F := Specs.D04.C15.RadialFluxObstruction.Model.radialField
  IsOpen U ∧ CrOn 1 U F ∧ (∀ x ∈ U, divergence F x = 0) ∧
    (¬ ∃ A : E 3 → E 3, CrOn 1 U A ∧ ∀ x ∈ U, curl A x = F x) ∧
    (¬ ∃ A : E 3 → E 3, CrOn 2 U A ∧ ∀ x ∈ U, curl A x = F x)

/-- Hence the star-shaped-domain existence assertion cannot hold on all open sets. -/
def global_vector_potential_may_failType : Prop :=
  ∃ (U : Set (E 3)) (F : E 3 → E 3),
    IsOpen U ∧ CrOn 1 U F ∧ (∀ x ∈ U, divergence F x = 0) ∧
    (¬ ∃ A : E 3 → E 3, CrOn 1 U A ∧ ∀ x ∈ U, curl A x = F x) ∧
    (¬ ∃ A : E 3 → E 3, CrOn 2 U A ∧ ∀ x ∈ U, curl A x = F x)

end Specs.D04.C11.StarShapedVectorPotential
