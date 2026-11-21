import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.PotentialPathIndependencePeriods
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.HomotopyOperatorRegularity
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! Independent statements for paper.tex, d04:11:local-potential.
All functions are ambient representatives restricted to the displayed open set.
The radial integral is the shared proper Riemann integral, not an assumed
primitive. Dimensions include zero; no connectedness is imposed for necessity.
The star centre is required to belong to U. -/
noncomputable section
open Set
namespace Specs.D04.C11.LocalAndStarShapedPotentials
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C11.PotentialPathIndependencePeriods.Model
open Specs.D04.C13.HomotopyOperatorRegularity.Model
namespace Model

/-- The equations ∂ᵢ Fⱼ = ∂ⱼ Fᵢ, with all indices and all points quantified. -/
def SymmetricPartials {n : ℕ} (U : Set (E n)) (F : E n → E n) : Prop :=
  ∀ x ∈ U, ∀ i j : Fin n,
    scalarPartialDerivative (fun y => F y j) x i =
      scalarPartialDerivative (fun y => F y i) x j

/-- The explicit primitive specified by the source, using its radial segment. -/
def radialPotential {n : ℕ} (a : E n) (F : E n → E n) (x : E n) : ℝ :=
  scalarIntegral (fun t => inner ℝ (F (a + t • (x-a))) (x-a))
end Model
open Model

abbrev SymmetricPartialsType := {n : ℕ} → Set (E n) → (E n → E n) → Prop
def SymmetricPartialsValue : SymmetricPartialsType := @Model.SymmetricPartials
abbrev radialPotentialType := {n : ℕ} → E n → (E n → E n) → E n → ℝ
def radialPotentialValue : radialPotentialType := @Model.radialPotential

def symmetry_iff_jacobianType : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n),
  IsOpen U → CrOn 1 U F →
    (SymmetricPartials U F ↔ ∀ x ∈ U, (jacobian F x).IsSymm)

def potential_C2Type : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n) (f : E n → ℝ),
  IsOpen U → CrOn 1 U F → IsPotential U F f → CrOn 2 U f

def potential_necessaryType : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n),
  IsOpen U → CrOn 1 U F → HasPotential U F → SymmetricPartials U F

/-- In particular the integral occurring in the explicit formula exists. -/
def radialPotential_integrableType : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n) (a : E n),
  IsOpen U → CrOn 1 U F → a ∈ U → StarConvex ℝ a U →
    ∀ x ∈ U, ScalarIntegrable (fun t => inner ℝ (F (a + t • (x-a))) (x-a))

/-- Existence, the specified formula, gradient equality, C² improvement, and
uniqueness up to one constant on the whole star-shaped domain. -/
def star_shaped_potentialType : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n) (a : E n),
  IsOpen U → CrOn 1 U F → a ∈ U → StarConvex ℝ a U → SymmetricPartials U F →
    IsPotential U F (radialPotential a F) ∧ CrOn 2 U (radialPotential a F) ∧
      ∀ g, IsPotential U F g → ∃ c : ℝ, ∀ x ∈ U, g x = radialPotential a F x + c

/-- Every positive-radius ball contained in U, not merely a chosen local ball. -/
def ball_potentialType : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n),
  IsOpen U → CrOn 1 U F → SymmetricPartials U F →
    ∀ (b : E n) (r : ℝ), 0 < r → Metric.ball b r ⊆ U →
      IsPotential (Metric.ball b r) F (radialPotential b F) ∧
        CrOn 2 (Metric.ball b r) (radialPotential b F)

def local_potentialType : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n),
  IsOpen U → CrOn 1 U F → SymmetricPartials U F →
    ∀ x ∈ U, ∃ r > 0, Metric.ball x r ⊆ U ∧ HasPotential (Metric.ball x r) F

def symmetry_iff_curl_zeroType : Prop := ∀ (U : Set (E 3)) (F : E 3 → E 3),
  IsOpen U → CrOn 1 U F → (SymmetricPartials U F ↔ ∀ x ∈ U, curl F x = 0)

end Specs.D04.C11.LocalAndStarShapedPotentials
