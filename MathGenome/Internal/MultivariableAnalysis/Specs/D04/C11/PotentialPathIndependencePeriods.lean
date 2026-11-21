import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.EuclideanVectorOperators
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.GradientIntegral
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.PathAlgebra
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.Components

/-! Independent statements for paper.tex, d04:11:potential.
Fields and potentials are ambient extensions, restricted to the specified open
set. Paths, piecewise C¹ data and proper work integrals are the Chapter 9 objects.
In particular all constant paths and singleton parameter intervals are included.
Connectedness permits the empty domain and dimensions include zero. -/
noncomputable section
open Set
namespace Specs.D04.C11.PotentialPathIndependencePeriods
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C01.Components.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model
namespace Model

def IsPotential {n} (U : Set (E n)) (F : E n → E n) (f : E n → ℝ) : Prop :=
  CrOn 1 U f ∧ EqOn (scalarGradient f) F U

def HasPotential {n} (U : Set (E n)) (F : E n → E n) : Prop :=
  ∃ f, IsPotential U F f

/-- Both ordered endpoints must agree; no regular or simple-path restriction. -/
def PathIndependent {n} (U : Set (E n)) (F : E n → E n) : Prop :=
  ∀ {a b c d : ℝ} (γ : IntervalPath n a b) (η : IntervalPath n c d)
    (v : PiecewiseC1Data γ) (w : PiecewiseC1Data η),
    trace γ ⊆ U → trace η ⊆ U → γ a = η c → γ b = η d →
    ∀ (hv : WorkIntegrable v F) (hw : WorkIntegrable w F),
      workLineIntegral v F hv = workLineIntegral w F hw

def ZeroPeriods {n} (U : Set (E n)) (F : E n → E n) : Prop :=
  ∀ {a b : ℝ} (γ : IntervalPath n a b) (v : PiecewiseC1Data γ),
    trace γ ⊆ U → γ a = γ b → ∀ hv : WorkIntegrable v F,
      workLineIntegral v F hv = 0
end Model
open Model

def IsPotentialType := {n : ℕ} → Set (E n) → (E n → E n) → (E n → ℝ) → Prop
def IsPotentialValue : IsPotentialType := @Model.IsPotential

def HasPotentialType := {n : ℕ} → Set (E n) → (E n → E n) → Prop
def HasPotentialValue : HasPotentialType := @Model.HasPotential

def PathIndependentType := HasPotentialType
def PathIndependentValue : PathIndependentType := @Model.PathIndependent

def ZeroPeriodsType := HasPotentialType
def ZeroPeriodsValue : ZeroPeriodsType := @Model.ZeroPeriods

def work_integrable_in_domainType : Prop := ∀ {n a b} (U : Set (E n))
  (F : E n → E n) (γ : IntervalPath n a b) (v : PiecewiseC1Data γ),
  ContinuousOn F U → trace γ ⊆ U → WorkIntegrable v F

def potential_equivalencesType : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n),
  IsOpen U → IsPreconnected U → ContinuousOn F U →
    (HasPotential U F ↔ PathIndependent U F) ∧
    (PathIndependent U F ↔ ZeroPeriods U F)

def potential_uniqueType : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n)
  (f g : E n → ℝ), IsOpen U → IsPreconnected U →
  IsPotential U F f → IsPotential U F g → ∃ c : ℝ, ∀ x ∈ U, g x = f x + c

def potential_regularType : Prop := ∀ {n} (r : ℕ) (U : Set (E n))
  (F : E n → E n) (f : E n → ℝ), IsOpen U →
  IsPotential U F f → CrOn r U F → CrOn (r+1) U f

def potential_smoothType : Prop := ∀ {n} (U : Set (E n))
  (F : E n → E n) (f : E n → ℝ), IsOpen U →
  IsPotential U F f → SmoothOn U F → SmoothOn U f

/-- Each actual connected component is open, with the full equivalence. -/
def component_equivalencesType : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n),
  IsOpen U → ContinuousOn F U → ∀ C ∈ componentsWithin U,
    IsOpen C ∧ (HasPotential C F ↔ PathIndependent C F) ∧
      (PathIndependent C F ↔ ZeroPeriods C F)

/-- Uniqueness is precisely componentwise constancy of the difference. -/
def component_uniqueType : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n)
  (f g : E n → ℝ), IsOpen U → IsPotential U F f → IsPotential U F g →
  ∀ C ∈ componentsWithin U, ∃! c : ℝ, ∀ x ∈ C, g x = f x + c

/-- Every assignment of real constants to the components is realizable,
independently of all other components. No finiteness or boundedness is required. -/
def independent_constantsType : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n)
  (f : E n → ℝ), IsOpen U → IsPotential U F f →
  ∀ c : {C : Set (E n) // C ∈ componentsWithin U} → ℝ,
    ∃ g : E n → ℝ, IsPotential U F g ∧
      ∀ C (hC : C ∈ componentsWithin U), ∀ x ∈ C, g x = f x + c ⟨C,hC⟩

end Specs.D04.C11.PotentialPathIndependencePeriods
