import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.EuclideanSmoothCutoffs
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.ProperDerivative
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Independent specification of paper.tex, d04:14:mollify.
Ambient functions represent maps on O by restriction. No behavior outside O
is prescribed. Uniform convergence is expressed on the actual compact box,
and the derivatives use the Euclidean continuous-linear-map operator norm.
Neither dimension is required to be positive. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace Specs.D04.C14.SmoothApproximationInC1
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.JordanRegions.Model

namespace Model

def C1ApproximationOn {n m : ℕ} (K : Set (E n)) (f : E n → E m)
    (F : ℕ → E n → E m) : Prop :=
  (∀ j, ∃ V : Set (E n), IsOpen V ∧ K ⊆ V ∧ ContDiffOn ℝ ∞ (F j) V) ∧
  TendstoUniformlyOn F f atTop K ∧
  TendstoUniformlyOn (fun j => fderiv ℝ (F j)) (fderiv ℝ f) atTop K ∧
  Tendsto (fun j => sSup ((fun x => ‖F j x - f x‖) '' K)) atTop (𝓝 0) ∧
  Tendsto (fun j => sSup ((fun x => ‖fderiv ℝ (F j) x - fderiv ℝ f x‖) '' K))
    atTop (𝓝 0)

/-- Convolution on a fixed bounded Jordan region, using precisely the shared
coordinatewise proper Riemann integral, not a measure integral. -/
def kernelAverage {n m : ℕ} (S : Set (E n)) (η : E n → ℝ)
    (g : E n → E m) (x : E n) : E m :=
  vectorRegionIntegral (fun y : S => η (x - y) • g y)

/-- The translated-input presentation is used for the uniform estimates. -/
def translatedAverage {n m : ℕ} (S : Set (E n)) (η : E n → ℝ)
    (g : E n → E m) (ε : ℝ) (x : E n) : E m :=
  vectorRegionIntegral (fun z : S => η z • g (x - ε • (z : E n)))

end Model

abbrev C1ApproximationOnType := {n m : ℕ} → Set (E n) →
  (E n → E m) → (ℕ → E n → E m) → Prop
def C1ApproximationOnValue : C1ApproximationOnType := @Model.C1ApproximationOn

abbrev kernelAverageType := {n m : ℕ} → Set (E n) → (E n → ℝ) →
  (E n → E m) → E n → E m
def kernelAverageValue : kernelAverageType := @Model.kernelAverage

abbrev translatedAverageType := {n m : ℕ} → Set (E n) → (E n → ℝ) →
  (E n → E m) → ℝ → E n → E m
def translatedAverageValue : translatedAverageType := @Model.translatedAverage

def compactly_supported_extensionType : Prop :=
  ∀ {n m : ℕ} (K O : Set (E n)) (f : E n → E m),
    IsCompact K → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O →
    ∃ g : E n → E m, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧
      ∃ V : Set (E n), IsOpen V ∧ K ⊆ V ∧ EqOn g f V ∧
        EqOn (fderiv ℝ g) (fderiv ℝ f) V

def kernelAverage_smoothType : Prop :=
  ∀ {n m : ℕ} (S : Set (E n)) (η : E n → ℝ) (g : E n → E m),
    Jordan S → ContDiff ℝ ∞ η → Continuous g →
    ContDiff ℝ ∞ (Model.kernelAverage S η g)

def translatedAverage_tendstoType : Prop :=
  ∀ {n m : ℕ} (S : Set (E n)) (η : E n → ℝ) (g : E n → E m),
    Jordan S → Continuous η → UniformContinuous g →
    regionIntegral (fun z : S => η z) = 1 →
    ∀ (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) →
      TendstoUniformly (fun j => Model.translatedAverage S η g (ε j)) g atTop

def translatedAverage_hasFDerivAtType : Prop :=
  ∀ {n m : ℕ} (S : Set (E n)) (η : E n → ℝ) (g : E n → E m),
    Jordan S → Continuous η → ContDiff ℝ 1 g → ∀ (ε : ℝ) (x : E n),
    HasFDerivAt (Model.translatedAverage S η g ε)
      (Specs.D04.C08.ProperDerivative.Model.operatorRegionIntegral
        (fun z : S => η z • fderiv ℝ g (x - ε • (z : E n)))) x

def translatedAverage_fderiv_tendstoType : Prop :=
  ∀ {n m : ℕ} (S : Set (E n)) (η : E n → ℝ) (g : E n → E m),
    Jordan S → Continuous η → ContDiff ℝ 1 g → HasCompactSupport g →
    regionIntegral (fun z : S => η z) = 1 →
    ∀ (ε : ℕ → ℝ), Tendsto ε atTop (𝓝 0) →
      TendstoUniformly (fun j => fderiv ℝ (Model.translatedAverage S η g (ε j)))
        (fderiv ℝ g) atTop

def smooth_approximation_in_C1Type : Prop :=
  ∀ {n m : ℕ} (Q : Box n) (O : Set (E n)) (f : E n → E m),
    IsOpen O → carrier Q ⊆ O → CrOn 1 O f →
    ∃ F : ℕ → E n → E m, Model.C1ApproximationOn (carrier Q) f F

end Specs.D04.C14.SmoothApproximationInC1
