import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.CantorFunction
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.NormalizedStieltjes
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.AcFtc
import Mathlib.MeasureTheory.Measure.MutuallySingular

/-! The canonical Cantor function of Chapter 3, with its Chapter 12 consequences.
The ambient real function is used through its restriction to [0,1]; no new
choice of a singular function is made. Measures are on the real Borel space.
The interval and cumulative formulas specify the Stieltjes measure of the
normalized constant extension, separately from its singularity and null support. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace D11.Ch12.SingularContinuousCounterexample

/-- The upstream compact normalization of the fixed digit staircase. -/
def extension : ℝ → ℝ :=
  Specs.D11.Ch12.NormalizedStieltjes.compactNormalization_value
    Specs.D11.Ch03.CantorFunction.Gamma_value 0 1

end D11.Ch12.SingularContinuousCounterexample

namespace Specs.D11.Ch12.SingularContinuousCounterexample
open _root_.D11.Ch12.SingularContinuousCounterexample
local notation "Γ" => Specs.D11.Ch03.CantorFunction.Gamma_value
local notation "C" => Specs.D11.Ch03.CantorSet.C_value

/-- Retains the original function, range, point values, and regularity. -/
def function_properties : Prop :=
  ContinuousOn Γ (Icc 0 1) ∧ Monotone Γ ∧ MapsTo Γ (Icc 0 1) (Icc 0 1) ∧
    Γ 0 = 0 ∧ Γ 1 = 1

def variation_one : Prop := Specs.D11.Ch12.variation_value Γ 0 1 = 1

/-- A genuine classical derivative, rather than merely the totalized `deriv`. -/
def derivative_zero : Prop := ∀ᵐ x ∂(volume : Measure ℝ), HasDerivAt Γ 0 x

def not_absolutely_continuous : Prop :=
  ¬ absolutelyContinuousOnIntervalValue Γ 0 1

def extension_properties : Prop :=
  Specs.D11.Ch12.ScalarStieltjesCorrespondence.NBV_value extension ∧
    Continuous extension ∧
    (∀ x, x ≤ 0 → extension x = 0) ∧
    (∀ x ∈ Icc (0 : ℝ) 1, extension x = Γ x) ∧
    (∀ x, 1 ≤ x → extension x = 1)

/-- Atomless, nonzero singular probability, carried by the fixed null Cantor
set. The two interval formulas identify its Stieltjes generator. -/
def stieltjes_probability : Prop :=
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ ≠ 0 ∧ NullSingletonClass μ ∧
    μ Cᶜ = 0 ∧ volume C = 0 ∧ μ ⟂ₘ volume ∧
    (∀ a b : ℝ, μ (Ioc a b) = ENNReal.ofReal (extension b - extension a)) ∧
    (∀ x : ℝ, μ (Iic x) = ENNReal.ofReal (extension x))

/-- Explicit strictness of the monotone derivative inequality: 0 < 1.
Integrability is stated so the integral is not justified by totalization. -/
def strict_derivative_inequality : Prop :=
  IntegrableOn (deriv Γ) (Icc (0 : ℝ) 1) ∧
    (∫ x in (0 : ℝ)..1, deriv Γ x) = 0 ∧
    (∫ x in (0 : ℝ)..1, deriv Γ x) < Γ 1 - Γ 0

end Specs.D11.Ch12.SingularContinuousCounterexample
