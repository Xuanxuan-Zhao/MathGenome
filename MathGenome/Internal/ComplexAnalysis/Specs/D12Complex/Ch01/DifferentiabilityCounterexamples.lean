import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.RealComplexDifferential
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Independent statements for the boundary examples in paper.tex:228–245,268–289.
The derivatives of the four slices are asserted to exist, in addition to their
values as `partialX` and `partialY`. -/
noncomputable section
namespace Specs.D12Complex.Ch01.DifferentiabilityCounterexamples
open _root_.D12Complex Complex ComplexConjugate

def F_type := ℂ → ℂ
def F_value : F_type := fun z => z ^ 5 / (‖z‖ : ℂ) ^ 4

def normSquared_type := ℂ → ℂ
def normSquared_value : normSquared_type := fun z => (‖z‖ ^ 2 : ℝ)

def F_zero_type : Prop := F_value 0 = 0

def F_norm_type : Prop := ∀ z : ℂ, ‖F_value z‖ = ‖z‖

def F_continuous_type : Prop := ContinuousAtPoint F_value 0

def F_ray_quotients_type : Prop :=
  ∀ t : ℝ, t ≠ 0 → F_value (t : ℂ) / (t : ℂ) = 1 ∧
    F_value ((t : ℂ) * (1 + I)) / ((t : ℂ) * (1 + I)) = -1

def F_slices_type : Prop :=
  HasDerivAt (fun t : ℝ => (F_value (t : ℂ)).re) 1 0 ∧
  HasDerivAt (fun t : ℝ => (F_value ((t : ℂ) * I)).re) 0 0 ∧
  HasDerivAt (fun t : ℝ => (F_value (t : ℂ)).im) 0 0 ∧
  HasDerivAt (fun t : ℝ => (F_value ((t : ℂ) * I)).im) 1 0

def F_partials_type : Prop :=
  partialX (fun z => (F_value z).re) 0 = 1 ∧
  partialY (fun z => (F_value z).re) 0 = 0 ∧
  partialX (fun z => (F_value z).im) 0 = 0 ∧
  partialY (fun z => (F_value z).im) 0 = 1

def F_not_differentiable_type : Prop := ¬ ComplexDifferentiableAt F_value 0

def conjugation_smooth_type : Prop := ContDiff ℝ ⊤ (conj : ℂ → ℂ)

def conjugation_not_differentiable_type : Prop :=
  ∀ a : ℂ, ¬ ComplexDifferentiableAt (conj : ℂ → ℂ) a

def conjugation_not_holomorphic_type : Prop :=
  ∀ U : Set ℂ, U.Nonempty → ¬ HolomorphicOn U (conj : ℂ → ℂ)

def normSquared_differentiable_iff_type : Prop :=
  ∀ a : ℂ, ComplexDifferentiableAt normSquared_value a ↔ a = 0

def normSquared_derivative_zero_type : Prop :=
  HasComplexDerivativeAt normSquared_value 0 0

def normSquared_not_holomorphic_type : Prop :=
  ∀ U : Set ℂ, 0 ∈ U → ¬ HolomorphicOn U normSquared_value

end Specs.D12Complex.Ch01.DifferentiabilityCounterexamples
