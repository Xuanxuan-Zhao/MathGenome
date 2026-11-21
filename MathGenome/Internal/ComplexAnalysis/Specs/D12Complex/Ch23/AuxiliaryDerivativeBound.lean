import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Independent statements of the auxiliary estimates in the proof of Schottky
control, paper.tex:4231–4237. Both estimates concern the given auxiliary
function g; no normalization or nonvanishing derivative is required.
-/

namespace Specs.D12Complex.Ch23.AuxiliaryDerivativeBound
open _root_.D12Complex Metric

def derivative_bound_type : Prop :=
  ∀ (f g : ℂ → ℂ), HolomorphicOn (ball 0 1) f →
    (∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0) →
    (∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1) →
    HolomorphicOn (ball 0 1) g →
    (∀ z ∈ ball (0 : ℂ) 1,
      f z = -Complex.exp ((Real.pi : ℂ) * Complex.I * Complex.cosh (2 * g z))) →
    ∀ a ∈ ball (0 : ℂ) 1, ‖deriv g a‖ ≤ 128 / (1 - ‖a‖)

def radial_bound_type : Prop :=
  ∀ (f g : ℂ → ℂ), HolomorphicOn (ball 0 1) f →
    (∀ z ∈ ball (0 : ℂ) 1, f z ≠ 0) →
    (∀ z ∈ ball (0 : ℂ) 1, f z ≠ 1) →
    HolomorphicOn (ball 0 1) g →
    (∀ z ∈ ball (0 : ℂ) 1,
      f z = -Complex.exp ((Real.pi : ℂ) * Complex.I * Complex.cosh (2 * g z))) →
    ∀ r : ℝ, 0 ≤ r → r < 1 →
    ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ ‖g 0‖ + 128 * r / (1 - r)

end Specs.D12Complex.Ch23.AuxiliaryDerivativeBound
