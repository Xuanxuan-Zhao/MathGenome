import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention

open MeasureTheory Filter
open scoped Topology

namespace Specs.ExpandedFA.PartIV.WienerLocal
open _root_.ExpandedFA.Fourier

/-- Local Fourier flattening, `paper.tex`, `fa2:p4:wiener-local`.
The L¹ norm is expressed as the integral of the pointwise norm. The frequency
identity holds on a neighborhood, with no nonvanishing condition. -/
def LocalFlattening : Prop :=
  ∀ (d : ℕ) (f : Euclidean d → ℂ), Integrable f →
    ∀ (ξ₀ : Euclidean d) (ε : ℝ), 0 < ε →
      ∃ h : Euclidean d → ℂ, Integrable h ∧ (∫ x, ‖h x‖) < ε ∧
        ∀ᶠ ξ in 𝓝 ξ₀, integralFourier h ξ = integralFourier f ξ₀ - integralFourier f ξ

/-- The real scalar case requires a real-valued correction. Its Fourier
transform is still the complex Fourier transform of the real input. -/
def RealLocalFlattening : Prop :=
  ∀ (d : ℕ) (f : Euclidean d → ℝ), Integrable f →
    ∀ (ξ₀ : Euclidean d) (ε : ℝ), 0 < ε →
      ∃ h : Euclidean d → ℝ, Integrable h ∧ (∫ x, ‖h x‖) < ε ∧
        ∀ᶠ ξ in 𝓝 ξ₀,
          integralFourier (fun x => (h x : ℂ)) ξ =
            integralFourier (fun x => (f x : ℂ)) ξ₀ -
              integralFourier (fun x => (f x : ℂ)) ξ


end Specs.ExpandedFA.PartIV.WienerLocal
