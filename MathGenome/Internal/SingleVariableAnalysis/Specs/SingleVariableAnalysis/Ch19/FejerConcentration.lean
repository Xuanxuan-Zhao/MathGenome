import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.FejerKernel

/-! K03.19.fejer_kernel, paper.tex:4946–4953.
The outside region is the disjoint union [-π,-δ] ∪ [δ,π] for 0 < δ < π.
Its integral is the sum of the two proper real Darboux integrals of the
real part of the canonical (real-valued) complex Fejer kernel. Integrability
is asserted, rather than supplied as an additional hypothesis. All integral
values carry witnesses; the estimates and limit hold for every such witness.
-/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.FejerConcentration
open Ch08.Integral

def pointwiseBound : Prop := ∀ (δ : ℝ), 0 < δ → δ < Real.pi →
  ∀ (N : ℕ) (t : ℝ), δ ≤ |t| → |t| ≤ Real.pi →
    0 ≤ (FejerKernel.kernelValue N t).re ∧
    (FejerKernel.kernelValue N t).re ≤
      1 / (((N : ℝ)+1) * Real.sin (δ/2)^2)

def outsideIntegrability : Prop := ∀ (δ : ℝ), 0 < δ → δ < Real.pi →
  ∀ N : ℕ,
    realIntegrableValue (fun t => (FejerKernel.kernelValue N t).re) (-Real.pi) (-δ) ∧
    realIntegrableValue (fun t => (FejerKernel.kernelValue N t).re) δ Real.pi

abbrev massType := (δ : ℝ) → (N : ℕ) →
  realIntegrableValue (fun t => (FejerKernel.kernelValue N t).re) (-Real.pi) (-δ) →
  realIntegrableValue (fun t => (FejerKernel.kernelValue N t).re) δ Real.pi → ℝ

def massValue : massType := fun _ N hl hr =>
  (1 / (2 * Real.pi)) *
    (realIntegralValue (fun t => (FejerKernel.kernelValue N t).re) hl +
     realIntegralValue (fun t => (FejerKernel.kernelValue N t).re) hr)

def outsideIntegralBound : Prop := ∀ (δ : ℝ), 0 < δ → δ < Real.pi →
  ∀ (N : ℕ)
    (hl : realIntegrableValue (fun t => (FejerKernel.kernelValue N t).re) (-Real.pi) (-δ))
    (hr : realIntegrableValue (fun t => (FejerKernel.kernelValue N t).re) δ Real.pi),
      0 ≤ massValue δ N hl hr ∧
      massValue δ N hl hr ≤ 1 / (((N : ℝ)+1) * Real.sin (δ/2)^2)

def concentration : Prop := ∀ (δ : ℝ), 0 < δ → δ < Real.pi →
  ∀ (hl : ∀ N : ℕ,
      realIntegrableValue (fun t => (FejerKernel.kernelValue N t).re) (-Real.pi) (-δ))
    (hr : ∀ N : ℕ,
      realIntegrableValue (fun t => (FejerKernel.kernelValue N t).re) δ Real.pi),
    Filter.Tendsto (fun N => massValue δ N (hl N) (hr N)) Filter.atTop (nhds 0)

end Specs.SingleVariableAnalysis.Ch19.FejerConcentration
