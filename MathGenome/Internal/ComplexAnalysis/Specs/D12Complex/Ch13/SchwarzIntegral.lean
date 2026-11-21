import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.PoissonHarmonic

/-! Schwarz's integral formula, paper.tex:2572–2582 (d12:13-05).
Only the real part has a continuous extension. The witness `u` is real-valued;
neither `f` nor its imaginary part is required to extend to the boundary.
The boundary datum is restricted only through its values on the circle.
`circleMap 0 R t` is the usual `R * exp (t * I)` parametrization. -/

noncomputable section
open Complex Metric Set

namespace Specs.D12Complex.Ch13.SchwarzIntegral
open _root_.D12Complex

def schwarz_integral_type : Prop :=
  ∀ (R : ℝ) (f : ℂ → ℂ) (φ : ℂ → ℝ),
    0 < R → HolomorphicOn (ball 0 R) f →
    (∃ u : ℂ → ℝ, ContinuousOn u (closedBall 0 R) ∧
      EqOn u (fun z => (f z).re) (ball 0 R) ∧ EqOn u φ (sphere 0 R)) →
    ∀ z : ℂ, ‖z‖ < R →
      f z = (2 * Real.pi)⁻¹ •
        (∫ t in (0 : ℝ)..2 * Real.pi,
          ((circleMap 0 R t + z) / (circleMap 0 R t - z)) *
            (φ (circleMap 0 R t) : ℂ)) + I * (f 0).im

end Specs.D12Complex.Ch13.SchwarzIntegral
