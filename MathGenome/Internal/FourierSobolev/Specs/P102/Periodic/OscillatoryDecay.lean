import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation

/-! Independent statement types for the interval and periodic Riemann–Lebesgue
assertions in paper.tex:173–178 and 216–220. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real

namespace P102.Periodic.Expected.OscillatoryDecay

/-- The filter explicitly expresses `|w| → ∞`. Endpoints carry no Lebesgue mass;
the closed interval formulation includes every bounded interval and its L¹ classes. -/
def intervalStatement : Prop :=
  ∀ (a b : ℝ) (h : ℝ → ℂ), IntegrableOn h (Icc a b) →
    Tendsto (fun w : ℝ => ∫ v in Icc a b, h v * Complex.exp (Complex.I * w * v))
      (comap (fun w : ℝ => |w|) atTop) (𝓝 0)

/-- Both half-integer frequencies needed in the localization argument. -/
def halfIntegerStatement : Prop :=
  ∀ (h : ℝ → ℂ), IntegrableOn h (Icc (-Real.pi) Real.pi) →
    Tendsto (fun N : ℕ => ∫ v in Icc (-Real.pi) Real.pi,
      h v * Complex.exp (Complex.I * ((N : ℝ) + 1 / 2) * v)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ∫ v in Icc (-Real.pi) Real.pi,
      h v * Complex.exp (Complex.I * (-((N : ℝ) + 1 / 2)) * v)) atTop (𝓝 0)

/-- On integers, the cofinite filter means `|k| → ∞`, covering both signs. -/
def coefficientStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ), Integrable f (haar T) →
    Tendsto (coefficient T f) cofinite (𝓝 0)

/-- The same conclusion on the canonical upstream L¹ quotient. -/
def coefficientL1Statement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : L1 T),
    Tendsto (coefficientL1 T f) cofinite (𝓝 0)

end P102.Periodic.Expected.OscillatoryDecay
