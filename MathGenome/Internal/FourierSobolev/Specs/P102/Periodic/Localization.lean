import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation

/-! Full statement types for Proposition 1.2 (`p102:U1-01`).
The local equality hypothesis is equality almost everywhere for restricted Haar
measure, so it applies to arbitrary representatives of the L¹ classes. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real

namespace P102.Periodic.Expected.Localization

def convolutionExistsStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ), Integrable f (haar T) →
    ∀ (N : ℕ) (x : Circle T), ConvolutionExistsAt T f (dirichletKernel T N) x

def convolutionStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ), Integrable f (haar T) →
    ∀ (N : ℕ) (x : Circle T),
      partialSum T N f x = convolution T f (dirichletKernel T N) x

/-- The angular formula on the full punctured fundamental interval, including
both endpoints and N = 0. The real quotient is embedded in ℂ. -/
def sineQuotientStatement : Prop :=
  ∀ (N : ℕ) (v : ℝ), -Real.pi ≤ v → v ≤ Real.pi → v ≠ 0 →
    dirichletKernel (2 * Real.pi) N (v : Circle (2 * Real.pi)) =
      ((Real.sin (((N : ℝ) + 1 / 2) * v) / Real.sin (v / 2) : ℝ) : ℂ)

def zeroStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (N : ℕ),
    dirichletKernel T N 0 = (2 * N + 1 : ℂ)

/-- Together with the quotient formula this is the continuous extension of
that quotient at zero, with the specified value. -/
def continuousExtensionStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (N : ℕ),
    Continuous (dirichletKernel T N) ∧
    Tendsto (fun t : ℝ => dirichletKernel T N (t : Circle T))
      (𝓝 0) (𝓝 (2 * N + 1 : ℂ))

def localizationStatement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f g : Circle T → ℂ),
    Integrable f (haar T) → Integrable g (haar T) →
    ∀ (x : Circle T) (U : Set (Circle T)), IsOpen U → x ∈ U →
      f =ᵐ[(haar T).restrict U] g →
      Tendsto (fun N : ℕ => partialSum T N f x - partialSum T N g x)
        atTop (𝓝 0)

def localizationL1Statement : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f g : L1 T)
    (x : Circle T) (U : Set (Circle T)), IsOpen U → x ∈ U →
      (f : Circle T → ℂ) =ᵐ[(haar T).restrict U] (g : Circle T → ℂ) →
      Tendsto (fun N : ℕ => partialSum T N f x - partialSum T N g x)
        atTop (𝓝 0)

end P102.Periodic.Expected.Localization
