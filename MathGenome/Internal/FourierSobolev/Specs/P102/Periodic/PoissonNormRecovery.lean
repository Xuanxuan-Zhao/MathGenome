import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.Foundation
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Full independent proposition types for Theorem 1.5, except its separately
allocated Lebesgue-point conclusion. All measures here are probability Haar. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal ComplexConjugate

namespace P102.Periodic.Expected.PoissonNormRecovery

/-- The rational kernel is nonnegative and even, including r = 0. -/
def kernelBasic : Prop := ∀ (T : ℝ) [Fact (0 < T)] (r : ℝ), 0 ≤ r → r < 1 →
  ∀ x : Circle T, 0 ≤ poissonKernel T r x ∧ poissonKernel T r (-x) = poissonKernel T r x

/-- The integer-frequency expansion is absolutely and uniformly convergent.
Both the series and its series of norms converge uniformly, with the net
of all finite frequency subsets as the index. -/
def kernelSeries : Prop := ∀ (T : ℝ) [Fact (0 < T)] (r : ℝ), 0 ≤ r → r < 1 →
  (∀ x : Circle T, Summable (fun k : ℤ => ‖(r ^ k.natAbs : ℂ) * mode T k x‖)) ∧
  TendstoUniformly
    (fun s : Finset ℤ => fun x : Circle T => ∑ k ∈ s, ‖(r ^ k.natAbs : ℂ) * mode T k x‖)
    (fun x => ∑' k : ℤ, ‖(r ^ k.natAbs : ℂ) * mode T k x‖) atTop ∧
  TendstoUniformly
    (fun s : Finset ℤ => fun x : Circle T => ∑ k ∈ s, (r ^ k.natAbs : ℂ) * mode T k x)
    (fun x => (poissonKernel T r x : ℂ)) atTop

/-- Normalized mass one and integrability. -/
def kernelMass : Prop := ∀ (T : ℝ) [Fact (0 < T)] (r : ℝ), 0 ≤ r → r < 1 →
  Integrable (poissonKernel T r) (haar T) ∧ (∫ x, poissonKernel T r x ∂haar T) = 1

/-- Monotonicity on the half-period written in angular coordinates. -/
def kernelMonotone : Prop := ∀ (T : ℝ) [Fact (0 < T)] (r : ℝ), 0 ≤ r → r < 1 →
  AntitoneOn (fun v : ℝ => poissonKernel T r ((T * v / (2 * Real.pi) : ℝ) : Circle T))
    (Icc 0 Real.pi)

/-- Decay off every fixed neighborhood of zero, as r approaches one from below. -/
def kernelDecay : Prop := ∀ (T : ℝ) [Fact (0 < T)] (U : Set (Circle T)),
  U ∈ 𝓝 (0 : Circle T) →
  TendstoUniformlyOn (fun r x => poissonKernel T r x) (fun _ => 0) (𝓝[<] 1) Uᶜ

/-- The same absolute uniform convergence for every L¹ input, with no Fourier
summability assumption on the unweighted coefficients. -/
def abelSeries : Prop := ∀ (T : ℝ) [Fact (0 < T)] (r : ℝ), 0 ≤ r → r < 1 →
  ∀ f : Circle T → ℂ, Integrable f (haar T) →
  (∀ x : Circle T, Summable (fun k : ℤ =>
    ‖(r ^ k.natAbs : ℂ) * coefficient T f k * mode T k x‖)) ∧
  TendstoUniformly
    (fun s : Finset ℤ => fun x : Circle T =>
      ∑ k ∈ s, ‖(r ^ k.natAbs : ℂ) * coefficient T f k * mode T k x‖)
    (fun x => ∑' k : ℤ, ‖(r ^ k.natAbs : ℂ) * coefficient T f k * mode T k x‖) atTop ∧
  TendstoUniformly
    (fun s : Finset ℤ => fun x : Circle T =>
      ∑ k ∈ s, (r ^ k.natAbs : ℂ) * coefficient T f k * mode T k x)
    (abelMean T r f) atTop

/-- Pointwise, everywhere-defined Poisson convolution, in the canonical order. -/
def abelConvolution : Prop := ∀ (T : ℝ) [Fact (0 < T)] (r : ℝ), 0 ≤ r → r < 1 →
  ∀ f : Circle T → ℂ, Integrable f (haar T) → ∀ x : Circle T,
    ConvolutionExistsAt T f (fun y => (poissonKernel T r y : ℂ)) x ∧
    abelMean T r f x = convolution T f (fun y => (poissonKernel T r y : ℂ)) x

/-- Complex continuous data. -/
def uniformRecovery : Prop := ∀ (T : ℝ) [Fact (0 < T)] (f : C(Circle T, ℂ)),
  TendstoUniformly (fun r => abelMean T r f) f (𝓝[<] 1)

/-- Real continuous data embedded into the canonical complex Abel series. -/
def realUniformRecovery : Prop := ∀ (T : ℝ) [Fact (0 < T)] (f : C(Circle T, ℝ)),
  TendstoUniformly (fun r => abelMean T r (fun x => (f x : ℂ)))
    (fun x => (f x : ℂ)) (𝓝[<] 1)

/-- Finite-Lp recovery, including p = 1, expressed by the representative
seminorm so the conclusion is independent of the choice of representatives. -/
def lpRecovery : Prop := ∀ (T : ℝ) [Fact (0 < T)] (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
  ∀ f : Lp ℂ p (haar T),
    (∀ r : ℝ, 0 ≤ r → r < 1 → MemLp (abelMean T r f) p (haar T)) ∧
    Tendsto (fun r => eLpNorm (fun x => abelMean T r f x - f x) p (haar T))
      (𝓝[<] 1) (𝓝 0)

/-- The real Lp class has the same conclusion after its isometric embedding
in the complex scalars used by the Fourier coefficient definition. -/
def realLpRecovery : Prop := ∀ (T : ℝ) [Fact (0 < T)] (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ →
  ∀ f : Lp ℝ p (haar T),
    (∀ r : ℝ, 0 ≤ r → r < 1 →
      MemLp (abelMean T r (fun x => (f x : ℂ))) p (haar T)) ∧
    Tendsto (fun r => eLpNorm
      (fun x => abelMean T r (fun y => (f y : ℂ)) x - (f x : ℂ)) p (haar T))
      (𝓝[<] 1) (𝓝 0)

end P102.Periodic.Expected.PoissonNormRecovery
