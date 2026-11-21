import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.PoissonNormRecovery
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace P102.Periodic.Expected.PoissonLebesgueRecovery

/-- The local condition uses angular coordinates and the specified value, rather
than the value of a possibly modified representative at the point. -/
def HasAngularLebesgueValue (T : ℝ) [Fact (0 < T)]
    (f : Circle T → ℂ) (x : Circle T) (L : ℂ) : Prop :=
  Tendsto (fun s : ℝ => (2 * s)⁻¹ *
    ∫ v in -s..s, ‖f (x - ((T * v / (2 * Real.pi) : ℝ) : Circle T)) - L‖)
    (𝓝[>] 0) (𝓝 0)

/-- Recovery at each specified Lebesgue value, without an a.e. differentiation
hypothesis. Real functions are included through their scalar embedding. -/
def lebesgueRecovery : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℂ), Integrable f (haar T) →
    ∀ (x : Circle T) (L : ℂ), HasAngularLebesgueValue T f x L →
      Tendsto (fun r : ℝ => abelMean T r f x) (𝓝[<] 1) (𝓝 L)

/-- Explicit real specialization of recovery, in the same complex Abel
series used by the upstream real continuous and Lp theorems. -/
def realLebesgueRecovery : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f : Circle T → ℝ), Integrable f (haar T) →
    ∀ (x : Circle T) (L : ℝ),
      Tendsto (fun s : ℝ => (2 * s)⁻¹ *
        ∫ v in -s..s, |f (x - ((T * v / (2 * Real.pi) : ℝ) : Circle T)) - L|)
        (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun r : ℝ => abelMean T r (fun y => (f y : ℂ)) x)
        (𝓝[<] 1) (𝓝 (L : ℂ))

/-- Both the local condition and the everywhere-defined Abel mean depend only
on the a.e. class. -/
def representativeInvariance : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (f g : Circle T → ℂ), f =ᵐ[haar T] g →
    (∀ (r : ℝ) (x : Circle T), abelMean T r f x = abelMean T r g x) ∧
    (∀ (x : Circle T) (L : ℂ),
      HasAngularLebesgueValue T f x L ↔ HasAngularLebesgueValue T g x L)

/-- The complete theorem, retaining the rational kernel, absolute uniform
expansion, convolution identity, continuous and finite-Lp conclusions. -/
def completeRecovery : Prop :=
  PoissonNormRecovery.kernelBasic ∧
  PoissonNormRecovery.kernelSeries ∧
  PoissonNormRecovery.kernelMass ∧
  PoissonNormRecovery.kernelMonotone ∧
  PoissonNormRecovery.kernelDecay ∧
  PoissonNormRecovery.abelSeries ∧
  PoissonNormRecovery.abelConvolution ∧
  PoissonNormRecovery.uniformRecovery ∧
  PoissonNormRecovery.realUniformRecovery ∧
  PoissonNormRecovery.lpRecovery ∧
  PoissonNormRecovery.realLpRecovery ∧
  (∀ (T : ℝ) [Fact (0 < T)] (r t : ℝ),
    poissonKernel T r (t : Circle T) =
      (1 - r ^ 2) / (1 - 2 * r * Real.cos (2 * Real.pi * t / T) + r ^ 2)) ∧
  lebesgueRecovery ∧ realLebesgueRecovery ∧ representativeInvariance

end P102.Periodic.Expected.PoissonLebesgueRecovery
