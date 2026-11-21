import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.PeriodicSetup
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Variation
import Mathlib.Topology.Order.Basic

/-! K03.19.jordan, paper.tex:4828–4877. The hypothesis is bounded
variation on one closed period with its actual assigned values. The origin
of that period is arbitrary. The limits are ordinary sided limits on ℝ;
partial sums are the symmetric integer sums with the shared proper Darboux
coefficients. In particular the conclusion applies at every period seam. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.Jordan
open Ch08.Integral Ch15.Variation PeriodicSetup Filter
open scoped Topology

def complexJordan : Prop :=
  ∀ (f : ℝ → ℂ) (a : ℝ), Function.Periodic f (2 * Real.pi) →
    boundedVariationValue f a (a + 2 * Real.pi) →
    ∃ _H : ∀ n : ℤ, complexIntegrableValue
      (fun y => f y * modeValue (-n) y) (-Real.pi) Real.pi,
      ∀ x : ℝ, ∃ Lminus Lplus : ℂ,
        Tendsto f (𝓝[Set.Iio x] x) (𝓝 Lminus) ∧
        Tendsto f (𝓝[Set.Ioi x] x) (𝓝 Lplus) ∧
        ∀ H' : ∀ n : ℤ, complexIntegrableValue
          (fun y => f y * modeValue (-n) y) (-Real.pi) Real.pi,
          Tendsto (fun N : ℕ => partialSumValue f H' N x) atTop
            (𝓝 ((Lminus + Lplus) / 2))

def realJordan : Prop :=
  ∀ (f : ℝ → ℝ) (a : ℝ), Function.Periodic f (2 * Real.pi) →
    boundedVariationValue f a (a + 2 * Real.pi) →
    ∃ _H : ∀ n : ℤ, complexIntegrableValue
      (fun y => (f y : ℂ) * modeValue (-n) y) (-Real.pi) Real.pi,
      ∀ x : ℝ, ∃ Lminus Lplus : ℝ,
        Tendsto f (𝓝[Set.Iio x] x) (𝓝 Lminus) ∧
        Tendsto f (𝓝[Set.Ioi x] x) (𝓝 Lplus) ∧
        ∀ H' : ∀ n : ℤ, complexIntegrableValue
          (fun y => (f y : ℂ) * modeValue (-n) y) (-Real.pi) Real.pi,
          Tendsto (fun N : ℕ => partialSumValue (fun y => (f y : ℂ)) H' N x) atTop
            (𝓝 (((Lminus + Lplus) / 2 : ℝ) : ℂ))

end Specs.SingleVariableAnalysis.Ch19.Jordan
