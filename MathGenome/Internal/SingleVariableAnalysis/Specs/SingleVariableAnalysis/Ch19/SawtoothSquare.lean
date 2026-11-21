import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Representation
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.Variation
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Basic.Real.Sign
import Mathlib.Topology.Order.Basic

/-! K03.19.examples, paper.tex:5013–5042 (the sawtooth and square wave).
Actual functions on ℝ retain their assigned values at jumps. All coefficients
use the shared proper Darboux integral. Series conclusions are ordinary limits
of ordered finite sums; they do not assert unconditional summability. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.SawtoothSquare
open Set Filter Ch08.Integral Ch15.Variation Ch19.PeriodicSetup Ch19.Representation
open scoped Topology BigOperators

abbrev waveType := ℝ → ℝ

def sawtoothValue : waveType := fun x =>
  let r := toIcoMod (show 0 < 2 * Real.pi by positivity) (-Real.pi) x
  if r = -Real.pi then 0 else r

def squareWaveValue : waveType := fun x => Real.sign (Real.sin x)

def sawtoothProfile : Prop :=
  Function.Periodic sawtoothValue (2 * Real.pi) ∧
  (∀ x ∈ Ioo (-Real.pi) Real.pi, sawtoothValue x = x) ∧
  (∀ k : ℤ, sawtoothValue ((2 * (k : ℝ) + 1) * Real.pi) = 0)

def squareWaveProfile : Prop :=
  Function.Periodic squareWaveValue (2 * Real.pi) ∧
  (∀ x ∈ Ioo 0 Real.pi, squareWaveValue x = 1) ∧
  (∀ x ∈ Ioo (-Real.pi) 0, squareWaveValue x = -1) ∧
  (∀ k : ℤ, squareWaveValue ((k : ℝ) * Real.pi) = 0)

def sawtoothBV : Prop := boundedVariationValue sawtoothValue (-Real.pi) Real.pi

def squareWaveBV : Prop := boundedVariationValue squareWaveValue (-Real.pi) Real.pi

/-- Integrability of all coefficient products is a conclusion, not a certificate
supplied by the caller. Values are independent of the integral witnesses. -/
def sawtoothCoefficients : Prop :=
  ∃ hf : realIntegrableValue sawtoothValue (-Real.pi) Real.pi,
  ∃ ha : CosineWeights sawtoothValue, ∃ hb : SineWeights sawtoothValue,
    aZeroValue sawtoothValue hf = 0 ∧
    ∀ n : ℕ+, cosineCoefficientValue sawtoothValue n (ha n) = 0 ∧
      sineCoefficientValue sawtoothValue n (hb n) =
        2 * (-1 : ℝ) ^ ((n : ℕ) + 1) / (n : ℝ)

def squareWaveCoefficients : Prop :=
  ∃ hf : realIntegrableValue squareWaveValue (-Real.pi) Real.pi,
  ∃ ha : CosineWeights squareWaveValue, ∃ hb : SineWeights squareWaveValue,
    aZeroValue squareWaveValue hf = 0 ∧
    ∀ n : ℕ+, cosineCoefficientValue squareWaveValue n (ha n) = 0 ∧
      sineCoefficientValue squareWaveValue n (hb n) =
        if Even (n : ℕ) then 0 else 4 / (Real.pi * (n : ℝ))

/-- Equality at every point includes the value zero at every seam. -/
def sawtoothSeries : Prop := ∀ x : ℝ,
  Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
    (2 * (-1 : ℝ) ^ (k + 2) / ((k + 1 : ℕ) : ℝ)) *
      Real.sin (((k + 1 : ℕ) : ℝ) * x)) atTop (𝓝 (sawtoothValue x))

/-- Ordered odd sine sums converge at continuity points and to zero at jumps. -/
def squareWaveSeries : Prop := ∀ x : ℝ,
  Tendsto (fun N : ℕ => (4 / Real.pi) * ∑ j ∈ Finset.range N,
    Real.sin (((2 * j + 1 : ℕ) : ℝ) * x) / ((2 * j + 1 : ℕ) : ℝ))
    atTop (𝓝 (squareWaveValue x))

def leibnizPi : Prop :=
  Tendsto (fun N : ℕ => ∑ j ∈ Finset.range N,
    (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ)) atTop (𝓝 (Real.pi / 4))

end Specs.SingleVariableAnalysis.Ch19.SawtoothSquare
