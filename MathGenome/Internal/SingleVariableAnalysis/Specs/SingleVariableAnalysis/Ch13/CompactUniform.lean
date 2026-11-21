import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Radius
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch12.MTest
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
K03.13.compact_uniform, paper.tex:1374–1383.
The n-th term of the formal k-th derivative uses the descending factorial
`n.descFactorial k = ∏ j ∈ range k, (n-j)`. It is zero for n < k;
thus inclusive partial sums indexed from zero represent precisely the
source series indexed by n ≥ k. At k = 0 these are the original terms.
The conclusions give uniform convergence of both the scalar series and
its magnitude series, and ordinary absolute convergence at each point.
Radii are the upstream extended coefficient-root radii, and centers are
real. The closed disks include r = 0. Real coefficients also have an
explicit complex-disk estimate with their original real radius.
These are formal derivative series; no differentiability is assumed.
-/
namespace Specs.SingleVariableAnalysis.Ch13.CompactUniform

open Specs.SingleVariableAnalysis.Ch13.PowerSeries
open Specs.SingleVariableAnalysis.Ch11.PartialSums
open Specs.SingleVariableAnalysis.Ch12.Uniform
open scoped ENNReal BigOperators

def realFormalDerivativeTermType : Type :=
  (ℕ → ℝ) → ℝ → ℕ → ℝ → ℕ → ℝ

noncomputable def realFormalDerivativeTermValue : realFormalDerivativeTermType :=
  fun a c k x n => (n.descFactorial k : ℝ) * a n * (x-c)^(n-k)

def complexFormalDerivativeTermType : Type :=
  (ℕ → ℂ) → ℝ → ℕ → ℂ → ℕ → ℂ

noncomputable def complexFormalDerivativeTermValue : complexFormalDerivativeTermType :=
  fun a c k z n => (n.descFactorial k : ℂ) * a n * (z-(c : ℂ))^(n-k)

def realFormalDerivativeZero : Prop :=
  ∀ (a : ℕ → ℝ) (c x : ℝ) (n : ℕ),
    realFormalDerivativeTermValue a c 0 x n = realPowerSeriesTermValue a c x n

def complexFormalDerivativeZero : Prop :=
  ∀ (a : ℕ → ℂ) (c : ℝ) (z : ℂ) (n : ℕ),
    complexFormalDerivativeTermValue a c 0 z n = complexPowerSeriesTermValue a c z n

def realFormalDerivativeFormula : Prop :=
  ∀ (a : ℕ → ℝ) (c x : ℝ) (k n : ℕ),
    realFormalDerivativeTermValue a c k x n =
      (∏ j ∈ Finset.range k, ((n-j : ℕ) : ℝ)) * a n * (x-c)^(n-k)

def complexFormalDerivativeFormula : Prop :=
  ∀ (a : ℕ → ℂ) (c : ℝ) (z : ℂ) (k n : ℕ),
    complexFormalDerivativeTermValue a c k z n =
      (∏ j ∈ Finset.range k, ((n-j : ℕ) : ℂ)) * a n * (z-(c : ℂ))^(n-k)

def realFormalDerivativeBelow : Prop :=
  ∀ (a : ℕ → ℝ) (c x : ℝ) (k n : ℕ), n < k →
    realFormalDerivativeTermValue a c k x n = 0

def complexFormalDerivativeBelow : Prop :=
  ∀ (a : ℕ → ℂ) (c : ℝ) (z : ℂ) (k n : ℕ), n < k →
    complexFormalDerivativeTermValue a c k z n = 0

def realPowerSeriesCompactUniform : Prop :=
  ∀ (a : ℕ → ℝ) (c r : ℝ), 0 ≤ r →
    ENNReal.ofReal r < realPowerSeriesRadiusValue a →
      (∃ f : {x : ℝ // |x-c| ≤ r} → ℝ,
        realUniformConvergesValue (fun N (x : {x : ℝ // |x-c| ≤ r}) =>
          realPowerSeriesPartialSumValue a c x N) f) ∧
      (∃ g : {x : ℝ // |x-c| ≤ r} → ℝ,
        realUniformConvergesValue (fun N (x : {x : ℝ // |x-c| ≤ r}) =>
          realPartialSumValue (fun n => |realPowerSeriesTermValue a c x n|) N) g) ∧
      ∀ x : {x : ℝ // |x-c| ≤ r}, RealPowerSeriesAbsolutelyConvergesValue a c x

def complexPowerSeriesCompactUniform : Prop :=
  ∀ (a : ℕ → ℂ) (c r : ℝ), 0 ≤ r →
    ENNReal.ofReal r < complexPowerSeriesRadiusValue a →
      (∃ f : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r} → ℂ,
        complexUniformConvergesValue (fun N (z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}) =>
          complexPowerSeriesPartialSumValue a c z N) f) ∧
      (∃ g : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r} → ℝ,
        realUniformConvergesValue (fun N (z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}) =>
          realPartialSumValue (fun n => ‖complexPowerSeriesTermValue a c z n‖) N) g) ∧
      ∀ z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}, ComplexPowerSeriesAbsolutelyConvergesValue a c z

def realFormalDerivativeCompactUniform : Prop :=
  ∀ (a : ℕ → ℝ) (c r : ℝ), 0 ≤ r →
    ENNReal.ofReal r < realPowerSeriesRadiusValue a → ∀ k : ℕ,
      (∃ f : {x : ℝ // |x-c| ≤ r} → ℝ,
        realUniformConvergesValue (fun N (x : {x : ℝ // |x-c| ≤ r}) => realPartialSumValue
          (realFormalDerivativeTermValue a c k x) N) f) ∧
      (∃ g : {x : ℝ // |x-c| ≤ r} → ℝ,
        realUniformConvergesValue (fun N (x : {x : ℝ // |x-c| ≤ r}) => realPartialSumValue
          (fun n => |realFormalDerivativeTermValue a c k x n|) N) g) ∧
      ∀ x : {x : ℝ // |x-c| ≤ r}, realSeriesConvergesValue
        (fun n => |realFormalDerivativeTermValue a c k x n|)

def complexFormalDerivativeCompactUniform : Prop :=
  ∀ (a : ℕ → ℂ) (c r : ℝ), 0 ≤ r →
    ENNReal.ofReal r < complexPowerSeriesRadiusValue a → ∀ k : ℕ,
      (∃ f : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r} → ℂ,
        complexUniformConvergesValue (fun N (z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}) => complexPartialSumValue
          (complexFormalDerivativeTermValue a c k z) N) f) ∧
      (∃ g : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r} → ℝ,
        realUniformConvergesValue (fun N (z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}) => realPartialSumValue
          (fun n => ‖complexFormalDerivativeTermValue a c k z n‖) N) g) ∧
      ∀ z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}, realSeriesConvergesValue
        (fun n => ‖complexFormalDerivativeTermValue a c k z n‖)

def realCoefficientsComplexCompactUniform : Prop :=
  ∀ (a : ℕ → ℝ) (c r : ℝ), 0 ≤ r →
    ENNReal.ofReal r < realPowerSeriesRadiusValue a → ∀ k : ℕ,
      (∃ f : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r} → ℂ,
        complexUniformConvergesValue (fun N (z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}) => complexPartialSumValue
          (complexFormalDerivativeTermValue (fun n => (a n : ℂ)) c k z) N) f) ∧
      (∃ g : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r} → ℝ,
        realUniformConvergesValue (fun N (z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}) => realPartialSumValue
          (fun n => ‖complexFormalDerivativeTermValue (fun n => (a n : ℂ)) c k z n‖) N) g) ∧
      ∀ z : {z : ℂ // ‖z-(c : ℂ)‖ ≤ r}, realSeriesConvergesValue
        (fun n => ‖complexFormalDerivativeTermValue (fun n => (a n : ℂ)) c k z n‖)

end Specs.SingleVariableAnalysis.Ch13.CompactUniform
