import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.PNat.Basic

/-! K03.19.periodic_setup, paper.tex:4669–4686.
The reference period is [-π,π]. The arbitrary-origin transport theorem is
allocated to PeriodicIntegral. Functions are actual functions on ℝ, with their
pointwise seam values; there is no a.e. quotient or endpoint replacement.

Integral witnesses are explicit, as in the upstream proper Darboux integral.
The existence propositions below require only integrability of f, not an extra
regularity or integrability assumption on its weighted products. The coefficient
maps may also be used for nonperiodic integrable functions on the reference
interval (as needed for the later derivative coefficient formula).
The real/complex conversion identities and invariance under finite seam changes
are allocated to Representation. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch19.PeriodicSetup
open Ch08.Integral
open scoped BigOperators

abbrev modeType := ℤ → ℝ → ℂ
def modeValue : modeType := fun n x => Complex.exp (Complex.I * ((n : ℂ) * (x : ℂ)))

abbrev periodicComplexType := (ℝ → ℂ) → Prop
def periodicComplexValue : periodicComplexType := fun f =>
  Function.Periodic f (2 * Real.pi) ∧ complexIntegrableValue f (-Real.pi) Real.pi

abbrev periodicRealType := (ℝ → ℝ) → Prop
def periodicRealValue : periodicRealType := fun f =>
  Function.Periodic f (2 * Real.pi) ∧ realIntegrableValue f (-Real.pi) Real.pi

abbrev coefficientType := (f : ℝ → ℂ) → (n : ℤ) →
  complexIntegrableValue (fun x => f x * modeValue (-n) x) (-Real.pi) Real.pi → ℂ

def coefficientValue : coefficientType := fun f n h =>
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    complexIntegralValue (fun x => f x * modeValue (-n) x) h

abbrev partialSumType := (f : ℝ → ℂ) →
  (∀ n : ℤ, complexIntegrableValue (fun x => f x * modeValue (-n) x)
    (-Real.pi) Real.pi) → ℕ → ℝ → ℂ

def partialSumValue : partialSumType := fun f h N x =>
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), coefficientValue f n (h n) * modeValue n x

abbrev aZeroType := (f : ℝ → ℝ) → realIntegrableValue f (-Real.pi) Real.pi → ℝ
def aZeroValue : aZeroType := fun f h => (1 / Real.pi) * realIntegralValue f h

-- Positive indices implement precisely the n≥1 convention of the source.
abbrev realCoefficientType := (f : ℝ → ℝ) → (n : ℕ+) →
  realIntegrableValue (fun x => f x * Real.cos ((n : ℝ) * x)) (-Real.pi) Real.pi → ℝ

def cosineCoefficientValue : realCoefficientType := fun f n h =>
  (1 / Real.pi) * realIntegralValue (fun x => f x * Real.cos ((n : ℝ) * x)) h

abbrev sineCoefficientType := (f : ℝ → ℝ) → (n : ℕ+) →
  realIntegrableValue (fun x => f x * Real.sin ((n : ℝ) * x)) (-Real.pi) Real.pi → ℝ

def sineCoefficientValue : sineCoefficientType := fun f n h =>
  (1 / Real.pi) * realIntegralValue (fun x => f x * Real.sin ((n : ℝ) * x)) h

def coefficientIntegrability : Prop := ∀ (f : ℝ → ℂ),
  complexIntegrableValue f (-Real.pi) Real.pi → ∀ n : ℤ,
  complexIntegrableValue (fun x => f x * modeValue (-n) x) (-Real.pi) Real.pi

def cosineIntegrability : Prop := ∀ (f : ℝ → ℝ),
  realIntegrableValue f (-Real.pi) Real.pi → ∀ n : ℕ+,
  realIntegrableValue (fun x => f x * Real.cos ((n : ℝ) * x)) (-Real.pi) Real.pi

def sineIntegrability : Prop := ∀ (f : ℝ → ℝ),
  realIntegrableValue f (-Real.pi) Real.pi → ∀ n : ℕ+,
  realIntegrableValue (fun x => f x * Real.sin ((n : ℝ) * x)) (-Real.pi) Real.pi

/-- Real functions can use the same complex Fourier coefficient definition. -/
def realEmbeddingIntegrability : Prop := ∀ (f : ℝ → ℝ),
  realIntegrableValue f (-Real.pi) Real.pi →
  complexIntegrableValue (fun x => (f x : ℂ)) (-Real.pi) Real.pi

end Specs.SingleVariableAnalysis.Ch19.PeriodicSetup
