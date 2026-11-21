import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
Shared Euclidean transform interfaces for paper.tex §§7.1 and 7.3.
The standard `EuclideanSpace` and its subtype carry their usual norms,
topologies, and Borel measurable structures. No positive dimension assumption
is made. The orthant includes its boundary.
-/

open MeasureTheory
open scoped RealInnerProductSpace ComplexConjugate

namespace ProbabilityFoundations.Ch07

/-- Real Euclidean space, including the one-point space in dimension zero. -/
abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The closed positive orthant as a subset of Euclidean space. -/
def positiveOrthantSet (d : ℕ) : Set (Euclidean d) := {x | ∀ j, 0 ≤ x j}

/-- The orthant with the subspace topology and induced Borel structure. -/
abbrev PositiveOrthant (d : ℕ) := ↥(positiveOrthantSet d)

instance (d : ℕ) : Zero (PositiveOrthant d) := ⟨⟨0, by intro j; simp⟩⟩

instance (d : ℕ) : Inhabited (PositiveOrthant d) := ⟨0⟩

end ProbabilityFoundations.Ch07

namespace Specs.ProbabilityFoundations.Ch07.TransformObjects

open _root_.ProbabilityFoundations.Ch07

/-- Type and canonical library value of the characteristic function. The
explicit integral convention is independently required below. These definitions
also make sense for arbitrary measures; probability laws are included. -/
def characteristicFunctionType :=
  {d : ℕ} → Measure (Euclidean d) → Euclidean d → ℂ

noncomputable def characteristicFunctionValue : characteristicFunctionType :=
  fun {_d} μ t => charFun μ t

/-- Frequency conversion to the negative-sign, 2π Fourier convention. -/
def fourierFrequencyType := {d : ℕ} → Euclidean d → Euclidean d

noncomputable def fourierFrequencyValue : fourierFrequencyType :=
  fun {_d} t => (-(2 * Real.pi)⁻¹ : ℝ) • t

/-- A finite list may have repetitions and may be empty. -/
def characteristicQuadraticFormType :=
  {d : ℕ} → (Euclidean d → ℂ) → {n : ℕ} → (Fin n → Euclidean d) → (Fin n → ℂ) → ℂ

noncomputable def characteristicQuadraticFormValue : characteristicQuadraticFormType :=
  fun {_d} φ {_n} t c => ∑ j, ∑ k, c j * conj (c k) * φ (t j - t k)

def isPositiveDefiniteType := {d : ℕ} → (Euclidean d → ℂ) → Prop

/-- A complex quadratic form is nonnegative precisely when its imaginary
part is zero and its real part is nonnegative. -/
def isPositiveDefiniteValue : isPositiveDefiniteType :=
  fun {d} φ => ∀ (n : ℕ) (t : Fin n → Euclidean d) (c : Fin n → ℂ),
    (characteristicQuadraticFormValue φ t c).im = 0 ∧
    0 ≤ (characteristicQuadraticFormValue φ t c).re

def convolutionType :=
  {d : ℕ} → Measure (Euclidean d) → Measure (Euclidean d) → Measure (Euclidean d)

noncomputable def convolutionValue : convolutionType :=
  fun {_d} μ ν => Measure.map (fun p => p.1 + p.2) (μ.prod ν)

def laplaceTransformType :=
  {d : ℕ} → Measure (PositiveOrthant d) → PositiveOrthant d → ℝ

noncomputable def laplaceTransformValue : laplaceTransformType :=
  fun {d} μ t => ∫ x, Real.exp (- inner ℝ (t : Euclidean d) (x : Euclidean d)) ∂μ

/-- The probability convention is exp(i⟨t,x⟩), with no 2π. -/
def characteristicFunctionFormula : Prop :=
  ∀ {d : ℕ} (μ : Measure (Euclidean d)) (t : Euclidean d),
    characteristicFunctionValue μ t =
      ∫ x, Complex.exp (Complex.I * (inner ℝ t x : ℂ)) ∂μ

/-- The same object in Mathlib's Fourier convention, evaluated at ξ=-t/(2π).
`fourierIntegral` integrates `fourierChar (-⟪x,ξ⟫)` and `fourierChar u`
is exp(2πiu). -/
def characteristicFunctionFourier : Prop :=
  ∀ {d : ℕ} (μ : Measure (Euclidean d)) (t : Euclidean d),
    characteristicFunctionValue μ t =
      VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ (Euclidean d))
        (1 : Euclidean d → ℂ) (fourierFrequencyValue t)

/-- An explicit kernel identity fixes the signs and normalization. -/
def fourierFrequencyKernel : Prop :=
  ∀ {d : ℕ} (t x : Euclidean d),
    Complex.exp (((-(2 * Real.pi) * inner ℝ (fourierFrequencyValue t) x : ℝ) : ℂ)
      * Complex.I) = Complex.exp (Complex.I * (inner ℝ t x : ℂ))

/-- The orthant is closed in the Euclidean topology. -/
def positiveOrthantClosed : Prop :=
  ∀ d : ℕ, IsClosed (positiveOrthantSet d)

end Specs.ProbabilityFoundations.Ch07.TransformObjects
