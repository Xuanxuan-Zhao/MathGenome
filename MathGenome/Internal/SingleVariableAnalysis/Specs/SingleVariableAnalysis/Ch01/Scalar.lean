import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
Independent specification of the shared scalar foundation (paper.tex, declared
foundations and K03.01.real_interface). All scalar objects are the existing
Mathlib real and complex numbers. No sequence convergence or complex metric
completeness assertion is part of this interface.
-/

namespace SingleVariableAnalysis

/-- The two scalar choices allowed in the manuscript. -/
inductive ScalarKind where
  | real
  | complex

end SingleVariableAnalysis

namespace Specs.SingleVariableAnalysis.Ch01.Scalar

open _root_.SingleVariableAnalysis
open scoped BigOperators ComplexConjugate

universe u

/-- Expected type and value of the scalar family: exactly `ℝ` or `ℂ`. -/
def scalarType : Type 1 := ScalarKind → Type

def scalarValue : scalarType
  | .real => ℝ
  | .complex => ℂ

def complexCoordinatesType : Type := ℂ ≃ ℝ × ℝ

def complexCoordinatesValue : complexCoordinatesType := Complex.equivRealProd

def modulusType : Type := ℂ → ℝ

noncomputable def modulusValue : modulusType := fun z => ‖z‖

/-- The completeness used as a foundation is the real least-upper-bound property. -/
def realLeastUpperBound : Prop :=
  ∀ A : Set ℝ, A.Nonempty → BddAbove A → ∃ b : ℝ, IsLUB A b

def complexPairDecomposition : Prop :=
  ∀ z : ℂ, (z.re : ℂ) + (z.im : ℂ) * Complex.I = z

def complexPairAddition : Prop :=
  ∀ z w : ℂ, ((z + w).re, (z + w).im) = (z.re + w.re, z.im + w.im)

def complexPairMultiplication : Prop :=
  ∀ z w : ℂ, ((z * w).re, (z * w).im) =
    (z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re)

def complexPairConjugation : Prop :=
  ∀ z : ℂ, ((conj z).re, (conj z).im) = (z.re, -z.im)

def complexModulusFormula : Prop :=
  ∀ z : ℂ, ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2)

def realNormFormula : Prop :=
  ∀ x : ℝ, ‖x‖ = |x|

/-- Arbitrary finite sets include the empty set; there are no positivity assumptions. -/
def realCauchySchwarz : Prop :=
  ∀ {ι : Type u} (s : Finset ι) (u v : ι → ℝ),
    (∑ j ∈ s, u j * v j) ^ 2 ≤ (∑ j ∈ s, u j ^ 2) * (∑ j ∈ s, v j ^ 2)

def complexCauchySchwarz : Prop :=
  ∀ {ι : Type u} (s : Finset ι) (u v : ι → ℂ),
    ‖∑ j ∈ s, conj (u j) * v j‖ ^ 2 ≤
      (∑ j ∈ s, ‖u j‖ ^ 2) * (∑ j ∈ s, ‖v j‖ ^ 2)

def complexTriangle : Prop :=
  ∀ z w : ℂ, ‖z + w‖ ≤ ‖z‖ + ‖w‖

def complexModulusMultiplicative : Prop :=
  ∀ z w : ℂ, ‖z * w‖ = ‖z‖ * ‖w‖

def complexConjugationModulus : Prop :=
  ∀ z : ℂ, ‖conj z‖ = ‖z‖

/-- The metric is the usual scalar metric, with no alternative notion of distance. -/
def complexDistanceFormula : Prop :=
  ∀ z w : ℂ, dist z w = Real.sqrt ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2)

end Specs.SingleVariableAnalysis.Ch01.Scalar
