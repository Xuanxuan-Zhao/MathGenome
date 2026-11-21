import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.Conventions
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-! Algebraic positive functionals and the null-space quotient in
`paper.tex`, fa2:p2:gns. No continuity or representation is assumed. -/
noncomputable section
namespace ExpandedFA.CStar.PositiveFunctionals.Spec
universe u
open scoped ComplexOrder

/-- Taking the span makes this definition available for every algebraic functional.
For positive functionals the null-space theorem proves that the span adds no elements. -/
def NullSpaceType := ∀ (A : Type u) [CStarAlgebra A], (A →ₗ[ℂ] ℂ) → Submodule ℂ A
def NullSpaceValue : NullSpaceType.{u} := fun A _ φ =>
  Submodule.span ℂ {a : A | φ (star a * a) = 0}

abbrev NullQuotient {A : Type u} [CStarAlgebra A] (φ : A →ₗ[ℂ] ℂ) :=
  A ⧸ NullSpaceValue A φ

def Schwarz : Prop := ∀ (A : Type u) [CStarAlgebra A] [Nontrivial A]
  (φ : A →ₗ[ℂ] ℂ), Conventions.Spec.PositiveFunctionalValue A φ →
  (∀ a, (φ (star a * a)).im = 0 ∧ 0 ≤ (φ (star a * a)).re) ∧
  ∀ a b, ‖φ (star b * a)‖ ^ 2 ≤
    (φ (star a * a)).re * (φ (star b * b)).re

def ContinuityAndNorm : Prop := ∀ (A : Type u) [CStarAlgebra A] [Nontrivial A]
  (φ : A →ₗ[ℂ] ℂ), Conventions.Spec.PositiveFunctionalValue A φ →
  Continuous φ ∧ ∃ F : A →L[ℂ] ℂ, F.toLinearMap = φ ∧
    (‖F‖ : ℂ) = φ 1 ∧ ‖F‖ = (φ 1).re ∧
    ∀ a, ‖φ a‖ ≤ (φ 1).re * ‖a‖

def NullLeftIdeal : Prop := ∀ (A : Type u) [CStarAlgebra A] [Nontrivial A]
  (φ : A →ₗ[ℂ] ℂ), Conventions.Spec.PositiveFunctionalValue A φ →
  (∀ a, a ∈ NullSpaceValue A φ ↔ φ (star a * a) = 0) ∧
  ∀ c a, a ∈ NullSpaceValue A φ → c * a ∈ NullSpaceValue A φ

/-- A positive definite sesquilinear form and its genuine norm on the actual
algebraic quotient. A `Seminorm` with trivial kernel is a norm; using a bundled
seminorm avoids replacing the quotient's existing addition or scalar action. -/
structure QuotientFormData {A : Type u} [CStarAlgebra A] (φ : A →ₗ[ℂ] ℂ) where
  form : NullQuotient φ → NullQuotient φ → ℂ
  norm : Seminorm ℂ (NullQuotient φ)
  on_classes : ∀ a b, form (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
    φ (star a * b)
  add_left : ∀ x y z, form (x + y) z = form x z + form y z
  add_right : ∀ x y z, form x (y + z) = form x y + form x z
  smul_left : ∀ (r : ℂ) x y, form (r • x) y = star r * form x y
  smul_right : ∀ (r : ℂ) x y, form x (r • y) = r * form x y
  hermitian : ∀ x y, star (form x y) = form y x
  diagonal_nonnegative : ∀ x, (form x x).im = 0 ∧ 0 ≤ (form x x).re
  positive_definite : ∀ x, form x x = 0 ↔ x = 0
  norm_sq : ∀ x, norm x ^ 2 = (form x x).re
  norm_eq_zero : ∀ x, norm x = 0 ↔ x = 0
  left_multiplication : ∀ c : A, ∃ T : NullQuotient φ →ₗ[ℂ] NullQuotient φ,
    (∀ a, T (Submodule.Quotient.mk a) = Submodule.Quotient.mk (c * a)) ∧
    ∀ x, norm (T x) ≤ ‖c‖ * norm x

def QuotientForm : Prop := ∀ (A : Type u) [CStarAlgebra A] [Nontrivial A]
  (φ : A →ₗ[ℂ] ℂ), Conventions.Spec.PositiveFunctionalValue A φ →
  Nonempty (QuotientFormData φ)

end ExpandedFA.CStar.PositiveFunctionals.Spec
