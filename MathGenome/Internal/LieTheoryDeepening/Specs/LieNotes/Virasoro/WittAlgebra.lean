import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.RingTheory.Derivation.Lie

/-! The Laurent derivation model of the Witt algebra in Proposition KM10. -/

noncomputable section

open LaurentPolynomial

namespace LieNotes.Virasoro.WittSpec

local notation "A" => LaurentPolynomial ℂ

abbrev Witt : Type := Derivation ℂ A A

def WittType : Type 1 := Type

private def derivativeLinear : A →ₗ[ℂ] A :=
  (AddMonoidAlgebra.basis ℤ ℂ).constr ℂ (fun i => (i : ℂ) • T (i - 1))

private theorem derivativeLinear_T (i : ℤ) :
    derivativeLinear (T i) = (i : ℂ) • T (i - 1) :=
  (AddMonoidAlgebra.basis ℤ ℂ).constr_basis ℂ _ i

/-- Formal differentiation on Laurent polynomials, with `t^i ↦ i t^(i-1)`. -/
def derivative : Witt := by
  refine Derivation.mk' derivativeLinear fun a b => ?_
  let mul := LinearMap.mul ℂ A
  have leibniz :
      mul.compr₂ derivativeLinear =
        mul.compl₂ derivativeLinear + (mul.compl₂ derivativeLinear).flip := by
    apply LinearMap.ext_basis (AddMonoidAlgebra.basis ℤ ℂ) (AddMonoidAlgebra.basis ℤ ℂ)
    intro i j
    simp only [mul, LinearMap.compr₂_apply, LinearMap.add_apply, LinearMap.flip_apply,
      LinearMap.compl₂_apply, LinearMap.mul_apply', AddMonoidAlgebra.basis_apply]
    change derivativeLinear (T i * T j) =
      T i * derivativeLinear (T j) + T j * derivativeLinear (T i)
    rw [← T_add, derivativeLinear_T, derivativeLinear_T, derivativeLinear_T,
      mul_smul_comm, mul_smul_comm, ← T_add, ← T_add]
    rw [show i + (j - 1) = i + j - 1 by omega, show j + (i - 1) = i + j - 1 by omega]
    rw [Int.cast_add, add_smul, add_comm]
  exact congrArg (fun f : A →ₗ[ℂ] A →ₗ[ℂ] A => f a b) leibniz

def DerivativeType : Type := Witt

def ModeType : Type := ℤ → Witt

/-- The signed vector field `L_m = -t^(m+1) ∂ₜ`. -/
def mode (m : ℤ) : Witt := (-(T (m + 1) : A)) • derivative

abbrev EvaluationType : Type := Witt →ₗ[ℂ] A

/-- The Laurent coefficient of a vector field, obtained by evaluating it at `t`. -/
def evaluation : EvaluationType where
  toFun D := D (T 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def DerivativeOnMonomials : Prop :=
  ∀ i : ℤ, derivative (T i) = (i : ℂ) • T (i - 1)

def ModeOnMonomials : Prop :=
  ∀ m i : ℤ, mode m (T i) = (-(i : ℂ)) • T (m + i)

def EvaluationDeterminesDerivation : Prop :=
  ∀ ⦃D E : Witt⦄, D (T 1) = E (T 1) → D = E

def EvaluationBijective : Prop := Function.Bijective evaluation

def DerivationFromCoefficient : Prop :=
  ∀ (D : Witt) (f : A), D f = D (T 1) * derivative f

def ModeBasis : Prop :=
  ∃ b : Module.Basis ℤ ℂ Witt,
    (∀ m : ℤ, b m = mode m) ∧
    ∀ (D : Witt) (m : ℤ), b.repr D m = -((D (T 1)).coeff (m + 1))

def ModeExpansion : Prop :=
  ∀ D : Witt,
    D = (D (T 1)).coeff.sum (fun j c => (-c) • mode (j - 1))

def ModeBracket : Prop :=
  ∀ m n : ℤ, ⁅mode m, mode n⁆ = ((m : ℂ) - (n : ℂ)) • mode (m + n)

theorem derivative_T (i : ℤ) : derivative (T i) = (i : ℂ) • T (i - 1) :=
  derivativeLinear_T i

end LieNotes.Virasoro.WittSpec
