import MathGenome.Internal.Specs.D05.M02.Examples
import MathGenome.Internal.Specs.D05.M03.Isomorphism
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
Independent statements for K05.08.interpolation, paper.tex:1228–1231.
The domain is the same formal-polynomial submodule used in K05.02.examples.
The nodes are indexed by `Fin r`, and distinctness is injectivity of that map.
A fraction `(X - aⱼ)/(aᵢ - aⱼ)` is multiplication by the constant inverse;
no polynomial division or identification with polynomial functions is intended.
All statements include r = 0, with no characteristic or infinitude assumption.
-/

noncomputable section

namespace Specs.D05.M08.Interpolation

open scoped BigOperators
open Polynomial

/-- Type of the paper's explicit Lagrange polynomials. -/
def lagrangePolynomial_type :=
  ∀ (K : Type*) [Field K] (r : ℕ), (Fin r → K) → Fin r → Polynomial K

/-- Each factor is `(x - aⱼ)/(aᵢ - aⱼ)`. -/
def lagrangePolynomial_value : lagrangePolynomial_type :=
  fun K _ r a i => ∏ j ∈ (Finset.univ : Finset (Fin r)).erase i,
    C ((a i - a j)⁻¹) * (X - C (a j))

def evaluation_type :=
  ∀ (K : Type*) [Field K] (r : ℕ), (Fin r → K) →
    Polynomial.degreeLT K r →ₗ[K] D05.Foundations.CoordinateModule K r

def evaluation_value : evaluation_type := fun K _ r a => {
  toFun := fun p i => (p : Polynomial K).eval (a i)
  map_add' := by intros; funext i; exact Polynomial.eval_add
  map_smul' := by intros; funext i; simp
}

def interpolationSum_type :=
  ∀ (K : Type*) [Field K] (r : ℕ), (Fin r → K) →
    D05.Foundations.CoordinateModule K r →ₗ[K] Polynomial K

/-- This linear map has the literal sum prescribed by the source as its value. -/
def interpolationSum_value : interpolationSum_type := fun K _ r a => {
  toFun := fun c => ∑ i : Fin r, c i • lagrangePolynomial_value K r a i
  map_add' := by
    intro c d
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro t c
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]
}

def denominators_nonzero : Prop :=
  ∀ (K : Type*) [Field K] (r : ℕ) (a : Fin r → K),
    Function.Injective a → ∀ i j : Fin r, i ≠ j → a i - a j ≠ 0

def basis_degree : Prop :=
  ∀ (K : Type*) [Field K] (r : ℕ) (a : Fin r → K),
    Function.Injective a → ∀ i : Fin r,
      (lagrangePolynomial_value K r a i).degree < (r : WithBot ℕ)

def basis_evaluation : Prop :=
  ∀ (K : Type*) [Field K] (r : ℕ) (a : Fin r → K),
    Function.Injective a → ∀ i j : Fin r,
      (lagrangePolynomial_value K r a i).eval (a j) = if i = j then 1 else 0

def interpolation_degree : Prop :=
  ∀ (K : Type*) [Field K] (r : ℕ) (a : Fin r → K),
    Function.Injective a → ∀ c : D05.Foundations.CoordinateModule K r,
      (interpolationSum_value K r a c).degree < (r : WithBot ℕ)

/-- Evaluation after the explicitly given sum returns every prescribed value. -/
def interpolation_evaluation : Prop :=
  ∀ (K : Type*) [Field K] (r : ℕ) (a : Fin r → K),
    Function.Injective a → ∀ (c : D05.Foundations.CoordinateModule K r) (j : Fin r),
      (interpolationSum_value K r a c).eval (a j) = c j

def evaluation_injective : Prop :=
  ∀ (K : Type*) [Field K] (r : ℕ) (a : Fin r → K),
    Function.Injective a → Function.Injective (evaluation_value K r a)

/-- Interpolating the values of a polynomial in the stated domain recovers it. -/
def reconstruction : Prop :=
  ∀ (K : Type*) [Field K] (r : ℕ) (a : Fin r → K),
    Function.Injective a → ∀ p : Polynomial.degreeLT K r,
      interpolationSum_value K r a (evaluation_value K r a p) = (p : Polynomial K)

/-- The forward and inverse maps are specified, not just abstract existence of
an isomorphism between equal-dimensional spaces. -/
def evaluation_isomorphism : Prop :=
  ∀ (K : Type*) [Field K] (r : ℕ) (a : Fin r → K),
    Function.Injective a → ∃ e : Polynomial.degreeLT K r ≃ₗ[K]
      D05.Foundations.CoordinateModule K r,
      e.toLinearMap = evaluation_value K r a ∧
        ∀ c, (e.symm c : Polynomial K) = interpolationSum_value K r a c

/-- The degree bound in dimension zero means precisely the zero polynomial;
the coordinate space is also zero, and the inverse is the empty sum. -/
def empty_case : Prop :=
  ∀ (K : Type*) [Field K] (a : Fin 0 → K),
    Polynomial.degreeLT K 0 = ⊥ ∧
    (∀ p : Polynomial.degreeLT K 0, (p : Polynomial K) = 0) ∧
    (∀ c : D05.Foundations.CoordinateModule K 0, c = 0) ∧
    (∀ c : D05.Foundations.CoordinateModule K 0,
      interpolationSum_value K 0 a c = 0)

end Specs.D05.M08.Interpolation
