import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.Free
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! Specifications for the Jacobson polynomials in an ordinary Lie algebra. -/

open scoped TensorProduct

namespace Specs.LieNotes.SuperRestricted.JacobsonPolynomials

open _root_.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary
open Polynomial (X)

universe u v

variable {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]

/-- Extract the coefficient of `t^j` from a Lie-algebra-valued polynomial. -/
noncomputable def polynomialCoeff (j : ℕ) : Polynomial k ⊗[k] G →ₗ[k] G :=
  (TensorProduct.lid k G).toLinearMap ∘ₗ
    TensorProduct.map (Polynomial.lcoeff k j) LinearMap.id

/-- The iterated adjoint of `t x + y` applied to the constant `x`. -/
noncomputable def adjointPolynomial (x y : G) (n : ℕ) : Polynomial k ⊗[k] G :=
  ((LieAlgebra.ad (Polynomial k) (Polynomial k ⊗[k] G)
      ((X ⊗ₜ[k] x) + (1 ⊗ₜ[k] y))) ^ n) (1 ⊗ₜ[k] x)

set_option linter.checkUnivs false in
def jacobsonTermType :=
  ∀ (k : Type u) [Field k] {G : Type v} [LieRing G] [LieAlgebra k G],
    ℕ → ℕ → G → G → G

/-- The inverse-scaled recurrence coefficient with index `1 ≤ i < p`. -/
def jacobsonTermValue (k : Type u) [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    (p i : ℕ) (x y : G) : G :=
  (i : k)⁻¹ • jacobsonCoeffValue x y (p - 1) (i - 1)

def coeff_adjointPolynomialType : Prop :=
  ∀ {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    (x y : G) (n j : ℕ),
    polynomialCoeff j (adjointPolynomial (k := k) x y n) = jacobsonCoeffValue x y n j

def jacobsonTerm_specType : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
    {G : Type v} [LieRing G] [LieAlgebra k G] (x y : G) {i : ℕ},
    1 ≤ i → i < p →
    ∀ s : G, s = jacobsonTermValue k p i x y ↔
      (i : k) • s = polynomialCoeff (i - 1) (adjointPolynomial (k := k) x y (p - 1))

/-- A single free Lie polynomial gives the term in every Lie algebra over the field. -/
def jacobsonTerm_isLiePolynomialType : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p] (i : ℕ),
    1 ≤ i → i < p →
    ∃ P : FreeLieAlgebra k Bool,
      ∀ {G : Type v} [LieRing G] [LieAlgebra k G] (x y : G),
        FreeLieAlgebra.lift k (fun b : Bool => if b then y else x) P =
          jacobsonTermValue k p i x y

def sum_jacobsonTermType : Prop :=
  ∀ (k : Type u) [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
    (p : ℕ) (x y : G),
    (∑ i ∈ Finset.Ico 1 p, jacobsonTermValue k p i x y) =
      jacobsonCorrectionValue k p x y

end Specs.LieNotes.SuperRestricted.JacobsonPolynomials
