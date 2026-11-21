import MathGenome.Internal.Specs.D05.M11.Bilinear
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.CharP.Two

/-!
Independent interface for K05.11.symmetric_quadratic (paper.tex:1672–1676).
The definitions use the existing bilinear forms and Mathlib quadratic forms.
The identities hold in arbitrary dimension, hence in particular on every
finite-dimensional space in the chapter. No characteristic restriction is
needed until the explicit characteristic-two example. The polar form is the
full difference q(x+y)-q(x)-q(y), without a factor of one half.
-/

namespace Specs.D05.M11.SymmetricQuadratic

universe u v

/-- Symmetry is a property of the given bilinear form. -/
def symmetric_type : Type (max (u + 1) (v + 1)) :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] → [Module K V] →
    LinearMap.BilinForm K V → Prop

def symmetric_value : symmetric_type.{u, v} :=
  fun {_ _} [_] [_] [_] B => B.IsSymm

/-- Quadratic forms retain homogeneity and a bilinear polar function in all characteristics. -/
def quadraticForm_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → [Module K V] →
    Type (max u v)

def quadraticForm_value : quadraticForm_type.{u, v} :=
  fun K V _ _ _ => QuadraticForm K V

/-- Every bilinear form has a bundled quadratic diagonal, even without symmetry. -/
def diagonal_type : Type (max (u + 1) (v + 1)) :=
  {K : Type u} → {V : Type v} → [Field K] → [AddCommGroup V] → [Module K V] →
    LinearMap.BilinForm K V → QuadraticForm K V

def diagonal_value : diagonal_type.{u, v} :=
  fun {_ _} [_] [_] [_] B => B.toQuadraticMap

/-- The symmetric predicate is exactly the paper's slot interchange identity. -/
def symmetric_iff : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V), B.IsSymm ↔ ∀ u v, B u v = B v u

/-- A raw function is represented by a quadratic form exactly when it has the
paper's homogeneity and bilinear polar function, with no assumed diagonal representation. -/
def quadratic_iff_axioms : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (q : V → K),
    (∃ Q : QuadraticForm K V, ∀ x, Q x = q x) ↔
      (∀ (a : K) (x : V), q (a • x) = a ^ 2 * q x) ∧
      (∃ P : LinearMap.BilinForm K V, ∀ x y, P x y = q (x + y) - q x - q y)

def diagonal_apply : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (x : V), diagonal_value B x = B x x

def diagonal_homogeneous : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (a : K) (x : V),
    diagonal_value B (a • x) = a ^ 2 * diagonal_value B x

/-- Expansion of the diagonal, including both cross terms for an arbitrary form. -/
def diagonal_polar : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (x y : V),
    diagonal_value B (x + y) - diagonal_value B x - diagonal_value B y =
      B x y + B y x

/-- The cross-term expression is itself a bilinear form. -/
def diagonal_polar_bilinear : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V),
    (diagonal_value B).polarBilin = B + B.flip

/-- Every quadratic form's polar function is represented by an actual bilinear
form, and this form is symmetric in all characteristics. -/
def quadratic_polar : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V),
    (∀ x y, Q.polarBilin x y = Q (x + y) - Q x - Q y) ∧ Q.polarBilin.IsSymm

/-- On the scalar line the two canonical quadratic functions are zero and square. -/
def scalar_examples_apply : Prop :=
  ∀ {K : Type*} [Field K] (x : K),
    (0 : QuadraticForm K K) x = 0 ∧ (QuadraticMap.sq (R := K)) x = x ^ 2

/-- In every field of characteristic two both example polar forms vanish. -/
def characteristic_two_polar : Prop :=
  ∀ {K : Type*} [Field K] [CharP K 2],
    (0 : QuadraticForm K K).polarBilin = 0 ∧
      (QuadraticMap.sq (R := K) : QuadraticForm K K).polarBilin = 0

/-- Despite those equal polar forms, evaluation at one distinguishes the forms. -/
def characteristic_two_distinct : Prop :=
  ∀ {K : Type*} [Field K] [CharP K 2],
    (QuadraticMap.sq (R := K) : QuadraticForm K K) 1 = 1 ∧
      (0 : QuadraticForm K K) ≠ QuadraticMap.sq (R := K)

/-- Thus the unnormalized polar construction is not injective in characteristic two. -/
def characteristic_two_not_injective : Prop :=
  ∀ {K : Type*} [Field K] [CharP K 2],
    ¬ Function.Injective (QuadraticMap.polarBilin : QuadraticForm K K →
      LinearMap.BilinForm K K)

end Specs.D05.M11.SymmetricQuadratic
