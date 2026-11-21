import Mathlib.Algebra.Module.MinimalAxioms
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
Independent statements for K05.02.vector_space (paper.tex:442–447).

Vector spaces are Mathlib `Module`s over fields, with their given abelian-group
addition. The first statement identifies precisely the paper's four laws with
such a structure on the *same* scalar action; no finite-dimensional hypothesis
is imposed. The complex-to-real statement constructs the restricted structure,
rather than assuming an arbitrary real action on the complex space.
-/

namespace Specs.D05.M02.VectorSpace

universe u v

/-- The type of the paper's vector-space structure, for a fixed abelian group. -/
def vectorSpace_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] → Type (max u v)

/-- The canonical value is Mathlib's module structure itself, over the named field. -/
def vectorSpace_value : vectorSpace_type.{u, v} :=
  fun K V _ _ => Module K V

/-- The four displayed laws are exactly what is needed on an abelian group. -/
def module_iff_axioms : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] (s : K → V → V),
    (∃ m : Module K V, ∀ (a : K) (v : V), (letI := m; a • v) = s a v) ↔
      (∀ (a : K) (u v : V), s a (u + v) = s a u + s a v) ∧
      (∀ (a b : K) (v : V), s (a + b) v = s a v + s b v) ∧
      (∀ (a b : K) (v : V), s (a * b) v = s a (s b v)) ∧
      (∀ v : V, s 1 v = v)

/-- The scalar zero acts as the zero map. -/
def zero_scalar : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (v : V),
    (0 : K) • v = 0

/-- Every scalar fixes the zero vector. -/
def scalar_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (a : K),
    a • (0 : V) = 0

/-- Negating the scalar negates the resulting vector. -/
def neg_scalar : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (a : K) (v : V),
    (-a) • v = -(a • v)

/-- A nonzero scalar cannot annihilate a nonzero vector. -/
def eq_zero_of_smul_eq_zero : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (a : K) (v : V),
    a • v = 0 → a ≠ 0 → v = 0

/-- Restricting along the usual inclusion of ℝ in ℂ gives a real vector space. -/
def complex_as_real : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V],
    ∃ m : Module ℝ V, ∀ (a : ℝ) (v : V),
      (letI := m; a • v) = (a : ℂ) • v

/-- The canonical restricted action is exactly complex multiplication by a real scalar. -/
def real_smul_eq_complex : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] (a : ℝ) (v : V),
    a • v = (a : ℂ) • v

/-- The same underlying vectors can have different dimensions over different fields. -/
def scalar_field_dimension_example : Prop :=
  Module.finrank ℝ ℂ = 2 ∧ Module.finrank ℂ ℂ = 1 ∧
    Module.finrank ℝ ℂ ≠ Module.finrank ℂ ℂ

end Specs.D05.M02.VectorSpace
