import MathGenome.Internal.Specs.D05.M02.BasisExtension
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent statements for K05.02.dimension (paper.tex:500–501).

Finite dimensionality is the canonical `FiniteDimensional` predicate, bridged
to the existence of a finite indexed spanning family. Dimension is Mathlib's
`Module.finrank`, used here on finite-dimensional spaces only. The empty basis
and zero space are included. No finite-dimensional assumption is made in the
spanning characterization, basis extraction, or comparison of finite bases.
-/

namespace Specs.D05.M02.Dimension

universe u v

def finiteDimensional_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] →
    [Module K V] → Prop

def finiteDimensional_value : finiteDimensional_type.{u, v} :=
  fun K V _ _ _ => FiniteDimensional K V

/-- The source's definition, including a possible empty spanning family. -/
def finiteDimensional_iff_finite_spanning : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    FiniteDimensional K V ↔
      ∃ (n : ℕ) (w : Fin n → V), Submodule.span K (Set.range w) = ⊤

/-- Extraction produces an actual basis with a finite index type. -/
def finite_basis_of_finite_spanning : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (n : ℕ) (w : Fin n → V), Submodule.span K (Set.range w) = ⊤ →
      ∃ m : ℕ, Nonempty (Module.Basis (Fin m) K V)

/-- Finite spanning and a finite basis are equivalent notions of finiteness. -/
def finiteDimensional_iff_finite_basis : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    FiniteDimensional K V ↔ ∃ n : ℕ, Nonempty (Module.Basis (Fin n) K V)

/-- Applying the length inequality in both directions makes basis length intrinsic. -/
def finite_bases_equal_length : Prop :=
  ∀ {K V I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] [Fintype J] (b : Module.Basis I K V) (c : Module.Basis J K V),
    Fintype.card I = Fintype.card J

def dimension_type : Type (max (u + 1) (v + 1)) :=
  (K : Type u) → (V : Type v) → [Field K] → [AddCommGroup V] →
    [Module K V] → [FiniteDimensional K V] → ℕ

/-- The natural-number dimension, on the finite-dimensional domain of the source. -/
noncomputable def dimension_value : dimension_type.{u, v} :=
  fun K V _ _ _ _ => Module.finrank K V

/-- The canonical dimension is exactly the common length of any finite basis. -/
def dimension_eq_card_basis : Prop :=
  ∀ {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype I] (b : Module.Basis I K V),
    Module.finrank K V = Fintype.card I

/-- This common length is attained by a basis, including in dimension zero. -/
def exists_basis_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], Nonempty (Module.Basis (Fin (Module.finrank K V)) K V)

/-- The empty basis spans precisely the zero space, in both directions. -/
def empty_basis_iff_zero_space : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    Nonempty (Module.Basis (Fin 0) K V) ↔ ∀ x : V, x = 0

/-- A zero space is finite-dimensional and has dimension zero. -/
def zero_space_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Subsingleton V],
    FiniteDimensional K V ∧ Module.finrank K V = 0

/-- In the source's finite-dimensional setting, dimension zero characterizes zero. -/
def dimension_zero_iff_zero_space : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], Module.finrank K V = 0 ↔ ∀ x : V, x = 0

end Specs.D05.M02.Dimension
