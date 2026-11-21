import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
LA-B03, notes/005/lie-algebras-and-representations.tex, lines 729–782.
This module specifies the linear Jordan decomposition, including arbitrary
characteristic-zero fields and the zero vector space. The derivation assertion
of the same proposition is allocated to LA-B03-Derivations.

Absolute semisimplicity is stated on the actual scalar extension to an algebraic
closure. The eigenspace theorem below also expresses its diagonalizability there.
Uniqueness compares all commuting semisimple/nilpotent decompositions, without
assuming polynomiality or preservation of subspaces of the competing parts.
-/

universe u v

namespace LieAlgebrasAndRepresentations

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

/-- Semisimplicity after extension of scalars to an algebraic closure. -/
def IsAbsolutelySemisimple (s : Module.End k V) : Prop :=
  Module.End.IsSemisimple (s.baseChange (AlgebraicClosure k))

/-- The additive Jordan decomposition, with the semisimple part listed first. -/
def IsJordanDecomposition (A s n : Module.End k V) : Prop :=
  A = s + n ∧ Commute s n ∧ IsAbsolutelySemisimple s ∧ IsNilpotent n

end LieAlgebrasAndRepresentations

namespace Specs.LieAlgebrasAndRepresentations.LinearJordan

open _root_.LieAlgebrasAndRepresentations

/-- Existence, polynomiality over the original field, stability, and full uniqueness. -/
def linear_jordan_decomposition_type : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (A : Module.End k V),
  ∃ s n : Module.End k V,
    IsJordanDecomposition A s n ∧
    (∃ p q : Polynomial k, Polynomial.aeval A p = s ∧ Polynomial.aeval A q = n) ∧
    (∀ W : Submodule k V, (∀ x ∈ W, A x ∈ W) →
      (∀ x ∈ W, s x ∈ W) ∧ (∀ x ∈ W, n x ∈ W)) ∧
    (∀ s' n' : Module.End k V, IsJordanDecomposition A s' n' → s' = s ∧ n' = n)

/-- Over a characteristic-zero field ordinary and absolute semisimplicity agree. -/
def absolutely_semisimple_iff_type : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (s : Module.End k V), IsAbsolutelySemisimple s ↔ s.IsSemisimple

/-- The extended semisimple part is spanned by genuine eigenspaces. -/
def absolutely_semisimple_eigenspaces_type : Prop :=
  ∀ {k : Type u} [Field k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (s : Module.End k V), IsAbsolutelySemisimple s →
    (⨆ a : AlgebraicClosure k, Module.End.eigenspace (s.baseChange (AlgebraicClosure k)) a) = ⊤

end Specs.LieAlgebrasAndRepresentations.LinearJordan
