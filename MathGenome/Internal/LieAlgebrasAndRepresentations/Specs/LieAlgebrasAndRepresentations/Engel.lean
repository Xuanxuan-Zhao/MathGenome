import Mathlib.Algebra.Lie.Engel
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.Fin

/-! LA-B01, notes/005/lie-algebras-and-representations.tex, lines 598–652.
The chapter assumes finite dimension; Engel's theorem uses an arbitrary field.
The coefficient in row i, column j is `b.repr (x (b j)) i`, so vanishing
when j ≤ i means strictly upper triangular, including the diagonal.
-/

universe u v
namespace Specs.LieAlgebrasAndRepresentations.Engel

attribute [local instance 100] LieRing.ofAssociativeRing

def common_kernel_type : Prop :=
  ∀ {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V]
    (A : LieSubalgebra k (Module.End k V))
    (_hA : ∀ x : A, IsNilpotent (x : Module.End k V)),
    ∃ v : V, v ≠ 0 ∧ ∀ x : A, (x : Module.End k V) v = 0

def strict_upper_triangular_basis_type : Prop :=
  ∀ {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V]
    (A : LieSubalgebra k (Module.End k V))
    (_hA : ∀ x : A, IsNilpotent (x : Module.End k V)),
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V),
      ∀ (x : A) (i j : Fin n), j ≤ i → b.repr ((x : Module.End k V) (b j)) i = 0

def engel_criterion_type : Prop :=
  ∀ (k : Type u) [Field k] (G : Type v) [LieRing G] [LieAlgebra k G]
    [FiniteDimensional k G],
    LieRing.IsNilpotent G ↔ ∀ x : G, IsNilpotent (LieAlgebra.ad k G x)

end Specs.LieAlgebrasAndRepresentations.Engel
