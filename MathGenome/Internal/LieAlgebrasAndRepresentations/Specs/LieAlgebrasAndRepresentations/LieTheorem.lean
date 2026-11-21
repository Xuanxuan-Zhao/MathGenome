import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! LA-B02, source lines 688–712, with the finite-dimensional chapter
convention at lines 600–603. Representations are left Lie modules. No
faithfulness or nonzero-action assumption is imposed. -/
universe u v w
namespace Specs.LieAlgebrasAndRepresentations.LieTheorem

/-- A common eigenvector, with its linear weight. -/
def common_eigenvector_type : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {G : Type v} [LieRing G] [LieAlgebra k G] [Module.Finite k G]
    [LieAlgebra.IsSolvable G]
    {V : Type w} [AddCommGroup V] [Module k V]
    [LieRingModule G V] [LieModule k G V] [Module.Finite k V] [Nontrivial V],
    ∃ (χ : Module.Dual k G) (v : V), v ≠ 0 ∧ ∀ x : G, ⁅x, v⁆ = χ x • v

/-- All action matrices in one finite ordered basis are upper triangular.
The coefficient in row i, column j vanishes whenever j < i. This also
allows the empty basis of the zero module. -/
def common_upper_triangular_basis_type : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {G : Type v} [LieRing G] [LieAlgebra k G] [Module.Finite k G]
    [LieAlgebra.IsSolvable G]
    {V : Type w} [AddCommGroup V] [Module k V]
    [LieRingModule G V] [LieModule k G V] [Module.Finite k V],
    ∃ (n : ℕ) (e : Module.Basis (Fin n) k V),
      ∀ (x : G) (i j : Fin n), j < i → e.repr ⁅x, e j⁆ i = 0

/-- Every nonzero irreducible representation has dimension one. -/
def irreducible_finrank_one_type : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {G : Type v} [LieRing G] [LieAlgebra k G] [Module.Finite k G]
    [LieAlgebra.IsSolvable G]
    {V : Type w} [AddCommGroup V] [Module k V]
    [LieRingModule G V] [LieModule k G V] [Module.Finite k V] [Nontrivial V]
    [LieModule.IsIrreducible k G V], Module.finrank k V = 1

end Specs.LieAlgebrasAndRepresentations.LieTheorem
