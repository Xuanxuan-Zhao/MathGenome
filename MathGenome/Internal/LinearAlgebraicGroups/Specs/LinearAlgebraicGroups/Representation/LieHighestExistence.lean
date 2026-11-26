import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.Dual.Defs

universe u v w t i j

namespace Specs.LinearAlgebraicGroups.Representation.LieHighestExistence

/-- The h operator of an actual sl₂ triple is spanned by its integral
eigenspaces over the given characteristic-zero field. -/
def RankOneDiagonalization : Prop :=
  ∀ (k : Type u) (L : Type v) (V : Type w)
    [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [LieRingModule L V] [LieModule k L V]
    {h e f : L}, IsSl2Triple h e f →
      (⨆ n : ℤ, (LieModule.toEnd k L V h).eigenspace (n : k)) = ⊤

/-- A spanning family of coroot operators and a toral grading element
yield a highest vector for all the specified positive vectors at once. -/
def HighestWeightExistence : Prop :=
  ∀ (k : Type u) (L : Type v) (V : Type w) (H : Type t)
    [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    [LieRingModule L V] [LieModule k L V]
    [LieRing H] [LieAlgebra k H] [IsLieAbelian H]
    (inclusion : H →ₗ⁅k⁆ L), Function.Injective inclusion →
    ∀ (ι : Type i) [Finite ι] (coroot : ι → H),
      Submodule.span k (Set.range coroot) = ⊤ →
      (∀ l, ∃ e f : L, IsSl2Triple (inclusion (coroot l)) e f) →
      ∀ (h₀ : H) (J : Type j) (x : J → L) (degree : J → ℤ),
        (∀ a, 0 < degree a ∧ ⁅inclusion h₀, x a⁆ = (degree a : k) • x a) →
        ∃ (lam : Module.Dual k H) (v : V), v ≠ 0 ∧
          (∀ h : H, ⁅inclusion h, v⁆ = lam h • v) ∧
          ∀ a, ⁅x a, v⁆ = 0

end Specs.LinearAlgebraicGroups.Representation.LieHighestExistence
