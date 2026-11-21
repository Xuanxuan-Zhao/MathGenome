import MathGenome.Internal.Specs.D05.M02.Dimension

/-!
Independent statement for K05.02.subspace_dimension (paper.tex:503–509).

`U : Submodule K V` is a vector subspace with the inherited operations.
The source's equality `U = V` is expressed by `U = ⊤` in the ambient
submodule lattice. Only the ambient space is assumed finite-dimensional;
finite dimensionality and an actual finite indexed basis of `U` are conclusions.
The dimension parameter `n` is arbitrary, including zero.
-/

namespace Specs.D05.M02.SubspaceDimension

/-- A subspace has a finite basis, dimension at most that of its ambient
space, and equal dimension exactly when it is the whole space. -/
def subspace_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Submodule K V) (n : ℕ),
    Module.finrank K V = n →
      FiniteDimensional K U ∧
      Nonempty (Module.Basis (Fin (Module.finrank K U)) K U) ∧
      Module.finrank K U ≤ n ∧
      (Module.finrank K U = n ↔ U = ⊤)

end Specs.D05.M02.SubspaceDimension
