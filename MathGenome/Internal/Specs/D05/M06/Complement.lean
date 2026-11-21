import MathGenome.Internal.Specs.D05.M06.DirectSum
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Prod

/-!
Independent statements for K05.06.complement (paper.tex:973–979).

The ambient space is finite-dimensional, including dimension zero, and the
subspace is arbitrary. Internal direct sums use the prerequisite's unique
component expansion, rather than an assumed decomposition certificate. The
external product comparison specifies the values of the actual addition map.
The final statement records the two different complements in the paper, with
`K × K` as the coordinate plane and `(1, 0)`, `(0, 1)` its standard vectors.
There is no inner product, chosen operator, or characteristic restriction.
-/

namespace Specs.D05.M06.Complement

/-- A complement spans the ambient space together with `U` and meets it in zero. -/
def exists_complement_sup_inf : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Submodule K V),
    ∃ W : Submodule K V, U ⊔ W = ⊤ ∧ U ⊓ W = ⊥

/-- The existence theorem in the paper's internal-direct-sum convention. -/
def exists_complement : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Submodule K V),
    ∃ W : Submodule K V,
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then W else U)

/-- The same complement gives an isomorphism by adding the included components. -/
def exists_complement_equiv : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (U : Submodule K V),
    ∃ W : Submodule K V,
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then W else U) ∧
      ∃ e : (U × W) ≃ₗ[K] V, ∀ (u : U) (w : W), e (u, w) = (u : V) + (w : V)

/-- Both lines specified in the paper complement the first coordinate line,
and they are distinct, over every field (including characteristic two). -/
def coordinate_complements : Prop :=
  ∀ (K : Type*) [Field K],
    let U := Submodule.span K ({(1, 0)} : Set (K × K))
    let W₀ := Submodule.span K ({(0, 1)} : Set (K × K))
    let W₁ := Submodule.span K ({(1, 0) + (0, 1)} : Set (K × K))
    Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then W₀ else U) ∧
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then W₁ else U) ∧ W₀ ≠ W₁

end Specs.D05.M06.Complement
