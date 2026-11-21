import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent statements for K05.15.tensor_intersections, paper.tex:2793–2798.
Each tensor product of subspaces is identified with its image under the tensor
of the two actual subtype inclusions, inside the common ambient tensor product.
Both ambient spaces are finite dimensional, as in the source; zero spaces and
all characteristics are included. No adapted basis or decomposition is assumed.
-/
namespace Specs.D05.M15.TensorIntersections

open scoped TensorProduct

/-- The natural map justifying the subspace identification is injective. -/
def tensor_subspace_injective : Prop :=
  ∀ {K V Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup Z] [Module K Z] [FiniteDimensional K V] [FiniteDimensional K Z]
    (U : Submodule K V) (W : Submodule K Z),
    Function.Injective (TensorProduct.map U.subtype W.subtype)

/-- Equality of the tensor subspaces in `V ⊗ Z`, with intersections in both factors. -/
def tensor_intersection : Prop :=
  ∀ {K V Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup Z] [Module K Z] [FiniteDimensional K V] [FiniteDimensional K Z]
    (U U' : Submodule K V) (W W' : Submodule K Z),
    LinearMap.range (TensorProduct.map U.subtype W.subtype) ⊓
      LinearMap.range (TensorProduct.map U'.subtype W'.subtype) =
    LinearMap.range (TensorProduct.map (U ⊓ U').subtype (W ⊓ W').subtype)

end Specs.D05.M15.TensorIntersections
