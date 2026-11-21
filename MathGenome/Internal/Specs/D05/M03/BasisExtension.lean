import MathGenome.Internal.Specs.D05.M02.Basis
import MathGenome.Internal.Specs.D05.M03.LinearMap

/-!
Independent statements for K05.03.basis_extension (paper.tex:539–545).
The given basis and the arbitrary target family use the same index type.
Neither space nor the index type is assumed finite or nonempty. Coordinates
are the canonical finitely supported coordinates of that basis.
-/

namespace Specs.D05.M03.BasisExtension

/-- Every assignment of values to a given basis extends to exactly one linear map. -/
def exists_unique_linear_map : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (b : Module.Basis I K V) (w : I → W),
    ∃! T : V →ₗ[K] W, ∀ i, T (b i) = w i

/-- Any map with the prescribed values has the paper's finite-support formula. -/
def linear_map_eq_sum : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (b : Module.Basis I K V) (w : I → W)
    (T : V →ₗ[K] W), (∀ i, T (b i) = w i) →
    ∀ x : V, T x = ∑ i ∈ (b.repr x).support, b.repr x i • w i

end Specs.D05.M03.BasisExtension
