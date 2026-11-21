import MathGenome.Internal.Specs.D05.M03.HomDimension
import Mathlib.LinearAlgebra.Matrix.ToLin
import MathGenome.Internal.D05.M02.Dimension
import MathGenome.Internal.D05.M03.BasisExtension

/-! K05.03.hom_dimension: elementary maps, their basis, and its dimension. -/

namespace D05.M03.HomDimension

open scoped BigOperators
open Specs.D05.M03.HomDimension (elementaryMap)

theorem elementaryMap_apply_basis {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {n m : ℕ} (b : Module.Basis (Fin n) K V) (c : Module.Basis (Fin m) K W)
    (i : Fin m) (j k : Fin n) :
    elementaryMap b c i j (b k) = if j = k then c i else 0 := by
  by_cases h : j = k
  · subst k
    simp [elementaryMap, Module.Basis.coord_apply]
  · simp [elementaryMap, Module.Basis.coord_apply, h]

theorem elementary_map_apply : Specs.D05.M03.HomDimension.elementary_map_apply :=
  elementaryMap_apply_basis

theorem elementary_map_exists_unique :
    Specs.D05.M03.HomDimension.elementary_map_exists_unique := by
  intro K V W _ _ _ _ _ n m b c i j
  exact D05.M03.BasisExtension.exists_unique_linear_map b
    (fun k => if j = k then c i else 0)

theorem elementary_maps_basis : Specs.D05.M03.HomDimension.elementary_maps_basis := by
  intro K V W _ _ _ _ _ n m b c
  refine ⟨b.linearMap c, fun p => b.ext fun k => ?_⟩
  rw [Module.Basis.linearMap_apply_apply, elementaryMap_apply_basis]

theorem linear_map_expansion : Specs.D05.M03.HomDimension.linear_map_expansion := by
  intro K V W _ _ _ _ _ n m b c T
  apply b.ext
  intro k
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, elementaryMap_apply_basis]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact (c.sum_repr (T (b k))).symm

theorem zero_relation_iff : Specs.D05.M03.HomDimension.zero_relation_iff := by
  intro K V W _ _ _ _ _ n m b c a
  constructor
  · intro h i j
    have hj := congrArg (fun T : V →ₗ[K] W => T (b j)) h
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, elementaryMap_apply_basis,
      smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      LinearMap.zero_apply] at hj
    have hi := congrArg (fun w : W => c.repr w i) hj
    simpa [Finsupp.single_apply] using hi
  · intro h
    simp [h]

theorem hom_dimension : Specs.D05.M03.HomDimension.hom_dimension := by
  intro K V W _ _ _ _ _ n m b c
  let := (b.linearMap c).finiteDimensional_of_finite
  simpa using D05.M02.Dimension.dimension_eq_card_basis (b.linearMap c)

theorem empty_shape_zero : Specs.D05.M03.HomDimension.empty_shape_zero := by
  intro K V W _ _ _ _ _ n m b c h T
  rw [linear_map_expansion b c T]
  rcases h with rfl | rfl <;> simp

end D05.M03.HomDimension
