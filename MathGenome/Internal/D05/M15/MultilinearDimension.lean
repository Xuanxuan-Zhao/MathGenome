import MathGenome.Internal.Specs.D05.M15.MultilinearDimension
import MathGenome.Internal.D05.M02.Dimension
import MathGenome.Internal.D05.M03.BasisExtension
import MathGenome.Internal.D05.M15.Multilinear
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! K05.15.multilinear_dimension: basis-tuple coordinates, elementary maps,
and the dimension formula, including nullary and zero-input cases. -/

namespace D05.M15.MultilinearDimension

open scoped BigOperators

theorem basis_values_determine :
    Specs.D05.M15.MultilinearDimension.basis_values_determine := by
  intro K I V W κ _ _ _ _ _ _ _ e B C h
  exact Module.Basis.ext_multilinear e h

theorem basis_expansion : Specs.D05.M15.MultilinearDimension.basis_expansion := by
  intro K I V W κ _ _ _ _ _ _ _ e B v
  classical
  have h := D05.M15.Multilinear.map_finite_combination B
    (fun i => (Finset.univ : Finset (κ i)))
    (fun i j => (e i).repr (v i) j) (fun i j => e i j)
  simpa only [Module.Basis.sum_repr, Fintype.piFinset_univ] using h

open scoped Classical in
/-- The product of coordinate functionals is the delta function on basis tuples.
The proof also covers the empty tuple, for which the product is one. -/
theorem coordinate_product_basis {K I : Type*} {V : I → Type*} {κ : I → Type*}
    [Field K] [Fintype I] [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (e : ∀ i, Module.Basis (κ i) K (V i)) (r s : ∀ i, κ i) :
    (∏ i, (e i).repr (e i (s i)) (r i)) = if s = r then 1 else 0 := by
  classical
  by_cases h : s = r
  · subst s
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi])

/-- A finite sum of products of input coordinates constructs the extension;
the delta identity gives its prescribed values. -/
theorem exists_unique_multilinear :
    Specs.D05.M15.MultilinearDimension.exists_unique_multilinear := by
  intro K I V W κ _ _ _ _ _ _ _ e w
  classical
  let B : MultilinearMap K V W :=
    ∑ r : ∀ i, κ i,
      (MultilinearMap.mkPiRing K I (w r)).compLinearMap (fun i => (e i).coord (r i))
  have hB (s : ∀ i, κ i) : B (fun i => e i (s i)) = w s := by
    simp only [B, sum_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiRing_apply, Module.Basis.coord_apply]
    simp_rw [coordinate_product_basis]
    simp
  refine ⟨B, hB, ?_⟩
  intro C hC
  exact basis_values_determine e C B (fun r => (hC r).trans (hB r).symm)

theorem elementary_basis : Specs.D05.M15.MultilinearDimension.elementary_basis := by
  intro K I L V W κ _ _ _ _ _ _ _ _ e f
  classical
  refine ⟨Basis.multilinearMap e f, ?_, ?_⟩
  · intro r l v
    exact Basis.multilinearMap_apply_apply e f (r, l) v
  · intro r s l
    rw [Basis.multilinearMap_apply_apply, coordinate_product_basis]
    split_ifs <;> simp

theorem dimension_formula : Specs.D05.M15.MultilinearDimension.dimension_formula := by
  intro K I V W _ _ _ _ _ _ _ _
  classical
  let b := Basis.multilinearMap (fun i => Module.finBasis K (V i)) (Module.finBasis K W)
  refine ⟨b.finiteDimensional_of_finite, ?_⟩
  rw [Module.finrank_eq_card_basis b]
  simp [Fintype.card_prod, Fintype.card_pi, Nat.mul_comm]

theorem nullary_dimension : Specs.D05.M15.MultilinearDimension.nullary_dimension := by
  intro K I V W _ _ _ _ _ _ _
  obtain ⟨E, _, _⟩ := D05.M15.Multilinear.nullary_equivalence (K := K) (V := V) (W := W)
  exact ⟨E.finiteDimensional, E.symm.finrank_eq⟩

theorem zero_input : Specs.D05.M15.MultilinearDimension.zero_input := by
  intro K I V W _ _ _ _ _ _ _ _ i hi
  have hzero (B : MultilinearMap K V W) (v : ∀ j, V j) : B v = 0 :=
    D05.M15.Multilinear.map_coord_zero B v i (hi (v i))
  have hdim : Module.finrank K (V i) = 0 :=
    D05.M02.Dimension.dimension_zero_iff_zero_space.mpr hi
  have hprod : Module.finrank K W * ∏ j, Module.finrank K (V j) = 0 := by
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hdim, mul_zero]
  exact ⟨hzero, (dimension_formula (K := K) (V := V) (W := W)).2.trans hprod, hprod⟩

end D05.M15.MultilinearDimension
