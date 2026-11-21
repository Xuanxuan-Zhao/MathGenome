import MathGenome.Internal.Specs.D07.Ch09.ProductIntersection
import MathGenome.Internal.D07.Ch08.IdealProduct
import MathGenome.Internal.D07.Ch09.Comaximal

/-! K07.09.product_intersection: comaximal products are intersections. -/

universe u v

namespace D07.Ch09.ProductIntersection

open Specs.D07.Ch09.ProductIntersection
open scoped BigOperators

theorem binaryProductIntersection : BinaryProductIntersection.{u} := by
  intro R _ I J h
  apply le_antisymm
  · exact D07.Ch08.IdealProduct.productLeIntersection R I J
      inferInstance inferInstance
  · intro x hx
    obtain ⟨i, hi, j, hj, hij⟩ :=
      (D07.Ch09.Comaximal.witnessCharacterization R I J).mp h
    have hxi : x * i ∈ I * J := by
      rw [mul_comm x i]
      exact Ideal.mul_mem_mul hi hx.2
    have hxj : x * j ∈ I * J := Ideal.mul_mem_mul hx.1 hj
    have heq : x * i + x * j = x := by rw [← mul_add, hij, mul_one]
    exact heq ▸ (I * J).add_mem hxi hxj

theorem finiteProductIntersection : FiniteProductIntersection.{u, v} := by
  intro R _ ι s I h
  apply Ideal.prod_eq_iInf_of_pairwise_isCoprime
  intro i hi j hj hij
  exact Ideal.isCoprime_iff_sup_eq.mpr (h i hi j hj hij)

theorem indexedProductIntersection : IndexedProductIntersection.{u, v} := by
  intro R _ ι _ I h
  simpa using finiteProductIntersection R ι Finset.univ I
    (fun i _ j _ hij => h i j hij)

end D07.Ch09.ProductIntersection
