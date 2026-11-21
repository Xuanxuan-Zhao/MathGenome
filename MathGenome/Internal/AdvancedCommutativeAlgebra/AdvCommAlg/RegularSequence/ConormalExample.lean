import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.AssociatedGraded
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Conormal
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.ConormalExample

namespace AdvCommAlg.RegularSequence.ConormalExample
noncomputable section
universe u
open TensorProduct
open Core
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem regular_relations_basis : Specs.regularRelationsBasis.{u} := by
  intro P _ f hf
  exact AssociatedGraded.conormalBasis f hf

variable (k : Type u) [Field k]

lemma extension_kernel : (extension k).ker = squareIdeal k := by
  ext p
  change Ideal.Quotient.mk (squareIdeal k) p = 0 ↔ p ∈ squareIdeal k
  exact Ideal.Quotient.eq_zero_iff_mem

lemma X_pow_not_mem (n m : ℕ) (h : n < m) :
    (Polynomial.X : Polynomial k) ^ n ∉ Ideal.span {Polynomial.X ^ m} := by
  rw [Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  intro hd
  have hz : (1 : k) = 0 := by
    simpa only [Polynomial.coeff_X_pow_self] using hd n h
  exact one_ne_zero hz

lemma xbar_nonzero : xbar k ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  simpa only [pow_one] using X_pow_not_mem k 1 2 (by decide)

lemma relation_class_nonzero : relationClass k ≠ 0 := by
  rw [Ne, Algebra.Extension.Cotangent.mk_eq_zero_iff]
  change (Polynomial.X : Polynomial k) ^ 2 ∉
    (extension k).ker ^ 2
  simp only [extension_kernel, squareIdeal, Ideal.span_singleton_pow]
  simpa only [← pow_mul] using X_pow_not_mem k 2 4 (by decide)

lemma xbar_relation_class_nonzero : xbar k • relationClass k ≠ 0 := by
  change algebraMap (Polynomial k) (Dual k) Polynomial.X • relationClass k ≠ 0
  rw [IsScalarTower.algebraMap_smul, ← map_smul,
    Ne, Algebra.Extension.Cotangent.mk_eq_zero_iff]
  change ((Polynomial.X : Polynomial k) * (Polynomial.X ^ 2 : Polynomial k) : Polynomial k) ∉
    (extension k).ker ^ 2
  simp only [extension_kernel, squareIdeal, Ideal.span_singleton_pow]
  change ((Polynomial.X : Polynomial k) * (Polynomial.X ^ 2 : Polynomial k) : Polynomial k) ∉
    Ideal.span {((Polynomial.X : Polynomial k) ^ 2) ^ 2}
  simpa only [← pow_succ', ← pow_mul] using X_pow_not_mem k 3 4 (by decide)

lemma square_relation_regular :
    RingTheory.Sequence.IsRegular (Polynomial k) [(Polynomial.X : Polynomial k) ^ 2] := by
  constructor
  · apply (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr
    intro a b hab
    exact mul_left_cancel₀ (pow_ne_zero 2 Polynomial.X_ne_zero) hab
  · change (⊤ : Ideal (Polynomial k)) ≠
      Ideal.ofList [Polynomial.X ^ 2] • (⊤ : Ideal (Polynomial k))
    rw [Ideal.ofList_singleton, Ideal.smul_eq_mul, Ideal.mul_top]
    intro ht
    have hm : (1 : Polynomial k) ∈ Ideal.span {Polynomial.X ^ 2} :=
      ht ▸ (Submodule.mem_top : (1 : Polynomial k) ∈ (⊤ : Ideal (Polynomial k)))
    exact X_pow_not_mem k 0 2 (by decide) (by simpa only [pow_zero] using hm)

lemma xbar_square : (xbar k) ^ 2 = 0 := by
  rw [xbar, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

lemma conormal_relation_image :
    conormalArrow k (relationClass k) = (2 * xbar k) • dX k := by
  change (extension k).cotangentComplex (Algebra.Extension.Cotangent.mk (relation k)) = _
  rw [Algebra.Extension.cotangentComplex_mk]
  change 1 ⊗ₜ[Polynomial k]
    KaehlerDifferential.D k (Polynomial k) (Polynomial.X ^ 2) = _
  rw [pow_two, Derivation.leibniz, TensorProduct.tmul_add]
  simp only [TensorProduct.tmul_smul]
  rw [← IsScalarTower.algebraMap_smul (Dual k) (Polynomial.X : Polynomial k)]
  change xbar k • dX k + xbar k • dX k = (2 * xbar k) • dX k
  rw [two_mul]
  exact (add_smul (xbar k) (xbar k) (dX k)).symm

lemma conormal_xbar_relation_image :
    conormalArrow k (xbar k • relationClass k) = 0 := by
  rw [map_smul, conormal_relation_image]
  rw [← mul_smul (xbar k) (2 * xbar k) (dX k)]
  have hz : xbar k * (2 * xbar k) = 0 := by
    rw [mul_left_comm, ← pow_two, xbar_square, mul_zero]
  rw [hz]
  exact zero_smul (Dual k) (dX k)

lemma conormal_not_injective : ¬ Function.Injective (conormalArrow k) := by
  intro hi
  exact xbar_relation_class_nonzero k
    (hi ((conormal_xbar_relation_image k).trans (map_zero _).symm))

theorem dual_numbers_example : Specs.dualNumbersExample.{u} := by
  intro k _
  refine ⟨square_relation_regular k, xbar_nonzero k, relation_class_nonzero k,
    xbar_relation_class_nonzero k, conormal_relation_image k,
    conormal_xbar_relation_image k, conormal_not_injective k, ?_⟩
  intro hs
  exact conormal_not_injective k hs.1

end
end AdvCommAlg.RegularSequence.ConormalExample
