import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Algebra

namespace Alg01SymmetricWitt.Symmetric.Algebra

open scoped DirectSum

abbrev commutatorIdeal := Specs.Alg01SymmetricWitt.Symmetric.Algebra.commutatorIdeal
abbrev degreeMap := Specs.Alg01SymmetricWitt.Symmetric.Algebra.degreeMap
abbrev degree := Specs.Alg01SymmetricWitt.Symmetric.Algebra.degree
abbrev pureProduct := Specs.Alg01SymmetricWitt.Symmetric.Algebra.pureProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The canonical tensor-to-symmetric map presents the quotient by the commutator ideal. -/
theorem quotientKernel :
    Function.Surjective (SymmetricAlgebra.algHom R M) ∧
      TwoSidedIdeal.ker (SymmetricAlgebra.algHom R M) = commutatorIdeal R M := by
  refine ⟨SymmetricAlgebra.algHom_surjective R M, ?_⟩
  change TwoSidedIdeal.ker (TensorAlgebra.symRingCon R M).mk' = _
  calc
    _ = TwoSidedIdeal.ofRingCon (TensorAlgebra.symRingCon R M) :=
      TwoSidedIdeal.ker_ringCon_mk' _
    _ = commutatorIdeal R M := by
      apply le_antisymm
      · rw [TwoSidedIdeal.ringCon_le_iff]
        change TensorAlgebra.symRingCon R M ≤ (commutatorIdeal R M).ringCon
        rw [TensorAlgebra.symRingCon, RingCon.ringConGen_le]
        intro a b hab
        cases hab with
        | mul_comm x y =>
          exact (TwoSidedIdeal.rel_iff _ _ _).2 (TwoSidedIdeal.subset_span ⟨(x, y), rfl⟩)
      · apply TwoSidedIdeal.span_le.mpr
        rintro _ ⟨⟨x, y⟩, rfl⟩
        apply (TwoSidedIdeal.rel_iff _ _ _).1
        exact RingCon.le_ringConGen _ _ (TensorAlgebra.SymRel.mul_comm x y)

/-- The tensor algebra is the direct sum of tensor powers with concatenation. -/
theorem tensorPresentation :
    ∃ e : (⨁ n, TensorPower R n M) ≃ₐ[R] TensorAlgebra R M,
      ∀ (n : ℕ) (x : Fin n → M),
        e (DirectSum.of (fun n => TensorPower R n M) n (PiTensorProduct.tprod R x)) =
          TensorAlgebra.tprod R M n x := by
  refine ⟨TensorAlgebra.equivDirectSum.symm, fun n x => ?_⟩
  exact TensorAlgebra.ofDirectSum_of_tprod x

/-- A pure product is the product of its degree-one factors in the symmetric algebra. -/
theorem pureProductCoe (n : ℕ) (x : Fin n → M) :
    ((pureProduct R M n x : degree R M n) : SymmetricAlgebra R M) =
      ∏ i, SymmetricAlgebra.ι R M (x i) := by
  change SymmetricAlgebra.algHom R M
    (TensorPower.toTensorAlgebra (PiTensorProduct.tprod R x)) = _
  rw [TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply, map_list_prod,
    List.map_ofFn, List.prod_ofFn]
  rfl

end Alg01SymmetricWitt.Symmetric.Algebra
