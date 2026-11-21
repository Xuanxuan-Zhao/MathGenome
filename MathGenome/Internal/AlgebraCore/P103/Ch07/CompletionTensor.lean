import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.CompletionTensor
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Finiteness.Small

/-! Theorem 7.4, tensor comparison. The library proof uses a finite free cover,
right exactness of tensor product, and exactness of completion. Finite modules
in a different universe are transported along a linear equivalence with a small
model; naturality ensures that this proves bijectivity of the specified map.
-/

universe u v w

namespace P103.Ch07.CompletionTensor

open P103.Adic TensorProduct
open P103.Specs.Ch07.CompletionTensor

noncomputable def comparison : comparisonType.{u, v} := comparisonValue

theorem comparison_tmul : comparison_tmulType.{u, v} := by
  intro R _ I M _ _ r m
  rfl

theorem comparison_bijective : comparison_bijectiveType.{u, v} := by
  intro R _ _ I M _ _ _
  let : Small.{u} M := Module.Finite.small R M
  let e := Shrink.linearEquiv.{u} R M
  let eT := TensorProduct.congr (LinearEquiv.refl R (Completion I R)) e
  let eC := AdicCompletion.congr I e
  have hs := AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I
    (Shrink.{u} M)
  have hn (x : Completion I R ⊗[R] Shrink.{u} M) :
      comparisonValue R I M (eT x) = eC (AdicCompletion.ofTensorProduct I _ x) := by
    exact (DFunLike.congr_fun (AdicCompletion.ofTensorProduct_naturality I e.toLinearMap) x).symm
  refine ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨x, rfl⟩ := eT.surjective x
    obtain ⟨y, rfl⟩ := eT.surjective y
    apply congrArg eT
    apply hs.injective
    apply eC.injective
    simpa only [← hn] using hxy
  · intro y
    obtain ⟨x, hx⟩ := hs.surjective (eC.symm y)
    refine ⟨eT x, ?_⟩
    rw [hn, hx, eC.apply_symm_apply]

theorem comparison_isomorphism : comparison_isomorphismType.{u, v} := by
  intro R _ _ I M _ _ _
  exact ⟨LinearEquiv.ofBijective (comparisonValue R I M)
    (comparison_bijective R I M), rfl⟩

theorem comparison_natural : comparison_naturalType.{u, v, w} := by
  intro R _ I M _ _ N _ _ f
  exact AdicCompletion.ofTensorProduct_naturality I f

noncomputable def finiteFreeCompletion : finiteFreeCompletionType.{u} :=
  finiteFreeCompletionValue

theorem finiteFreeCompletion_coordinate : finiteFreeCompletion_coordinateType.{u} := by
  intro R _ I n x j
  simp only [finiteFreeCompletionValue, AdicCompletion.piEquivFin_apply]
  rfl

theorem finiteFreeComparison : finiteFreeComparisonType.{u} := by
  intro R _ I n
  apply AlgebraTensorModule.ext
  intro r m
  funext j
  simp [finiteFreeCompletionValue, AdicCompletion.piEquivFin_apply,
    AdicCompletion.pi, comparisonValue, AdicCompletion.map_of, Algebra.smul_def,
    AdicCompletion.algebraMap_apply, mul_comm]

end P103.Ch07.CompletionTensor
