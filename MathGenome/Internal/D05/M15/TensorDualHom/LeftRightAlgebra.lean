import MathGenome.Internal.Specs.D05.M15.TensorDualHom.LeftRightAlgebra
import MathGenome.Internal.D05.M03.HomDimension
import Mathlib.Algebra.Azumaya.Matrix
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finite

/-! The canonical left/right action of the finite endomorphism algebra.
The matrix inverse in Mathlib is valid even for an empty matrix index type;
we use its two inverse identities directly, without a faithful-action or
positive-dimension hypothesis from the Azumaya class.
-/

namespace D05.M15.TensorDualHom.LeftRightAlgebra

open scoped TensorProduct
open MulOpposite
open Specs.D05.M03.HomDimension (elementaryMap)

noncomputable abbrev oppositeAction (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] :=
  Specs.D05.M15.TensorDualHom.LeftRightAlgebra.oppositeAction K V

noncomputable abbrev leftRight (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] :=
  Specs.D05.M15.TensorDualHom.LeftRightAlgebra.leftRight K V

theorem leftRight_tmul : Specs.D05.M15.TensorDualHom.LeftRightAlgebra.leftRight_tmul := by
  intro K V _ _ _ a b X
  exact AlgHom.mulLeftRight_apply K (Module.End K V) a (op b) X

theorem oppositeAction_tmul :
    Specs.D05.M15.TensorDualHom.LeftRightAlgebra.oppositeAction_tmul := by
  intro K V _ _ _ a b X
  exact AlgHom.mulLeftRight_apply K (Module.End K V) a (op b) X

/-- Transport bijectivity through a change of algebra, without requiring
either algebra to have a faithful scalar action. -/
theorem mulLeftRight_bijective_of_equiv {K A B : Type*} [Field K] [Ring A] [Ring B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B)
    (h : Function.Bijective (AlgHom.mulLeftRight K A)) :
    Function.Bijective (AlgHom.mulLeftRight K B) := by
  apply (Function.Bijective.of_comp_iff (AlgHom.mulLeftRight K B)
    (Algebra.TensorProduct.congr e e.op).bijective).mp
  change Function.Bijective
    ((AlgHom.mulLeftRight K B).comp (Algebra.TensorProduct.congr e e.op).toAlgHom)
  rw [IsAzumaya.mulLeftRight_comp_congr]
  exact (e.toLinearEquiv.conjAlgEquiv K).bijective.comp h

/-- The explicit matrix-unit inverse works for every finite basis, including
the basis indexed by `Fin 0`. -/
theorem oppositeAction_bijective {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] :
    Function.Bijective (oppositeAction K V) := by
  classical
  let b := Module.finBasis K V
  apply mulLeftRight_bijective_of_equiv (LinearMap.toMatrixAlgEquiv b).symm
  exact Function.bijective_iff_has_inverse.mpr
    ⟨AlgHom.mulLeftRightMatrix_inv K (Fin (Module.finrank K V)),
      DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.inv_comp K _),
      DFunLike.congr_fun (AlgHom.mulLeftRightMatrix.comp_inv K _)⟩

theorem algebra_isomorphism :
    Specs.D05.M15.TensorDualHom.LeftRightAlgebra.algebra_isomorphism := by
  intro K V _ _ _ _
  exact ⟨AlgEquiv.ofBijective (oppositeAction K V) oppositeAction_bijective, rfl⟩

theorem linear_isomorphism :
    Specs.D05.M15.TensorDualHom.LeftRightAlgebra.linear_isomorphism := by
  intro K V _ _ _ _
  refine ⟨(TensorProduct.congr (LinearEquiv.refl K (Module.End K V))
    (opLinearEquiv K)).trans
      (AlgEquiv.ofBijective (oppositeAction K V) oppositeAction_bijective).toLinearEquiv,
    rfl⟩

theorem composition_rule :
    Specs.D05.M15.TensorDualHom.LeftRightAlgebra.composition_rule := by
  intro K V _ _ _ a b c d
  apply LinearMap.ext
  intro X
  change leftRight K V (a ⊗ₜ[K] b) (leftRight K V (c ⊗ₜ[K] d) X) =
    leftRight K V ((a * c) ⊗ₜ[K] (d * b)) X
  rw [leftRight_tmul, leftRight_tmul, leftRight_tmul]
  simp only [mul_assoc]

theorem opposite_tensor_product :
    Specs.D05.M15.TensorDualHom.LeftRightAlgebra.opposite_tensor_product := by
  intro K V _ _ _ a b c d
  simp only [Algebra.TensorProduct.tmul_mul_tmul, op_mul]

/-- Multiplication of the upstream elementary endomorphisms. -/
theorem elementaryMap_mul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (e : Module.Basis (Fin n) K V) (i j k l : Fin n) :
    elementaryMap e e i j * elementaryMap e e k l =
      if j = k then elementaryMap e e i l else 0 := by
  classical
  apply e.ext
  intro a
  by_cases hj : j = k <;> by_cases hl : l = a <;>
    simp [Module.End.mul_apply, D05.M03.HomDimension.elementaryMap_apply_basis, hj, hl]

theorem matrix_unit_action :
    Specs.D05.M15.TensorDualHom.LeftRightAlgebra.matrix_unit_action := by
  intro K V _ _ _ n e i j a b k l
  classical
  rw [leftRight_tmul, elementaryMap_mul]
  by_cases h : j = a
  · simp only [h, ↓reduceIte, elementaryMap_mul, true_and]
  · simp only [h, ↓reduceIte, zero_mul, false_and]

theorem zero_dimension : Specs.D05.M15.TensorDualHom.LeftRightAlgebra.zero_dimension := by
  intro K V _ _ _ _ h
  have : Subsingleton V := Module.finrank_zero_iff.mp h
  exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem matrix_unit_basis :
    Specs.D05.M15.TensorDualHom.LeftRightAlgebra.matrix_unit_basis := by
  intro K V _ _ _ n e
  classical
  obtain ⟨B, hB⟩ := D05.M03.HomDimension.elementary_maps_basis e e
  refine ⟨B.linearMap B, ?_⟩
  intro i j k l
  apply B.ext
  intro p
  rw [Module.Basis.linearMap_apply_apply, hB, hB, matrix_unit_action]
  by_cases h : (j, k) = p
  · subst p
    simp
  · have h' : ¬ (j = p.1 ∧ p.2 = k) := by
      rintro ⟨rfl, hk⟩
      exact h (Prod.ext rfl hk.symm)
    simp [h, h']

theorem ordinary_not_multiplicative :
    Specs.D05.M15.TensorDualHom.LeftRightAlgebra.ordinary_not_multiplicative := by
  intro K V _ _ _ n e i j hij h
  classical
  have hc := h (1 ⊗ₜ[K] elementaryMap e e i i) (1 ⊗ₜ[K] elementaryMap e e i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, elementaryMap_mul,
    ite_eq_left (show i = i from rfl)] at hc
  have hx := LinearMap.congr_fun hc (1 : Module.End K V)
  change leftRight K V (1 ⊗ₜ[K] elementaryMap e e i j) 1 =
    leftRight K V (1 ⊗ₜ[K] elementaryMap e e i i)
      (leftRight K V (1 ⊗ₜ[K] elementaryMap e e i j) 1) at hx
  rw [leftRight_tmul, leftRight_tmul] at hx
  simp only [one_mul, elementaryMap_mul, Ne.symm hij, ↓reduceIte] at hx
  have hv := LinearMap.congr_fun hx (e j)
  simp only [D05.M03.HomDimension.elementaryMap_apply_basis, ↓reduceIte,
    LinearMap.zero_apply] at hv
  exact e.ne_zero i hv

end D05.M15.TensorDualHom.LeftRightAlgebra
