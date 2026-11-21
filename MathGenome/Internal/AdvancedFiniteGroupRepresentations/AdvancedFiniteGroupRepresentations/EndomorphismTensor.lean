import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.TensorActions
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.EndomorphismTensor
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
universe u
namespace AdvancedFiniteGroupRepresentations
open Module

abbrev EndomorphismTensor := @Specs.AdvancedFiniteGroupRepresentations.EndomorphismTensor
abbrev endomorphismTensorMap := @Specs.AdvancedFiniteGroupRepresentations.endomorphismTensorMap
abbrev IsInvariantEndomorphismTensor :=
  @Specs.AdvancedFiniteGroupRepresentations.IsInvariantEndomorphismTensor

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

@[simp] theorem endomorphismTensor_pure (n : ℕ) (T : Fin n → Module.End ℂ V) :
    endomorphismTensorMap V n (pureTensor (Module.End ℂ V) n T) = PiTensorProduct.map T := by
  simp [endomorphismTensorMap, Specs.AdvancedFiniteGroupRepresentations.endomorphismTensorMap,
    PiTensorProduct.liftAlgHom, pureTensor, Specs.AdvancedFiniteGroupRepresentations.pureTensor]

@[simp] theorem endomorphismTensor_apply_pure (n : ℕ) (T : Fin n → Module.End ℂ V)
    (v : Fin n → V) :
    endomorphismTensorMap V n (pureTensor (Module.End ℂ V) n T) (pureTensor V n v) =
      pureTensor V n (fun i => T i (v i)) := by
  rw [endomorphismTensor_pure]
  exact PiTensorProduct.map_tprod T v

/-- Matrix units tensor to matrix units in the tensor basis. Empty index
sets and the empty family require no separate positivity assumption. -/
theorem endomorphismTensor_matrix_unit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℂ V) (n : ℕ) (p : Fin n → ι × ι) :
    endomorphismTensorMap V n ((Basis.piTensorProduct (fun _ : Fin n => b.end)) p) =
      (Basis.piTensorProduct (fun _ : Fin n => b)).end
        ((fun i => (p i).1), (fun i => (p i).2)) := by
  classical
  rw [Basis.piTensorProduct_apply]
  change endomorphismTensorMap V n (pureTensor (Module.End ℂ V) n _) = _
  rw [endomorphismTensor_pure]
  apply (Basis.piTensorProduct (fun _ : Fin n => b)).ext
  intro k
  rw [Basis.end_apply_apply]
  simp only [Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, Basis.end_apply_apply]
  by_cases h : (fun i => (p i).2) = k
  · subst k
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact (PiTensorProduct.tprod ℂ).map_coord_zero i (ite_eq_right hi)

private def wordPairEquiv (ι : Type*) (n : ℕ) :
    (Fin n → ι × ι) ≃ (Fin n → ι) × (Fin n → ι) where
  toFun p := (fun i => (p i).1, fun i => (p i).2)
  invFun p i := (p.1 i, p.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

theorem endomorphismTensor_bijective [FiniteDimensional ℂ V] (n : ℕ) :
    Function.Bijective (endomorphismTensorMap V n) := by
  classical
  let b := Module.finBasis ℂ V
  let e := (Basis.piTensorProduct (fun _ : Fin n => b.end)).equiv
    (Basis.piTensorProduct (fun _ : Fin n => b)).end
    (wordPairEquiv (Fin (Module.finrank ℂ V)) n)
  have he : (endomorphismTensorMap V n).toLinearMap = e.toLinearMap := by
    apply (Basis.piTensorProduct (fun _ : Fin n => b.end)).ext
    intro p
    rw [AlgHom.toLinearMap_apply, endomorphismTensor_matrix_unit]
    simp only [e, LinearEquiv.coe_coe, Basis.equiv_apply]
    rfl
  change Function.Bijective (endomorphismTensorMap V n).toLinearMap
  rw [he]
  exact e.bijective

theorem endomorphismTensor_isomorphism [FiniteDimensional ℂ V] (n : ℕ) :
    ∃ Φ : EndomorphismTensor V n ≃ₐ[ℂ] Module.End ℂ (TensorPower V n),
      ∀ t, Φ t = endomorphismTensorMap V n t := by
  exact ⟨AlgEquiv.ofBijective (endomorphismTensorMap V n)
    (endomorphismTensor_bijective V n), fun _ => rfl⟩

theorem endomorphismTensor_equivariant (n : ℕ) (σ : SymmetricGroup n)
    (t : EndomorphismTensor V n) :
    endomorphismTensorMap V n (slotOperator (Module.End ℂ V) n σ t) =
      slotOperator V n σ * endomorphismTensorMap V n t * slotOperator V n σ⁻¹ := by
  have hp (T : Fin n → Module.End ℂ V) :
      endomorphismTensorMap V n
          (slotOperator (Module.End ℂ V) n σ (pureTensor (Module.End ℂ V) n T)) =
        slotOperator V n σ *
          endomorphismTensorMap V n (pureTensor (Module.End ℂ V) n T) *
          slotOperator V n σ⁻¹ := by
    rw [slot_pureTensor]
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change endomorphismTensorMap V n (pureTensor (Module.End ℂ V) n _)
        (pureTensor V n v) =
      slotOperator V n σ (endomorphismTensorMap V n (pureTensor (Module.End ℂ V) n T)
        (slotOperator V n σ⁻¹ (pureTensor V n v)))
    rw [endomorphismTensor_apply_pure, slot_pureTensor, endomorphismTensor_apply_pure,
      slot_pureTensor]
    apply congrArg (pureTensor V n)
    funext i
    change T (σ⁻¹ i) (v i) = T (σ⁻¹ i) (v (σ (σ⁻¹ i)))
    exact congrArg (fun j => T (σ⁻¹ i) (v j)) (Equiv.apply_symm_apply σ i).symm
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c T =>
    change endomorphismTensorMap V n
        (slotOperator (Module.End ℂ V) n σ (c • pureTensor (Module.End ℂ V) n T)) = _
    simp only [map_smul, smul_mul_assoc, mul_smul_comm, hp]
    rfl
  | add x y hx hy =>
    simp only [map_add, mul_add, add_mul, hx, hy]

theorem endomorphismTensor_invariant_iff [FiniteDimensional ℂ V] (n : ℕ)
    (t : EndomorphismTensor V n) :
    IsInvariantEndomorphismTensor V n t ↔
      endomorphismTensorMap V n t ∈ Subalgebra.centralizer ℂ (tensorA V n : Set _) := by
  constructor
  · intro ht
    have hf : endomorphismTensorMap V n t ∈
        Subalgebra.centralizer ℂ (Set.range (slotOperator V n)) := by
      rintro _ ⟨σ, rfl⟩
      have he := endomorphismTensor_equivariant V n σ t
      rw [ht σ] at he
      calc
        slotOperator V n σ * endomorphismTensorMap V n t =
            (slotOperator V n σ * endomorphismTensorMap V n t * slotOperator V n σ⁻¹) *
              slotOperator V n σ := by
          rw [mul_assoc, mul_assoc, ← slot_mul, inv_mul_cancel, slot_one, mul_one]
        _ = endomorphismTensorMap V n t * slotOperator V n σ :=
          congrArg (fun F => F * slotOperator V n σ) he.symm
    intro a ha
    exact (Algebra.adjoin_le_centralizer_centralizer ℂ
      (Set.range (slotOperator V n)) ha (endomorphismTensorMap V n t) hf).symm
  · intro ht σ
    apply (endomorphismTensor_bijective V n).1
    rw [endomorphismTensor_equivariant]
    have hc := ht (slotOperator V n σ) (Algebra.subset_adjoin ⟨σ, rfl⟩)
    rw [hc, mul_assoc, ← slot_mul, mul_inv_cancel, slot_one, mul_one]

theorem endomorphismTensor_invariants_image [FiniteDimensional ℂ V] (n : ℕ) :
    (endomorphismTensorMap V n) '' {t | IsInvariantEndomorphismTensor V n t} =
      (Subalgebra.centralizer ℂ (A := Module.End ℂ (TensorPower V n))
        (tensorA V n : Set _) : Set (Module.End ℂ (TensorPower V n))) := by
  ext F
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (endomorphismTensor_invariant_iff V n t).mp ht
  · intro hF
    obtain ⟨t, rfl⟩ := (endomorphismTensor_bijective V n).2 F
    exact ⟨t, (endomorphismTensor_invariant_iff V n t).mpr hF, rfl⟩

theorem endomorphismTensor_zero_dimension [FiniteDimensional ℂ V] (n : ℕ)
    (hn : 0 < n) (hd : Module.finrank ℂ V = 0) :
    Subsingleton (EndomorphismTensor V n) ∧
      (0 : Module.End ℂ (TensorPower V n)) = 1 := by
  let := tensorPower_zero_dimension V n hn hd
  refine ⟨⟨fun x y => (endomorphismTensor_bijective V n).1 ?_⟩,
    tensorEnd_zero_dimension V n hn hd⟩
  exact Subsingleton.elim _ _

theorem endomorphismTensor_zero (t : EndomorphismTensor V 0) :
    endomorphismTensorMap V 0 t =
      (PiTensorProduct.isEmptyEquiv (Fin 0) t) • (1 : Module.End ℂ (TensorPower V 0)) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c T =>
    change endomorphismTensorMap V 0 (c • pureTensor (Module.End ℂ V) 0 T) = _
    have hT : T = 1 := funext (fun i => Fin.elim0 i)
    have hm : PiTensorProduct.map (1 : Fin 0 → Module.End ℂ V) = 1 :=
      PiTensorProduct.map_one
    simp only [map_smul, endomorphismTensor_pure, hT, hm,
      PiTensorProduct.isEmptyEquiv_apply_tprod, smul_eq_mul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy, add_smul]

end AdvancedFiniteGroupRepresentations
