import MathGenome.Internal.D05.M15.TensorMaps
import MathGenome.Internal.Specs.D05.M15.PermutationActions

/-! K05.15.permutation_actions: the left permutation action on tensor powers. -/

namespace D05.M15.PermutationActions

/-- Reuse the canonical reindexing of the upstream finite tensor power. -/
noncomputable abbrev permutationOperator :=
  @Specs.D05.M15.PermutationActions.permutationOperator

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem reordered_multilinear (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    ∃ b : MultilinearMap K (fun _ : Fin p => V)
        (PiTensorProduct K (fun _ : Fin p => V)),
      ∀ v : Fin p → V, b v = PiTensorProduct.tprod K (fun j => v (σ⁻¹ j)) := by
  exact ⟨(PiTensorProduct.tprod K).domDomCongr σ.symm, fun _ => rfl⟩

theorem operator_apply (p : ℕ) (σ : Equiv.Perm (Fin p)) (v : Fin p → V) :
    permutationOperator (K := K) p σ (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (fun j => v (σ⁻¹ j)) := by
  exact PiTensorProduct.reindex_tprod σ v

theorem operator_unique (p : ℕ) (σ : Equiv.Perm (Fin p))
    (F : PiTensorProduct K (fun _ : Fin p => V) →ₗ[K]
      PiTensorProduct K (fun _ : Fin p => V))
    (hF : ∀ v : Fin p → V, F (PiTensorProduct.tprod K v) =
      PiTensorProduct.tprod K (fun j => v (σ⁻¹ j))) :
    F = permutationOperator p σ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  exact (hF v).trans (operator_apply p σ v).symm

/-- Two reindexings select slot τ⁻¹(σ⁻¹(j)), exactly (στ)⁻¹(j).
The universal property extends this calculation from elementary tensors. -/
theorem operator_mul (p : ℕ) (σ τ : Equiv.Perm (Fin p)) :
    (permutationOperator (K := K) (V := V) p σ).comp
        (permutationOperator p τ) = permutationOperator p (σ * τ) := by
  apply operator_unique p (σ * τ)
  intro v
  simp only [LinearMap.comp_apply, operator_apply, mul_inv_rev, Equiv.Perm.coe_mul,
    Function.comp_apply]

theorem operator_one (p : ℕ) :
    permutationOperator (K := K) (V := V) p 1 = LinearMap.id := by
  symm
  apply operator_unique p 1
  intro v
  rfl

theorem operator_inverse (p : ℕ) (σ : Equiv.Perm (Fin p)) :
    (permutationOperator (K := K) (V := V) p σ⁻¹).comp
        (permutationOperator p σ) = LinearMap.id ∧
    (permutationOperator (K := K) (V := V) p σ).comp
        (permutationOperator p σ⁻¹) = LinearMap.id := by
  constructor
  · rw [operator_mul, inv_mul_cancel, operator_one]
  · rw [operator_mul, mul_inv_cancel, operator_one]

theorem degree_zero_scalar (σ : Equiv.Perm (Fin 0))
    (t : PiTensorProduct K (fun _ : Fin 0 => V)) :
    PiTensorProduct.isEmptyEquiv (R := K) (s := fun _ : Fin 0 => V) (Fin 0)
        (permutationOperator 0 σ t) =
      PiTensorProduct.isEmptyEquiv (R := K) (s := fun _ : Fin 0 => V) (Fin 0) t := by
  have hσ : σ = 1 := Subsingleton.elim _ _
  rw [hσ, operator_one]
  rfl

end D05.M15.PermutationActions
