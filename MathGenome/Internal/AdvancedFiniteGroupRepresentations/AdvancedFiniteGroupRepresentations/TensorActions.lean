import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.Partitions
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorActions
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section
universe u
namespace AdvancedFiniteGroupRepresentations

abbrev TensorPower := @Specs.AdvancedFiniteGroupRepresentations.TensorPower
abbrev LinearGroup := @Specs.AdvancedFiniteGroupRepresentations.LinearGroup
abbrev pureTensor := @Specs.AdvancedFiniteGroupRepresentations.pureTensor
abbrev slotOperator := @Specs.AdvancedFiniteGroupRepresentations.slotOperator
abbrev diagonalOperator := @Specs.AdvancedFiniteGroupRepresentations.diagonalOperator
abbrev tensorA := @Specs.AdvancedFiniteGroupRepresentations.tensorA
abbrev tensorB := @Specs.AdvancedFiniteGroupRepresentations.tensorB
abbrev tensorPowerZeroEquiv := @Specs.AdvancedFiniteGroupRepresentations.tensorPowerZeroEquiv

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

theorem slot_pureTensor (n : ℕ) (σ : SymmetricGroup n) (v : Fin n → V) :
    slotOperator V n σ (pureTensor V n v) = pureTensor V n (fun i => v (σ⁻¹ i)) := by
  exact PiTensorProduct.reindex_tprod σ v

theorem diagonal_pureTensor (n : ℕ) (g : LinearGroup V) (v : Fin n → V) :
    diagonalOperator V n g (pureTensor V n v) = pureTensor V n (fun i => g (v i)) := by
  exact PiTensorProduct.map_tprod _ v

theorem slot_one (n : ℕ) : slotOperator V n 1 = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change slotOperator V n 1 (pureTensor V n v) = pureTensor V n v
  rw [slot_pureTensor]
  rfl

theorem slot_mul (n : ℕ) (σ τ : SymmetricGroup n) :
    slotOperator V n (σ * τ) = slotOperator V n σ * slotOperator V n τ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change slotOperator V n (σ * τ) (pureTensor V n v) =
    slotOperator V n σ (slotOperator V n τ (pureTensor V n v))
  simp only [slot_pureTensor]
  rfl

theorem diagonal_one (n : ℕ) : diagonalOperator V n 1 = 1 := by
  exact PiTensorProduct.map_one

theorem diagonal_mul (n : ℕ) (g h : LinearGroup V) :
    diagonalOperator V n (g * h) = diagonalOperator V n g * diagonalOperator V n h := by
  exact PiTensorProduct.map_mul (fun _ : Fin n => g.toLinearMap) (fun _ => h.toLinearMap)

/-- The slot action is a representation, with the left-action convention. -/
def slotRepresentation (n : ℕ) : SymmetricGroup n →* Module.End ℂ (TensorPower V n) where
  toFun := slotOperator V n
  map_one' := slot_one V n
  map_mul' := slot_mul V n

/-- The diagonal action is a representation of the general linear group. -/
def diagonalRepresentation (n : ℕ) : LinearGroup V →* Module.End ℂ (TensorPower V n) where
  toFun := diagonalOperator V n
  map_one' := diagonal_one V n
  map_mul' := diagonal_mul V n

theorem tensor_actions_commute (n : ℕ) (σ : SymmetricGroup n) (g : LinearGroup V) :
    Commute (slotOperator V n σ) (diagonalOperator V n g) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change slotOperator V n σ (diagonalOperator V n g (pureTensor V n v)) =
    diagonalOperator V n g (slotOperator V n σ (pureTensor V n v))
  rw [diagonal_pureTensor, slot_pureTensor, slot_pureTensor, diagonal_pureTensor]

/-- Linear extension of the slot representation to the complex group algebra. -/
def slotAlgebraMap (n : ℕ) : GroupAlgebra n →ₐ[ℂ] Module.End ℂ (TensorPower V n) :=
  MonoidAlgebra.lift ℂ _ _ (slotRepresentation V n)

@[simp] theorem slotAlgebraMap_single (n : ℕ) (σ : SymmetricGroup n) (c : ℂ) :
    slotAlgebraMap V n (MonoidAlgebra.single σ c) = c • slotOperator V n σ := by
  exact MonoidAlgebra.lift_single _ _ _

theorem slotAlgebraMap_range (n : ℕ) : (slotAlgebraMap V n).range = tensorA V n := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change slotAlgebraMap V n x ∈ tensorA V n
    induction x using MonoidAlgebra.induction_on with
    | of σ =>
      change slotAlgebraMap V n (MonoidAlgebra.single σ 1) ∈ tensorA V n
      rw [slotAlgebraMap_single, one_smul]
      exact Algebra.subset_adjoin ⟨σ, rfl⟩
    | add x y hx hy =>
      rw [map_add]
      exact (tensorA V n).add_mem hx hy
    | smul c x hx =>
      rw [map_smul]
      exact (tensorA V n).smul_mem hx c
  · apply Algebra.adjoin_le
    rintro _ ⟨σ, rfl⟩
    exact ⟨MonoidAlgebra.single σ 1, by simp⟩

theorem tensorA_image (n : ℕ) :
    ∃ φ : GroupAlgebra n →ₐ[ℂ] Module.End ℂ (TensorPower V n),
      (∀ σ, φ (MonoidAlgebra.single σ 1) = slotOperator V n σ) ∧
        φ.range = tensorA V n := by
  exact ⟨slotAlgebraMap V n, by simp, slotAlgebraMap_range V n⟩

theorem tensorB_span (n : ℕ) :
    (tensorB V n).toSubmodule = Submodule.span ℂ (Set.range (diagonalOperator V n)) := by
  change (Algebra.adjoin ℂ (Set.range (diagonalRepresentation V n))).toSubmodule =
    Submodule.span ℂ (Set.range (diagonalRepresentation V n))
  rw [Algebra.adjoin_eq_span, MonoidHom.mclosure_range, MonoidHom.coe_mrange]

theorem tensor_subalgebras_commute (n : ℕ) (a : Module.End ℂ (TensorPower V n))
    (ha : a ∈ tensorA V n) (b : Module.End ℂ (TensorPower V n))
    (hb : b ∈ tensorB V n) : Commute a b := by
  have hB : tensorB V n ≤ Subalgebra.centralizer ℂ (Set.range (slotOperator V n)) := by
    apply Algebra.adjoin_le
    rintro _ ⟨g, rfl⟩
    intro _ hσ
    rcases hσ with ⟨σ, rfl⟩
    exact tensor_actions_commute V n σ g
  have hA : tensorA V n ≤ Subalgebra.centralizer ℂ (tensorB V n : Set _) := by
    apply Algebra.adjoin_le
    rintro _ ⟨σ, rfl⟩
    intro y hy
    exact (hB hy (slotOperator V n σ) ⟨σ, rfl⟩).symm
  exact (hA ha b hb).symm

theorem tensorPower_finite [FiniteDimensional ℂ V] (n : ℕ) :
    FiniteDimensional ℂ (TensorPower V n) := inferInstance

theorem tensorPowerZeroEquiv_pure (v : Fin 0 → V) :
    tensorPowerZeroEquiv V (pureTensor V 0 v) = 1 := by
  exact PiTensorProduct.isEmptyEquiv_apply_tprod (Fin 0) v

theorem slot_zero (σ : SymmetricGroup 0) : slotOperator V 0 σ = 1 := by
  rw [zero_labels_trivial σ]
  exact slot_one V 0

theorem diagonal_zero (g : LinearGroup V) : diagonalOperator V 0 g = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change diagonalOperator V 0 g (pureTensor V 0 v) = pureTensor V 0 v
  rw [diagonal_pureTensor]
  congr 1
  exact funext (fun i => Fin.elim0 i)

theorem tensorPower_zero_dimension [FiniteDimensional ℂ V] (n : ℕ)
    (hn : 0 < n) (hd : Module.finrank ℂ V = 0) : Subsingleton (TensorPower V n) := by
  let : Subsingleton V := (Module.finrank_zero_iff (R := ℂ) (M := V)).mp hd
  have hz : ∀ x : TensorPower V n, x = 0 := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c v =>
      have hv : PiTensorProduct.tprod ℂ v = 0 :=
        (PiTensorProduct.tprod ℂ).map_coord_zero ⟨0, hn⟩ (Subsingleton.elim _ _)
      rw [hv, smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem tensorEnd_zero_dimension [FiniteDimensional ℂ V] (n : ℕ)
    (hn : 0 < n) (hd : Module.finrank ℂ V = 0) :
    (0 : Module.End ℂ (TensorPower V n)) = 1 := by
  let := tensorPower_zero_dimension V n hn hd
  exact Subsingleton.elim _ _

end AdvancedFiniteGroupRepresentations
