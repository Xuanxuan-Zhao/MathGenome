import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Partitions
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! FR-D01, the two tensor actions (including the conventions after its proof).
The automorphism group `V ≃ₗ[ℂ] V` is the general linear group. All constructions
are available for any complex vector space; the zero-dimension statements use
finite dimensionality. The adjoin models of A and B are identified with the
specified algebra image and linear span by the required propositions below.
-/
open scoped TensorProduct
noncomputable section
universe u
namespace Specs.AdvancedFiniteGroupRepresentations

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

abbrev TensorPower (n : ℕ) := ⨂[ℂ] (_ : Fin n), V

def TensorPowerType := (V : Type u) → [AddCommGroup V] → [Module ℂ V] → ℕ → Type u

abbrev LinearGroup := V ≃ₗ[ℂ] V

def LinearGroupType := (V : Type u) → [AddCommGroup V] → [Module ℂ V] → Type u

def pureTensor (n : ℕ) : (Fin n → V) → TensorPower V n := PiTensorProduct.tprod ℂ

def pureTensorType := (V : Type u) → [AddCommGroup V] → [Module ℂ V] →
  (n : ℕ) → (Fin n → V) → TensorPower V n

def slotOperator (n : ℕ) (σ : SymmetricGroup n) : Module.End ℂ (TensorPower V n) :=
  (PiTensorProduct.reindex ℂ (fun _ : Fin n => V) σ).toLinearMap

def slotOperatorType := (V : Type u) → [AddCommGroup V] → [Module ℂ V] →
  (n : ℕ) → SymmetricGroup n → Module.End ℂ (TensorPower V n)

def diagonalOperator (n : ℕ) (g : LinearGroup V) : Module.End ℂ (TensorPower V n) :=
  PiTensorProduct.map (fun _ : Fin n => g.toLinearMap)

def diagonalOperatorType := (V : Type u) → [AddCommGroup V] → [Module ℂ V] →
  (n : ℕ) → LinearGroup V → Module.End ℂ (TensorPower V n)

def tensorA (n : ℕ) : Subalgebra ℂ (Module.End ℂ (TensorPower V n)) :=
  Algebra.adjoin ℂ (Set.range (slotOperator V n))

def tensorAType := (V : Type u) → [AddCommGroup V] → [Module ℂ V] →
  (n : ℕ) → Subalgebra ℂ (Module.End ℂ (TensorPower V n))

def tensorB (n : ℕ) : Subalgebra ℂ (Module.End ℂ (TensorPower V n)) :=
  Algebra.adjoin ℂ (Set.range (diagonalOperator V n))

def tensorBType := (V : Type u) → [AddCommGroup V] → [Module ℂ V] →
  (n : ℕ) → Subalgebra ℂ (Module.End ℂ (TensorPower V n))

def tensorPowerZeroEquiv : TensorPower V 0 ≃ₗ[ℂ] ℂ :=
  PiTensorProduct.isEmptyEquiv (Fin 0)

def tensorPowerZeroEquivType := (V : Type u) → [AddCommGroup V] → [Module ℂ V] →
  TensorPower V 0 ≃ₗ[ℂ] ℂ

def slot_pureTensorType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ) (σ : SymmetricGroup n)
    (v : Fin n → V), slotOperator V n σ (pureTensor V n v) =
      pureTensor V n (fun i => v (σ⁻¹ i))

def diagonal_pureTensorType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ) (g : LinearGroup V)
    (v : Fin n → V), diagonalOperator V n g (pureTensor V n v) =
      pureTensor V n (fun i => g (v i))

def slot_oneType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ),
    slotOperator V n 1 = 1

def slot_mulType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ) (σ τ : SymmetricGroup n),
    slotOperator V n (σ * τ) = slotOperator V n σ * slotOperator V n τ

def diagonal_oneType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ),
    diagonalOperator V n 1 = 1

def diagonal_mulType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ) (g h : LinearGroup V),
    diagonalOperator V n (g * h) = diagonalOperator V n g * diagonalOperator V n h

def tensor_actions_commuteType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ) (σ : SymmetricGroup n)
    (g : LinearGroup V), Commute (slotOperator V n σ) (diagonalOperator V n g)

def tensorA_imageType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ),
    ∃ φ : GroupAlgebra n →ₐ[ℂ] Module.End ℂ (TensorPower V n),
      (∀ σ, φ (MonoidAlgebra.single σ 1) = slotOperator V n σ) ∧
        φ.range = tensorA V n

def tensorB_spanType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ),
    (tensorB V n).toSubmodule = Submodule.span ℂ (Set.range (diagonalOperator V n))

def tensor_subalgebras_commuteType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ)
    (a : Module.End ℂ (TensorPower V n)), a ∈ tensorA V n →
    ∀ b, b ∈ tensorB V n → Commute a b

def tensorPower_finiteType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    FiniteDimensional ℂ (TensorPower V n)

def tensorPowerZeroEquiv_pureType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (v : Fin 0 → V),
    tensorPowerZeroEquiv V (pureTensor V 0 v) = 1

def slot_zeroType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (σ : SymmetricGroup 0),
    slotOperator V 0 σ = 1

def diagonal_zeroType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (g : LinearGroup V),
    diagonalOperator V 0 g = 1

def tensorPower_zero_dimensionType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ), 0 < n → Module.finrank ℂ V = 0 → Subsingleton (TensorPower V n)

def tensorEnd_zero_dimensionType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ), 0 < n → Module.finrank ℂ V = 0 →
      (0 : Module.End ℂ (TensorPower V n)) = 1

end Specs.AdvancedFiniteGroupRepresentations
