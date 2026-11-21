import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorActions
import Mathlib.RingTheory.PiTensorProduct

/-! FR-D02 (4.2), with the finite-dimensional convention and the boundary
conventions of FR-D01. The source algebra uses composition in each factor.
The expected propositions below are independent of the implementation. -/
noncomputable section
universe u
namespace Specs.AdvancedFiniteGroupRepresentations

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

abbrev EndomorphismTensor (n : ℕ) := TensorPower (Module.End ℂ V) n

def EndomorphismTensorType :=
  (V : Type u) → [AddCommGroup V] → [Module ℂ V] → ℕ → Type u

/-- The canonical algebra map induced by applying each endomorphism in its slot. -/
def endomorphismTensorMap (n : ℕ) :
    EndomorphismTensor V n →ₐ[ℂ] Module.End ℂ (TensorPower V n) :=
  PiTensorProduct.liftAlgHom
    (PiTensorProduct.mapMultilinear ℂ (fun _ : Fin n => V) (fun _ => V))
    PiTensorProduct.map_one PiTensorProduct.map_mul

def endomorphismTensorMapType :=
  (V : Type u) → [AddCommGroup V] → [Module ℂ V] → (n : ℕ) →
    EndomorphismTensor V n →ₐ[ℂ] Module.End ℂ (TensorPower V n)

/-- Fixed tensors for the same left slot action as on the vector tensor power. -/
def IsInvariantEndomorphismTensor (n : ℕ) (t : EndomorphismTensor V n) : Prop :=
  ∀ σ : SymmetricGroup n, slotOperator (Module.End ℂ V) n σ t = t

def IsInvariantEndomorphismTensorType :=
  (V : Type u) → [AddCommGroup V] → [Module ℂ V] → (n : ℕ) →
    EndomorphismTensor V n → Prop

def endomorphismTensor_pureType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ) (T : Fin n → Module.End ℂ V),
    endomorphismTensorMap V n (pureTensor (Module.End ℂ V) n T) = PiTensorProduct.map T

def endomorphismTensor_apply_pureType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ)
    (T : Fin n → Module.End ℂ V) (v : Fin n → V),
    endomorphismTensorMap V n (pureTensor (Module.End ℂ V) n T) (pureTensor V n v) =
      pureTensor V n (fun i => T i (v i))

def endomorphismTensor_bijectiveType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    Function.Bijective (endomorphismTensorMap V n)

/-- Existence of an algebra isomorphism equal to the canonical map on every tensor. -/
def endomorphismTensor_isomorphismType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    ∃ Φ : EndomorphismTensor V n ≃ₐ[ℂ] Module.End ℂ (TensorPower V n),
      ∀ t, Φ t = endomorphismTensorMap V n t

def endomorphismTensor_equivariantType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ) (σ : SymmetricGroup n)
    (t : EndomorphismTensor V n),
    endomorphismTensorMap V n (slotOperator (Module.End ℂ V) n σ t) =
      slotOperator V n σ * endomorphismTensorMap V n t * slotOperator V n σ⁻¹

/-- Together with bijectivity, this identifies the invariant tensors with End_A(X). -/
def endomorphismTensor_invariant_iffType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (t : EndomorphismTensor V n),
    IsInvariantEndomorphismTensor V n t ↔
      endomorphismTensorMap V n t ∈ Subalgebra.centralizer ℂ (tensorA V n : Set _)

def endomorphismTensor_invariants_imageType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    (endomorphismTensorMap V n) '' {t | IsInvariantEndomorphismTensor V n t} =
      (Subalgebra.centralizer ℂ (A := Module.End ℂ (TensorPower V n))
        (tensorA V n : Set _) : Set (Module.End ℂ (TensorPower V n)))

def endomorphismTensor_zero_dimensionType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ), 0 < n → Module.finrank ℂ V = 0 →
      Subsingleton (EndomorphismTensor V n) ∧
        (0 : Module.End ℂ (TensorPower V n)) = 1

def endomorphismTensor_zeroType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (t : EndomorphismTensor V 0),
    endomorphismTensorMap V 0 t =
      (PiTensorProduct.isEmptyEquiv (Fin 0) t) • (1 : Module.End ℂ (TensorPower V 0))

end Specs.AdvancedFiniteGroupRepresentations
