import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorActions
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CycleTypes
import Mathlib.LinearAlgebra.Trace

/-! FR-D07, first identity (the character average is allocated separately).
The multiset of parts of `cyclePartition` includes every fixed point once.
Powers below are powers in the endomorphism algebra, hence the usual iterates
of the given linear automorphism. No diagonalizability hypothesis is imposed.
-/
noncomputable section
universe u
namespace Specs.AdvancedFiniteGroupRepresentations

variable (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- The product of the traces over all cycles, including singleton cycles. -/
def cycleTraceProduct {n : ℕ} (σ : SymmetricGroup n) (g : LinearGroup V) : ℂ :=
  ((cyclePartition σ).parts.map
    (fun k => LinearMap.trace ℂ V (g.toLinearMap ^ k))).prod

def cycleTraceProductType :=
  (V : Type u) → [AddCommGroup V] → [Module ℂ V] →
    {n : ℕ} → SymmetricGroup n → LinearGroup V → ℂ

def tensor_cycle_traceType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ) (σ : SymmetricGroup n) (g : LinearGroup V),
    LinearMap.trace ℂ (TensorPower V n)
      (slotOperator V n σ * diagonalOperator V n g) = cycleTraceProduct V σ g

def tensor_cycle_trace_zeroType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : SymmetricGroup 0) (g : LinearGroup V),
    LinearMap.trace ℂ (TensorPower V 0)
      (slotOperator V 0 σ * diagonalOperator V 0 g) = 1 ∧
      cycleTraceProduct V σ g = 1

def tensor_cycle_trace_zero_dimensionType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ) (σ : SymmetricGroup n) (g : LinearGroup V),
    0 < n → Module.finrank ℂ V = 0 →
    LinearMap.trace ℂ (TensorPower V n)
      (slotOperator V n σ * diagonalOperator V n g) = 0 ∧
      cycleTraceProduct V σ g = 0

end Specs.AdvancedFiniteGroupRepresentations
