import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.InvariantTensorPolarization
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer

/-! FR-D03, with the canonical actions and the boundary conventions of FR-D01.
The span statement supplies the passage from arbitrary to invertible operator
powers. No positivity assumption is imposed on the final centralizer identity. -/
noncomputable section
universe u
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Every operator tensor power lies in the linear span of the GL(V) action. -/
def operatorPower_mem_diagonalSpanType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ) (T : Module.End ℂ V),
    PiTensorProduct.map (fun _ : Fin n => T) ∈
      Submodule.span ℂ (Set.range (diagonalOperator V n))

/-- At degree zero both algebras are the whole scalar endomorphism algebra. -/
def tensorAlgebras_zeroType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    tensorA V 0 = ⊤ ∧ tensorB V 0 = ⊤

/-- In positive degree on the zero space, the ambient endomorphism algebra is zero. -/
def tensorAlgebras_zero_dimensionType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ), 0 < n → Module.finrank ℂ V = 0 →
      (0 : Module.End ℂ (TensorPower V n)) = 1 ∧
      tensorA V n = ⊤ ∧ tensorB V n = ⊤

/-- The first centralizer identity, as equality of actual complex subalgebras. -/
def firstCentralizerType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    Subalgebra.centralizer ℂ (tensorA V n : Set (Module.End ℂ (TensorPower V n))) =
      tensorB V n

end Specs.AdvancedFiniteGroupRepresentations
