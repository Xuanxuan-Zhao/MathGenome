import MathGenome.Internal.Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices
import MathGenome.Internal.Specs.D07.Ch18.NilpotenceExamplesSolvableNonnilpotent
import MathGenome.Internal.Specs.D07.Ch18.NilpotenceExamplesReverseInterlacingFailure

/-! The three examples in paper.tex:5197–5227. The quaternion example uses
the actual eight complex matrices, with an explicit equivalence to Q₈.
Exact class refers to least upper-series termination, including at zero.
The other two examples reuse the independent statements of the prerequisites. -/
namespace Specs.D07.Ch18.NilpotenceExamples

open Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices
open Specs.D07.Ch18.CentralSeries Specs.D07.Ch18.NilpotenceCriteria
open scoped commutatorElement

/-- All assertions about the source's concrete quaternion group. -/
def QuaternionExample : Prop :=
  ∃ H : Subgroup MatrixGroup,
    (∀ g : MatrixGroup, g ∈ H ↔ (g : Mat) ∈ eightMatrices) ∧
    Nat.card H = 8 ∧
    ∃ e : QuaternionGroup 2 ≃* H,
      (∀ q, (((e q : H) : MatrixGroup) : Mat) = modelMatrix q) ∧
      (∃ g h : H, g * h ≠ h * g) ∧
      (∀ g : H, g ∈ Subgroup.center H ↔
        ((g : MatrixGroup) : Mat) = E ∨ ((g : MatrixGroup) : Mat) = -E) ∧
      (∀ g : H, ((g : MatrixGroup) : Mat) ≠ E →
        ((g : MatrixGroup) : Mat) ≠ -E →
        ∃ h : H, (((h : H) : MatrixGroup) : Mat) ∈ ({I, J, K} : Set Mat) ∧
          g * h ≠ h * g) ∧
      Nat.card (H ⧸ Subgroup.center H) = 4 ∧
      (∀ x y : H ⧸ Subgroup.center H, x * y = y * x) ∧
      upperValue H 2 = ⊤ ∧ hasClassValue H 2 ∧ Group.IsNilpotent H

def SymmetricExample : Prop :=
  NilpotenceExamplesSolvableNonnilpotent.DerivedSubgroup ∧
  NilpotenceExamplesSolvableNonnilpotent.FirstDerivedTerm ∧
  NilpotenceExamplesSolvableNonnilpotent.SecondDerivedTerm ∧
  NilpotenceExamplesSolvableNonnilpotent.MixedCommutator ∧
  NilpotenceExamplesSolvableNonnilpotent.LowerCentralTerms ∧
  NilpotenceExamplesSolvableNonnilpotent.Solvable ∧
  NilpotenceExamplesSolvableNonnilpotent.NotNilpotent ∧
  NilpotenceExamplesSolvableNonnilpotent.NoClassBound

def ReverseInterlacingExample : Prop :=
  NilpotenceExamplesReverseInterlacingFailure.GeometricCounterexample

/-- The explicit permutations used in the S₃ calculation; Fin 3 labels
the source's three points by 0,1,2. -/
def SymmetricCalculations : Prop :=
  let a : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  let s : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 0 ∧
  ⁅a, s⁆ = a ^ 2 ∧ a ^ 2 ≠ 1 ∧ s * a * s⁻¹ = a⁻¹ ∧
  (∀ x y : Equiv.Perm (Fin 3), Equiv.Perm.sign ⁅x, y⁆ = 1) ∧
  (∀ x y : alternatingGroup (Fin 3), x * y = y * x)

/-- Additional identities from the octagon paragraph, transported through
any isomorphism to the actual geometric symmetry group. The prerequisite
GeometricCounterexample supplies the isomorphism with the specified motions. -/
def OctagonCalculations : Prop :=
  ∀ (c a : ℂ), a ≠ 0 →
    ∀ e : DihedralGroup 8 ≃* NilpotenceExamplesReverseInterlacingFailure.Octagon c a,
      let D := NilpotenceExamplesReverseInterlacingFailure.Octagon c a
      let r := e (DihedralGroup.r 1)
      let s := e (DihedralGroup.sr 0)
      ⁅r, s⁆ = r ^ 2 ∧ ⁅r ^ 2, s⁆ = r ^ 4 ∧ r ^ 4 ∈ Subgroup.center D ∧
      (∀ g : D, ∃ b : Fin 8, g = r ^ b.val ∨ g = r ^ b.val * s) ∧
      (∀ g h : D, h ∈ Subgroup.zpowers (r ^ 2) →
        g * h * g⁻¹ = h ∨ g * h * g⁻¹ = h⁻¹) ∧
      (∃ hN : (Subgroup.zpowers (r ^ 2)).Normal,
        letI := hN
        ∀ x y : D ⧸ Subgroup.zpowers (r ^ 2), x * y = y * x)

def AllExamples : Prop :=
  QuaternionExample ∧ SymmetricExample ∧ ReverseInterlacingExample ∧
    SymmetricCalculations ∧ OctagonCalculations

end Specs.D07.Ch18.NilpotenceExamples
