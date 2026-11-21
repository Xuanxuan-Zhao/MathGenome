import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Complex.Module

/-! Independent specification of the complex splitting in K07.22.complex_tensor_example,
paper.tex:6923–6944. The canonical tensor algebra has its complex action through
its first factor; the product algebra has the diagonal complex action. -/

noncomputable section
open scoped TensorProduct
namespace Specs.D07.Ch22.ComplexTensorExampleComplexTensorSplitter

abbrev ComplexTensor := ℂ ⊗[ℝ] ℂ

def normal (u v : ℂ) : ComplexTensor := u ⊗ₜ[ℝ] (1 : ℂ) + v ⊗ₜ[ℝ] Complex.I

def firstIdempotent : ComplexTensor :=
  (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] (1 : ℂ) - Complex.I ⊗ₜ[ℝ] Complex.I)

def secondIdempotent : ComplexTensor :=
  (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] (1 : ℂ) + Complex.I ⊗ₜ[ℝ] Complex.I)

/-- The prescribed algebra equivalence, its values on every elementary tensor,
its inverse coordinates, and the images of the two specified idempotents. -/
def Splitting : Prop :=
  ∃ e : ComplexTensor ≃ₐ[ℂ] (ℂ × ℂ),
    (∀ z w : ℂ, e (z ⊗ₜ[ℝ] w) = (z * w, z * starRingEnd ℂ w)) ∧
    (∀ x y : ℂ, e.symm (x, y) = normal ((x + y) / 2) ((x - y) / (2 * Complex.I))) ∧
    e firstIdempotent = (1, 0) ∧ e secondIdempotent = (0, 1)

/-- Existence and uniqueness of the pair of complex normal coordinates. -/
def UniqueNormalForm : Prop :=
  ∀ t : ComplexTensor, ∃! p : ℂ × ℂ, t = normal p.1 p.2

/-- Nonzero, mutually orthogonal idempotents, whose sum is the identity. -/
def Idempotents : Prop :=
  firstIdempotent ≠ 0 ∧ secondIdempotent ≠ 0 ∧
    firstIdempotent * firstIdempotent = firstIdempotent ∧
    secondIdempotent * secondIdempotent = secondIdempotent ∧
    firstIdempotent * secondIdempotent = 0 ∧
    secondIdempotent * firstIdempotent = 0 ∧
    firstIdempotent + secondIdempotent = 1

/-- A tensor product of the two fields in this example fails to be a domain. -/
def NotDomain : Prop := ¬ IsDomain ComplexTensor

end Specs.D07.Ch22.ComplexTensorExampleComplexTensorSplitter
