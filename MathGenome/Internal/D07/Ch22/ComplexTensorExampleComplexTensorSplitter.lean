import MathGenome.Internal.Specs.D07.Ch22.ComplexTensorExampleComplexTensorSplitter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

noncomputable section
open scoped TensorProduct
namespace D07.Ch22.ComplexTensorExampleComplexTensorSplitter
open Specs.D07.Ch22.ComplexTensorExampleComplexTensorSplitter

/-- Multiplication and conjugate multiplication, extended through scalar extension. -/
def splitHom : ComplexTensor →ₐ[ℂ] (ℂ × ℂ) :=
  AlgHom.liftEquiv ℝ ℂ ℂ (ℂ × ℂ)
    ((AlgHom.id ℝ ℂ).prod Complex.conjAe.toAlgHom)

@[simp] theorem splitHom_tmul (z w : ℂ) :
    splitHom (z ⊗ₜ[ℝ] w) = (z * w, z * starRingEnd ℂ w) := by
  rfl

@[simp] theorem splitHom_normal (u v : ℂ) :
    splitHom (normal u v) = (u + v * Complex.I, u - v * Complex.I) := by
  simp [normal, sub_eq_add_neg]

/-- Expand the second complex factor in the real basis 1,i. -/
theorem exists_normal (t : ComplexTensor) : ∃ u v : ℂ, t = normal u v := by
  induction t using TensorProduct.inductionOn with
  | tmul z w =>
    refine ⟨z * w.re, z * w.im, ?_⟩
    conv_lhs => rw [← Complex.re_add_im w]
    rw [TensorProduct.tmul_add]
    unfold normal
    congr 1
    · rw [show (w.re : ℂ) = w.re • (1 : ℂ) by simp]
      rw [← TensorProduct.smul_tmul]
      simp [Complex.real_smul, mul_comm]
    · rw [show (w.im : ℂ) * Complex.I = w.im • Complex.I by rfl]
      rw [← TensorProduct.smul_tmul]
      simp [Complex.real_smul, mul_comm]
  | add a b ha hb =>
    obtain ⟨u, v, rfl⟩ := ha
    obtain ⟨x, y, rfl⟩ := hb
    refine ⟨u + x, v + y, ?_⟩
    simp only [normal, TensorProduct.add_tmul]
    abel

/-- The two images determine both normal coordinates. -/
theorem coordinates_injective {u v x y : ℂ}
    (h : splitHom (normal u v) = splitHom (normal x y)) : u = x ∧ v = y := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [splitHom_normal] at h₁ h₂
  have hu : u = x := by linear_combination (h₁ + h₂) / 2
  have hv : (v - y) * Complex.I = 0 := by linear_combination (h₁ - h₂) / 2
  exact ⟨hu, sub_eq_zero.mp ((mul_eq_zero.mp hv).resolve_right Complex.I_ne_zero)⟩

theorem splitHom_injective : Function.Injective splitHom := by
  intro a b h
  obtain ⟨u, v, rfl⟩ := exists_normal a
  obtain ⟨x, y, rfl⟩ := exists_normal b
  obtain ⟨rfl, rfl⟩ := coordinates_injective h
  rfl

/-- Solve the two linear equations over the complex field. -/
theorem splitHom_inverse (x y : ℂ) :
    splitHom (normal ((x + y) / 2) ((x - y) / (2 * Complex.I))) = (x, y) := by
  rw [splitHom_normal]
  apply Prod.ext <;> dsimp <;> field_simp <;> ring

def splitEquiv : ComplexTensor ≃ₐ[ℂ] (ℂ × ℂ) :=
  AlgEquiv.ofBijective splitHom ⟨splitHom_injective, fun p =>
    ⟨normal ((p.1 + p.2) / 2) ((p.1 - p.2) / (2 * Complex.I)),
      splitHom_inverse p.1 p.2⟩⟩

@[simp] theorem splitEquiv_tmul (z w : ℂ) :
    splitEquiv (z ⊗ₜ[ℝ] w) = (z * w, z * starRingEnd ℂ w) := splitHom_tmul z w

@[simp] theorem splitEquiv_symm (x y : ℂ) :
    splitEquiv.symm (x, y) = normal ((x + y) / 2) ((x - y) / (2 * Complex.I)) := by
  apply splitEquiv.injective
  exact (splitEquiv.apply_symm_apply (x, y)).trans (splitHom_inverse x y).symm

@[simp] theorem first_image : splitEquiv firstIdempotent = (1, 0) := by
  change splitHom firstIdempotent = (1, 0)
  simp only [firstIdempotent, map_smul, map_sub, splitHom_tmul]
  ext <;> norm_num [Complex.I_mul_I]

@[simp] theorem second_image : splitEquiv secondIdempotent = (0, 1) := by
  change splitHom secondIdempotent = (0, 1)
  simp only [secondIdempotent, map_smul, map_add, splitHom_tmul]
  ext <;> norm_num [Complex.I_mul_I]

theorem splitting : Splitting :=
  ⟨splitEquiv, splitEquiv_tmul, splitEquiv_symm, first_image, second_image⟩

theorem uniqueNormalForm : UniqueNormalForm := by
  intro t
  obtain ⟨u, v, h⟩ := exists_normal t
  refine ⟨(u, v), h, ?_⟩
  intro p hp
  obtain ⟨h₁, h₂⟩ := coordinates_injective (congrArg splitHom (hp.symm.trans h))
  exact Prod.ext h₁ h₂

theorem idempotents : Idempotents := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg splitEquiv h
    simp at this
  · intro h
    have := congrArg splitEquiv h
    simp at this
  · apply splitEquiv.injective
    simp
  · apply splitEquiv.injective
    simp
  · apply splitEquiv.injective
    simp
  · apply splitEquiv.injective
    simp
  · apply splitEquiv.injective
    simp

theorem notDomain : NotDomain := by
  intro h
  let : IsDomain ComplexTensor := h
  obtain ⟨h₁, h₂, _, _, h₁₂, _⟩ := idempotents
  exact (mul_ne_zero h₁ h₂) h₁₂

end D07.Ch22.ComplexTensorExampleComplexTensorSplitter
