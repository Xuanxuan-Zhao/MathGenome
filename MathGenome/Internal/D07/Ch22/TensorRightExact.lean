import MathGenome.Internal.Specs.D07.Ch22.TensorRightExact
import MathGenome.Internal.D07.Ch22.TensorFunctor
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Tactic.NormNum

/-! Right exactness and the multiplication-by-two counterexample. -/

noncomputable section
universe u v w t s
namespace D07.Ch22.TensorRightExact
open Specs.D07.Ch22.TensorRightExact
open scoped TensorProduct
attribute [-instance] AddCommGroup.toIntModule

theorem rightExactness : RightExactness.{u, v, w, t, s} := by
  intro R _ A _ _ B _ _ C _ _ N _ _ f g hg hfg
  have he : Function.Exact f g := LinearMap.exact_iff.mpr hfg.symm
  exact ⟨LinearMap.rTensor_surjective N hg,
    (Function.Exact.linearMap_ker_eq (rTensor_exact N he hg)).symm⟩

theorem doublingFormula : DoublingFormula := by
  intro x
  simp [doubling]

theorem doublingInjective : DoublingInjective := by
  intro x y h
  have hxy : (2 : ℤ) * x = 2 * y := by
    rw [doublingFormula, doublingFormula] at h
    exact h
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hxy

theorem counterexampleUnit : CounterexampleUnit := by
  obtain ⟨e, he, _⟩ := D07.Ch22.TensorFunctor.unitIsomorphism ℤ ModTwo
  exact ⟨e, he⟩

/-- Every element of the actual ideal quotient is annihilated by two. -/
theorem two_smul_modTwo (n : ModTwo) : (2 : ℤ) • n = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective n
  change (Ideal.span ({(2 : ℤ)} : Set ℤ)).mkQ ((2 : ℤ) • a) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Ideal.mul_mem_right a _ (Ideal.subset_span rfl)

theorem tensorDoublingZero : TensorDoublingZero := by
  apply TensorProduct.ext'
  intro a n
  change doubling a ⊗ₜ[ℤ] n = 0
  rw [doublingFormula]
  change ((2 : ℤ) • a) ⊗ₜ[ℤ] n = 0
  rw [TensorProduct.smul_tmul,
    two_smul_modTwo, TensorProduct.tmul_zero]

/-- The quotient class of one is nonzero: two does not divide one. -/
theorem modTwo_one_ne_zero : (1 : ModTwo) ≠ 0 := by
  intro h
  have hm : (1 : ℤ) ∈ Ideal.span ({(2 : ℤ)} : Set ℤ) :=
    (Ideal.Quotient.eq_zero_iff_mem).mp h
  have hd : (2 : ℤ) ∣ 1 := Ideal.mem_span_singleton.mp hm
  norm_num at hd

theorem tensorSourceNontrivial : TensorSourceNontrivial := by
  have : Nontrivial ModTwo := ⟨⟨1, 0, modTwo_one_ne_zero⟩⟩
  exact (TensorProduct.lid ℤ ModTwo).surjective.nontrivial

theorem leftExactnessFailure : LeftExactnessFailure := by
  have : Nontrivial (ℤ ⊗[ℤ] ModTwo) := tensorSourceNontrivial
  intro h
  have hsub : Subsingleton (ℤ ⊗[ℤ] ModTwo) := by
    refine ⟨fun x y => h ?_⟩
    rw [tensorDoublingZero]
    rfl
  exact not_subsingleton _ hsub

end D07.Ch22.TensorRightExact
