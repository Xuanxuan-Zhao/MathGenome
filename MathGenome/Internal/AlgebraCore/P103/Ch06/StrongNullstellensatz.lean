import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.StrongNullstellensatz

/-!
The geometric part of Theorem 6.7. Mathlib's Nullstellensatz is stated
using singleton vanishing ideals; the kernel identity below identifies
these with the evaluation kernels in the source. Its finite-variable
hypothesis holds for every `Fin n`, including `Fin 0`.
-/
namespace P103.Ch06.StrongNullstellensatz

open P103.Specs.Ch06.StrongNullstellensatz

universe u

private theorem evaluation_kernel_eq_vanishingIdeal
    (k : Type u) [Field k] (n : ℕ) (x : Fin n → k) :
    RingHom.ker (MvPolynomial.eval x) = MvPolynomial.vanishingIdeal k {x} := by
  ext p
  exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).symm

theorem maximal_iff_evaluation_kernel : maximal_iff_evaluation_kernelType.{u} := by
  intro k _ _ n m
  simpa only [evaluation_kernel_eq_vanishingIdeal] using
    (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton
      (K := k) (I := m))

theorem evaluation_kernel_maximal : evaluation_kernel_maximalType.{u} := by
  intro k _ n x
  rw [evaluation_kernel_eq_vanishingIdeal]
  infer_instance

theorem vanishingIdeal_zeroLocus : vanishingIdeal_zeroLocusType.{u} := by
  intro k _ _ n J
  exact MvPolynomial.vanishingIdeal_zeroLocus_eq_radical J

theorem unit_ideal : unit_idealType.{u} := by
  intro k _ n
  have h : MvPolynomial.zeroLocus k (⊤ : Ideal (MvPolynomial (Fin n) k)) = ∅ :=
    MvPolynomial.zeroLocus_top
  exact ⟨h, h ▸ MvPolynomial.vanishingIdeal_empty⟩

theorem vanishingIdeal_empty : vanishingIdeal_emptyType.{u} := by
  intro k _ n
  exact MvPolynomial.vanishingIdeal_empty

theorem zero_variables : zero_variablesType.{u} := by
  intro k _
  ext x
  simp only [Set.mem_univ, Set.mem_singleton_iff, true_iff]
  exact funext fun i => Fin.elim0 i

end P103.Ch06.StrongNullstellensatz
