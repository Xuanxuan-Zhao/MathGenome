import MathGenome.Internal.D05.M06.Invariant
import MathGenome.Internal.D05.M08.Evaluation
import MathGenome.Internal.D05.M09.Eigenspace
import MathGenome.Internal.Specs.D05.M09.CommutantInvariance

/-! K05.09.commutant_invariance: polynomial kernels and images are preserved
by commuting operators. The proofs also apply without finite dimension. -/

noncomputable section

namespace D05.M09.CommutantInvariance

open scoped BigOperators

/-- Powers commute by the elementary induction embodied by `Commute.pow_right`. -/
theorem commutes_powers : Specs.D05.M09.CommutantInvariance.commutes_powers := by
  intro K V _ _ _ S T h j
  exact (show Commute S T from h).pow_right j

/-- Extend commutation term by term in the finite coefficient expansion. -/
theorem commutes_polynomial : Specs.D05.M09.CommutantInvariance.commutes_polynomial := by
  intro K V _ _ _ S T h p
  rw [D05.M08.Evaluation.coefficient_sum T p, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_smul_comm, smul_mul_assoc, commutes_powers S T h j]

theorem shifted_power_evaluation :
    Specs.D05.M09.CommutantInvariance.shifted_power_evaluation := by
  intro K V _ _ _ T μ k
  change Polynomial.aeval T _ = _
  rw [map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  rfl

theorem polynomial_kernel_invariant :
    Specs.D05.M09.CommutantInvariance.polynomial_kernel_invariant := by
  intro K V _ _ _ S T h p x hx
  have hx0 := LinearMap.mem_ker.mp hx
  change (Specs.D05.M08.Evaluation.evaluation_value K V T p) (S x) = 0
  calc
    _ = S ((Specs.D05.M08.Evaluation.evaluation_value K V T p) x) :=
      (congrArg (fun f : Module.End K V => f x) (commutes_polynomial S T h p)).symm
    _ = 0 := by rw [hx0, map_zero]

theorem polynomial_image_invariant :
    Specs.D05.M09.CommutantInvariance.polynomial_image_invariant := by
  intro K V _ _ _ S T h p x hx
  obtain ⟨v, rfl⟩ := hx
  exact ⟨S v,
    (congrArg (fun f : Module.End K V => f v) (commutes_polynomial S T h p)).symm⟩

theorem shifted_power_kernel_invariant :
    Specs.D05.M09.CommutantInvariance.shifted_power_kernel_invariant := by
  intro K V _ _ _ S T h μ k
  have hp := polynomial_kernel_invariant S T h ((Polynomial.X - Polynomial.C μ) ^ k)
  rwa [shifted_power_evaluation T μ k] at hp

theorem eigenspace_invariant : Specs.D05.M09.CommutantInvariance.eigenspace_invariant := by
  intro K V _ _ _ S T h μ
  rw [D05.M09.Eigenspace.eigenspace_eq_kernel]
  simpa only [pow_one] using shifted_power_kernel_invariant S T h μ 1

theorem genEigenspace_invariant :
    Specs.D05.M09.CommutantInvariance.genEigenspace_invariant := by
  intro K V _ _ _ S T h μ k
  rw [Module.End.genEigenspace_nat]
  exact shifted_power_kernel_invariant S T h μ k

theorem generalized_eigenspace_invariant :
    Specs.D05.M09.CommutantInvariance.generalized_eigenspace_invariant := by
  intro K V _ _ _ _ S T h μ
  exact shifted_power_kernel_invariant S T h μ (Module.finrank K V)

theorem self_polynomial_kernel_invariant :
    Specs.D05.M09.CommutantInvariance.self_polynomial_kernel_invariant := by
  intro K V _ _ _ T p
  exact polynomial_kernel_invariant T T rfl p

theorem self_polynomial_image_invariant :
    Specs.D05.M09.CommutantInvariance.self_polynomial_image_invariant := by
  intro K V _ _ _ T p
  exact polynomial_image_invariant T T rfl p

end D05.M09.CommutantInvariance
