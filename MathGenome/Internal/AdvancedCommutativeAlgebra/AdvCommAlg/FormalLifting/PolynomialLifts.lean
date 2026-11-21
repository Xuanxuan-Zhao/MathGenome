import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.PolynomialLifts

/-! FL-05: lift the images of the variables, then evaluate at those lifts.
This works for every surjection, so in particular for square-zero quotients.
-/
namespace AdvCommAlg.FormalLifting

universe u v w z

open Specs.AdvCommAlg.FormalLifting

/-- Every map out of a polynomial algebra lifts along a surjective algebra map. -/
theorem polynomial_lifts : polynomialSurjectionLifts.{u,v,w,z} := by
  intro A Λ C D _ _ _ _ _ q hq f
  let x : Λ → C := fun i => Classical.choose (hq (f (MvPolynomial.X i)))
  refine ⟨MvPolynomial.aeval x, MvPolynomial.algHom_ext fun i => ?_⟩
  change q (MvPolynomial.aeval x (MvPolynomial.X i)) = f (MvPolynomial.X i)
  rw [MvPolynomial.aeval_X]
  exact Classical.choose_spec (hq (f (MvPolynomial.X i)))

/-- A polynomial algebra on an arbitrary variable type is formally smooth. -/
theorem polynomial_formallySmooth : polynomialFormallySmooth.{u,v} := by
  intro A Λ _
  change FormallySmooth A (MvPolynomial Λ A)
  intro C _ _ N _ f
  exact polynomial_lifts A Λ C (C ⧸ N) (Ideal.Quotient.mkₐ A N)
    Ideal.Quotient.mk_surjective f

end AdvCommAlg.FormalLifting
