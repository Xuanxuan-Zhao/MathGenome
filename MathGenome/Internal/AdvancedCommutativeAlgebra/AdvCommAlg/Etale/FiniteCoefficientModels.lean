import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.FiniteCoefficientModels
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-! The first assertion of ET-15: finite coefficient models for étale algebras.

Mathlib's coefficient descent includes the relations, an inverse of the
Jacobian determinant, and a polynomial certificate for that inverse. Its
descended submersive presentation has the same relative dimension, hence
remains étale. The resulting tensor equivalence is an A-algebra equivalence.
-/
namespace AdvCommAlg.Etale

universe u v

/-- An étale A-algebra descends to an étale algebra over a finitely generated
ℤ-subalgebra of A, with its full algebra structure preserved by base change. -/
theorem finite_coefficient_models :
    Specs.AdvCommAlg.Etale.finiteCoefficientModels.{u,v} := by
  intro A B _ _ _ h
  haveI : Algebra.Etale A B := h
  exact Algebra.Etale.exists_subalgebra_fg ℤ A B

end AdvCommAlg.Etale
