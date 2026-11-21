import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.FinitePresentationDescent
import Mathlib.RingTheory.Finiteness.Descent
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.FaithfullyFlatDescent

/-! ET-14: faithfully flat descent of étaleness. We first descend finite
presentation, then apply FL-17 to descend the square-zero lifting property.
There is no finiteness hypothesis on the faithfully flat base extension. -/
namespace AdvCommAlg.Etale

open TensorProduct

universe u v w

/-- If A' is faithfully flat over A and A' ⊗[A] B is étale over A',
then B is étale over A, including finite presentation over A. -/
theorem etale_of_faithfullyFlat :
    Specs.AdvCommAlg.Etale.faithfullyFlatDescent.{u,v,w} := by
  intro A A' B _ _ _ _ _ _ h
  obtain ⟨hfin, hformal⟩ := (etale_iff A' (A' ⊗[A] B)).mp h
  let : Algebra.FinitePresentation A' (A' ⊗[A] B) := hfin
  let : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
      (R := A) (S := B) A'
  exact (etale_iff A B).mpr ⟨inferInstance,
    FormalLifting.formallyEtale_of_faithfullyFlat A A' B hformal⟩

end AdvCommAlg.Etale
