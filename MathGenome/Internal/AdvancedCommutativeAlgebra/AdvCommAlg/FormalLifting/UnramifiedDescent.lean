import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.UnramifiedDescent
import Mathlib.RingTheory.Etale.Descent

/-! Faithfully flat descent of the uniqueness assertion in FL-17.
Mathlib's descent theorem uses vanishing of differentials, arbitrary base
change for differentials, and faithful detection of zero modules.  The
accepted FL-01 equivalence transfers it to the square-zero lifting property.
-/
namespace AdvCommAlg.FormalLifting

open TensorProduct

universe u v w

/-- Formal unramifiedness descends along a faithfully flat extension of
the base ring, without any finiteness hypothesis on the algebra. -/
theorem formallyUnramified_of_faithfullyFlat
    (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] [Module.FaithfullyFlat A A']
    (h : FormallyUnramified A' (A' ⊗[A] B)) : FormallyUnramified A B := by
  let : Algebra.FormallyUnramified A' (A' ⊗[A] B) :=
    (formallyUnramified_iff A' (A' ⊗[A] B)).mp h
  have hdesc : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat
      (R := A) (S := B) A'
  apply (formallyUnramified_iff A B).mpr
  exact hdesc

end AdvCommAlg.FormalLifting
