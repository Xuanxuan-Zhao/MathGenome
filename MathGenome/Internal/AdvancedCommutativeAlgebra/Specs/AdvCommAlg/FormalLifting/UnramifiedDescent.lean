import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! FL-17, paper.tex:871–883, uniqueness descent.  The tensor product
uses the left A'-algebra structure.  Formal unramifiedness means uniqueness
of square-zero lifts, as in FL-01.  There is no finiteness or nonzero-ring
assumption.  The finite-presentation qualification in FL-17 applies only
to the separately allocated smoothness and étaleness assertions. -/
namespace Specs.AdvCommAlg.FormalLifting

open TensorProduct

universe u v w

/-- Uniqueness of square-zero lifts descends under any faithfully flat
extension of the base, for every commutative A-algebra B. -/
def unramifiedDescent : Prop :=
  ∀ (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] [Module.FaithfullyFlat A A'],
    formallyUnramifiedValue A' (A' ⊗[A] B) → formallyUnramifiedValue A B

end Specs.AdvCommAlg.FormalLifting
