import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Definitions
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval

/-! The unnumbered order example after RK-02, paper.tex:2149–2152.
The indices 0, 1, 2 denote X, Y, Z respectively. -/
noncomputable section
universe u
namespace AdvCommAlg.RegularSequence.OrderExample

abbrev Poly (k : Type u) [CommSemiring k] := MvPolynomial (Fin 3) k
abbrev X {k : Type u} [Field k] : Poly k := MvPolynomial.X 0
abbrev Y {k : Type u} [Field k] : Poly k := MvPolynomial.X 1
abbrev Z {k : Type u} [Field k] : Poly k := MvPolynomial.X 2

namespace Specs

def ordered_regularType : Prop :=
  ∀ (k : Type u) [Field k],
    RingTheory.Sequence.IsRegular (Poly k) ([X, Y * (1 - X), Z * (1 - X)] : List (Poly k))

def rotated_not_weaklyRegularType : Prop :=
  ∀ (k : Type u) [Field k],
    ¬ RingTheory.Sequence.IsWeaklyRegular (Poly k) ([Y * (1 - X), Z * (1 - X), X] : List (Poly k))

def class_Y_nonzero_and_annihilatedType : Prop :=
  ∀ (k : Type u) [Field k],
    let I : Ideal (Poly k) := Ideal.span {Y * (1 - X)}
    Ideal.Quotient.mk I Y ≠ 0 ∧
      Ideal.Quotient.mk I (Z * (1 - X)) * Ideal.Quotient.mk I Y = 0

end Specs
end AdvCommAlg.RegularSequence.OrderExample
