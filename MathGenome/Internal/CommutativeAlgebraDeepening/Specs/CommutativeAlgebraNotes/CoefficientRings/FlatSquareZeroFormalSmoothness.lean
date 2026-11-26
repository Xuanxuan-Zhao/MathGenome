import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Smooth.Basic

namespace Specs.CommutativeAlgebraNotes.CoefficientRings

universe u v

/-- The second assertion of C01. The ideal `K.map (algebraMap A B)` is the
extension of `K` to `B`, and the quotient algebra structure is the canonical one. -/
def flatSquareZeroFormalSmoothness : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (K : Ideal A), K ^ 2 = ⊥ →
      Algebra.FormallySmooth (A ⧸ K) (B ⧸ K.map (algebraMap A B)) →
      Algebra.FormallySmooth A B

end Specs.CommutativeAlgebraNotes.CoefficientRings
