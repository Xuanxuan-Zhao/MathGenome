import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.FieldFormalSmoothness
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.FlatSquareZeroFormalSmoothness

namespace CommutativeAlgebraNotes.CoefficientRings

universe u v w

/-- Every field is formally smooth over its prime subfield. A flat algebra is
formally smooth if its reduction over a square-zero ideal is formally smooth. -/
theorem formalSmoothLiftingFacts :
    (∀ (L : Type u) [Field L], Algebra.FormallySmooth (↥(⊥ : Subfield L)) L) ∧
    (∀ {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
      (K : Ideal A), K ^ 2 = ⊥ →
        Algebra.FormallySmooth (A ⧸ K) (B ⧸ K.map (algebraMap A B)) →
        Algebra.FormallySmooth A B) := by
  constructor
  · intro L _
    exact primeSubfieldFormallySmooth L
  · intro A B _ _ _ _ K hK hSmooth
    exact formallySmooth_of_flat_of_squareZero_quotient K hK hSmooth

end CommutativeAlgebraNotes.CoefficientRings
