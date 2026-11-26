import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Smooth.Quotient

namespace CommutativeAlgebraNotes.CoefficientRings

/-- A flat algebra is formally smooth if its reduction along a square-zero ideal
of the base is formally smooth over the corresponding quotient of the base. -/
theorem formallySmooth_of_flat_of_squareZero_quotient
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (K : Ideal A) (hK : K ^ 2 = ⊥)
    (hSmooth : Algebra.FormallySmooth (A ⧸ K) (B ⧸ K.map (algebraMap A B))) :
    Algebra.FormallySmooth A B := by
  refine Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat
    (R' := A ⧸ K) (S' := B ⧸ K.map (algebraMap A B))
    Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective ?_ ?_ hSmooth
  · simp only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  · simpa only [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker] using hK

end CommutativeAlgebraNotes.CoefficientRings
