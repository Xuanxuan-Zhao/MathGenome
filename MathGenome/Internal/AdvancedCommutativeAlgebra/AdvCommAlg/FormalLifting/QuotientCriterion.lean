import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.EtaleCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.SurjectiveBase
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.QuotientCriterion

/-! The quotient assertion of FL-12, with arbitrary ideals and no
finite generation or nonzero-ring assumptions. -/
namespace AdvCommAlg.FormalLifting

universe u

/-- Every quotient map is formally unramified. -/
theorem quotient_formallyUnramified (A : Type u) [CommRing A] (I : Ideal A) :
    FormallyUnramified A (A ⧸ I) := by
  exact (formallyUnramified_iff_subsingleton_omega A (A ⧸ I)).mpr
    (Differentials.subsingleton_quotient A I)

/-- The surjective-map smoothness criterion specializes to `I = I²`.
Here idempotence refers to multiplication of ideals, without requiring
the ideal to have an idempotent generator. -/
theorem quotient_formallySmooth_iff (A : Type u) [CommRing A] (I : Ideal A) :
    FormallySmooth A (A ⧸ I) ↔ I = I ^ 2 := by
  refine (formallySmooth_iff A (A ⧸ I)).trans ?_
  rw [Algebra.FormallySmooth.iff_of_surjective
      (show Function.Surjective (algebraMap A (A ⧸ I)) from
        Ideal.Quotient.mk_surjective),
    Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  simp only [IsIdempotentElem, pow_two, eq_comm]

/-- For a quotient map, existence of lifts already implies uniqueness. -/
theorem quotient_formallySmooth_iff_formallyEtale
    (A : Type u) [CommRing A] (I : Ideal A) :
    FormallySmooth A (A ⧸ I) ↔ FormallyEtale A (A ⧸ I) := by
  rw [formallyEtale_iff_formallySmooth_and_subsingleton_omega]
  exact (and_iff_left (Differentials.subsingleton_quotient A I)).symm

/-- Formal étaleness of a quotient is equivalent to idempotence of its ideal. -/
theorem quotient_formallyEtale_iff (A : Type u) [CommRing A] (I : Ideal A) :
    FormallyEtale A (A ⧸ I) ↔ I = I ^ 2 := by
  exact (quotient_formallySmooth_iff_formallyEtale A I).symm.trans
    (quotient_formallySmooth_iff A I)

/-- Nonzero square-zero ideals cannot define formally smooth quotients. -/
theorem quotient_not_formallySmooth_of_square_zero
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I ≠ ⊥) (hI2 : I ^ 2 = ⊥) :
    ¬ FormallySmooth A (A ⧸ I) := by
  intro h
  exact hI (((quotient_formallySmooth_iff A I).mp h).trans hI2)

end AdvCommAlg.FormalLifting
