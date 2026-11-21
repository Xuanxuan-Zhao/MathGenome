import MathGenome.Internal.Specs.D05.M08.Minpoly
import MathGenome.Internal.D05.M08.Annihilating
import MathGenome.Internal.D05.Foundations.IdealsGcd
import Mathlib.FieldTheory.Minpoly.Field

/-! The minimal polynomial of a finite-dimensional endomorphism, including
the zero-space convention, as in K05.08.minpoly. -/

noncomputable section

namespace D05.M08.Minpoly

/-- The canonical minimal polynomial, with its ideal-generator interpretation
proved below. -/
def minimalPolynomial (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V) : Polynomial K :=
  minpoly K T

/-- The upstream finite relation supplies algebraicity; over a field it can
be normalized to a monic relation, even in the zero endomorphism algebra. -/
theorem endomorphism_isIntegral {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (T : Module.End K V) : IsIntegral K T := by
  obtain ⟨p, hp, _, hmem⟩ := Annihilating.exists_nonzero_annihilator T
  exact IsAlgebraic.isIntegral ⟨p, hp, (Annihilating.mem_annihilator T p).mp hmem⟩

theorem monic : Specs.D05.M08.Minpoly.monic := by
  intro K V _ _ _ _ T
  exact minpoly.monic (endomorphism_isIntegral T)

theorem ne_zero : Specs.D05.M08.Minpoly.ne_zero := by
  intro K V _ _ _ _ T
  exact (monic T).ne_zero

theorem annihilates : Specs.D05.M08.Minpoly.annihilates := by
  intro K V _ _ _ _ T
  exact minpoly.aeval K T

theorem divides_iff_annihilates : Specs.D05.M08.Minpoly.divides_iff_annihilates := by
  intro K V _ _ _ _ T p
  exact minpoly.dvd_iff

theorem ideal_generated : Specs.D05.M08.Minpoly.ideal_generated := by
  intro K V _ _ _ _ T
  ext p
  exact (divides_iff_annihilates T p).symm.trans Ideal.mem_span_singleton.symm

theorem unique_monic_generator : Specs.D05.M08.Minpoly.unique_monic_generator := by
  intro K V _ _ _ _ T
  refine ⟨minimalPolynomial K V T, ⟨monic T, ideal_generated T⟩, ?_⟩
  intro p hp
  exact Foundations.IdealsGcd.monic_generators_eq hp.1 (monic T)
    (hp.2.symm.trans (ideal_generated T))

theorem least_degree : Specs.D05.M08.Minpoly.least_degree := by
  intro K V _ _ _ _ T p hp hp0
  exact Polynomial.natDegree_le_of_dvd ((divides_iff_annihilates T p).mpr hp) hp0

theorem multiples_annihilate : Specs.D05.M08.Minpoly.multiples_annihilate := by
  intro K V _ _ _ _ T q
  change Polynomial.aeval T (q * minpoly K T) = 0
  rw [map_mul, minpoly.aeval, mul_zero]

theorem zero_space : Specs.D05.M08.Minpoly.zero_space := by
  intro K V _ _ _ _ _ T
  exact minpoly.subsingleton K T

theorem zero_dimension : Specs.D05.M08.Minpoly.zero_dimension := by
  intro K V _ _ _ _ T h
  have hzero := D05.M02.Dimension.dimension_zero_iff_zero_space.mp h
  let : Subsingleton V := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  exact zero_space T

theorem positive_degree : Specs.D05.M08.Minpoly.positive_degree := by
  intro K V _ _ _ _ T h
  let : Nontrivial V := Module.nontrivial_of_finrank_pos h
  exact minpoly.natDegree_pos (endomorphism_isIntegral T)

theorem nonzero_constant_not_annihilator :
    Specs.D05.M08.Minpoly.nonzero_constant_not_annihilator := by
  intro K V _ _ _ _ T h a ha hmem
  have hle := least_degree T (Polynomial.C a) hmem (Polynomial.C_ne_zero.mpr ha)
  have hpos := positive_degree T h
  rw [Polynomial.natDegree_C] at hle
  exact Nat.not_succ_le_zero 0 (hpos.trans hle)

end D05.M08.Minpoly
