import MathGenome.Internal.Specs.D07.Ch19.SturmChainSquarefreeReduction
import MathGenome.Internal.D07.Ch12.CharacteristicZeroSeparability
import Mathlib.RingTheory.Polynomial.Radical

noncomputable section

namespace D07.Ch19.SturmChainSquarefreeReduction

open Polynomial UniqueFactorizationMonoid
open EuclideanDomain (divRadical divRadical_dvd_self divRadical_mul_radical divRadical_ne_zero)
open scoped Classical

variable {K : Type*} [Field K]

/-- Dividing by the derivative gcd leaves a divisor of the product of
all distinct irreducible factors. This holds even in positive characteristic. -/
theorem reduction_dvd_radical {f : Polynomial K} (hf : f ≠ 0) :
    f / gcd f f.derivative ∣ radical f := by
  have hd : gcd f f.derivative ≠ 0 := gcd_ne_zero_of_left hf
  have ht : divRadical f ∣ gcd f f.derivative :=
    dvd_gcd (divRadical_dvd_self f) (divRadical_dvd_derivative f)
  obtain ⟨u, hu⟩ := ht
  have heq : divRadical f * (u * (f / gcd f f.derivative)) =
      divRadical f * radical f := by
    rw [← mul_assoc, ← hu, EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left _ _),
      divRadical_mul_radical]
  have heq' := mul_left_cancel₀ (divRadical_ne_zero hf) heq
  exact ⟨u, heq'.symm.trans (mul_comm _ _)⟩

/-- The radical argument does not use a splitting field. -/
theorem reduction_squarefree_of_ne_zero {f : Polynomial K} (hf : f ≠ 0) :
    Squarefree (f / gcd f f.derivative) :=
  squarefree_radical.squarefree_of_dvd (reduction_dvd_radical hf)

/-- In characteristic zero squarefreeness implies coprimality with the derivative.
We use the upstream characteristic-zero theorem only for irreducible factors. -/
theorem separable_of_squarefree [CharZero K] {s : Polynomial K} (hs : Squarefree s) :
    s.Separable := by
  apply isCoprime_of_irreducible_dvd (fun h => hs.ne_zero h.1)
  rintro p hp ⟨q, rfl⟩ hpd
  have hsep : p.Separable :=
    Ch12.CharacteristicZeroSeparability.irreducible_polynomial_separable K p hp
  have hpq : p ∣ q := by
    rw [derivative_mul, dvd_add_left (dvd_mul_right p _)] at hpd
    exact hsep.dvd_of_dvd_mul_left hpd
  exact hp.not_isUnit (hs p (mul_dvd_mul_left p hpq))

/-- The gcd has smaller degree than f, so the quotient stays nonconstant. -/
theorem reduction_natDegree_pos [CharZero K] {f : Polynomial K}
    (hf : 0 < f.natDegree) : 0 < (f / gcd f f.derivative).natDegree := by
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf
  have hdf : f.derivative ≠ 0 := derivative_ne_zero.mpr hf.ne'
  have hd : gcd f f.derivative ≠ 0 := gcd_ne_zero_of_left hf0
  have hs : f / gcd f f.derivative ≠ 0 := left_div_gcd_ne_zero hf0
  have hlt : (gcd f f.derivative).natDegree < f.natDegree :=
    (natDegree_le_of_dvd (gcd_dvd_right _ _) hdf).trans_lt (natDegree_derivative_lt hf.ne')
  have heq : (gcd f f.derivative).natDegree + (f / gcd f f.derivative).natDegree =
      f.natDegree := by
    rw [← natDegree_mul hd hs, EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left _ _)]
  omega

/-- A real root of f is retained by the quotient: f divides f' times
that quotient, and formal differentiation lowers root multiplicity by one. -/
theorem reduction_eval_eq_zero_iff [CharZero K] {f : Polynomial K}
    (hf : f ≠ 0) (a : K) :
    (f / gcd f f.derivative).eval a = 0 ↔ f.eval a = 0 := by
  have hd : gcd f f.derivative ≠ 0 := gcd_ne_zero_of_left hf
  have hmul := EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left f f.derivative)
  constructor
  · intro ha
    exact (show (f / gcd f f.derivative).IsRoot a from ha).dvd
      (EuclideanDomain.div_dvd_of_dvd (gcd_dvd_left _ _))
  · intro ha
    apply isRoot_of_isRoot_of_dvd_derivative_mul hf _ ha
    obtain ⟨t, ht⟩ := gcd_dvd_right f f.derivative
    refine ⟨t, ?_⟩
    nth_rw 1 [ht]
    rw [mul_right_comm, hmul]

open Specs.D07.Ch19.SturmChainSquarefreeReduction

theorem monic_gcd_specification : MonicGcdSpecification := by
  intro f hf
  have hd : gcd f f.derivative ≠ 0 := gcd_ne_zero_of_left (ne_zero_of_natDegree_gt hf)
  refine ⟨?_, gcd_dvd_left _ _, gcd_dvd_right _ _, fun q hq hq' => dvd_gcd hq hq'⟩
  simpa only [normalize_gcd] using monic_normalize hd

theorem reduction_nonconstant : ReductionNonconstant := by
  intro f hf
  exact reduction_natDegree_pos hf

theorem reduction_roots : ReductionRoots := by
  intro f hf a
  exact reduction_eval_eq_zero_iff (ne_zero_of_natDegree_gt hf) a

theorem reduction_squarefree : ReductionSquarefree := by
  intro f hf
  exact reduction_squarefree_of_ne_zero (ne_zero_of_natDegree_gt hf)

theorem reduction_no_repeated_irreducible : ReductionNoRepeatedIrreducible := by
  intro f hf p hp hdiv
  exact hp.not_isUnit (reduction_squarefree f hf p (by simpa only [pow_two] using hdiv))

theorem reduction_gcd_one : ReductionGcdOne := by
  intro f hf
  have hsep := separable_of_squarefree (reduction_squarefree f hf)
  change gcd _ _ = 1
  rw [← normalize_gcd, normalize_eq_one]
  exact (gcd_isUnit_iff _ _).mpr hsep

theorem reduction_multiplicity : ReductionMultiplicity := by
  intro f hf a
  have hsep := separable_of_squarefree (reduction_squarefree f hf)
  have hle := rootMultiplicity_le_one_of_separable hsep a
  split_ifs with ha
  · have hroot : (f / gcd f f.derivative).IsRoot a := (reduction_roots f hf a).mpr ha
    have hpos := (rootMultiplicity_pos hsep.ne_zero).mpr hroot
    omega
  · exact rootMultiplicity_eq_zero (fun h => ha ((reduction_roots f hf a).mp h))

/-- Transfer from the normalized gcd to the source's arbitrary monic gcd. -/
theorem reduction_for_monic_gcd : ReductionForMonicGcd := by
  intro f hf d hd hdf hdf' hgreatest
  have hcanonical := monic_gcd_specification f hf
  have heq : d = gcd f f.derivative :=
    eq_of_monic_of_associated hd hcanonical.1
      (associated_of_dvd_dvd (dvd_gcd hdf hdf')
        (hgreatest _ hcanonical.2.1 hcanonical.2.2.1))
  subst d
  exact ⟨EuclideanDomain.mul_div_cancel'
      (gcd_ne_zero_of_left (ne_zero_of_natDegree_gt hf)) (gcd_dvd_left _ _),
    reduction_nonconstant f hf, reduction_roots f hf, reduction_squarefree f hf,
    reduction_no_repeated_irreducible f hf, reduction_gcd_one f hf,
    reduction_multiplicity f hf⟩

end D07.Ch19.SturmChainSquarefreeReduction
