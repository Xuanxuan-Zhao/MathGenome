import MathGenome.Internal.Specs.D05.M10.SemisimpleDecomposition.NilpotentLift
import MathGenome.Internal.D05.M10.SemisimpleDecomposition.Units
import MathGenome.Internal.D05.Foundations.DifferentiationTaylor
import MathGenome.Internal.D05.Foundations.QuotientBasisUnits
import MathGenome.Internal.D05.M10.Semisimple.ScalarExtension
import Mathlib.Tactic.Ring

/-! A finite Newton construction inside the original polynomial quotient.
No semisimple part is assumed. The general ideal estimates also apply to
commutative algebras in arbitrary characteristic. -/
noncomputable section
namespace D05.M10.SemisimpleDecomposition.NilpotentLift
open Polynomial
open D05.Specs.M10.SemisimpleDecomposition.NilpotentLift

variable {K : Type*} [Field K]

/-- Distinct monic irreducibles have a separable product in characteristic zero. -/
theorem product_separable [CharZero K] {n : ℕ} (p : Fin n → K[X])
    (hm : ∀ i, (p i).Monic) (hi : ∀ i, Irreducible (p i))
    (hinj : Function.Injective p) : (squarefreePart p).Separable := by
  apply Polynomial.separable_prod
  · intro i j hij
    apply (hi i).coprime_iff_not_dvd.mpr
    intro hd
    exact hij (hinj (Polynomial.eq_of_monic_of_associated (hm i) (hm j)
      ((hi i).associated_of_dvd (hi j) hd)))
  · intro i
    exact (D05.M10.Semisimple.ScalarExtension.irreducible_derivative (p i) (hi i)).2.2

/-- The largest exponent bounds every factor exponent, including an empty family. -/
theorem modulus_dvd_power {n : ℕ} (p : Fin n → K[X]) (a : Fin n → ℕ) :
    modulus p a ∣ squarefreePart p ^ maxExponent a := by
  rw [squarefreePart, ← Finset.prod_pow]
  apply Finset.prod_dvd_prod_of_dvd
  intro i _
  exact pow_dvd_pow (p i) (Finset.le_sup (Finset.mem_univ i))

theorem factorizationProperties :
    D05.Specs.M10.SemisimpleDecomposition.NilpotentLift.factorizationProperties := by
  intro K _ _ n hn p a hm hi hinj ha
  have hmm : (modulus p a).Monic := monic_prod_of_monic _ _ (fun i _ => (hm i).pow (a i))
  have hfm : squarefreePart p ∣ modulus p a :=
    Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => dvd_pow_self (p i) (by have := ha i; omega))
  let i : Fin n := ⟨0, hn⟩
  have hpi : p i ∣ modulus p a :=
    (Finset.dvd_prod_of_mem p (Finset.mem_univ i)).trans hfm
  have hdeg : 0 < (modulus p a).natDegree := by
    exact lt_of_lt_of_le (hi i).natDegree_pos
      (Polynomial.natDegree_le_of_dvd hpi hmm.ne_zero)
  refine ⟨hmm, hdeg, monic_prod_of_monic _ _ (fun i _ => hm i),
    product_separable p hm hi hinj, hfm, modulus_dvd_power p a, ?_⟩
  exact lt_of_lt_of_le (ha i) (Finset.le_sup (Finset.mem_univ i))

theorem idealNilpotent :
    D05.Specs.M10.SemisimpleDecomposition.NilpotentLift.idealNilpotent := by
  intro K _ n p a
  change Ideal.span {AdjoinRoot.mk (modulus p a) (squarefreePart p)} ^ maxExponent a = ⊥
  rw [Ideal.span_singleton_pow, ← map_pow,
    AdjoinRoot.mk_eq_zero.mpr (modulus_dvd_power p a)]
  simp

/-- Polynomial evaluation respects congruence modulo any ideal. -/
theorem eval_sub_mem {A : Type*} [CommRing A] [Algebra K A]
    (f : K[X]) (J : Ideal A) {y x : A} (h : y - x ∈ J) :
    aeval y f - aeval x f ∈ J := by
  have hd := Polynomial.sub_dvd_eval_sub y x (f.map (algebraMap K A))
  simp only [Polynomial.eval_map, ← Polynomial.aeval_def] at hd
  obtain ⟨q, hq⟩ := hd
  rw [hq]
  exact J.mul_mem_right q h

/-- Nilpotence lifts a unit at x to all elements congruent to x. -/
theorem derivative_unit_of_congruent {A : Type*} [CommRing A] [Algebra K A]
    (f : K[X]) (J : Ideal A) (hJ : IsNilpotent J) {x y : A}
    (hu : IsUnit (aeval x f.derivative)) (h : y - x ∈ J) :
    IsUnit (aeval y f.derivative) := by
  apply Units.isUnitOfIsUnitQuotient A J hJ
  have he : Ideal.Quotient.mk J (aeval y f.derivative) =
      Ideal.Quotient.mk J (aeval x f.derivative) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (eval_sub_mem _ J h)
  rw [he]
  exact hu.map (Ideal.Quotient.mk J)

theorem derivativeUnit :
    D05.Specs.M10.SemisimpleDecomposition.NilpotentLift.derivativeUnit := by
  intro K _ _ n p a hm hi hinj y hy
  have hc : IsCoprime (squarefreePart p).derivative (modulus p a) :=
    ((product_separable p hm hi hinj).symm.pow_right (n := maxExponent a)).of_isCoprime_of_dvd_right
      (modulus_dvd_power p a)
  have hu : IsUnit (aeval (AdjoinRoot.root (modulus p a)) (squarefreePart p).derivative) := by
    rw [AdjoinRoot.aeval_eq]
    exact (D05.Foundations.QuotientBasisUnits.isUnit_mk_iff_isCoprime _ _).mpr hc
  exact derivative_unit_of_congruent _ _ ⟨maxExponent a, by
    simpa only [Ideal.zero_eq_bot] using idealNilpotent K n p a⟩ hu hy

/-- Taylor's quadratic term is the whole remaining Newton error. -/
theorem newton_error {A : Type*} [CommRing A] [Algebra K A]
    (f : K[X]) (y : A) (hu : IsUnit (aeval y f.derivative)) :
    ∃ q : A, aeval (newtonStep f y) f =
      (-(aeval y f * Ring.inverse (aeval y f.derivative))) ^ 2 * q := by
  obtain ⟨P, _, hP⟩ := D05.Foundations.DifferentiationTaylor.evaluatedQuadraticRemainder K f
  let h := -(aeval y f * Ring.inverse (aeval y f.derivative))
  refine ⟨P.eval₂ (aeval y).toRingHom h, ?_⟩
  have ht := hP A y h (Commute.all _ _)
  have hc : aeval y f + h * aeval y f.derivative = 0 := by
    dsimp [h]
    rw [neg_mul, mul_assoc, Ring.inverse_mul_cancel _ hu]
    simp
  simpa only [h, ← sub_eq_add_neg, newtonStep] using (ht.trans (by rw [hc, zero_add]))

theorem newtonImproves :
    D05.Specs.M10.SemisimpleDecomposition.NilpotentLift.newtonImproves := by
  intro K A _ _ _ f J y s _hs hu hf
  have hh : -(aeval y f * Ring.inverse (aeval y f.derivative)) ∈ J ^ s :=
    (J ^ s).neg_mem ((J ^ s).mul_mem_right _ hf)
  refine ⟨?_, ?_⟩
  · simpa [newtonStep] using hh
  · obtain ⟨q, hq⟩ := newton_error f y hu
    rw [hq]
    have hp := Ideal.pow_mem_pow hh 2
    rw [← pow_mul, Nat.mul_comm s 2] at hp
    exact (J ^ (2 * s)).mul_mem_right q hp

/-- Congruence, invertibility, and the precise error bound at every finite stage. -/
theorem iteration_properties {A : Type*} [CommRing A] [Algebra K A]
    (f : K[X]) (J : Ideal A) (x : A) (hJ : IsNilpotent J)
    (hu : IsUnit (aeval x f.derivative)) (hf : aeval x f ∈ J) :
    ∀ j, newtonIter f x j - x ∈ J ∧
      IsUnit (aeval (newtonIter f x j) f.derivative) ∧
      aeval (newtonIter f x j) f ∈ J ^ (2 ^ j) := by
  intro j
  induction j with
  | zero => simpa only [newtonIter, sub_self, pow_zero, pow_one] using
      And.intro (J.zero_mem) (And.intro hu hf)
  | succ j ih =>
    obtain ⟨hstep, herr⟩ := newtonImproves K A f J (newtonIter f x j) (2 ^ j)
      Nat.one_le_two_pow ih.2.1 ih.2.2
    have hcong : newtonIter f x (j + 1) - x ∈ J := by
      have he : newtonIter f x (j + 1) - x =
          (newtonStep f (newtonIter f x j) - newtonIter f x j) +
          (newtonIter f x j - x) := by rw [newtonIter]; ring
      rw [he]
      exact J.add_mem ((Ideal.pow_le_self (by positivity : (2 : ℕ) ^ j ≠ 0)) hstep) ih.1
    refine ⟨hcong, derivative_unit_of_congruent f J hJ hu hcong, ?_⟩
    simpa only [newtonIter, pow_succ, Nat.mul_comm] using herr

theorem finiteLift :
    D05.Specs.M10.SemisimpleDecomposition.NilpotentLift.finiteLift := by
  intro K _ _ n hn p a hm hi hinj ha
  let m := modulus p a
  let f := squarefreePart p
  let r := maxExponent a
  let J := radicalIdeal p a
  let x := AdjoinRoot.root m
  have hJ : J ^ r = ⊥ := idealNilpotent K n p a
  have hnil : IsNilpotent J := ⟨r, by simpa only [Ideal.zero_eq_bot] using hJ⟩
  have hf : aeval x f ∈ J := by
    rw [AdjoinRoot.aeval_eq]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hu : IsUnit (aeval x f.derivative) :=
    derivativeUnit K n p a hm hi hinj x (by change x - x ∈ J; rw [sub_self]; exact J.zero_mem)
  have hit := iteration_properties f J x hnil hu hf
  refine ⟨hit, ?_⟩
  let y := newtonIter f x r
  obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective y
  have hbound : r ≤ 2 ^ r := Nat.lt_two_pow_self.le
  have hroot : aeval y f = 0 := by
    have he := Ideal.pow_le_pow_right (I := J) hbound ((hit r).2.2)
    simpa only [hJ, Ideal.mem_bot] using he
  have hdiff : (x - y) ^ r = 0 := by
    have hd : x - y ∈ J := by simpa only [neg_sub] using J.neg_mem (hit r).1
    have he := Ideal.pow_mem_pow hd r
    simpa only [hJ, Ideal.mem_bot] using he
  exact ⟨r, y, g, le_rfl, hbound, rfl, (hit r).1, hroot, hg, hdiff⟩

end D05.M10.SemisimpleDecomposition.NilpotentLift
