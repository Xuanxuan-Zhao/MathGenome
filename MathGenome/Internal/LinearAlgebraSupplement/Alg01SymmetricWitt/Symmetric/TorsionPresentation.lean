import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.TorsionPresentation
import MathGenome.Internal.LinearAlgebraSupplement.Alg01SymmetricWitt.Symmetric.Grading
import Mathlib.Algebra.Polynomial.Coeff

namespace Alg01SymmetricWitt.Symmetric.TorsionPresentation

open Polynomial
open scoped Polynomial DirectSum
open Alg01SymmetricWitt.Symmetric.Algebra (degree degreeMap)
open Specs.Alg01SymmetricWitt.Symmetric.TorsionPresentation
  (relationIdeal PolynomialQuotient quotientMap quotientDegree)

private abbrev Sym := SymmetricAlgebra ℤ (ZMod 2)
private abbrev generator : Sym := SymmetricAlgebra.ι ℤ (ZMod 2) 1

private theorem quotientMap_relation : quotientMap (C 2 * X) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

private theorem two_smul_quotientX : (2 : ℤ) • quotientMap X = 0 := by
  rw [zsmul_eq_mul]
  simpa only [map_mul, C_ofNat, map_ofNat, Int.cast_ofNat] using quotientMap_relation

private noncomputable def cyclicMap {A : Type*} [AddCommGroup A] (x : A)
    (hx : (2 : ℤ) • x = 0) : ZMod 2 →ₗ[ℤ] A :=
  (ZMod.lift 2 ⟨(LinearMap.toSpanSingleton ℤ A x).toAddMonoidHom, hx⟩).toIntLinearMap

private theorem cyclicMap_cast {A : Type*} [AddCommGroup A] (x : A)
    (hx : (2 : ℤ) • x = 0) (a : ℤ) : cyclicMap x hx (a : ZMod 2) = a • x :=
  ZMod.lift_coe 2 ⟨(LinearMap.toSpanSingleton ℤ A x).toAddMonoidHom, hx⟩ a

private theorem two_smul_generator : (2 : ℤ) • generator = 0 := by
  rw [← map_smul, show (2 : ℤ) • (1 : ZMod 2) = 0 by decide, map_zero]

private noncomputable def toQuotient : Sym →ₐ[ℤ] PolynomialQuotient :=
  SymmetricAlgebra.lift (cyclicMap (quotientMap X) two_smul_quotientX)

private theorem toQuotient_ι (a : ℤ) :
    toQuotient (SymmetricAlgebra.ι ℤ (ZMod 2) (a : ZMod 2)) = a • quotientMap X := by
  rw [toQuotient, SymmetricAlgebra.lift_ι_apply, cyclicMap_cast]

private theorem toQuotient_generator : toQuotient generator = quotientMap X := by
  simpa using toQuotient_ι 1

private noncomputable def polynomialEval : ℤ[X] →ₐ[ℤ] Sym := aeval generator

private theorem polynomialEval_relation : polynomialEval (C 2 * X) = 0 := by
  rw [map_mul]
  change aeval generator (C 2) * aeval generator X = 0
  rw [C_ofNat, map_ofNat, aeval_X]
  simpa only [zsmul_eq_mul, Int.cast_ofNat] using two_smul_generator

private theorem relationIdeal_le_evalKer : relationIdeal ≤ RingHom.ker polynomialEval.toRingHom :=
  (Ideal.span_singleton_le_iff_mem _).mpr polynomialEval_relation

private noncomputable def fromQuotient : PolynomialQuotient →ₐ[ℤ] Sym where
  __ := Ideal.Quotient.lift relationIdeal polynomialEval.toRingHom
    (fun _ hp => relationIdeal_le_evalKer hp)
  commutes' a := polynomialEval.commutes a

@[simp] private theorem fromQuotient_mk (p : ℤ[X]) :
    fromQuotient (quotientMap p) = polynomialEval p := rfl

/-- The algebra equivalence that sends the class of `1` to the class of `X`. -/
noncomputable def presentationEquiv : SymmetricAlgebra ℤ (ZMod 2) ≃ₐ[ℤ] PolynomialQuotient :=
  AlgEquiv.ofAlgHom toQuotient fromQuotient
    (by
      apply Ideal.Quotient.algHom_ext ℤ
      apply Polynomial.algHom_ext
      change toQuotient (fromQuotient (quotientMap X)) = quotientMap X
      rw [fromQuotient_mk, polynomialEval, aeval_X, toQuotient_generator])
    (by
      apply SymmetricAlgebra.algHom_ext
      ext x
      obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
      change fromQuotient (toQuotient (SymmetricAlgebra.ι ℤ (ZMod 2) (a : ZMod 2))) =
        SymmetricAlgebra.ι ℤ (ZMod 2) (a : ZMod 2)
      rw [toQuotient_ι, map_smul, fromQuotient_mk, polynomialEval, aeval_X, ← map_smul]
      congr 1
      simp [zsmul_eq_mul])

@[simp] theorem presentationEquiv_generator :
    presentationEquiv (SymmetricAlgebra.ι ℤ (ZMod 2) 1) = quotientMap X :=
  toQuotient_generator

private noncomputable def quotientMonomial (n : ℕ) : ℤ →ₗ[ℤ] PolynomialQuotient :=
  quotientMap.toLinearMap.comp (monomial n)

private theorem quotientDegree_eq_range (n : ℕ) :
    quotientDegree n = LinearMap.range (quotientMonomial n) :=
  (LinearMap.range_comp (monomial n) quotientMap.toLinearMap).symm

private theorem mem_quotientDegree_iff (n : ℕ) (p : PolynomialQuotient) :
    p ∈ quotientDegree n ↔ ∃ a : ℤ, quotientMap (monomial n a) = p := by
  rw [quotientDegree_eq_range, LinearMap.mem_range]
  rfl

private theorem quotientMonomial_mem (n : ℕ) (a : ℤ) :
    quotientMap (monomial n a) ∈ quotientDegree n :=
  (mem_quotientDegree_iff n _).2 ⟨a, rfl⟩

instance quotientGradedMonoid : SetLike.GradedMonoid quotientDegree where
  one_mem := by simpa using quotientMonomial_mem 0 1
  mul_mem := by
    intro i j a b ha hb
    obtain ⟨r, rfl⟩ := (mem_quotientDegree_iff i a).1 ha
    obtain ⟨s, rfl⟩ := (mem_quotientDegree_iff j b).1 hb
    rw [← map_mul, monomial_mul_monomial]
    exact quotientMonomial_mem _ _

private theorem toQuotient_ι_mem (x : ZMod 2) :
    toQuotient (SymmetricAlgebra.ι ℤ (ZMod 2) x) ∈ quotientDegree 1 := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  rw [toQuotient_ι, zsmul_eq_mul, ← map_intCast quotientMap, ← map_mul,
    ← C_eq_intCast, ← pow_one (X : ℤ[X]), C_mul_X_pow_eq_monomial]
  exact quotientMonomial_mem _ _

/-- The algebra equivalence carries each symmetric degree onto the corresponding quotient degree. -/
theorem presentationEquiv_map_degree (n : ℕ) :
    (degree ℤ (ZMod 2) n).map presentationEquiv.toLinearMap = quotientDegree n := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    rintro _ ⟨t, rfl⟩
    change toQuotient (degreeMap ℤ (ZMod 2) n t) ∈ quotientDegree n
    induction t using PiTensorProduct.induction_on with
    | smul_tprod a x =>
      rw [map_smul, map_smul]
      apply Submodule.smul_mem
      rw [Grading.degreeMap_tprod, map_prod]
      have h := SetLike.prod_mem_graded quotientDegree (fun _ : Fin n => (1 : ℕ))
        (fun i => toQuotient (SymmetricAlgebra.ι ℤ (ZMod 2) (x i)))
        (F := Finset.univ) (fun i _ => toQuotient_ι_mem (x i))
      simpa using h
    | add a b ha hb =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
  · intro p hp
    obtain ⟨a, rfl⟩ := (mem_quotientDegree_iff n p).1 hp
    have hg : generator ^ n ∈ degree ℤ (ZMod 2) n := by
      refine ⟨PiTensorProduct.tprod ℤ (fun _ : Fin n => (1 : ZMod 2)), ?_⟩
      rw [Grading.degreeMap_tprod]
      simp [generator]
    refine ⟨a • generator ^ n, Submodule.smul_mem _ _ hg, ?_⟩
    change presentationEquiv (a • generator ^ n) = quotientMap (monomial n a)
    rw [map_smul, map_pow, presentationEquiv_generator, zsmul_eq_mul,
      ← map_intCast quotientMap, ← map_pow, ← map_mul, ← C_eq_intCast,
      C_mul_X_pow_eq_monomial]
    simp

theorem presentation :
    Specs.Alg01SymmetricWitt.Symmetric.TorsionPresentation.presentation :=
  ⟨presentationEquiv, presentationEquiv_generator, presentationEquiv_map_degree⟩

/-- The restriction of the presentation to a homogeneous component. -/
noncomputable def presentationDegreeEquiv (n : ℕ) :
    degree ℤ (ZMod 2) n ≃ₗ[ℤ] quotientDegree n :=
  presentationEquiv.toLinearEquiv.ofSubmodules _ _ (presentationEquiv_map_degree n)

private theorem quotientIsInternal : DirectSum.IsInternal quotientDegree := by
  let f := DirectSum.lmap (fun n => (presentationDegreeEquiv n).toLinearMap)
  have hf : Function.Bijective f :=
    ⟨(DirectSum.lmap_injective _).2 (fun n => (presentationDegreeEquiv n).injective),
      (DirectSum.lmap_surjective _).2 (fun n => (presentationDegreeEquiv n).surjective)⟩
  have hComm : (DirectSum.coeLinearMap quotientDegree).comp f =
      presentationEquiv.toLinearMap.comp (DirectSum.coeLinearMap (degree ℤ (ZMod 2))) := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    change DirectSum.coeLinearMap quotientDegree (DirectSum.lmap _
      (DirectSum.of (fun n => ↥(degree ℤ (ZMod 2) n)) n x)) =
      presentationEquiv (DirectSum.coeLinearMap _
        (DirectSum.of (fun n => ↥(degree ℤ (ZMod 2) n)) n x))
    rw [DirectSum.lmap_of, DirectSum.coeLinearMap_of, DirectSum.coeLinearMap_of]
    rfl
  have hSym : DirectSum.IsInternal (degree ℤ (ZMod 2)) :=
    DirectSum.Decomposition.isInternal _
  change Function.Bijective (DirectSum.coeLinearMap quotientDegree)
  have hComp : Function.Bijective ((DirectSum.coeLinearMap quotientDegree).comp f) := by
    rw [hComm]
    exact presentationEquiv.bijective.comp hSym
  exact ⟨fun x y hxy => by
    obtain ⟨a, rfl⟩ := hf.2 x
    obtain ⟨b, rfl⟩ := hf.2 y
    exact congrArg f (hComp.1 hxy),
    fun q => by
      obtain ⟨a, ha⟩ := hComp.2 q
      exact ⟨f a, ha⟩⟩

/-- The quotient grading by images of homogeneous polynomials. -/
noncomputable instance quotientGradedAlgebra : GradedAlgebra quotientDegree :=
  quotientIsInternal.gradedAlgebra

/-- A homogeneous term of the quotient is the image of the same polynomial term. -/
theorem decompose_quotientMap (p : ℤ[X]) (n : ℕ) :
    (DirectSum.decompose quotientDegree (quotientMap p) n : PolynomialQuotient) =
      quotientMap (monomial n (p.coeff n)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    change (((DirectSum.decomposeLinearEquiv quotientDegree) (quotientMap (p + q))) n :
      PolynomialQuotient) = quotientMap (monomial n ((p + q).coeff n))
    rw [map_add, map_add, DirectSum.add_apply]
    change ((DirectSum.decompose quotientDegree (quotientMap p) n : PolynomialQuotient) +
      (DirectSum.decompose quotientDegree (quotientMap q) n : PolynomialQuotient)) = _
    rw [hp, hq, coeff_add, map_add, map_add]
  | monomial m a =>
    by_cases h : m = n
    · subst m
      rw [coeff_monomial_same]
      exact DirectSum.decompose_of_mem_same _ (quotientMonomial_mem n a)
    · simp only [coeff_monomial, h, ite_false, map_zero]
      exact DirectSum.decompose_of_mem_ne _ (quotientMonomial_mem m a) h

theorem quotientGrading :
    Specs.Alg01SymmetricWitt.Symmetric.TorsionPresentation.quotientGrading :=
  ⟨quotientGradedAlgebra, decompose_quotientMap⟩

private theorem relation_eq_monomial : (C 2 * X : ℤ[X]) = monomial 1 2 := by
  rw [← C_mul_X_pow_eq_monomial, pow_one]

private theorem quotientMonomial_zero_eq_zero (a : ℤ)
    (h : quotientMap (monomial 0 a) = 0) : a = 0 := by
  have hm : monomial 0 a ∈ relationIdeal := Ideal.Quotient.eq_zero_iff_mem.mp h
  obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp hm
  have hc := congrArg (fun q : ℤ[X] => q.coeff 0) hp
  simpa [relation_eq_monomial, mul_coeff_zero, coeff_monomial] using hc

private theorem quotientMonomial_succ_eq_zero_iff (n : ℕ) (a : ℤ) :
    quotientMap (monomial (n + 1) a) = 0 ↔ (2 : ℤ) ∣ a := by
  change Ideal.Quotient.mk relationIdeal (monomial (n + 1) a) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change monomial (n + 1) a ∈ Ideal.span ({C 2 * X} : Set ℤ[X]) ↔ _
  rw [relation_eq_monomial, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.coeff n, ?_⟩
    have hc := congrArg (fun q : ℤ[X] => q.coeff (n + 1)) hp
    simpa only [coeff_monomial_same, coeff_monomial_mul] using hc
  · rintro ⟨b, rfl⟩
    refine ⟨monomial n b, ?_⟩
    rw [monomial_mul_monomial, Nat.add_comm 1 n]

private theorem constants_coe (a : ℤ) :
    (algebraMap ℤ (quotientDegree 0) a : PolynomialQuotient) = quotientMap (C a) := by
  rw [SetLike.GradeZero.coe_algebraMap]
  exact (quotientMap.commutes a).symm

/-- Constants identify the degree-zero subalgebra with the integers. -/
noncomputable def degreeZeroEquiv : ℤ ≃ₐ[ℤ] quotientDegree 0 := by
  let f := Algebra.ofId ℤ (quotientDegree 0)
  refine AlgEquiv.ofBijective f ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_zero f).2
    intro a ha
    apply quotientMonomial_zero_eq_zero a
    rw [monomial_zero_left, ← constants_coe a]
    change (f a : PolynomialQuotient) = 0
    rw [ha]
    rfl
  · intro x
    obtain ⟨a, ha⟩ := (mem_quotientDegree_iff 0 x).1 x.property
    refine ⟨a, Subtype.ext ?_⟩
    change (algebraMap ℤ (quotientDegree 0) a : PolynomialQuotient) = _
    rw [constants_coe]
    simpa only [monomial_zero_left] using ha

@[simp] theorem degreeZeroEquiv_coe (a : ℤ) :
    (degreeZeroEquiv a : PolynomialQuotient) = quotientMap (C a) :=
  constants_coe a

theorem degreeZero : Specs.Alg01SymmetricWitt.Symmetric.TorsionPresentation.degreeZero :=
  ⟨quotientGradedAlgebra, degreeZeroEquiv, degreeZeroEquiv_coe⟩

private noncomputable def quotientPower (n : ℕ) : quotientDegree n :=
  ⟨quotientMap (monomial n 1), quotientMonomial_mem n 1⟩

private theorem smul_quotientPower (n : ℕ) (a : ℤ) :
    (↑(a • quotientPower n) : PolynomialQuotient) = quotientMap (monomial n a) := by
  change a • quotientMonomial n 1 = quotientMonomial n a
  rw [← map_smul]
  simp

private theorem two_smul_quotientPower (n : ℕ) :
    (2 : ℤ) • quotientPower (n + 1) = 0 :=
  Subtype.ext <| (smul_quotientPower _ 2).trans
    ((quotientMonomial_succ_eq_zero_iff n 2).2 dvd_rfl)

private noncomputable def positiveDegreeMap (n : ℕ) : ZMod 2 →ₗ[ℤ] quotientDegree (n + 1) :=
  cyclicMap (quotientPower (n + 1)) (two_smul_quotientPower n)

private theorem positiveDegreeMap_cast (n : ℕ) (a : ℤ) :
    (positiveDegreeMap n (a : ZMod 2) : PolynomialQuotient) =
      quotientMap (monomial (n + 1) a) := by
  rw [positiveDegreeMap, cyclicMap_cast, smul_quotientPower]

/-- In degree `n + 1`, the coefficient of `X ^ (n + 1)` is taken modulo two. -/
noncomputable def degreePositiveEquiv (n : ℕ) : ZMod 2 ≃ₗ[ℤ] quotientDegree (n + 1) := by
  refine LinearEquiv.ofBijective (positiveDegreeMap n) ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_zero (positiveDegreeMap n)).2
    intro x hx
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    have ha : quotientMap (monomial (n + 1) a) = 0 := by
      rw [← positiveDegreeMap_cast, hx]
      rfl
    exact (CharP.intCast_eq_zero_iff (ZMod 2) 2 a).2
      ((quotientMonomial_succ_eq_zero_iff n a).1 ha)
  · intro x
    obtain ⟨a, ha⟩ := (mem_quotientDegree_iff (n + 1) x).1 x.property
    exact ⟨(a : ZMod 2), Subtype.ext ((positiveDegreeMap_cast n a).trans ha)⟩

@[simp] theorem degreePositiveEquiv_coe (n : ℕ) (a : ℤ) :
    (degreePositiveEquiv n (a : ZMod 2) : PolynomialQuotient) =
      quotientMap (monomial (n + 1) a) :=
  positiveDegreeMap_cast n a

theorem degreePositive :
    Specs.Alg01SymmetricWitt.Symmetric.TorsionPresentation.degreePositive := by
  intro n hn
  cases n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n => exact ⟨degreePositiveEquiv n, degreePositiveEquiv_coe n⟩

end Alg01SymmetricWitt.Symmetric.TorsionPresentation
