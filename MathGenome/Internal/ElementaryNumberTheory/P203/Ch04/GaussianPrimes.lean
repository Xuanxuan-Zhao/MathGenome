import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.GaussianPrimes
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch04.GaussianArithmetic
import MathGenome.AbstractAlgebra.PolynomialApplications

/-! Rational and Gaussian primes in Theorem 4.3. -/
namespace P203.Ch04.GaussianPrimes

open P203Specs.Ch04.GaussianPrimes
open D07.Foundations.IntegerArithmetic

theorem one_add_i_prime : OneAddIPrime :=
  D07.Ch19.GaussianPrimesTwoSquares.one_add_i_prime

theorem two_ramifies : TwoRamifies :=
  D07.Ch19.GaussianPrimesTwoSquares.two_ramifies

theorem rational_prime_criterion : RationalPrimeCriterion :=
  D07.Ch19.GaussianPrimesTwoSquares.rational_prime_criterion

theorem prime_of_prime_norm : PrimeOfPrimeNorm :=
  D07.Ch19.GaussianPrimesTwoSquares.prime_of_prime_norm

private lemma positive_prime_not_square {p : ℤ} (hp : PositivePrime p) (a : ℤ) :
    p ≠ a ^ 2 := by
  intro h
  have hn : p.natAbs = a.natAbs ^ 2 := by rw [h, Int.natAbs_pow]
  have hs : Nat.Prime (a.natAbs ^ 2) := hn ▸ hp.2
  have := hs.eq_one_of_pow
  omega

/-- The four units force an element associated to its conjugate onto an axis
or a diagonal. -/
lemma coordinates_of_associated_conjugate (z : GaussianInt)
    (h : Associated z (star z)) :
    z.re = 0 ∨ z.im = 0 ∨ z.re = z.im ∨ z.re = -z.im := by
  obtain ⟨u, hu⟩ := h
  have hunits := (GaussianArithmetic.units (u : GaussianInt)).2.1.mp
    ((GaussianArithmetic.units (u : GaussianInt)).1.mp u.isUnit)
  rcases hunits with h | h | h | h
  · rw [h] at hu
    have hi := congrArg Zsqrtd.im hu
    simp at hi
    right; left; omega
  · rw [h] at hu
    have hr := congrArg Zsqrtd.re hu
    simp at hr
    left; omega
  · rw [h] at hu
    have hr := congrArg Zsqrtd.re hu
    simp at hr
    right; right; right; omega
  · rw [h] at hu
    have hr := congrArg Zsqrtd.re hu
    simp at hr
    right; right; left; omega

lemma nonassociate_conjugate_of_prime_norm {p : ℤ} (hp : PositivePrime p)
    (hp4 : p % 4 = 1) (z : GaussianInt) (hz : z.norm = p) :
    ¬ Associated z (star z) := by
  intro h
  have hn : z.re ^ 2 + z.im ^ 2 = p :=
    (GaussianArithmetic.norm_properties z).1.symm.trans hz
  rcases coordinates_of_associated_conjugate z h with ha | hb | hab | hab
  · simp only [ha, zero_pow (by decide : 2 ≠ 0), zero_add] at hn
    exact positive_prime_not_square hp z.im hn.symm
  · simp only [hb, zero_pow (by decide : 2 ≠ 0), add_zero] at hn
    exact positive_prime_not_square hp z.re hn.symm
  · rw [hab] at hn
    omega
  · rw [hab, neg_sq] at hn
    omega

theorem conjugate_factorization : ConjugateFactorization := by
  intro p hp hp4
  obtain ⟨a, b, hab⟩ :=
    (D07.Ch19.GaussianPrimesTwoSquares.prime_two_square_criterion p hp).mpr (Or.inr hp4)
  let π : GaussianInt := ⟨a, b⟩
  have hn : π.norm = p := by
    simpa [π, Zsqrtd.norm, pow_two] using hab.symm
  have hsn : (star π).norm = p := by rw [Zsqrtd.norm_conj, hn]
  refine ⟨π, hn, hsn, ?_, ?_, ?_, nonassociate_conjugate_of_prime_norm hp hp4 π hn⟩
  · rw [← Zsqrtd.norm_eq_mul_conj, hn]
  · exact prime_of_prime_norm π (hn ▸ hp)
  · exact prime_of_prime_norm (star π) (hsn ▸ hp)

theorem gaussian_prime_classification : GaussianPrimeClassification :=
  D07.Ch19.GaussianPrimesTwoSquares.gaussian_prime_classification

end P203.Ch04.GaussianPrimes
