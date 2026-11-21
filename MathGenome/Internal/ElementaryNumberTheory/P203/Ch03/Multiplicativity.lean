import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.Multiplicativity
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.Convolution
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch01.FactorizationValuations

namespace P203.Multiplicativity
open P203Specs

variable {R : Type*} [CommRing R]

/-- Extend arbitrary prime-power data using the finite prime factorization. -/
noncomputable def canonicalExtension (c : ℕ → ℕ → R) : ArithmeticFunction R :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod c, by simp⟩

theorem canonicalExtension_multiplicative (c : ℕ → ℕ → R) :
    (canonicalExtension c).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [canonicalExtension], ?_⟩
  intro a b ha hb hab
  simp only [canonicalExtension, ArithmeticFunction.coe_mk, ite_eq_right ha, ite_eq_right hb,
    ite_eq_right (mul_ne_zero ha hb)]
  rw [Nat.factorization_mul_of_coprime hab,
    Finsupp.prod_add_index_of_disjoint hab.disjoint_primeFactors]

theorem canonicalExtension_prime_pow (c : ℕ → ℕ → R)
    {p j : ℕ} (hp : p.Prime) (hj : 0 < j) :
    canonicalExtension c (p ^ j) = c p j := by
  change (if p ^ j = 0 then 0 else (p ^ j).factorization.prod c) = _
  rw [ite_eq_right (pow_ne_zero j hp.ne_zero), hp.factorization_pow]
  simp [Finsupp.prod, hj.ne']

/-- Positivity removes the implementation-only zero case. -/
theorem multiplicativityBridge : P203Specs.Multiplicativity.MultiplicativityBridge := by
  intro R _ f
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · rintro ⟨h1, hmul⟩
    refine ⟨by simpa using h1, ?_⟩
    intro a b ha hb hab
    rw [Convolution.zeroExtend_apply_pos f (Nat.mul_pos (Nat.pos_of_ne_zero ha)
        (Nat.pos_of_ne_zero hb)),
      Convolution.zeroExtend_apply_pos f (Nat.pos_of_ne_zero ha),
      Convolution.zeroExtend_apply_pos f (Nat.pos_of_ne_zero hb)]
    exact hmul ⟨a, Nat.pos_of_ne_zero ha⟩ ⟨b, Nat.pos_of_ne_zero hb⟩ hab
  · rintro ⟨h1, hmul⟩
    refine ⟨by simpa using h1, ?_⟩
    intro a b hab
    have h := hmul a.pos.ne' b.pos.ne' hab
    change zeroExtend f ((a * b : ℕ+) : ℕ) = _ at h
    simpa only [Convolution.zeroExtend_apply] using h

theorem primePowerFormula : P203Specs.Multiplicativity.PrimePowerFormula := by
  intro R _ f hf n
  have h := (multiplicativityBridge R f).mp hf
  rw [← Convolution.zeroExtend_apply f n, h.multiplicative_factorization _ n.pos.ne']
  change (∏ p ∈ (n : ℕ).primeFactors, zeroExtend f (p ^ (n : ℕ).factorization p)) = _
  apply Finset.prod_congr rfl
  intro p hp
  have hv := (Ch01.valuationFactorizationBridge p (Nat.prime_of_mem_primeFactors hp)
    (n : ℤ) (by exact_mod_cast n.pos.ne')).1
  rw [hv]
  simp

/-- Two canonical multiplicative functions agreeing on positive prime powers agree everywhere. -/
theorem eq_of_prime_powers {f g : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    (h : ∀ p : ℕ, p.Prime → ∀ j : ℕ, 0 < j → f (p ^ j) = g (p ^ j)) : f = g := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers f hf g hg).mpr
  intro p j hp
  by_cases hj : j = 0
  · simp [hj, hf.map_one, hg.map_one]
  · exact h p hp j (Nat.pos_of_ne_zero hj)

theorem primePowerExtension : P203Specs.Multiplicativity.PrimePowerExtension := by
  intro R _ c
  let F := canonicalExtension c
  have hF := canonicalExtension_multiplicative c
  have hzero : zeroExtend (restrictPositive F) = F := (positiveEquiv R).right_inv F
  refine ⟨restrictPositive F, ⟨?_, ?_⟩, ?_⟩
  · apply (multiplicativityBridge R _).mpr
    rw [hzero]
    exact hF
  · intro p hp j hj
    rw [hzero]
    exact canonicalExtension_prime_pow c hp hj
  · intro g hg
    apply (positiveEquiv R).injective
    change zeroExtend g = zeroExtend (restrictPositive F)
    rw [hzero]
    apply eq_of_prime_powers ((multiplicativityBridge R g).mp hg.1) hF
    intro p hp j hj
    rw [hg.2 p hp j hj]
    exact (canonicalExtension_prime_pow c hp hj).symm

theorem convolutionClosure : P203Specs.Multiplicativity.ConvolutionClosure := by
  intro R _ f g hf hg
  apply (multiplicativityBridge R _).mpr
  rw [Convolution.productBridge R]
  exact ((multiplicativityBridge R f).mp hf).mul ((multiplicativityBridge R g).mp hg)

/-- The coefficient of a convolution at p^j only uses the prime-power
coefficients of each factor (including exponent zero). -/
theorem mul_prime_pow_congr (f g h : ArithmeticFunction R) {p : ℕ}
    (hp : p.Prime) (hgh : ∀ j : ℕ, g (p ^ j) = h (p ^ j)) (j : ℕ) :
    (f * g) (p ^ j) = (f * h) (p ^ j) := by
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun a b => f a * g b),
    Nat.sum_divisorsAntidiagonal' (fun a b => f a * h b)]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp (Nat.dvd_of_mem_divisors hd)
  rw [hgh k]

/-- A convolution inverse of a multiplicative function is multiplicative.
Extend the inverse's prime-power data, then use uniqueness of inverses. -/
theorem multiplicative_of_inverse {f g : ArithmeticFunction R}
    (hf : f.IsMultiplicative) (hfg : f * g = 1) : g.IsMultiplicative := by
  have hg1 : g 1 = 1 := by
    have h := congrArg (fun F : ArithmeticFunction R => F 1) hfg
    simpa only [ArithmeticFunction.mul_apply_one, hf.map_one, one_mul,
      ArithmeticFunction.one_one] using h
  let h := canonicalExtension (fun p j => g (p ^ j))
  have hh : h.IsMultiplicative := canonicalExtension_multiplicative _
  have hpow : ∀ p : ℕ, p.Prime → ∀ j : ℕ, h (p ^ j) = g (p ^ j) := by
    intro p hp j
    by_cases hj : j = 0
    · simp [hj, hh.map_one, hg1]
    · exact canonicalExtension_prime_pow _ hp (Nat.pos_of_ne_zero hj)
  have hfh : f * h = 1 := by
    apply eq_of_prime_powers (hf.mul hh) ArithmeticFunction.isMultiplicative_one
    intro p hp j _
    rw [mul_prime_pow_congr f h g hp (hpow p hp) j, hfg]
  have heq : h = g := by
    calc
      h = h * (f * g) := by rw [hfg, mul_one]
      _ = (f * h) * g := by rw [← mul_assoc, mul_comm h f]
      _ = g := by rw [hfh, one_mul]
  rw [← heq]
  exact hh

theorem inverseClosure : P203Specs.Multiplicativity.InverseClosure := by
  intro R _ f hf
  have hunit : IsUnit (f 1) := by rw [hf.1]; exact isUnit_one
  obtain ⟨g, hg, huniq⟩ := Convolution.positiveUniqueInverse R f hunit
  have hfg : zeroExtend f * zeroExtend g = 1 := by
    rw [← Convolution.productBridge R, hg.1, Convolution.identityBridge R]
  have hgm : P203Specs.Multiplicativity.IsMultiplicative g :=
    (multiplicativityBridge R g).mpr
      (multiplicative_of_inverse ((multiplicativityBridge R f).mp hf) hfg)
  exact ⟨g, ⟨hgm, hg⟩, fun k hk => huniq k hk.2⟩

end P203.Multiplicativity
