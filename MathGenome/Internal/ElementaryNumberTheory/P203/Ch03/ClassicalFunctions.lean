import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.ClassicalFunctions
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.Convolution
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch02.TotientClassicalCongruences

namespace P203.ClassicalFunctions
open P203Specs P203Specs.ClassicalFunctions

theorem functionValues : FunctionValues := by
  intro n
  refine ⟨ArithmeticFunction.zeta_apply_ne n.pos.ne', ?_, rfl, ?_, ?_, rfl, fun _ => rfl⟩
  · intro k
    simp [idK, ArithmeticFunction.pow_apply, n.pos.ne']
  · exact (Ch02.totient_eq_natTotient n n.pos).symm
  · change (n : ℕ).totient = _
    have h := Nat.filter_coprime_Ico_eq_totient (n : ℕ) 1
    have hi : Finset.Ico 1 (1 + (n : ℕ)) = Finset.Icc 1 (n : ℕ) := by
      ext a
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hi] at h
    simpa only [Nat.coprime_comm] using h.symm

theorem mobiusDefinition : MobiusDefinition := by
  constructor
  · intro n
    by_cases hn : Squarefree (n : ℕ)
    · rw [ite_eq_left hn, ArithmeticFunction.moebius_apply_of_squarefree hn]
      congr 1
      rw [ArithmeticFunction.cardFactors_apply, Nat.primeFactors,
        List.toFinset_card_of_nodup hn.nodup_primeFactorsList]
    · exact (ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn).trans
        (ite_eq_right hn).symm
  · intro n
    rw [← not_iff_not, not_exists]
    simp only [not_and]
    change mu n ≠ 0 ↔ _
    rw [ArithmeticFunction.moebius_ne_zero_iff_squarefree,
      Nat.squarefree_iff_prime_squarefree]
    simp only [pow_two]

theorem sigmaZero : SigmaZero := by
  apply ArithmeticFunction.ext
  exact fun n => ArithmeticFunction.sigma_zero_apply n

theorem divisorConvolutions : DivisorConvolutions := by
  constructor
  · rw [← sigmaZero]
    simpa only [ArithmeticFunction.pow_zero_eq_zeta] using
      (ArithmeticFunction.zeta_mul_pow_eq_sigma (k := 0)).symm
  · intro k
    exact ArithmeticFunction.zeta_mul_pow_eq_sigma.symm

theorem integerConvolutions : IntegerConvolutions := by
  constructor
  · rw [divisorConvolutions.1, ArithmeticFunction.natCoe_mul]
  · intro k
    rw [divisorConvolutions.2 k, ArithmeticFunction.natCoe_mul]

/-- The C01 identification transports a canonical convolution back to
the sum over positive divisors, without an extra condition at zero. -/
theorem restrict_mul {R : Type*} [CommRing R] (f g : ArithmeticFunction R) :
    restrictPositive (f * g) =
      positiveConvolution (restrictPositive f) (restrictPositive g) := by
  apply (positiveEquiv R).injective
  change zeroExtend _ = zeroExtend _
  rw [Convolution.productBridge R]
  have hf : zeroExtend (restrictPositive f) = f := (positiveEquiv R).right_inv f
  have hg : zeroExtend (restrictPositive g) = g := (positiveEquiv R).right_inv g
  rw [hf, hg]
  exact (positiveEquiv R).right_inv (f * g)

theorem positiveConvolutions : PositiveConvolutions := by
  constructor
  · rw [integerConvolutions.1]
    exact restrict_mul _ _
  · intro k
    rw [integerConvolutions.2 k]
    exact restrict_mul _ _

theorem multiplicativity : Multiplicativity := by
  refine ⟨ArithmeticFunction.isMultiplicative_moebius, ?_, ?_,
    fun _ => ArithmeticFunction.isMultiplicative_sigma⟩
  · exact ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩
  · rw [← sigmaZero]
    exact ArithmeticFunction.isMultiplicative_sigma

theorem primePowerValues : PrimePowerValues := by
  intro p hp j hj
  refine ⟨ArithmeticFunction.moebius_apply_prime_pow hp (by omega), ?_, ?_,
    fun _ => ArithmeticFunction.sigma_apply_prime_pow hp⟩
  · change (p ^ j).totient = _
    rw [Nat.totient_prime_pow hp (by omega), Nat.mul_sub_left_distrib, mul_one,
      ← pow_succ, Nat.sub_add_cancel hj]
  · rw [← sigmaZero]
    exact ArithmeticFunction.sigma_zero_apply_prime_pow hp

theorem valuesAtOne : ValuesAtOne := by
  exact ⟨ArithmeticFunction.moebius_apply_one, Nat.totient_one,
    by simp [tau], ArithmeticFunction.sigma_one,
    ArithmeticFunction.vonMangoldt_apply_one⟩

theorem vonMangoldtDefinition : VonMangoldtDefinition := by
  constructor
  · intro p hp j hj
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega)]
    exact ArithmeticFunction.vonMangoldt_apply_prime hp
  · intro n hn
    apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
    intro h
    obtain ⟨p, j, hp, hj, he⟩ := (isPrimePow_nat_iff (n : ℕ)).mp h
    exact hn ⟨p, j, hp, hj, he⟩

theorem vonMangoldtConvolution : VonMangoldtConvolution :=
  ArithmeticFunction.zeta_mul_vonMangoldt

theorem positiveVonMangoldtConvolution : PositiveVonMangoldtConvolution := by
  change positiveConvolution (restrictPositive (one : ArithmeticFunction ℝ))
    (restrictPositive vonMangoldt) = restrictPositive log
  rw [← restrict_mul, vonMangoldtConvolution]

end P203.ClassicalFunctions
