import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.PrimeProduct

import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.ClassicalFunctions
/-! Conditional draft for paper.tex:1208–1234. Every public target helper
retains the complete, ordered C03 premises; no original closed target is defined.
The proofs use canonical Mathlib functions and do not import the unproved C03
implementation. -/
namespace P203.PrimeProduct

open P203Specs.PrimeProduct

theorem primeIndex_conditional
    (_divisorConvolutions : P203Specs.ClassicalFunctions.DivisorConvolutions)
    (_functionValues : P203Specs.ClassicalFunctions.FunctionValues)
    (_integerConvolutions : P203Specs.ClassicalFunctions.IntegerConvolutions)
    (_mobiusDefinition : P203Specs.ClassicalFunctions.MobiusDefinition)
    (_multiplicativity : P203Specs.ClassicalFunctions.Multiplicativity)
    (_positiveConvolutions : P203Specs.ClassicalFunctions.PositiveConvolutions)
    (_positiveVonMangoldtConvolution : P203Specs.ClassicalFunctions.PositiveVonMangoldtConvolution)
    (_primePowerValues : P203Specs.ClassicalFunctions.PrimePowerValues)
    (_sigmaZero : P203Specs.ClassicalFunctions.SigmaZero)
    (_valuesAtOne : P203Specs.ClassicalFunctions.ValuesAtOne)
    (_vonMangoldtConvolution : P203Specs.ClassicalFunctions.VonMangoldtConvolution)
    (_vonMangoldtDefinition : P203Specs.ClassicalFunctions.VonMangoldtDefinition) :
    P203Specs.PrimeProduct.PrimeIndex := by
  intro x p
  constructor
  · intro hp
    have h := Nat.mem_primesLE.mp hp
    exact ⟨h.2, (Nat.le_floor_iff' h.2.ne_zero).mp h.1⟩
  · rintro ⟨hp, hpx⟩
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff' hp.ne_zero).mpr hpx, hp⟩

theorem primePowerIndex_conditional
    (_divisorConvolutions : P203Specs.ClassicalFunctions.DivisorConvolutions)
    (_functionValues : P203Specs.ClassicalFunctions.FunctionValues)
    (_integerConvolutions : P203Specs.ClassicalFunctions.IntegerConvolutions)
    (_mobiusDefinition : P203Specs.ClassicalFunctions.MobiusDefinition)
    (_multiplicativity : P203Specs.ClassicalFunctions.Multiplicativity)
    (_positiveConvolutions : P203Specs.ClassicalFunctions.PositiveConvolutions)
    (_positiveVonMangoldtConvolution : P203Specs.ClassicalFunctions.PositiveVonMangoldtConvolution)
    (_primePowerValues : P203Specs.ClassicalFunctions.PrimePowerValues)
    (_sigmaZero : P203Specs.ClassicalFunctions.SigmaZero)
    (_valuesAtOne : P203Specs.ClassicalFunctions.ValuesAtOne)
    (_vonMangoldtConvolution : P203Specs.ClassicalFunctions.VonMangoldtConvolution)
    (_vonMangoldtDefinition : P203Specs.ClassicalFunctions.VonMangoldtDefinition) :
    P203Specs.PrimeProduct.PrimePowerIndex := by
  intro x p k
  constructor
  · rintro ⟨hp, hk⟩
    have h := Nat.mem_primesLE.mp hp
    have hk' := Finset.mem_Icc.mp hk
    have hn : ⌊x⌋₊ ≠ 0 := Nat.ne_of_gt (h.2.pos.trans_le h.1)
    have hpow := Nat.pow_le_of_le_log hn hk'.2
    exact ⟨h.2, hk'.1, (Nat.le_floor_iff' (pow_ne_zero _ h.2.ne_zero)).mp hpow⟩
  · rintro ⟨hp, hk, hpow⟩
    have hpow' : p ^ k ≤ ⌊x⌋₊ := (Nat.le_floor_iff' (pow_ne_zero _ hp.ne_zero)).mpr hpow
    have hpn : p ≤ ⌊x⌋₊ :=
      (Nat.le_of_dvd (pow_pos hp.pos _) (dvd_pow_self p (by omega))).trans hpow'
    exact ⟨Nat.mem_primesLE.mpr ⟨hpn, hp⟩,
      Finset.mem_Icc.mpr ⟨hk, Nat.le_log_of_pow_le hp.one_lt hpow'⟩⟩

theorem identifications_conditional
    (_divisorConvolutions : P203Specs.ClassicalFunctions.DivisorConvolutions)
    (_functionValues : P203Specs.ClassicalFunctions.FunctionValues)
    (_integerConvolutions : P203Specs.ClassicalFunctions.IntegerConvolutions)
    (_mobiusDefinition : P203Specs.ClassicalFunctions.MobiusDefinition)
    (_multiplicativity : P203Specs.ClassicalFunctions.Multiplicativity)
    (_positiveConvolutions : P203Specs.ClassicalFunctions.PositiveConvolutions)
    (_positiveVonMangoldtConvolution : P203Specs.ClassicalFunctions.PositiveVonMangoldtConvolution)
    (_primePowerValues : P203Specs.ClassicalFunctions.PrimePowerValues)
    (_sigmaZero : P203Specs.ClassicalFunctions.SigmaZero)
    (_valuesAtOne : P203Specs.ClassicalFunctions.ValuesAtOne)
    (_vonMangoldtConvolution : P203Specs.ClassicalFunctions.VonMangoldtConvolution)
    (_vonMangoldtDefinition : P203Specs.ClassicalFunctions.VonMangoldtDefinition) :
    P203Specs.PrimeProduct.Identifications := by
  intro x
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [P, primes, primorial_eq_prod_primesLE, Nat.cast_prod]
  · exact (Chebyshev.theta_eq_sum_primesLE x).symm
  · change (∑ p ∈ Nat.primesLE ⌊x⌋₊,
        ∑ k ∈ Finset.Icc 1 (Nat.log p ⌊x⌋₊), Real.log (p : ℝ)) = Chebyshev.psi x
    rw [Chebyshev.psi_eq_psi_coe_floor x, Chebyshev.psi_eq_sum_mul_log_prime]
    simp
  · change psi x = Chebyshev.psi x
    rw [psi, primes, Chebyshev.psi_eq_psi_coe_floor x,
      Chebyshev.psi_eq_sum_mul_log_prime]
    simp
  · exact Nat.primesLE_card_eq_primeCounting _

theorem primeProductBound_conditional
    (_divisorConvolutions : P203Specs.ClassicalFunctions.DivisorConvolutions)
    (_functionValues : P203Specs.ClassicalFunctions.FunctionValues)
    (_integerConvolutions : P203Specs.ClassicalFunctions.IntegerConvolutions)
    (_mobiusDefinition : P203Specs.ClassicalFunctions.MobiusDefinition)
    (_multiplicativity : P203Specs.ClassicalFunctions.Multiplicativity)
    (_positiveConvolutions : P203Specs.ClassicalFunctions.PositiveConvolutions)
    (_positiveVonMangoldtConvolution : P203Specs.ClassicalFunctions.PositiveVonMangoldtConvolution)
    (_primePowerValues : P203Specs.ClassicalFunctions.PrimePowerValues)
    (_sigmaZero : P203Specs.ClassicalFunctions.SigmaZero)
    (_valuesAtOne : P203Specs.ClassicalFunctions.ValuesAtOne)
    (_vonMangoldtConvolution : P203Specs.ClassicalFunctions.VonMangoldtConvolution)
    (_vonMangoldtDefinition : P203Specs.ClassicalFunctions.VonMangoldtDefinition) :
    P203Specs.PrimeProduct.PrimeProductBound := by
  intro x hx
  have hp : P x = (primorial ⌊x⌋₊ : ℝ) := by
    simp [P, primes, primorial_eq_prod_primesLE, Nat.cast_prod]
  rw [hp]
  calc
    (primorial ⌊x⌋₊ : ℝ) ≤ ((4 ^ ⌊x⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast primorial_le_four_pow ⌊x⌋₊
    _ = (4 : ℝ) ^ (⌊x⌋₊ : ℝ) := by simp
    _ ≤ (4 : ℝ) ^ x :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le (by linarith))

theorem belowTwo_conditional
    (_divisorConvolutions : P203Specs.ClassicalFunctions.DivisorConvolutions)
    (_functionValues : P203Specs.ClassicalFunctions.FunctionValues)
    (_integerConvolutions : P203Specs.ClassicalFunctions.IntegerConvolutions)
    (_mobiusDefinition : P203Specs.ClassicalFunctions.MobiusDefinition)
    (_multiplicativity : P203Specs.ClassicalFunctions.Multiplicativity)
    (_positiveConvolutions : P203Specs.ClassicalFunctions.PositiveConvolutions)
    (_positiveVonMangoldtConvolution : P203Specs.ClassicalFunctions.PositiveVonMangoldtConvolution)
    (_primePowerValues : P203Specs.ClassicalFunctions.PrimePowerValues)
    (_sigmaZero : P203Specs.ClassicalFunctions.SigmaZero)
    (_valuesAtOne : P203Specs.ClassicalFunctions.ValuesAtOne)
    (_vonMangoldtConvolution : P203Specs.ClassicalFunctions.VonMangoldtConvolution)
    (_vonMangoldtDefinition : P203Specs.ClassicalFunctions.VonMangoldtDefinition) :
    P203Specs.PrimeProduct.BelowTwo := by
  intro x hx
  have hp : primes x = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have h := Nat.mem_primesLE.mp hp
    have hpx := (Nat.le_floor_iff' h.2.ne_zero).mp h.1
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast h.2.two_le
    linarith
  simp [P, theta, psi, piCount, hp]

end P203.PrimeProduct

theorem _root_.«P203».«PrimeProduct».«belowTwo» : _root_.«P203Specs».«PrimeProduct».«BelowTwo» :=
  @_root_.«P203».«PrimeProduct».«belowTwo_conditional» (@_root_.«P203».«ClassicalFunctions».«divisorConvolutions») (@_root_.«P203».«ClassicalFunctions».«functionValues») (@_root_.«P203».«ClassicalFunctions».«integerConvolutions») (@_root_.«P203».«ClassicalFunctions».«mobiusDefinition») (@_root_.«P203».«ClassicalFunctions».«multiplicativity») (@_root_.«P203».«ClassicalFunctions».«positiveConvolutions») (@_root_.«P203».«ClassicalFunctions».«positiveVonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«primePowerValues») (@_root_.«P203».«ClassicalFunctions».«sigmaZero») (@_root_.«P203».«ClassicalFunctions».«valuesAtOne») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtDefinition»)
theorem _root_.«P203».«PrimeProduct».«identifications» : _root_.«P203Specs».«PrimeProduct».«Identifications» :=
  @_root_.«P203».«PrimeProduct».«identifications_conditional» (@_root_.«P203».«ClassicalFunctions».«divisorConvolutions») (@_root_.«P203».«ClassicalFunctions».«functionValues») (@_root_.«P203».«ClassicalFunctions».«integerConvolutions») (@_root_.«P203».«ClassicalFunctions».«mobiusDefinition») (@_root_.«P203».«ClassicalFunctions».«multiplicativity») (@_root_.«P203».«ClassicalFunctions».«positiveConvolutions») (@_root_.«P203».«ClassicalFunctions».«positiveVonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«primePowerValues») (@_root_.«P203».«ClassicalFunctions».«sigmaZero») (@_root_.«P203».«ClassicalFunctions».«valuesAtOne») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtDefinition»)
theorem _root_.«P203».«PrimeProduct».«primeIndex» : _root_.«P203Specs».«PrimeProduct».«PrimeIndex» :=
  @_root_.«P203».«PrimeProduct».«primeIndex_conditional» (@_root_.«P203».«ClassicalFunctions».«divisorConvolutions») (@_root_.«P203».«ClassicalFunctions».«functionValues») (@_root_.«P203».«ClassicalFunctions».«integerConvolutions») (@_root_.«P203».«ClassicalFunctions».«mobiusDefinition») (@_root_.«P203».«ClassicalFunctions».«multiplicativity») (@_root_.«P203».«ClassicalFunctions».«positiveConvolutions») (@_root_.«P203».«ClassicalFunctions».«positiveVonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«primePowerValues») (@_root_.«P203».«ClassicalFunctions».«sigmaZero») (@_root_.«P203».«ClassicalFunctions».«valuesAtOne») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtDefinition»)
theorem _root_.«P203».«PrimeProduct».«primePowerIndex» : _root_.«P203Specs».«PrimeProduct».«PrimePowerIndex» :=
  @_root_.«P203».«PrimeProduct».«primePowerIndex_conditional» (@_root_.«P203».«ClassicalFunctions».«divisorConvolutions») (@_root_.«P203».«ClassicalFunctions».«functionValues») (@_root_.«P203».«ClassicalFunctions».«integerConvolutions») (@_root_.«P203».«ClassicalFunctions».«mobiusDefinition») (@_root_.«P203».«ClassicalFunctions».«multiplicativity») (@_root_.«P203».«ClassicalFunctions».«positiveConvolutions») (@_root_.«P203».«ClassicalFunctions».«positiveVonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«primePowerValues») (@_root_.«P203».«ClassicalFunctions».«sigmaZero») (@_root_.«P203».«ClassicalFunctions».«valuesAtOne») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtDefinition»)
theorem _root_.«P203».«PrimeProduct».«primeProductBound» : _root_.«P203Specs».«PrimeProduct».«PrimeProductBound» :=
  @_root_.«P203».«PrimeProduct».«primeProductBound_conditional» (@_root_.«P203».«ClassicalFunctions».«divisorConvolutions») (@_root_.«P203».«ClassicalFunctions».«functionValues») (@_root_.«P203».«ClassicalFunctions».«integerConvolutions») (@_root_.«P203».«ClassicalFunctions».«mobiusDefinition») (@_root_.«P203».«ClassicalFunctions».«multiplicativity») (@_root_.«P203».«ClassicalFunctions».«positiveConvolutions») (@_root_.«P203».«ClassicalFunctions».«positiveVonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«primePowerValues») (@_root_.«P203».«ClassicalFunctions».«sigmaZero») (@_root_.«P203».«ClassicalFunctions».«valuesAtOne») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtDefinition»)
