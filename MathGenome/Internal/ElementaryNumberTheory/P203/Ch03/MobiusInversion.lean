import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.MobiusInversion
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.Convolution

import MathGenome.Internal.ElementaryNumberTheory.P203.Ch03.ClassicalFunctions
/-! Conditional draft of Theorem 3.4. Each public target helper keeps the
entire ordered frozen C03 contract as explicit parameters. No original closed
target is declared here, and no C03 implementation is imported. -/
namespace P203.MobiusInversion

universe u
open P203Specs P203Specs.ClassicalFunctions

private theorem eq_iff_positive {R : Type u} [Zero R]
    (F G : ArithmeticFunction R) :
    F = G ↔ ∀ n : ℕ+, F n = G n := by
  constructor
  · intro h n
    rw [h]
  · intro h
    apply ArithmeticFunction.ext
    intro n
    cases n with
    | zero => simp
    | succ n => exact h ⟨n + 1, Nat.succ_pos n⟩

private theorem zeta_phi :
    (one : ArithmeticFunction ℤ) * (phi : ArithmeticFunction ℤ) =
      (idK 1 : ArithmeticFunction ℤ) := by
  apply ArithmeticFunction.ext
  intro n
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  change (∑ d ∈ n.divisors, (Nat.totient d : ℤ)) = _
  rw [← Nat.cast_sum, Nat.sum_totient]
  simp [ArithmeticFunction.pow_apply]

theorem inversion_conditional
    (_h0 : P203Specs.ClassicalFunctions.DivisorConvolutions)
    (_h1 : P203Specs.ClassicalFunctions.FunctionValues)
    (_h2 : P203Specs.ClassicalFunctions.IntegerConvolutions)
    (_h3 : P203Specs.ClassicalFunctions.MobiusDefinition)
    (_h4 : P203Specs.ClassicalFunctions.Multiplicativity)
    (_h5 : P203Specs.ClassicalFunctions.PositiveConvolutions)
    (_h6 : P203Specs.ClassicalFunctions.PositiveVonMangoldtConvolution)
    (_h7 : P203Specs.ClassicalFunctions.PrimePowerValues)
    (_h8 : P203Specs.ClassicalFunctions.SigmaZero)
    (_h9 : P203Specs.ClassicalFunctions.ValuesAtOne)
    (_h10 : P203Specs.ClassicalFunctions.VonMangoldtConvolution)
    (_h11 : P203Specs.ClassicalFunctions.VonMangoldtDefinition) :
    P203Specs.MobiusInversion.Inversion.{u} := by
  intro R _ f g
  let F := zeroExtend f
  let G := zeroExtend g
  have hz : (∀ n : ℕ+, g n = ∑ d ∈ (n : ℕ).divisors, zeroExtend f d) ↔
      G = (one : ArithmeticFunction R) * F := by
    rw [eq_iff_positive]
    simp only [ArithmeticFunction.coe_zeta_mul_apply, G, F,
      P203.Convolution.zeroExtend_apply]
  have hm : (∀ n : ℕ+, f n = ∑ d ∈ (n : ℕ).divisors,
        (mu d : R) * zeroExtend g ((n : ℕ) / d)) ↔
      F = (mu : ArithmeticFunction R) * G := by
    rw [eq_iff_positive]
    apply forall_congr'
    intro n
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => (mu : ArithmeticFunction R) a * G b)]
    simp only [ArithmeticFunction.intCoe_apply, F, G,
      P203.Convolution.zeroExtend_apply]
  rw [hz, hm]
  constructor
  · intro h
    rw [h, ← mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]
  · intro h
    rw [h, ← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]

theorem mobiusInverse_conditional
    (_h0 : P203Specs.ClassicalFunctions.DivisorConvolutions)
    (_h1 : P203Specs.ClassicalFunctions.FunctionValues)
    (_h2 : P203Specs.ClassicalFunctions.IntegerConvolutions)
    (_h3 : P203Specs.ClassicalFunctions.MobiusDefinition)
    (_h4 : P203Specs.ClassicalFunctions.Multiplicativity)
    (_h5 : P203Specs.ClassicalFunctions.PositiveConvolutions)
    (_h6 : P203Specs.ClassicalFunctions.PositiveVonMangoldtConvolution)
    (_h7 : P203Specs.ClassicalFunctions.PrimePowerValues)
    (_h8 : P203Specs.ClassicalFunctions.SigmaZero)
    (_h9 : P203Specs.ClassicalFunctions.ValuesAtOne)
    (_h10 : P203Specs.ClassicalFunctions.VonMangoldtConvolution)
    (_h11 : P203Specs.ClassicalFunctions.VonMangoldtDefinition) :
    P203Specs.MobiusInversion.MobiusInverse := by
  exact ArithmeticFunction.moebius_mul_coe_zeta

theorem totientSum_conditional
    (_h0 : P203Specs.ClassicalFunctions.DivisorConvolutions)
    (_h1 : P203Specs.ClassicalFunctions.FunctionValues)
    (_h2 : P203Specs.ClassicalFunctions.IntegerConvolutions)
    (_h3 : P203Specs.ClassicalFunctions.MobiusDefinition)
    (_h4 : P203Specs.ClassicalFunctions.Multiplicativity)
    (_h5 : P203Specs.ClassicalFunctions.PositiveConvolutions)
    (_h6 : P203Specs.ClassicalFunctions.PositiveVonMangoldtConvolution)
    (_h7 : P203Specs.ClassicalFunctions.PrimePowerValues)
    (_h8 : P203Specs.ClassicalFunctions.SigmaZero)
    (_h9 : P203Specs.ClassicalFunctions.ValuesAtOne)
    (_h10 : P203Specs.ClassicalFunctions.VonMangoldtConvolution)
    (_h11 : P203Specs.ClassicalFunctions.VonMangoldtDefinition) :
    P203Specs.MobiusInversion.TotientSum := by
  intro n
  change (∑ d ∈ (n : ℕ).divisors, (Nat.totient d : ℤ)) = (n : ℕ)
  rw [← Nat.cast_sum, Nat.sum_totient]

theorem totientConvolution_conditional
    (_h0 : P203Specs.ClassicalFunctions.DivisorConvolutions)
    (_h1 : P203Specs.ClassicalFunctions.FunctionValues)
    (_h2 : P203Specs.ClassicalFunctions.IntegerConvolutions)
    (_h3 : P203Specs.ClassicalFunctions.MobiusDefinition)
    (_h4 : P203Specs.ClassicalFunctions.Multiplicativity)
    (_h5 : P203Specs.ClassicalFunctions.PositiveConvolutions)
    (_h6 : P203Specs.ClassicalFunctions.PositiveVonMangoldtConvolution)
    (_h7 : P203Specs.ClassicalFunctions.PrimePowerValues)
    (_h8 : P203Specs.ClassicalFunctions.SigmaZero)
    (_h9 : P203Specs.ClassicalFunctions.ValuesAtOne)
    (_h10 : P203Specs.ClassicalFunctions.VonMangoldtConvolution)
    (_h11 : P203Specs.ClassicalFunctions.VonMangoldtDefinition) :
    P203Specs.MobiusInversion.TotientConvolution := by
  change (phi : ArithmeticFunction ℤ) = mu * (idK 1 : ArithmeticFunction ℤ)
  rw [← zeta_phi, ← mul_assoc, ArithmeticFunction.moebius_mul_coe_zeta, one_mul]

theorem mangoldtConvolution_conditional
    (_h0 : P203Specs.ClassicalFunctions.DivisorConvolutions)
    (_h1 : P203Specs.ClassicalFunctions.FunctionValues)
    (_h2 : P203Specs.ClassicalFunctions.IntegerConvolutions)
    (_h3 : P203Specs.ClassicalFunctions.MobiusDefinition)
    (_h4 : P203Specs.ClassicalFunctions.Multiplicativity)
    (_h5 : P203Specs.ClassicalFunctions.PositiveConvolutions)
    (_h6 : P203Specs.ClassicalFunctions.PositiveVonMangoldtConvolution)
    (_h7 : P203Specs.ClassicalFunctions.PrimePowerValues)
    (_h8 : P203Specs.ClassicalFunctions.SigmaZero)
    (_h9 : P203Specs.ClassicalFunctions.ValuesAtOne)
    (_h10 : P203Specs.ClassicalFunctions.VonMangoldtConvolution)
    (_h11 : P203Specs.ClassicalFunctions.VonMangoldtDefinition) :
    P203Specs.MobiusInversion.MangoldtConvolution := by
  change vonMangoldt = (mu : ArithmeticFunction ℝ) * log
  rw [← _h10, ← mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, one_mul]

end P203.MobiusInversion

universe v8_closure_68bcc6c3f88bc10f_u0
theorem _root_.«P203».«MobiusInversion».«inversion» : _root_.«P203Specs».«MobiusInversion».«Inversion».{v8_closure_68bcc6c3f88bc10f_u0} :=
  @_root_.«P203».«MobiusInversion».«inversion_conditional».{v8_closure_68bcc6c3f88bc10f_u0} (@_root_.«P203».«ClassicalFunctions».«divisorConvolutions») (@_root_.«P203».«ClassicalFunctions».«functionValues») (@_root_.«P203».«ClassicalFunctions».«integerConvolutions») (@_root_.«P203».«ClassicalFunctions».«mobiusDefinition») (@_root_.«P203».«ClassicalFunctions».«multiplicativity») (@_root_.«P203».«ClassicalFunctions».«positiveConvolutions») (@_root_.«P203».«ClassicalFunctions».«positiveVonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«primePowerValues») (@_root_.«P203».«ClassicalFunctions».«sigmaZero») (@_root_.«P203».«ClassicalFunctions».«valuesAtOne») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtDefinition»)
theorem _root_.«P203».«MobiusInversion».«mangoldtConvolution» : _root_.«P203Specs».«MobiusInversion».«MangoldtConvolution» :=
  @_root_.«P203».«MobiusInversion».«mangoldtConvolution_conditional» (@_root_.«P203».«ClassicalFunctions».«divisorConvolutions») (@_root_.«P203».«ClassicalFunctions».«functionValues») (@_root_.«P203».«ClassicalFunctions».«integerConvolutions») (@_root_.«P203».«ClassicalFunctions».«mobiusDefinition») (@_root_.«P203».«ClassicalFunctions».«multiplicativity») (@_root_.«P203».«ClassicalFunctions».«positiveConvolutions») (@_root_.«P203».«ClassicalFunctions».«positiveVonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«primePowerValues») (@_root_.«P203».«ClassicalFunctions».«sigmaZero») (@_root_.«P203».«ClassicalFunctions».«valuesAtOne») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtDefinition»)
theorem _root_.«P203».«MobiusInversion».«mobiusInverse» : _root_.«P203Specs».«MobiusInversion».«MobiusInverse» :=
  @_root_.«P203».«MobiusInversion».«mobiusInverse_conditional» (@_root_.«P203».«ClassicalFunctions».«divisorConvolutions») (@_root_.«P203».«ClassicalFunctions».«functionValues») (@_root_.«P203».«ClassicalFunctions».«integerConvolutions») (@_root_.«P203».«ClassicalFunctions».«mobiusDefinition») (@_root_.«P203».«ClassicalFunctions».«multiplicativity») (@_root_.«P203».«ClassicalFunctions».«positiveConvolutions») (@_root_.«P203».«ClassicalFunctions».«positiveVonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«primePowerValues») (@_root_.«P203».«ClassicalFunctions».«sigmaZero») (@_root_.«P203».«ClassicalFunctions».«valuesAtOne») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtDefinition»)
theorem _root_.«P203».«MobiusInversion».«totientConvolution» : _root_.«P203Specs».«MobiusInversion».«TotientConvolution» :=
  @_root_.«P203».«MobiusInversion».«totientConvolution_conditional» (@_root_.«P203».«ClassicalFunctions».«divisorConvolutions») (@_root_.«P203».«ClassicalFunctions».«functionValues») (@_root_.«P203».«ClassicalFunctions».«integerConvolutions») (@_root_.«P203».«ClassicalFunctions».«mobiusDefinition») (@_root_.«P203».«ClassicalFunctions».«multiplicativity») (@_root_.«P203».«ClassicalFunctions».«positiveConvolutions») (@_root_.«P203».«ClassicalFunctions».«positiveVonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«primePowerValues») (@_root_.«P203».«ClassicalFunctions».«sigmaZero») (@_root_.«P203».«ClassicalFunctions».«valuesAtOne») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtDefinition»)
theorem _root_.«P203».«MobiusInversion».«totientSum» : _root_.«P203Specs».«MobiusInversion».«TotientSum» :=
  @_root_.«P203».«MobiusInversion».«totientSum_conditional» (@_root_.«P203».«ClassicalFunctions».«divisorConvolutions») (@_root_.«P203».«ClassicalFunctions».«functionValues») (@_root_.«P203».«ClassicalFunctions».«integerConvolutions») (@_root_.«P203».«ClassicalFunctions».«mobiusDefinition») (@_root_.«P203».«ClassicalFunctions».«multiplicativity») (@_root_.«P203».«ClassicalFunctions».«positiveConvolutions») (@_root_.«P203».«ClassicalFunctions».«positiveVonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«primePowerValues») (@_root_.«P203».«ClassicalFunctions».«sigmaZero») (@_root_.«P203».«ClassicalFunctions».«valuesAtOne») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtConvolution») (@_root_.«P203».«ClassicalFunctions».«vonMangoldtDefinition»)
