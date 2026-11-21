import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.Convolution

/-! Theorem 3.1: the positive-domain Dirichlet ring, via Mathlib's canonical
`ArithmeticFunction`, including the unit criterion and unique inverse. -/

set_option backward.isDefEq.respectTransparency false

namespace P203
namespace Convolution

open P203Specs

@[simp] theorem zeroExtend_apply {R : Type*} [Zero R]
    (f : PositiveFunction R) (n : ℕ+) : zeroExtend f (n : ℕ) = f n := by
  dsimp [zeroExtend]
  rw [dite_eq_left n.pos]
  exact congrArg f (PNat.coe_injective rfl)

@[simp] theorem zeroExtend_apply_pos {R : Type*} [Zero R]
    (f : PositiveFunction R) {n : ℕ} (hn : 0 < n) :
    zeroExtend f n = f ⟨n, hn⟩ := by
  simpa only [PNat.mk_coe] using zeroExtend_apply f ⟨n, hn⟩

theorem identification : P203Specs.Convolution.Identification := by
  intro R _
  exact ⟨(positiveEquiv R).left_inv, (positiveEquiv R).right_inv,
    fun f n => zeroExtend_apply f n, fun _ => ArithmeticFunction.map_zero⟩

theorem additionBridge : P203Specs.Convolution.AdditionBridge := by
  intro R _ f g
  apply ArithmeticFunction.ext
  intro n
  by_cases hn : 0 < n
  · simp only [zeroExtend, ArithmeticFunction.coe_mk,
      ArithmeticFunction.add_apply, dite_eq_left hn, positiveAdd]
  · have h : n = 0 := Nat.eq_zero_of_not_pos hn
    simp [h]

theorem productBridge : P203Specs.Convolution.ProductBridge := by
  intro R _ f g
  apply ArithmeticFunction.ext
  intro n
  by_cases hn : 0 < n
  · change zeroExtend (positiveConvolution f g) (⟨n, hn⟩ : ℕ+) = _
    rw [zeroExtend_apply_pos (positiveConvolution f g) hn, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => zeroExtend f a * zeroExtend g b)]
    dsimp only [positiveConvolution]
    symm
    rw [← Finset.sum_attach]
    simp only [Finset.attach_eq_univ]
    apply Finset.sum_congr rfl
    intro d _
    rw [zeroExtend_apply_pos f (Nat.pos_of_mem_divisors d.property),
      zeroExtend_apply_pos g (Nat.div_pos
        (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors d.property))
        (Nat.pos_of_mem_divisors d.property))]
    congr 2
  · have h : n = 0 := Nat.eq_zero_of_not_pos hn
    simp [h]

theorem identityBridge : P203Specs.Convolution.IdentityBridge := by
  intro R _
  apply ArithmeticFunction.ext
  intro n
  by_cases hn : 0 < n
  · change zeroExtend (delta R) (⟨n, hn⟩ : ℕ+) = _
    rw [zeroExtend_apply_pos (delta R) hn, ArithmeticFunction.one_apply]
    simp only [delta]
    congr 1
    exact propext PNat.coe_injective.eq_iff.symm
  · have h : n = 0 := Nat.eq_zero_of_not_pos hn
    simp [h]

theorem ringOperations : P203Specs.Convolution.RingOperations := by
  intro R _
  let := positiveRing R
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f g
    change restrictPositive (zeroExtend f + zeroExtend g) = positiveAdd f g
    rw [← additionBridge R f g]
    exact (positiveEquiv R).left_inv _
  · intro f g
    change restrictPositive (zeroExtend f * zeroExtend g) = positiveConvolution f g
    rw [← productBridge R f g]
    exact (positiveEquiv R).left_inv _
  · change restrictPositive (1 : ArithmeticFunction R) = delta R
    rw [← identityBridge R]
    exact (positiveEquiv R).left_inv _
  · rfl
  · intro f
    funext n
    change -(zeroExtend f (n : ℕ)) = -(f n)
    rw [zeroExtend_apply]

theorem unitCriterion : P203Specs.Convolution.UnitCriterion := by
  intro R _ f
  exact ArithmeticFunction.isUnit_iff_isUnit_apply_one

theorem uniqueInverse : P203Specs.Convolution.UniqueInverse := by
  intro R _ f hf
  obtain ⟨u, hu⟩ := (unitCriterion R f).mpr hf
  subst f
  refine ⟨↑(u⁻¹), ⟨u.val_inv, u.inv_val⟩, ?_⟩
  intro g hg
  calc
    g = (↑(u⁻¹) * ↑u) * g := by rw [Units.inv_mul, one_mul]
    _ = ↑(u⁻¹) := by rw [mul_assoc, hg.1, mul_one]

theorem positiveUnitCriterion : P203Specs.Convolution.PositiveUnitCriterion := by
  intro R _
  let := positiveRing R
  intro f
  let e : PositiveFunction R ≃+* ArithmeticFunction R := (positiveEquiv R).ringEquiv
  have h : IsUnit f ↔ IsUnit (zeroExtend f) := by
    constructor
    · intro hf
      exact hf.map e.toMonoidHom
    · intro hf
      have hh := hf.map e.symm.toMonoidHom
      change IsUnit (restrictPositive (zeroExtend f)) at hh
      rw [(identification R).1] at hh
      exact hh
  rw [h, unitCriterion R]
  exact Iff.rfl

theorem positiveUniqueInverse : P203Specs.Convolution.PositiveUniqueInverse := by
  intro R _ f hf
  have hf' : IsUnit (zeroExtend f 1) := by
    rw [zeroExtend_apply_pos f Nat.zero_lt_one]
    convert hf using 1
  obtain ⟨g, hg, huniq⟩ := uniqueInverse R (zeroExtend f) hf'
  refine ⟨restrictPositive g, ⟨?_, ?_⟩, ?_⟩
  · apply (positiveEquiv R).injective
    change zeroExtend _ = zeroExtend _
    rw [productBridge R, (identification R).2.1, hg.1, identityBridge R]
  · apply (positiveEquiv R).injective
    change zeroExtend _ = zeroExtend _
    rw [productBridge R, (identification R).2.1, hg.2, identityBridge R]
  · intro k hk
    apply (positiveEquiv R).injective
    change zeroExtend k = zeroExtend (restrictPositive g)
    rw [(identification R).2.1]
    apply huniq
    constructor
    · rw [← productBridge R, hk.1, identityBridge R]
    · rw [← productBridge R, hk.2, identityBridge R]

end Convolution
end P203
