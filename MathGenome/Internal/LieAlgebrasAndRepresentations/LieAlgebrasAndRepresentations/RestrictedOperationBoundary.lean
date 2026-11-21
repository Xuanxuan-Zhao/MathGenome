import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! Restricted Lie operations in prime characteristic. -/

open scoped BigOperators
open Finset
open _root_.Shared.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieAlgebrasAndRepresentations.RestrictedOperationBoundary

universe u v

open Specs.LieAlgebrasAndRepresentations.RestrictedOperationBoundary

abbrev jacobsonCoeff := @jacobsonCoeffValue
abbrev jacobsonCorrection := jacobsonCorrectionValue
abbrev IsRestrictedPower := isRestrictedPowerValue
abbrev RestrictedPower := restrictedPowerValue
abbrev derivationPower := @derivationPowerValue
abbrev restrictedRelations := restrictedRelationsValue
abbrev RestrictedEnveloping := restrictedEnvelopingValue
abbrev quotientMap := quotientMapValue

variable {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]

private theorem prime_char (k : Type u) [Field k] (p : ℕ) [CharP k p] [NeZero p] :
    Nat.Prime p :=
  CharP.char_prime_of_ne_zero k (NeZero.ne p)

private theorem cast_choose_eq_zero (hi : i ≠ 0) (hip : i < p) : (p.choose i : k) = 0 :=
  (CharP.cast_eq_zero_iff k p _).2 ((prime_char k p).dvd_choose_self hi hip)

omit [NeZero p] in
private theorem end_natCast_char (M : Type*) [AddCommGroup M] [Module k M] :
    (p : Module.End k M) = 0 := by
  ext m
  simp only [Module.End.natCast_apply, LinearMap.zero_apply]
  rw [← Nat.cast_smul_eq_nsmul k, CharP.cast_eq_zero k p, zero_smul]

theorem derivationPower_isDerivation : derivationPower_isDerivationType.{u, v} := by
  intro k _ p _ _ G _ _ D x y
  have hp := prime_char k p
  have hpos := hp.pos
  have hpred : p - 1 + 1 = p := by omega
  simp only [derivationPowerValue, Module.End.pow_apply, LieDerivation.coeFn_coe]
  rw [D.iterate_apply_lie', sum_range_succ]
  conv_lhs => arg 1; rw [← hpred, sum_range_succ']; rw [hpred]
  simp only [Nat.choose_self, Nat.choose_zero_right, tsub_self, tsub_zero,
    Function.iterate_zero_apply, one_nsmul]
  have hsum : (∑ i ∈ range (p - 1),
      p.choose (i + 1) • ⁅D^[i + 1] x, D^[p - (i + 1)] y⁆) = 0 := by
    apply sum_eq_zero
    intro i hi
    have hcast : (p.choose (i + 1) : k) = 0 :=
      cast_choose_eq_zero (by omega) (by have := mem_range.mp hi; omega)
    rw [← Nat.cast_smul_eq_nsmul k, hcast, zero_smul]
  -- The two endpoint terms of the generalized Leibniz expansion survive.
  rw [hsum]
  simp [add_comm]

open scoped TensorProduct in
theorem associativeDerivationPower_isDerivation :
    associativeDerivationPower_isDerivationType.{u, v} := by
  intro k _ p _ _ A _ _ D a b
  let d : Module.End k A := D
  let left : Module.End k (A ⊗[k] A) := TensorProduct.map d 1
  let right : Module.End k (A ⊗[k] A) := TensorProduct.map 1 d
  let product : A ⊗[k] A →ₗ[k] A := TensorProduct.lift (LinearMap.mul k A)
  -- Multiplication intertwines the sum on the tensor factors with the derivation.
  have hleibniz : product.comp (left + right) = d.comp product := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add, left, right,
      TensorProduct.map_tmul, Module.End.one_apply, product, TensorProduct.lift.tmul,
      LinearMap.mul_apply', d, Derivation.coeFn_coe, D.leibniz, smul_eq_mul]
    rw [mul_comm (D x) y, add_comm]
  have hcomm : Commute left right := by
    change left * right = right * left
    simp only [left, right, ← TensorProduct.map_mul, mul_one, one_mul]
  -- The binomial formula leaves just the two pure powers in characteristic p.
  have hsplit : (left + right) ^ p = left ^ p + right ^ p := by
    simpa only [end_natCast_char (k := k) (p := p), zero_mul, add_zero] using
      hcomm.add_pow_prime_eq' (prime_char k p)
  have hsemiconj : Function.Semiconj product (⇑(left + right)) d :=
    fun z => LinearMap.congr_fun hleibniz z
  have hpow : product (((left + right) ^ p) (a ⊗ₜ[k] b)) =
      (d ^ p) (product (a ⊗ₜ[k] b)) := by
    simpa only [Module.End.pow_apply] using hsemiconj.iterate_right p (a ⊗ₜ[k] b)
  rw [hsplit] at hpow
  simp only [left, right, product, TensorProduct.map_pow, one_pow, LinearMap.add_apply,
    TensorProduct.map_tmul, Module.End.one_apply, map_add, TensorProduct.lift.tmul,
    LinearMap.mul_apply'] at hpow
  simpa only [d, add_comm, mul_comm] using hpow.symm

section Associative

variable {A : Type*} [Ring A] [Algebra k A]

private theorem left_pow_apply (z a : A) (n : ℕ) :
    (LinearMap.mulLeft k z ^ n : Module.End k A) a = z ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, LinearMap.mulLeft_apply, pow_succ', mul_assoc]

private theorem right_pow_apply (z a : A) (n : ℕ) :
    (LinearMap.mulRight k z ^ n : Module.End k A) a = a * z ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, LinearMap.mulRight_apply, pow_succ, mul_assoc]

private theorem left_commute_right (z : A) :
    Commute (LinearMap.mulLeft k z : Module.End k A) (LinearMap.mulRight k z) := by
  ext a
  simp [Module.End.mul_apply, mul_assoc]

private theorem ad_eq_left_sub_right (z : A) :
    (LieAlgebra.ad k A z : Module.End k A) = LinearMap.mulLeft k z - LinearMap.mulRight k z := by
  ext a
  rfl

private theorem ad_pow_apply (z a : A) :
    ((LieAlgebra.ad k A z : Module.End k A) ^ p) a = ⁅z ^ p, a⁆ := by
  let l := LinearMap.mulLeft k z
  let r := LinearMap.mulRight k z
  have h : Commute (l - r) r := (left_commute_right z).sub_left (Commute.refl _)
  have hcast : (p : Module.End k A) = 0 := end_natCast_char A
  have hp := h.add_pow_prime_eq' (prime_char k p)
  rw [sub_add_cancel, hcast, zero_mul, add_zero] at hp
  have h' : (l - r) ^ p = l ^ p - r ^ p := eq_sub_of_add_eq hp.symm
  rw [ad_eq_left_sub_right, h', LinearMap.sub_apply, left_pow_apply, right_pow_apply]
  rfl

private theorem choose_pred_cast (j : ℕ) (hj : j < p) :
    ((p - 1).choose j : k) = (-1 : k) ^ j := by
  have hp := prime_char k p
  induction j with
  | zero => simp
  | succ j ih =>
      have h : (p.choose (j + 1) : k) = 0 := cast_choose_eq_zero (by omega) hj
      have he : (p.choose (j + 1) : k) =
          ((p - 1).choose j : k) + ((p - 1).choose (j + 1) : k) := by
        rw [← Nat.cast_add]
        apply congrArg (fun n : ℕ => (n : k))
        have hpos := hp.pos
        conv_lhs => rw [show p = (p - 1) + 1 by omega]
        exact Nat.choose_succ_succ _ _
      rw [h] at he
      rw [eq_neg_of_add_eq_zero_right he.symm, ih (by omega), pow_succ, mul_neg_one]

/-- The binomial coefficients of the commutator power `p - 1`, including
their signs, are all one in characteristic `p`. -/
private theorem ad_pow_pred_apply (z a : A) :
    ((LieAlgebra.ad k A z : Module.End k A) ^ (p - 1)) a =
      ∑ j ∈ range p, z ^ (p - 1 - j) * a * z ^ j := by
  have hpos := (prime_char k p).pos
  rw [ad_eq_left_sub_right, sub_eq_neg_add]
  rw [((left_commute_right z).symm.neg_left).add_pow]
  rw [show p - 1 + 1 = p by omega]
  simp only [LinearMap.sum_apply]
  apply sum_congr rfl
  intro j hj
  have hsign : ((p - 1).choose j : k) * (-1 : k) ^ j = 1 := by
    rw [choose_pred_cast j (mem_range.mp hj), ← mul_pow]
    simp
  rw [neg_pow, show (-1 : Module.End k A) = algebraMap k (Module.End k A) (-1) by simp,
    ← map_pow, ← Algebra.smul_def, smul_mul_assoc, smul_mul_assoc]
  simp only [LinearMap.smul_apply, Module.End.mul_apply, Module.End.natCast_apply,
    left_pow_apply, right_pow_apply, ← Nat.cast_smul_eq_nsmul k]
  rw [mul_smul_comm, smul_mul_assoc, smul_smul, mul_comm, hsign, one_smul]

open Polynomial

private theorem derivative_pow_succ_noncomm (z : A[X]) (n : ℕ) :
    derivative (z ^ (n + 1)) =
      ∑ j ∈ range (n + 1), z ^ (n - j) * derivative z * z ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', derivative_mul, ih, mul_sum, add_comm (derivative z * _)]
      conv_rhs => rw [sum_range_succ]
      apply congrArg₂ (· + ·)
      · apply sum_congr rfl
        intro j hj
        have h := mem_range.mp hj
        rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ', ← mul_assoc, ← mul_assoc]
      · simp

private theorem coeff_ad_polynomial (x y : A) (n j : ℕ) :
    (((LieAlgebra.ad k A[X] (C x * X + C y) : Module.End k A[X]) ^ n) (C x)).coeff j =
      jacobsonCoeff x y n j := by
  induction n generalizing j with
  | zero =>
      cases j <;> simp [jacobsonCoeff, jacobsonCoeffValue, coeff_C]
  | succ n ih =>
      let z := ((LieAlgebra.ad k A[X] (C x * X + C y) : Module.End k A[X]) ^ n) (C x)
      rw [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply]
      change ((C x * X + C y) * z - z * (C x * X + C y)).coeff j = _
      have h : (C x * X + C y) * z - z * (C x * X + C y) =
          (C x * z - z * C x) * X + (C y * z - z * C y) := by
        simp only [add_mul, mul_add, sub_mul, mul_assoc, (commute_X z).eq]
        abel
      rw [h, coeff_add]
      cases j with
      | zero =>
          simp only [coeff_mul_X_zero, zero_add, coeff_sub, coeff_C_mul, coeff_mul_C]
          rw [ih 0]
          rfl
      | succ j =>
          simp only [coeff_mul_X, coeff_sub, coeff_C_mul, coeff_mul_C]
          rw [ih j, ih (j + 1)]
          rfl

/-- Jacobson's formula for the associative `p`-th power, using the
commutator Lie algebra. -/
private theorem associative_pow_add (x y : A) :
    (x + y) ^ p = x ^ p + y ^ p + jacobsonCorrection k p x y := by
  let z : A[X] := C x * X + C y
  let f := z ^ p
  have hpos := (prime_char k p).pos
  have hpred : p - 1 + 1 = p := by omega
  have hz : derivative z = C x := by simp [z]
  -- The formal derivative is the signed commutator expansion in characteristic p.
  have hder : derivative f =
      ((LieAlgebra.ad k A[X] z : Module.End k A[X]) ^ (p - 1)) (C x) := by
    rw [ad_pow_pred_apply, ← hz]
    unfold f
    simpa only [hpred] using derivative_pow_succ_noncomm z (p - 1)
  have hcoeff (j : ℕ) (hj : j < p - 1) :
      f.coeff (j + 1) = (((j + 1 : ℕ) : k)⁻¹) • jacobsonCoeff x y (p - 1) j := by
    have hn : ((j + 1 : ℕ) : k) ≠ 0 := by
      intro h
      exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega : j + 1 < p))
        ((CharP.cast_eq_zero_iff k p _).mp h)
    have hc := congrArg (fun q : A[X] => q.coeff j) hder
    change f.derivative.coeff j = _ at hc
    rw [coeff_derivative, coeff_ad_polynomial] at hc
    rw [← Nat.cast_succ] at hc
    rw [← hc, ← map_natCast (algebraMap k A), ← Algebra.commutes, ← Algebra.smul_def,
      smul_smul, inv_mul_cancel₀ hn, one_smul]
  -- Evaluating the polynomial at one sums its two endpoint coefficients
  -- and the mixed coefficients recovered from the derivative.
  have hzdegree : z.natDegree ≤ 1 := by
    exact natDegree_add_le_of_le (by simpa only [pow_one] using natDegree_C_mul_X_pow_le x 1)
      (by simp : (C y).natDegree ≤ 1)
  have hfdegree : f.natDegree < p + 1 := by
    apply Nat.lt_succ_of_le
    simpa only [f, mul_one] using natDegree_pow_le_of_le p hzdegree
  have hlast : f.coeff p = x ^ p := by
    simpa [f, z, coeff_add, coeff_C_mul_X, coeff_C] using
      (coeff_pow_of_natDegree_le (p := z) (m := p) hzdegree)
  have eval_pow (a : A) (ha : ∀ b : A, Commute b a) : f.eval a = z.eval a ^ p :=
    map_pow (eval₂RingHom' (RingHom.id A) a ha) z p
  have hfirst : f.coeff 0 = y ^ p := by
    rw [coeff_zero_eq_eval_zero, eval_pow 0 Commute.zero_right]
    simp [z]
  have heval : f.eval 1 = (x + y) ^ p := by
    rw [eval_pow 1 Commute.one_right]
    simp [z]
  rw [← heval, eval_eq_sum_range' hfdegree, sum_range_succ, hlast]
  conv_lhs => arg 1; rw [← hpred, sum_range_succ']
  simp only [one_pow, mul_one]
  rw [hfirst]
  change (∑ j ∈ range (p - 1), f.coeff (j + 1)) + y ^ p + x ^ p = _
  rw [sum_congr rfl (fun j hj => hcoeff j (mem_range.mp hj))]
  unfold jacobsonCorrection jacobsonCorrectionValue
  abel

end Associative

section Transport

variable {G H : Type*} [LieRing G] [LieAlgebra k G] [LieRing H] [LieAlgebra k H]

private theorem map_jacobsonCoeff (f : G →ₗ⁅k⁆ H) (x y : G) (n j : ℕ) :
    f (jacobsonCoeff x y n j) = jacobsonCoeff (f x) (f y) n j := by
  induction n generalizing j with
  | zero => cases j <;> simp [jacobsonCoeff, jacobsonCoeffValue]
  | succ n ih => cases j <;> simp [jacobsonCoeff, jacobsonCoeffValue, ih]

private theorem map_jacobsonCorrection (f : G →ₗ⁅k⁆ H) (x y : G) (p : ℕ) :
    f (jacobsonCorrection k p x y) = jacobsonCorrection k p (f x) (f y) := by
  simp only [jacobsonCorrection, jacobsonCorrectionValue, map_sum, map_smul, map_jacobsonCoeff]

private theorem map_ad_pow (f : G →ₗ⁅k⁆ H) (x y : G) (n : ℕ) :
    f (((LieAlgebra.ad k G x : Module.End k G) ^ n) y) =
      ((LieAlgebra.ad k H (f x) : Module.End k H) ^ n) (f y) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, LieHom.map_lie, ih]

private theorem restrictedPower_of_injective {A : Type*} [Ring A] [Algebra k A]
    (f : G →ₗ⁅k⁆ A) (hf : Function.Injective f) (op : G → G)
    (h : ∀ x, f (op x) = f x ^ p) : IsRestrictedPower k p op := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    ext y
    apply hf
    rw [LieAlgebra.ad_apply, LieHom.map_lie, h, map_ad_pow, ad_pow_apply]
  · intro a x
    apply hf
    rw [h, map_smul, map_smul, h, smul_pow]
  · intro x y
    apply hf
    simp only [h, map_add, map_jacobsonCorrection]
    exact associative_pow_add (p := p) _ _

end Transport

theorem derivations_admit_restrictedPower : derivations_admit_restrictedPowerType.{u, v} := by
  intro k _ p _ _ G _ _
  let op (D : LieDerivation k G G) : LieDerivation k G G :=
    ⟨derivationPower p D, fun x y => by
      rw [derivationPower_isDerivation, ← lie_skew y, sub_neg_eq_add, add_comm]⟩
  let f := LieDerivation.toLinearMapLieHom k G
  exact ⟨⟨op, restrictedPower_of_injective f (LieDerivation.toLinearMapLieHom_injective k G)
    op (fun _ => rfl)⟩, fun _ => rfl⟩

theorem associativeDerivations_admit_restrictedPower :
    associativeDerivations_admit_restrictedPowerType.{u, v} := by
  intro k _ p _ _ A _ _
  let op (D : Derivation k A A) : Derivation k A A :=
    Derivation.mk' ((D : Module.End k A) ^ p) fun a b => by
      simpa only [smul_eq_mul] using associativeDerivationPower_isDerivation (p := p) D a b
  let f : Derivation k A A →ₗ⁅k⁆ Module.End k A :=
    { toFun := Derivation.toLinearMap
      map_add' := Derivation.coe_add_linearMap
      map_smul' := Derivation.coe_smul_linearMap
      map_lie' := fun {_ _} => Derivation.commutator_coe_linear_map }
  have hf : Function.Injective f := by
    intro D E h
    apply Derivation.coe_injective
    funext a
    exact LinearMap.congr_fun h a
  exact ⟨⟨op, restrictedPower_of_injective f hf op (fun _ => rfl)⟩, fun _ => rfl⟩

theorem quotientMap_spec : quotientMap_specType.{u, v} := by
  intro k _ p _ _ G _ _ power
  refine ⟨Ideal.Quotient.mkₐ_surjective k _, fun _ => Ideal.Quotient.eq_zero_iff_mem, ?_⟩
  intro x
  rw [← map_pow, ← sub_eq_zero, ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact TwoSidedIdeal.subset_span ⟨x, rfl⟩

end LieAlgebrasAndRepresentations.RestrictedOperationBoundary
