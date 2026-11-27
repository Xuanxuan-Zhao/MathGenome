import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.PicardVessiotExistence
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.RankOneMultiplicativeGroup
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.RationalDifferentialFullGroup

namespace GaloisFormalization.PV

universe u v

open scoped nonZeroDivisors Matrix
open Polynomial

section Derivative

variable {C : Type u} [Field C]

local notation "K" => RatFunc C
local notation "ι[" C "]" => algebraMap (Polynomial C) (RatFunc C)

/- Use the canonical integer algebra in the operator interface. -/
attribute [local instance 2000] Ring.toIntAlgebra

private theorem derivation_on_polynomial (D : Specs.operatorField .differential K)
    (hD : Specs.isRationalDerivative D) (p : Polynomial C) :
    Specs.apply D (ι[C] p) = ι[C] p.derivative := by
  let d : Derivation ℤ K K := D
  change d (ι[C] p) = ι[C] p.derivative
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, derivative_C_mul_X_pow, map_mul, map_pow,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X, d.leibniz, d.leibniz_pow]
    have hc : d (RatFunc.C c) = 0 := hD.1 c
    have hX : d (RatFunc.X : K) = 1 := hD.2
    simp [hc, hX, smul_eq_mul, nsmul_eq_mul, mul_assoc, RatFunc.algebraMap_C, mul_left_comm]

theorem rationalDerivative_existsUnique : Specs.rationalDerivativeExistsUnique.{u} := by
  intro C _
  let d : Derivation ℤ (Polynomial C) (Polynomial C) :=
    Derivation.mk' ((Polynomial.derivative (R := C)).restrictScalars ℤ) fun a b => by
      change derivative (a * b) = a * derivative b + b * derivative a
      rw [derivative_mul, mul_comm (derivative a), add_comm]
  let D : Derivation ℤ (RatFunc C) (RatFunc C) :=
    Operator.localizeDerivation (Polynomial C)⁰ d
  have hD (p : Polynomial C) : D (ι[C] p) = ι[C] p.derivative :=
    Operator.localizeDerivation_algebraMap _ d p
  refine ⟨D, ⟨fun c => ?_, ?_⟩, ?_⟩
  · change D (RatFunc.C c) = 0
    rw [← RatFunc.algebraMap_C, hD, Polynomial.derivative_C, map_zero]
  · change D (RatFunc.X : RatFunc C) = 1
    rw [← RatFunc.algebraMap_X, hD, Polynomial.derivative_X, map_one]
  · intro E hE
    change (show Derivation ℤ (RatFunc C) (RatFunc C) from E) = D
    refine Operator.localizedDerivation_ext (Polynomial C)⁰ fun p => ?_
    exact (derivation_on_polynomial E hE p).trans (hD p).symm

private theorem derivative_fraction (D : Specs.operatorField .differential K)
    (hD : Specs.isRationalDerivative D) (p q : Polynomial C) :
    Specs.apply D (ι[C] p / ι[C] q) =
      ι[C] (p.derivative * q - p * q.derivative) / (ι[C] q) ^ 2 := by
  let d : Derivation ℤ K K := D
  change d _ = _
  rw [d.leibniz_div]
  change (ι[C] q)⁻¹ ^ 2 * (ι[C] q * Specs.apply D (ι[C] p) - ι[C] p * Specs.apply D (ι[C] q)) = _
  rw [derivation_on_polynomial D hD, derivation_on_polynomial D hD, map_sub, map_mul,
    map_mul, div_eq_mul_inv, inv_pow, mul_comm (ι[C] q) (ι[C] p.derivative), mul_comm]

private theorem polynomialMap_ne_zero {p : Polynomial C} (hp : p ≠ 0) :
    ι[C] p ≠ 0 :=
  RatFunc.algebraMap_ne_zero hp

theorem rationalDerivative_constants : Specs.rationalDerivativeConstants.{u} := by
  intro C _ _ D hD
  let f : C →+* Specs.constantSubfield D :=
    (algebraMap C (RatFunc C)).codRestrict (Specs.constantSubfield D).toSubring hD.1
  have hf : Function.Bijective f := by
    refine ⟨f.injective, ?_⟩
    intro x
    let r : RatFunc C := x.val
    let p := r.num
    let q := r.denom
    have hq : q ≠ 0 := RatFunc.denom_ne_zero r
    have hx : Specs.apply D r = 0 := x.property
    have hz : ι[C] (p.derivative * q - p * q.derivative) / (ι[C] q) ^ 2 = 0 := by
      rw [← derivative_fraction D hD, r.num_div_denom]
      exact hx
    have he : p.derivative * q = p * q.derivative := by
      apply sub_eq_zero.mp
      by_contra hne
      exact (div_ne_zero (polynomialMap_ne_zero hne)
        (pow_ne_zero _ (polynomialMap_ne_zero hq))) hz
    have hc : IsCoprime p q := r.isCoprime_num_denom
    have hp' : p.derivative = 0 :=
      Polynomial.dvd_derivative_iff.mp (hc.dvd_of_dvd_mul_right (he.symm ▸ dvd_mul_right _ _))
    have hq' : q.derivative = 0 :=
      Polynomial.dvd_derivative_iff.mp
        (hc.symm.dvd_of_dvd_mul_left (he ▸ dvd_mul_left _ _))
    refine ⟨p.coeff 0 / q.coeff 0, Subtype.ext ?_⟩
    change algebraMap C (RatFunc C) _ = r
    rw [← r.num_div_denom]
    change algebraMap C (RatFunc C) _ = ι[C] p / ι[C] q
    rw [map_div₀, RatFunc.algebraMap_eq_C]
    rw [← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C]
    congr 1
    · exact congrArg ι[C] (Polynomial.eq_C_of_derivative_eq_zero hp').symm
    · exact congrArg ι[C] (Polynomial.eq_C_of_derivative_eq_zero hq').symm
  exact ⟨RingEquiv.ofBijective f hf, fun _ => rfl⟩

theorem rationalLogDerivative : Specs.rationalLogDerivative.{u} := by
  intro C _ D hD p q hp hq
  change Specs.apply D (ι[C] p / ι[C] q) / (ι[C] p / ι[C] q) =
    ι[C] (p.derivative * q - p * q.derivative) / ι[C] (p * q) ∧
      (p.derivative * q - p * q.derivative).degree < (p * q).degree
  refine ⟨?_, ?_⟩
  · rw [derivative_fraction D hD, map_mul]
    field_simp [polynomialMap_ne_zero hp, polynomialMap_ne_zero hq]
  · apply (Polynomial.degree_sub_le _ _).trans_lt
    rw [max_lt_iff, Polynomial.degree_mul, Polynomial.degree_mul, Polynomial.degree_mul]
    exact ⟨WithBot.add_lt_add_right (Polynomial.degree_ne_bot.mpr hq)
        (Polynomial.degree_derivative_lt hp),
      WithBot.add_lt_add_left (Polynomial.degree_ne_bot.mpr hp)
        (Polynomial.degree_derivative_lt hq)⟩

theorem rationalDerivative_noPowerSolution : Specs.rationalDerivativeNoPowerSolution.{u} := by
  intro C _ _ D hD m hm b hb
  let r : RatFunc C := b
  let p := r.num
  let q := r.denom
  let n := p.derivative * q - p * q.derivative
  have hp : p ≠ 0 := RatFunc.num_ne_zero b.ne_zero
  have hq : q ≠ 0 := r.denom_ne_zero
  obtain ⟨hlog, hdeg⟩ := rationalLogDerivative D hD hp hq
  change Specs.apply D (ι[C] p / ι[C] q) / (ι[C] p / ι[C] q) = ι[C] n / ι[C] (p * q) at hlog
  have he : ι[C] n = (m : RatFunc C) * ι[C] (p * q) := by
    apply (div_eq_iff (polynomialMap_ne_zero (mul_ne_zero hp hq))).mp
    rw [← hlog, r.num_div_denom]
    exact (div_eq_iff b.ne_zero).mpr hb
  have he' : n = Polynomial.C (m : C) * (p * q) := by
    apply (RatFunc.algebraMap_injective C)
    simpa only [map_mul, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, map_natCast] using he
  change n.degree < (p * q).degree at hdeg
  rw [he', Polynomial.degree_C_mul (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))] at hdeg
  exact lt_irrefl _ hdeg

end Derivative

private theorem rationalDerivative_isBaseField {C : Type u} [Field C] [CharZero C]
    [IsAlgClosed C] (D : Specs.operatorField .differential (RatFunc C))
    (hD : Specs.isRationalDerivative D) : Specs.isBaseField D := by
  obtain ⟨e, _⟩ := rationalDerivative_constants D hD
  exact ⟨inferInstance, IsAlgClosed.of_ringEquiv C _ e⟩

theorem rationalDifferential_fullGroup : Specs.rationalDifferentialFullGroup.{u, v} := by
  intro C _ _ _ D hD R _ _ E T Y hpv hY
  have h := rankOneMultiplicativeGroup D (Specs.exponentialSystem C) E T Y
    (rationalDerivative_isBaseField D hD) hpv hY
  rcases h.1 with hall | ⟨m, hm, hroots⟩
  · exact hall
  · exfalso
    obtain ⟨hfixed, hbase, hsolution⟩ := h.2.1 m hm
    obtain ⟨b, hb⟩ := hsolution.mp (hbase.mp (hfixed.mp hroots.le))
    change Specs.apply D (b : RatFunc C) = (m : RatFunc C) *
      (1 : Matrix (Fin 1) (Fin 1) (RatFunc C)) 0 0 * (b : RatFunc C) at hb
    rw [Matrix.one_apply_eq, mul_one] at hb
    exact rationalDerivative_noPowerSolution D hD hm b hb

theorem rationalDifferential_fullGroup_exists : Specs.rationalDifferentialFullGroupExists.{u} := by
  intro C _ _ _ D hD
  obtain ⟨R, _, _, E, T, hpv, _⟩ := picardVessiot_exists D (Specs.exponentialSystem C)
    (rationalDerivative_isBaseField D hD)
  obtain ⟨Y, hY, _⟩ := hpv.1.2.2
  exact ⟨R, inferInstance, inferInstance, E, T, Y, hpv, hY,
    rationalDifferential_fullGroup D hD E T Y hpv hY⟩

end GaloisFormalization.PV
