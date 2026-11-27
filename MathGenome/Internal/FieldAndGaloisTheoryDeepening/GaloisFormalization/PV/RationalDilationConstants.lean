import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.OperatorRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.RationalDilationConstants

open scoped Polynomial

namespace GaloisFormalization.PV

open Polynomial

variable {K : Type*} [Field K]

/-- The automorphism of `K(X)` given by substitution of `q * X` for `X`. -/
noncomputable def rationalDilation (q : Kˣ) : RatFunc K ≃ₐ[K] RatFunc K :=
  IsFractionRing.algEquivOfAlgEquiv (Specs.polynomialDilation q)

/-- The difference operator on the rational function field. -/
noncomputable def rationalDilationOperator (q : Kˣ) : Operator .difference (RatFunc K) :=
  Operator.difference (rationalDilation q).toRingEquiv

@[simp]
theorem rationalDilation_algebraMap (q : Kˣ) (p : K[X]) :
    rationalDilation q (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (p.comp (C (q : K) * X)) := by
  rw [rationalDilation, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  simp [Specs.polynomialDilation, comp_eq_aeval]

@[simp]
theorem rationalDilation_mk (q : Kˣ) (p d : K[X]) :
    rationalDilation q (RatFunc.mk p d) =
      RatFunc.mk (p.comp (C (q : K) * X)) (d.comp (C (q : K) * X)) := by
  simp only [RatFunc.mk_eq_div, map_div₀, rationalDilation_algebraMap]

@[simp]
theorem rationalDilation_symm (q : Kˣ) :
    (rationalDilation q).symm = rationalDilation q⁻¹ := by
  simp only [rationalDilation, IsFractionRing.algEquivOfAlgEquiv_symm,
    Specs.polynomialDilation, Polynomial.algEquivOfCompEqX_symm, inv_inv]

private theorem degree_eq_of_dilation_fixed_fraction (q : Kˣ) (hq : orderOf q = 0)
    {p d : K[X]} (hp : p ≠ 0) (hd : d ≠ 0)
    (hfixed : rationalDilation q (RatFunc.mk p d) = RatFunc.mk p d) :
    p.degree = d.degree := by
  let v : K[X] := C (q : K) * X
  have hv : v.natDegree = 1 := natDegree_C_mul_X _ q.ne_zero
  have hl : v.leadingCoeff = (q : K) := by simp [v]
  have hd' : d.comp v ≠ 0 :=
    (comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_iff_ne_zero.mpr q.ne_zero)).not.mpr hd
  rw [rationalDilation_mk, RatFunc.mk_eq_div, RatFunc.mk_eq_div] at hfixed
  have hcross : p.comp v * d = p * d.comp v := by
    apply RatFunc.algebraMap_injective
    simpa only [map_mul] using
      (div_eq_div_iff (RatFunc.algebraMap_ne_zero hd') (RatFunc.algebraMap_ne_zero hd)).mp hfixed
  have hlead := congrArg leadingCoeff hcross
  simp only [leadingCoeff_mul, leadingCoeff_comp (hv.trans_ne Nat.one_ne_zero), hl] at hlead
  have hpow : (q : K) ^ p.natDegree = (q : K) ^ d.natDegree := by
    apply mul_left_cancel₀ (mul_ne_zero (leadingCoeff_ne_zero.mpr hp) (leadingCoeff_ne_zero.mpr hd))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hlead
  have hn : p.natDegree = d.natDegree := by
    apply (pow_inj_iff_of_orderOf_eq_zero hq).mp
    exact Units.ext (by simpa only [Units.val_pow_eq_pow_val] using hpow)
  rw [degree_eq_natDegree hp, degree_eq_natDegree hd, hn]

private theorem exists_algebraMap_of_dilation_fixed (q : Kˣ) (hq : orderOf q = 0) (f : RatFunc K)
    (hf : rationalDilation q f = f) : ∃ c : K, algebraMap K (RatFunc K) c = f := by
  by_cases hf0 : f = 0
  · exact ⟨0, by simp [hf0]⟩
  let p := f.num
  let d := f.denom
  have hp : p ≠ 0 := RatFunc.num_ne_zero hf0
  have hd : d ≠ 0 := f.denom_ne_zero
  have hmk : RatFunc.mk p d = f :=
    (RatFunc.mk_eq_div p d).trans f.num_div_denom
  have hdeg : p.degree = d.degree :=
    degree_eq_of_dilation_fixed_fraction q hq hp hd (hmk ▸ hf)
  let c := p.leadingCoeff
  let r := p - C c * d
  have hc : c ≠ 0 := leadingCoeff_ne_zero.mpr hp
  -- Subtract the constant with the same leading term to lower the numerator degree.
  have hrdeg : r.degree < p.degree := by
    refine degree_sub_lt_left (q := C c * d) ?_ hp ?_
    · rw [degree_C_mul hc, hdeg]
    · rw [leadingCoeff_mul, leadingCoeff_C, (RatFunc.monic_denom f).leadingCoeff, mul_one]
  have hC : algebraMap K[X] (RatFunc K) (C c) = algebraMap K (RatFunc K) c := by
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), algebraMap_apply,
      Algebra.algebraMap_self_apply]
  have hr : RatFunc.mk r d = f - algebraMap K (RatFunc K) c := by
    simp only [r, RatFunc.mk_eq_div, map_sub, map_mul, sub_div, mul_div_assoc,
      div_self (RatFunc.algebraMap_ne_zero hd), mul_one, hC, f.num_div_denom, p, d]
  have hr0 : r = 0 := by
    by_contra hr0
    have hrfixed : rationalDilation q (RatFunc.mk r d) = RatFunc.mk r d := by
      rw [hr, map_sub, hf, AlgEquiv.commutes]
    exact hrdeg.ne ((degree_eq_of_dilation_fixed_fraction q hq hr0 hd hrfixed).trans hdeg.symm)
  refine ⟨c, ?_⟩
  have hzero : RatFunc.mk r d = 0 := by simp [hr0, RatFunc.mk_eq_div]
  exact (sub_eq_zero.mp (hr.symm.trans hzero)).symm

/-- The constants of the rational dilation are exactly the embedded coefficient field. -/
theorem rationalDilation_constantSubfield (q : Kˣ) (hq : orderOf q = 0) :
    (rationalDilationOperator q).constantSubfield = (algebraMap K (RatFunc K)).fieldRange := by
  ext f
  rw [Operator.mem_constantSubfield, RingHom.mem_fieldRange]
  change rationalDilation q f = f ↔ ∃ c : K, algebraMap K (RatFunc K) c = f
  refine ⟨exists_algebraMap_of_dilation_fixed q hq f, ?_⟩
  rintro ⟨c, rfl⟩
  exact (rationalDilation q).commutes c

/-- With the source's hypotheses the dilation makes `K(X)` a Picard–Vessiot base field. -/
theorem rationalDilation_isBaseField [CharZero K] [IsAlgClosed K]
    (q : Kˣ) (hq : orderOf q = 0) : (rationalDilationOperator q).IsBaseField := by
  refine ⟨inferInstance, ?_⟩
  rw [rationalDilation_constantSubfield q hq]
  exact IsAlgClosed.of_ringEquiv K _ (algebraMap K (RatFunc K)).rangeRestrictFieldEquiv

end GaloisFormalization.PV
