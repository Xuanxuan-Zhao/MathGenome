import MathGenome.Internal.Specs.D07.Ch19.PrimitiveFermatCommonFactorClassification
import Mathlib.NumberTheory.FLT.Polynomial
import MathGenome.Internal.D07.Appendix.AlgebraicFta

/-!
The common-factor conclusion of K07.19.primitive_fermat.

Let d = gcd(f,g). The equation gives d^n | h^n, so integral closedness
of the polynomial UFD gives d | h. Cancel d^n to obtain the quotient
equation. The two gcd quotients are coprime; taking powers and using their
sum equal to the third power gives the other two coprimalities.
Mathlib's polynomial Fermat theorem (proved from Mason–Stothers) now makes
all three quotients constant. Evaluating at zero retains their scalar equation.
For the counterexample, the proved upstream FTA supplies an nth root of 2.
-/

universe u

namespace D07.Ch19.PrimitiveFermatCommonFactorClassification

open Polynomial
open Specs.D07.Ch19.PrimitiveFermatCommonFactorClassification

theorem common_gcd_reduction : CommonGcdReduction.{u} := by
  intro F _ _ n hn f g h hf hg hh heq
  classical
  dsimp only
  let d := gcd f g
  have hd : d ≠ 0 := gcd_ne_zero_of_left hf
  have hdf : d ∣ f := gcd_dvd_left f g
  have hdg : d ∣ g := gcd_dvd_right f g
  have hdh : d ∣ h := by
    apply (IsIntegrallyClosed.pow_dvd_pow_iff (by omega : n ≠ 0)).mp
    rw [← heq]
    exact dvd_add (pow_dvd_pow_of_dvd hdf n) (pow_dvd_pow_of_dvd hdg n)
  have hfe : f = d * (f / d) := (EuclideanDomain.mul_div_cancel' hd hdf).symm
  have hge : g = d * (g / d) := (EuclideanDomain.mul_div_cancel' hd hdg).symm
  have hhe : h = d * (h / d) := (EuclideanDomain.mul_div_cancel' hd hdh).symm
  have hf0 : f / d ≠ 0 := left_div_gcd_ne_zero hf
  have hg0 : g / d ≠ 0 := right_div_gcd_ne_zero hg
  have hh0 : h / d ≠ 0 := by
    intro hz
    exact hh (hhe.trans (by rw [hz, mul_zero]))
  have heq0 : (f / d) ^ n + (g / d) ^ n = (h / d) ^ n := by
    apply mul_left_cancel₀ (pow_ne_zero n hd)
    calc
      d ^ n * ((f / d) ^ n + (g / d) ^ n) = f ^ n + g ^ n := by
        rw [mul_add, ← mul_pow, ← mul_pow, ← hfe, ← hge]
      _ = h ^ n := heq
      _ = d ^ n * (h / d) ^ n := by rw [← mul_pow, ← hhe]
  have hfg : IsCoprime (f / d) (g / d) := isCoprime_div_gcd_div_gcd hg
  have hfgp : IsCoprime ((f / d) ^ n) ((g / d) ^ n) := hfg.pow
  have hfh : IsCoprime (f / d) (h / d) := by
    apply (IsCoprime.pow_iff (by omega : 0 < n) (by omega : 0 < n)).mp
    rw [← heq0]
    simpa only [mul_one] using hfgp.mul_add_left_right 1
  have hgh : IsCoprime (g / d) (h / d) := by
    apply (IsCoprime.pow_iff (by omega : 0 < n) (by omega : 0 < n)).mp
    rw [← heq0]
    simpa only [mul_one] using hfgp.symm.add_mul_left_right 1
  refine ⟨hd, ?_, hdh, ?_, hf0, hg0, hh0, hfe, hge, hhe, hfg, hfh, hgh, heq0⟩
  · simpa only [d, normalize_gcd] using (monic_normalize hd)
  · intro e hef heg _
    exact dvd_gcd hef heg

theorem common_factor_classification : CommonFactorClassification.{u} := by
  intro F _ _ n hn f g h hf hg hh heq
  classical
  obtain ⟨hd, _, _, _, hf0, hg0, hh0, hfe, hge, hhe, hfg, _, _, heq0⟩ :=
    common_gcd_reduction F n hn f g h hf hg hh heq
  let d := gcd f g
  obtain ⟨hfc, hgc, hhc⟩ := Polynomial.flt hn
    (Nat.cast_ne_zero.mpr (by omega : n ≠ 0)) hf0 hg0 hh0 hfg heq0
  obtain ⟨a, ha⟩ := natDegree_eq_zero.mp hfc
  obtain ⟨b, hb⟩ := natDegree_eq_zero.mp hgc
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hhc
  refine ⟨d, a, b, c, hd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact C_ne_zero.mp (ha ▸ hf0)
  · exact C_ne_zero.mp (hb ▸ hg0)
  · exact C_ne_zero.mp (hc ▸ hh0)
  · simpa only [← ha] using hfe
  · simpa only [← hb] using hge
  · simpa only [← hc] using hhe
  · have hs := congrArg (fun p : Polynomial F => p.eval 0) heq0
    simpa only [← ha, ← hb, ← hc, eval_add, eval_pow, eval_C] using hs

theorem complex_counterexample : ComplexCounterexample := by
  intro n hn
  have : IsAlgClosed ℂ := D07.Appendix.AlgebraicFta.algebraically_closed
  obtain ⟨c, hcn⟩ := IsAlgClosed.exists_pow_nat_eq (2 : ℂ) (by omega : 0 < n)
  have hc : c ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega : n ≠ 0)] at hcn
    norm_num at hcn
  refine ⟨c, hc, hcn, X_ne_zero, mul_ne_zero (C_ne_zero.mpr hc) X_ne_zero, ?_, ?_, ?_, ?_⟩
  · rw [mul_pow, ← C_pow, hcn]
    simp only [map_ofNat]
    ring
  · intro a he
    have hs := congrArg (fun p : Polynomial ℂ => p.coeff 1) he
    simp at hs
  · intro a he
    have hs := congrArg (fun p : Polynomial ℂ => p.coeff 1) he
    exact hc (by simpa using hs)
  · intro hi
    have hu := isCoprime_self.mp hi
    have hz := natDegree_eq_zero_of_isUnit hu
    simp at hz

end D07.Ch19.PrimitiveFermatCommonFactorClassification
