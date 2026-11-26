import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorDimensionAndMultiplicity
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.ExteriorTensorGradedLayers
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.ENat.BigOperators
import Mathlib.RingTheory.PowerSeries.Basic

namespace CommutativeAlgebraNotes.Intersection.ExteriorTensorDimensionAndMultiplicity

open Polynomial
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)
open P103.HilbertSamuelDimension (backwardDifference backwardDifference_degree
  backwardDifference_coeff)
open P103.HilbertSamuelPolynomial (quotientLength layerLength quotientLength_succ layerLength_zero)
open P103.Ch06.FiniteColength (finite_colength_iff)
open ExteriorTensorProduct ExteriorTensorInverseLimit ExteriorTensorGradedLayers
open DegreeMultiplicity

noncomputable section

local notation "δ" => (1 - PowerSeries.X : PowerSeries ℚ)

private theorem coeff_difference_zero (f : ℕ → ℚ) :
    PowerSeries.coeff 0 (δ * PowerSeries.mk f) = f 0 := by
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk]
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

private theorem coeff_difference_succ (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff (n + 1) (δ * PowerSeries.mk f) = f (n + 1) - f n := by
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_mk]

private theorem sum_coeff_difference (f : ℕ → ℚ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i (δ * PowerSeries.mk f) = f n := by
  induction n with
  | zero => simp [coeff_difference_zero]
  | succ n ih => rw [Finset.sum_range_succ, ih, coeff_difference_succ]; ring

/-- Multiply the cumulative series by (1 - X) once per finite difference.
The last difference has finite support and its sum telescopes to the eventual constant. -/
private theorem cumulative_numerator (d : ℕ) (p : Polynomial ℚ) (f : ℕ → ℚ)
    (hd : p.natDegree = d) (hf : ∃ N : ℕ, ∀ n ≥ N, f n = p.eval (n : ℚ)) :
    ∃ Q : Polynomial ℚ, δ ^ (d + 1) * PowerSeries.mk f = (Q : PowerSeries ℚ) ∧
      Q.eval 1 = (d.factorial : ℚ) * p.coeff d := by
  induction d generalizing p f with
  | zero =>
    obtain ⟨N, hN⟩ := hf
    have hconst := eq_C_of_natDegree_eq_zero hd
    let g := δ * PowerSeries.mk f
    let Q := ∑ i ∈ Finset.range (N + 1), monomial i (PowerSeries.coeff i g)
    refine ⟨Q, ?_, ?_⟩
    · rw [pow_one]
      ext i
      change PowerSeries.coeff i g = PowerSeries.coeff i (Q : PowerSeries ℚ)
      rw [Polynomial.coeff_coe]
      simp only [Q, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
      split_ifs with hi
      · rfl
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        change PowerSeries.coeff (j + 1) (δ * PowerSeries.mk f) = 0
        rw [coeff_difference_succ, hN (j + 1) (by omega), hN j (by omega), hconst]
        simp
    · simp only [Q, eval_finsetSum, eval_monomial, one_pow, mul_one, Nat.factorial_zero,
        Nat.cast_one, one_mul]
      rw [show (∑ i ∈ Finset.range (N + 1), PowerSeries.coeff i g) = f N from
        sum_coeff_difference f N, hN N le_rfl, hconst, eval_C, coeff_C_zero]
  | succ d ih =>
    let g := δ * PowerSeries.mk f
    have hpos : 0 < p.natDegree := hd.symm ▸ Nat.zero_lt_succ d
    have hdegree : (backwardDifference p).natDegree = d := by
      rw [(backwardDifference_degree p hpos).2, hd, Nat.add_sub_cancel]
    have hagree : ∃ N : ℕ, ∀ n ≥ N,
        PowerSeries.coeff n g = (backwardDifference p).eval (n : ℚ) := by
      obtain ⟨N, hN⟩ := hf
      refine ⟨N + 1, fun n hn => ?_⟩
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      change PowerSeries.coeff (j + 1) (δ * PowerSeries.mk f) = _
      rw [coeff_difference_succ, hN (j + 1) (by omega), hN j (by omega)]
      simp only [backwardDifference, eval_sub, taylor_apply, eval_comp,
        eval_add, eval_X, eval_C, Nat.cast_succ, add_neg_cancel_right]
    obtain ⟨Q, hQ, heval⟩ := ih (backwardDifference p) (fun n => PowerSeries.coeff n g)
      hdegree hagree
    have hg : PowerSeries.mk (fun n => PowerSeries.coeff n g) = g := by
      ext n
      exact PowerSeries.coeff_mk n _
    refine ⟨Q, ?_, ?_⟩
    · simpa only [hg, g, pow_succ δ (d + 1), mul_assoc] using hQ
    · have hc := backwardDifference_coeff p hpos
      rw [← coeff_natDegree, hd, Nat.add_sub_cancel] at hc
      rw [heval, hc, Nat.factorial_succ, Nat.cast_mul]
      ring

private theorem degree_le_of_numerators {H : PowerSeries ℚ} {d e : ℕ}
    {P Q : Polynomial ℚ} (hP : δ ^ d * H = (P : PowerSeries ℚ))
    (hQ : δ ^ e * H = (Q : PowerSeries ℚ)) (hQ₁ : Q.eval 1 ≠ 0) : e ≤ d := by
  by_contra! hlt
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (show d + 1 ≤ e by omega)
  have he : e = (r + 1) + d := by omega
  have h : ((((1 : Polynomial ℚ) - Polynomial.X) ^ (r + 1) * P :
      Polynomial ℚ) : PowerSeries ℚ) = Q := by
    rw [coe_mul, coe_pow, coe_sub, coe_one, coe_X, ← hP, ← mul_assoc, ← pow_add, ← he]
    exact hQ
  have h' := congrArg (Polynomial.eval 1) (Polynomial.coe_injective ℚ h)
  apply hQ₁
  simpa using h'.symm

section Local

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (E : Type*) [AddCommGroup E] [Module R E] [Module.Finite R E] [Nontrivial E]

private theorem maximalIdeal_finite_colength :
    IsFiniteLength R (E ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R E))) := by
  apply (finite_colength_iff R E (IsLocalRing.maximalIdeal R) le_rfl).2
  have ha : Module.annihilator R E ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal fun h =>
      (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial E›) (Module.annihilator_eq_top_iff.mp h)
  rw [sup_eq_left.mpr ha]
  exact Ideal.IsPrime.radical inferInstance

end Local

section Series

variable (R : Type*) [CommRing R]
variable (E : Type*) [AddCommGroup E] [Module R E]

private def layerSeries (I : Ideal R) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (layerLength I E n : ℚ)

variable [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R E] [Nontrivial E]

private theorem layerSeries_numerator (I : Ideal R)
    (hI : I = IsLocalRing.maximalIdeal R) :
    ∃ (d : ℕ) (Q : Polynomial ℚ), moduleDimensionValue R E = (d : WithBot ℕ∞) ∧
      δ ^ d * layerSeries R E I = (Q : PowerSeries ℚ) ∧
      Q.eval 1 = hilbertSamuelMultiplicity I E ∧ 0 < Q.eval 1 := by
  have hle := hI.le
  have hlen : IsFiniteLength R (E ⧸ (I • (⊤ : Submodule R E))) :=
    hI ▸ maximalIdeal_finite_colength R E
  let p := hilbertSamuelPolynomial I E
  let f : ℕ → ℚ := fun n => quotientLength I E n
  have hd := (hilbertSamuelPolynomialDegree R E I hle hlen).2
  obtain ⟨Q, hQ, heval⟩ :=
    cumulative_numerator p.natDegree p f rfl (hilbertSamuelPolynomialEventually R E I hle hlen)
  have hseries : layerSeries R E I = δ * PowerSeries.mk f := by
    ext n
    cases n with
    | zero =>
      rw [coeff_difference_zero, layerSeries, PowerSeries.coeff_mk, layerLength_zero]
    | succ n =>
      rw [coeff_difference_succ, layerSeries, PowerSeries.coeff_mk]
      change (layerLength I E (n + 1) : ℚ) =
        (quotientLength I E (n + 1) : ℚ) - (quotientLength I E n : ℚ)
      rw [quotientLength_succ I hle hlen, Nat.cast_add, add_sub_cancel_right]
  have hm : hilbertSamuelMultiplicity I E = (p.natDegree.factorial : ℚ) * p.coeff p.natDegree :=
    hilbertSamuelMultiplicityAtDimension R E I _ hd
  have hQ₁ := heval.trans hm.symm
  refine ⟨p.natDegree, Q, hd, ?_, hQ₁, ?_⟩
  · rw [hseries, ← mul_assoc, ← pow_succ, hQ]
  · rw [hQ₁]
    exact hilbertSamuelMultiplicityPositive R E I hle hlen

end Series

section Exterior

variable (k : Type*) [Field k] (a b : ℕ) (M N : Type*)
  [AddCommGroup M] [Module (X k a) M] [Module.Finite (X k a) M] [Nontrivial M]
  [AddCommGroup N] [Module (Y k b) N] [Module.Finite (Y k b) N] [Nontrivial N]

local notation "A" => ExteriorTensorProduct.X k a
local notation "B" => ExteriorTensorProduct.Y k b
local notation "R" => S k a b
local notation "T" => Product k a b M N
local notation "mA" => variableIdeal k (Fin a)
local notation "mB" => variableIdeal k (YIndex b)
local notation "mR" => jointIdeal k a b

private theorem layerSeries_exterior :
    layerSeries R T mR = layerSeries A M mA * layerSeries B N mB := by
  ext j
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range]
  simp only [layerSeries, PowerSeries.coeff_mk]
  have hc := layerLengthConvolution k a b M N j
  change Module.length R (P103.HilbertSamuelPolynomial.Layer mR T j) =
    ∑ i : Fin (j + 1),
      Module.length A (P103.HilbertSamuelPolynomial.Layer mA M i) *
        Module.length B (P103.HilbertSamuelPolynomial.Layer mB N (j - i)) at hc
  have hA := variableIdeal_eq_maximalIdeal (k := k) (σ := Fin a)
  have hB := variableIdeal_eq_maximalIdeal (k := k) (σ := YIndex b)
  have hlenA := P103.HilbertSamuelPolynomial.finite_lengths A M mA hA.le
    (hA ▸ maximalIdeal_finite_colength A M)
  have hlenB := P103.HilbertSamuelPolynomial.finite_lengths B N mB hB.le
    (hB ▸ maximalIdeal_finite_colength B N)
  unfold layerLength
  rw [hc, ENat.toNat_sum]
  · push_cast
    simp only [ENat.toNat_mul, Nat.cast_mul]
  · intro i _
    exact WithTop.mul_ne_top (Module.length_ne_top_iff.mpr (hlenA i).1)
      (Module.length_ne_top_iff.mpr (hlenB (j - i)).1)

private theorem layerLength_zero_pos {D U : Type*} [CommRing D] [IsNoetherianRing D]
    [IsLocalRing D] [AddCommGroup U] [Module D U] [Module.Finite D U] [Nontrivial U]
    (I : Ideal D) (hI : I = IsLocalRing.maximalIdeal D) : 0 < layerLength I U 0 := by
  rw [layerLength_zero]
  exact P103.HilbertSamuelPolynomial.quotientLength_pos I hI.le
    (hI ▸ maximalIdeal_finite_colength D U) 0

private theorem exterior_nontrivial : Nontrivial T := by
  have h := congrArg (PowerSeries.coeff 0) (layerSeries_exterior k a b M N)
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul] at h
  simp only [← PowerSeries.coeff_zero_eq_constantCoeff, layerSeries,
    PowerSeries.coeff_mk] at h
  have hA := layerLength_zero_pos mA (variableIdeal_eq_maximalIdeal (σ := Fin a)) (U := M)
  have hB := layerLength_zero_pos mB (variableIdeal_eq_maximalIdeal (σ := YIndex b)) (U := N)
  rcases subsingleton_or_nontrivial T with hT | hT
  · have hz : layerLength mR T 0 = 0 := by
      unfold layerLength
      rw [Module.length_eq_zero]
      rfl
    rw [hz, Nat.cast_zero] at h
    exact False.elim ((mul_pos (by exact_mod_cast hA) (by exact_mod_cast hB)).ne' h.symm)
  · exact hT

end Exterior

/-- The completed exterior tensor product over a field adds support dimensions and
multiplies Hilbert–Samuel multiplicities. -/
theorem dimensionAndMultiplicity :
    Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorDimensionAndMultiplicity.DimensionAndMultiplicity := by
  intro k _ a b M N _ _ _ _ _ _ _ _
  dsimp only
  let A := ExteriorTensorProduct.X k a
  let B := Y k b
  let R := S k a b
  let T := Product k a b M N
  let mA := variableIdeal k (Fin a)
  let mB := variableIdeal k (YIndex b)
  let mR := jointIdeal k a b
  let : Module.Finite R T := ExteriorTensorProduct.finite
  let : Nontrivial T := exterior_nontrivial k a b M N
  obtain ⟨d, P, hd, hP, hPe, hPpos⟩ :=
    layerSeries_numerator A M mA variableIdeal_eq_maximalIdeal
  obtain ⟨e, Q, he, hQ, hQe, hQpos⟩ :=
    layerSeries_numerator B N mB variableIdeal_eq_maximalIdeal
  obtain ⟨s, F, hs, hF, hFe, hFpos⟩ :=
    layerSeries_numerator R T mR variableIdeal_eq_maximalIdeal
  have hPQ : δ ^ (d + e) * layerSeries R T mR = ((P * Q : Polynomial ℚ) : PowerSeries ℚ) := by
    rw [layerSeries_exterior k a b M N, coe_mul, ← hP, ← hQ, pow_add]
    ac_rfl
  have hPQpos : 0 < (P * Q).eval 1 := by
    rw [eval_mul]
    exact mul_pos hPpos hQpos
  have hse : s = d + e :=
    le_antisymm (degree_le_of_numerators hPQ hF hFpos.ne')
      (degree_le_of_numerators hF hPQ hPQpos.ne')
  refine ⟨inferInstanceAs (Nontrivial T), ?_, ?_⟩
  · change moduleDimensionValue R T = moduleDimensionValue A M + moduleDimensionValue B N
    rw [hs, hd, he, hse]
    norm_cast
  · change hilbertSamuelMultiplicity mR T =
      hilbertSamuelMultiplicity mA M * hilbertSamuelMultiplicity mB N
    have hFpq : F = P * Q :=
      Polynomial.coe_injective ℚ (hF.symm.trans (hse.symm ▸ hPQ))
    rw [← hFe, hFpq, eval_mul, hPe, hQe]

end

end CommutativeAlgebraNotes.Intersection.ExteriorTensorDimensionAndMultiplicity
