import MathGenome.Internal.Specs.D07.Ch19.PartialFractions
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain

/-! Normalized partial fractions over an arbitrary field. -/

universe u

namespace D07.Ch19.PartialFractions

open Polynomial
open Specs.D07.Ch19.PartialFractions
open scoped BigOperators

variable {F : Type u} [Field F] {r : ℕ}

lemma factors_coprime {p : Fin r → Polynomial F}
    (hm : ∀ i, (p i).Monic) (hi : ∀ i, Irreducible (p i))
    (hd : Function.Injective p) :
    Set.Pairwise (↑(Finset.univ : Finset (Fin r))) (fun i j => IsCoprime (p i) (p j)) := by
  intro i _ j _ hij
  apply (hi i).coprime_iff_not_dvd.mpr
  intro hdiv
  exact hij (hd (eq_of_monic_of_associated (hm i) (hm j)
    ((hi i).associated_of_dvd (hi j) hdiv)))

lemma factor_image_ne_zero {p : Fin r → Polynomial F}
    (hm : ∀ i, (p i).Monic) (i : Fin r) :
    algebraMap (Polynomial F) (FractionRing (Polynomial F)) (p i) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hm i).ne_zero

lemma decomposition_exists (p : Fin r → Polynomial F) (e : Fin r → ℕ)
    (f : Polynomial F) (hm : ∀ i, (p i).Monic)
    (hc : Set.Pairwise (↑(Finset.univ : Finset (Fin r)))
      (fun i j => IsCoprime (p i) (p j))) :
    ∃ ha : Form F r e, IsDecomposition f p e ha := by
  have hinv (i : Fin r) (_ : i ∈ (Finset.univ : Finset (Fin r))) :
      (algebraMap (Polynomial F) (FractionRing (Polynomial F)) (p i))⁻¹ *
        algebraMap (Polynomial F) (FractionRing (Polynomial F)) (p i) = 1 :=
    inv_mul_cancel₀ (factor_image_ne_zero hm i)
  obtain ⟨h, a, hb, heq⟩ :=
    Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
      f (fun i _ => hm i) hc e hinv
  refine ⟨(h, a), (fun i j => hb i (Finset.mem_univ i) j), ?_⟩
  simpa only [denominator, map_prod, map_pow, div_eq_mul_inv, inv_pow,
    Finset.prod_inv_distrib] using heq

lemma decomposition_unique {p : Fin r → Polynomial F} {e : Fin r → ℕ}
    {f : Polynomial F} (hm : ∀ i, (p i).Monic)
    (hc : Set.Pairwise (↑(Finset.univ : Finset (Fin r)))
      (fun i j => IsCoprime (p i) (p j)))
    {ha hb : Form F r e} (ha_valid : IsDecomposition f p e ha)
    (hb_valid : IsDecomposition f p e hb) : ha = hb := by
  have hinv (i : Fin r) (_ : i ∈ (Finset.univ : Finset (Fin r))) :
      (algebraMap (Polynomial F) (FractionRing (Polynomial F)) (p i))⁻¹ *
        algebraMap (Polynomial F) (FractionRing (Polynomial F)) (p i) = 1 :=
    inv_mul_cancel₀ (factor_image_ne_zero hm i)
  have heq := ha_valid.2.symm.trans hb_valid.2
  simp only [div_eq_mul_inv, ← inv_pow] at heq
  obtain ⟨hh, hab⟩ := Polynomial.quo_add_sum_rem_mul_pow_inverse_unique
    (q₁ := ha.1) (q₂ := hb.1)
    (fun i _ => hm i) hc hinv (fun i _ j => ha_valid.1 i j)
      (fun i _ j => hb_valid.1 i j) heq
  exact Prod.ext hh (funext (fun i => hab i (Finset.mem_univ i)))

theorem normalized_partial_fractions : NormalizedPartialFractions.{u} := by
  intro F _ r p e f hm hi hd _he
  have hc := factors_coprime hm hi hd
  obtain ⟨ha, hvalid⟩ := decomposition_exists p e f hm hc
  exact ⟨ha, hvalid, fun hb hb_valid => decomposition_unique hm hc hb_valid hvalid⟩

theorem denominator_normalization : DenominatorNormalization.{u} := by
  intro F _ r p e hm hi he
  have hmon : (denominator p e).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => (hm i).pow (e i))
  refine ⟨hmon, hmon.ne_zero, ?_⟩
  constructor
  · intro hq
    by_contra hr
    let i : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    have hd : p i ∣ denominator p e :=
      dvd_trans (dvd_pow_self (p i) (Nat.ne_of_gt (he i)))
        (Finset.dvd_prod_of_mem (fun k => p k ^ e k) (Finset.mem_univ i))
    rw [hq] at hd
    exact (hi i).not_isUnit (isUnit_iff_dvd_one.mpr hd)
  · rintro rfl
    simp [denominator]

/-- Clearing the actual nonzero denominator in the fraction field. -/
lemma clear_decomposition {p : Fin r → Polynomial F} {e : Fin r → ℕ}
    {f : Polynomial F} (hm : ∀ i, (p i).Monic)
    {ha : Form F r e} (hv : IsDecomposition f p e ha) :
    f = ha.1 * denominator p e + ∑ i, ∑ j : Fin (e i),
      ha.2 i j * p i ^ (e i - (j.val + 1)) *
        ∏ k ∈ Finset.univ.erase i, p k ^ e k := by
  let φ := algebraMap (Polynomial F) (FractionRing (Polynomial F))
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have hq : φ (denominator p e) ≠ 0 := by
    apply (map_ne_zero_iff φ hinj).mpr
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hm i).ne_zero)
  apply hinj
  have heq : φ f = (φ ha.1 + ∑ i, ∑ j : Fin (e i),
      φ (ha.2 i j) / φ (p i) ^ (j.val + 1)) * φ (denominator p e) :=
    (div_eq_iff hq).mp hv.2
  rw [heq, add_mul, map_add, map_mul]
  congr 1
  simp only [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hprod : denominator p e = p i ^ e i *
      ∏ k ∈ Finset.univ.erase i, p k ^ e k :=
    (Finset.mul_prod_erase Finset.univ (fun k => p k ^ e k) (Finset.mem_univ i)).symm
  rw [hprod, map_mul, map_mul, map_mul, map_pow, map_pow,
    pow_sub₀ (φ (p i)) (factor_image_ne_zero hm i) (Nat.succ_le_of_lt j.isLt)]
  simp only [div_eq_mul_inv]
  ac_rfl

theorem top_numerators_nonzero : TopNumeratorsNonzero.{u} := by
  intro F _ r p e f hm hi _hd he hred ha hv i hzero
  have hpiq : p i ∣ denominator p e := by
    exact dvd_trans (dvd_pow_self (p i) (Nat.ne_of_gt (he i)))
      (Finset.dvd_prod_of_mem (fun k => p k ^ e k) (Finset.mem_univ i))
  have hpif : p i ∣ f := by
    rw [clear_decomposition hm hv]
    apply dvd_add
    · exact dvd_mul_of_dvd_right hpiq _
    · apply Finset.dvd_sum
      intro k _
      apply Finset.dvd_sum
      intro j _
      by_cases hki : k = i
      · subst k
        by_cases hj : j.val + 1 = e i
        · have hlast : j = ⟨e i - 1, Nat.sub_lt (he i) (by decide)⟩ := by
            apply Fin.ext
            change j.val = e i - 1
            omega
          rw [hlast, hzero, zero_mul, zero_mul]
          exact dvd_zero _
        · have hpos : 0 < e i - (j.val + 1) := by omega
          exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
            (dvd_pow_self (p i) (Nat.ne_of_gt hpos)) _) _
      · have hmem : i ∈ (Finset.univ : Finset (Fin r)).erase k := by
          simp [Ne.symm hki]
        exact dvd_mul_of_dvd_right
          (dvd_trans (dvd_pow_self (p i) (Nat.ne_of_gt (he i)))
            (Finset.dvd_prod_of_mem (fun l => p l ^ e l) hmem)) _
  exact (hi i).not_isUnit (hred.isUnit_of_dvd' hpif hpiq)

theorem empty_denominator : EmptyDenominator.{u} := by
  intro F _ f p e ha
  have hden : denominator p e = 1 := by simp [denominator]
  refine ⟨hden, ?_⟩
  simp only [IsDecomposition, hden, map_one, div_one, Finset.univ_eq_empty,
    Finset.sum_empty, add_zero]
  constructor
  · intro hv
    exact ((IsFractionRing.injective (Polynomial F) (FractionRing (Polynomial F))) hv.2).symm
  · intro hh
    exact ⟨fun i => Fin.elim0 i, by rw [hh]⟩

theorem zero_numerator : ZeroNumerator.{u} := by
  intro F _ r p e hm hi hd _he ha hv
  have hz : IsDecomposition (0 : Polynomial F) p e (0, fun _ _ => 0) := by
    refine ⟨fun i _ => ?_, ?_⟩
    · simpa only [degree_zero] using
        (bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr (hm i).ne_zero))
    · simp
  exact decomposition_unique hm (factors_coprime hm hi hd) hv hz

end D07.Ch19.PartialFractions
