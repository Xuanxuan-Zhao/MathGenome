import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.SerreIntersectionDimension
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.EqualCharacteristicIntersection
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.RamifiedIntersectionDimension
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.UnramifiedIntersection
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.HeightAndGrade
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalLocalization
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.RegularLocalLowDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-! Serre's dimension and height bounds over regular local rings (I13). -/

open IsLocalRing AdvCommAlg.CohenMacaulay
open P103.Specs.Ch06.DimensionConventions (moduleDimensionValue ringDimensionValue)
open scoped TensorProduct

namespace CommutativeAlgebraNotes.Intersection.SerreIntersectionDimension

universe u v w

/-- The dimension bound in all characteristics. -/
theorem dimensionBound : Specs.dimensionBoundType.{u,v,w} := by
  intro R _ _ M N _ _ _ _ hlen
  let d := (maximalIdeal R).spanFinrank
  have hd : ringKrullDim R = (d : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  rw [hd]
  have equalCase (hchar : ringChar (ResidueField R) = ringChar R) :
      moduleDimensionValue R M + moduleDimensionValue R N ≤ (d : WithBot ℕ∞) := by
    obtain ⟨_, _, _, _, _, _, _, hbound, _⟩ :=
      EqualCharacteristicIntersection.equalCharacteristic R d hd hchar M N hlen
    exact hbound
  let : IsDomain R := AdvCommAlg.Normality.regularLocal_isDomain R
  rcases CharP.char_is_prime_or_zero R (ringChar R) with hprime | hzero
  · have hcast : (ringChar R : ResidueField R) = 0 := by
      rw [← map_natCast (residue R), CharP.cast_eq_zero, map_zero]
    exact equalCase (CharP.ringChar_of_prime_eq_zero hprime hcast)
  · let p := ringChar (ResidueField R)
    rcases CharP.char_is_prime_or_zero (ResidueField R) p with hp | hreszero
    · let : CharP R 0 := ringChar.of_eq hzero
      let : CharZero R := CharP.charP_to_charZero R
      by_cases hram : (p : R) ∈ maximalIdeal R ^ 2
      · exact RamifiedIntersectionDimension.ramifiedIntersectionDimension
          R p d hp hd hram M N hlen
      · exact (UnramifiedIntersection.unramifiedIntersection
          R p d hp hd hram M N hlen).1
    · exact equalCase (hreszero.trans hzero.symm)

private theorem quotientDimension {A : Type u} [CommRing A] (I : Ideal A) :
    moduleDimensionValue A (ModuleCat.of A (A ⧸ I)) = ringKrullDim (A ⧸ I) := by
  change ringDimensionValue (A ⧸ Module.annihilator A (A ⧸ I)) = _
  rw [Ideal.annihilator_quotient]
  rfl

/-- The height bound follows by applying the dimension bound in the
localization at the chosen minimal prime over the sum. -/
theorem heightBound : Specs.heightBoundType.{u} := by
  intro R _ _ p q r _ _ hr
  let : r.IsPrime := hr.isPrime
  let A := Localization.AtPrime r
  let : IsRegularLocalRing A := regularLocal_localization_atPrime R r
  let P := p.map (algebraMap R A)
  let Q := q.map (algebraMap R A)
  have hpr : p ≤ r := (show p ≤ p + q from le_sup_left).trans hr.le
  have hqr : q ≤ r := (show q ≤ p + q from le_sup_right).trans hr.le
  let : P.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime r hpr
  let : Q.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime r hqr
  have hpheight : P.height = p.height := by
    rw [← IsLocalization.height_under r.primeCompl, Ideal.under_map_of_isLocalizationAtPrime r hpr]
  have hqheight : Q.height = q.height := by
    rw [← IsLocalization.height_under r.primeCompl, Ideal.under_map_of_isLocalizationAtPrime r hqr]
  have hrheight : ringKrullDim A = (r.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height r A
  let M := ModuleCat.of A (A ⧸ P)
  let N := ModuleCat.of A (A ⧸ Q)
  have hlen : IsFiniteLength A (M ⊗[A] N) := by
    apply (IsolatedTorSupport.isolated_tensor_iff M N).2
    have hrad : (P ⊔ Q).radical = maximalIdeal A := by
      change (p.map (algebraMap R A) ⊔ q.map (algebraMap R A)).radical = _
      rw [← Ideal.map_sup]
      exact (IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes A r (p + q) hr).trans
        Localization.AtPrime.map_eq_maximalIdeal
    change Module.support A (A ⧸ P) ∩ Module.support A (A ⧸ Q) ⊆ _
    simp only [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    rw [← PrimeSpectrum.zeroLocus_sup, ← PrimeSpectrum.zeroLocus_radical, hrad,
      PrimeSpectrum.zeroLocus_eq_singleton]
    exact Set.Subset.rfl
  have hsum := dimensionBound A M N hlen
  rw [quotientDimension P, quotientDimension Q, hrheight] at hsum
  have hCM : CohenMacaulayRing A := fun s => by
    let := regularLocal_localization_atPrime A s.asIdeal
    exact regularLocal_cohenMacaulay (Localization.AtPrime s.asIdeal)
  have hpdim := prime_height_add_quotient_dimension hCM ⟨P, inferInstance⟩
  have hqdim := prime_height_add_quotient_dimension hCM ⟨Q, inferInstance⟩
  change (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) = ringKrullDim A at hpdim
  change (Q.height : WithBot ℕ∞) + ringKrullDim (A ⧸ Q) = ringKrullDim A at hqdim
  rw [hpheight, hrheight] at hpdim
  rw [hqheight, hrheight] at hqdim
  obtain ⟨dp, hdp⟩ := WithBot.ne_bot_iff_exists.mp
    (ne_bot_of_le_ne_bot (by simp) (ringKrullDim_nonneg_of_nontrivial (R := A ⧸ P)))
  obtain ⟨dq, hdq⟩ := WithBot.ne_bot_iff_exists.mp
    (ne_bot_of_le_ne_bot (by simp) (ringKrullDim_nonneg_of_nontrivial (R := A ⧸ Q)))
  rw [← hdp, ← hdq, ← WithBot.coe_add, WithBot.coe_le_coe] at hsum
  rw [← hdp, ← WithBot.coe_add, WithBot.coe_eq_coe] at hpdim
  rw [← hdq, ← WithBot.coe_add, WithBot.coe_eq_coe] at hqdim
  apply (ENat.add_le_add_iff_right (Ideal.height_ne_top_of_isPrime (I := r))).mp
  calc
    r.height + r.height = (p.height + dp) + (q.height + dq) :=
      congrArg₂ (· + ·) hpdim.symm hqdim.symm
    _ = (p.height + q.height) + (dp + dq) := add_add_add_comm _ _ _ _
    _ ≤ (p.height + q.height) + r.height := add_le_add_right hsum _

end CommutativeAlgebraNotes.Intersection.SerreIntersectionDimension
