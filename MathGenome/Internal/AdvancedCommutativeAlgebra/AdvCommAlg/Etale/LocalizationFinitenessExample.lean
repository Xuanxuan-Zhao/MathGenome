import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.LocalizationFinitenessExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Localization
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.RingTheory.Localization.FractionRing

/-! The localization examples of ET-16. -/
namespace AdvCommAlg.Etale

universe u v

open Specs.AdvCommAlg.Etale.LocalizationExamples

/-- The explicit quotient presentation and its invertible Jacobian. -/
theorem principal_localization_presentation : principalPresentation.{u,v} := by
  intro A L _ _ _ a _
  refine ⟨⟨(IsLocalization.algEquiv (Submonoid.powers a) L
    (Localization.Away a)).trans (Localization.awayEquivAdjoin a)⟩, ?_,
    IsLocalization.Away.algebraMap_isUnit a⟩
  simp

/-- Finite presentation follows from the one-generator, one-relation quotient. -/
theorem principal_localization_etale : principalEtale.{u,v} := by
  intro A L _ _ _ a _
  have hfp : Algebra.FinitePresentation A L :=
    IsLocalization.Away.finitePresentation a
  exact (etale_iff A L).mpr ⟨hfp,
    FormalLifting.localization_etale A L (Submonoid.powers a)⟩

theorem localization_formally_etale : localizationFormallyEtale.{u,v} := by
  exact FormalLifting.localization_etale

/-- Addition and multiplication can cancel denominator factors but cannot add primes. -/
theorem adjoin_denominator_primes : adjoinDenominatorPrimes := by
  intro s q hq
  induction hq using Algebra.adjoin_induction with
  | mem r hr =>
      intro p hp hd
      exact Finset.mem_biUnion.mpr ⟨r, hr, hp.mem_primeFactors hd r.den_ne_zero⟩
  | algebraMap z =>
      intro p hp hd
      have h : p ∣ 1 := by simpa using hd
      exact False.elim (hp.not_dvd_one h)
  | add x y _ _ hx hy =>
      intro p hp hd
      rcases hp.dvd_mul.mp (hd.trans (Rat.add_den_dvd x y)) with h | h
      · exact hx p hp h
      · exact hy p hp h
  | mul x y _ _ hx hy =>
      intro p hp hd
      rcases hp.dvd_mul.mp (hd.trans (Rat.mul_den_dvd x y)) with h | h
      · exact hx p hp h
      · exact hy p hp h

theorem rationals_not_finiteType : rationalsNotFiniteType := by
  intro h
  obtain ⟨s, hs⟩ := h.out
  let P := s.biUnion (fun r : ℚ => r.den.primeFactors)
  obtain ⟨p, hpgt, hp⟩ := Nat.exists_infinite_primes (P.sup id + 1)
  have hq : (p : ℚ)⁻¹ ∈ Algebra.adjoin ℤ (s : Set ℚ) := by
    rw [hs]
    trivial
  have hden : ((p : ℚ)⁻¹).den = p := by simp [Rat.den_inv, hp.ne_zero]
  have hmem : p ∈ P := adjoin_denominator_primes s _ hq p hp (by rw [hden])
  have hle : p ≤ P.sup id := Finset.le_sup (f := id) hmem
  omega

theorem rationals_formally_etale_not_etale : rationalsFormallyEtaleNotEtale := by
  constructor
  · exact localization_formally_etale ℤ ℚ (nonZeroDivisors ℤ)
  · intro h
    have hfp := ((etale_iff ℤ ℚ).mp h).1
    let := hfp
    exact rationals_not_finiteType inferInstance

end AdvCommAlg.Etale
