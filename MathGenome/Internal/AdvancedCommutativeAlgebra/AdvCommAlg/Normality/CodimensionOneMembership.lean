import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.AssociatedPrimeDetection
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.RegularQuotient
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.CodimensionOneMembership
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.RingTheory.Localization.Ideal

universe u
open scoped Pointwise
namespace AdvCommAlg.Normality

noncomputable abbrev totalQuotientToAtPrime := Specs.totalQuotientToAtPrimeValue

theorem nonZeroDivisor_atPrime (A : Type u) [CommRing A]
    (p : PrimeSpectrum A) (b : A) (hb : b ∈ nonZeroDivisors A) :
    algebraMap A (Localization.AtPrime p.asIdeal) b ∈
      nonZeroDivisors (Localization.AtPrime p.asIdeal) :=
  IsLocalization.nonZeroDivisors_le_comap p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) hb

theorem totalQuotientToAtPrime_algebraMap (A : Type u) [CommRing A]
    (p : PrimeSpectrum A) (a : A) :
    totalQuotientToAtPrime A p (algebraMap A (FractionRing A) a) =
      algebraMap (Localization.AtPrime p.asIdeal)
        (FractionRing (Localization.AtPrime p.asIdeal))
        (algebraMap A (Localization.AtPrime p.asIdeal) a) :=
  IsLocalization.map_eq _ _

/-- Associated primes of the quotient by a nonzerodivisor have height at most one
in an S₂ ring. The quotient is localized as a module, so this also applies to
rings with nilpotents. -/
lemma associatedPrime_quotient_height_le_one (A : Type u) [CommRing A]
    [IsNoetherianRing A] (hS : CohenMacaulay.RingSerreCondition A 2)
    (b : A) (hb : b ∈ nonZeroDivisors A) (p : PrimeSpectrum A)
    (hp : p.asIdeal ∈ associatedPrimes A (A ⧸ Ideal.span {b})) :
    p.asIdeal.height ≤ 1 := by
  let S := Localization.AtPrime p.asIdeal
  let I : Ideal A := Ideal.span {b}
  let J : Ideal S := I.localized' S p.asIdeal.primeCompl (Algebra.linearMap A S)
  let C := S ⧸ J
  let f : A ⧸ I →ₗ[A] C := I.toLocalizedQuotient' S p.asIdeal.primeCompl
    (Algebra.linearMap A S)
  have hJ : J = Ideal.span {algebraMap A S b} := by
    dsimp [J, I]
    rw [Ideal.localized'_eq_map, Ideal.map_span]
    simp
  have hass : IsLocalRing.maximalIdeal S ∈ associatedPrimes S C := by
    apply Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      p.asIdeal.primeCompl f
    change (IsLocalRing.maximalIdeal S).under A ∈ associatedPrimes A (A ⧸ I)
    rw [IsLocalization.AtPrime.under_maximalIdeal S p.asIdeal]
    exact hp
  haveI : Nontrivial C := by
    by_contra h
    haveI : Subsingleton C := not_nontrivial_iff_subsingleton.mp h
    exact not_isAssociatedPrime_of_subsingleton hass
  have hz : IsLocalRing.depth (ModuleCat.of S C) = 0 :=
    (CohenMacaulay.depth_eq_zero_iff_maximal_associated S C).mpr hass
  have hbS := nonZeroDivisor_atPrime A p b hb
  have hbmem : algebraMap A S b ∈ IsLocalRing.maximalIdeal S := by
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff S p.asIdeal b).mpr
    apply hp.annihilator_le
    rw [Submodule.annihilator_top, Ideal.annihilator_quotient]
    exact Ideal.subset_span (by simp)
  have hreg : RingTheory.Sequence.IsRegular S [algebraMap A S b] := by
    apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
      (by simpa using hbmem)).mpr
    apply (RingTheory.Sequence.isWeaklyRegular_singleton_iff S _).mpr
    exact (isRegular_iff_mem_nonZeroDivisors.mpr hbS).left
  have hm : IsLocalRing.maximalIdeal S • (⊤ : Submodule S S) ≠ ⊤ := by
    change IsLocalRing.maximalIdeal S * ⊤ ≠ ⊤
    simpa using (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  have hQ : (Ideal.ofList [algebraMap A S b] • (⊤ : Submodule S S)) = J := by
    change Ideal.ofList [algebraMap A S b] * ⊤ = J
    rw [Ideal.mul_top, Ideal.ofList_singleton, hJ]
  have hdrop := Depth.grade_quotient_regular S (IsLocalRing.maximalIdeal S) hm
    [algebraMap A S b] hreg (by simpa using hbmem)
  rw [hQ] at hdrop
  have hd : IsLocalRing.depth (ModuleCat.of S S) ≤ 1 := by
    have hzero : Depth.grade (IsLocalRing.maximalIdeal S) C = 0 := by
      exact (Depth.grade_eq_idealDepth _ (ModuleCat.of S C)).trans hz
    have he : Depth.grade (IsLocalRing.maximalIdeal S) S - 1 = 0 := by
      simpa only [List.length_singleton, Nat.cast_one] using hdrop.symm.trans hzero
    rw [← Depth.depth_eq_libraryDepth]
    exact tsub_eq_zero_iff_le.mp he
  let e : (LocalizedModule.AtPrime p.asIdeal A) ≃ₗ[S] S :=
    (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl A) (Algebra.linearMap A S)).extendScalarsOfIsLocalization
      p.asIdeal.primeCompl S
  haveI : Nontrivial (LocalizedModule.AtPrime p.asIdeal A) := e.toEquiv.nontrivial
  have hs := hS p (by
    change Nontrivial (LocalizedModule.AtPrime p.asIdeal A)
    infer_instance)
  rw [Module.supportDim_eq_of_equiv e, Module.supportDim_self_eq_ringKrullDim,
    IsLocalRing.depth_eq_of_linearEquiv e,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal S] at hs
  have hh : min (2 : WithBot ℕ∞) (p.asIdeal.height : WithBot ℕ∞) ≤ 1 :=
    hs.trans (WithBot.coe_le_coe.mpr hd)
  rcases min_le_iff.mp hh with h | h
  · norm_num at h
  · exact WithBot.coe_le_coe.mp h

/-- Membership in A is detected in the total quotient rings of its prime
localizations of height at most one, assuming only the Noetherian S₂ condition. -/
theorem codimensionOne_membership (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hS : CohenMacaulay.RingSerreCondition A 2) (z : FractionRing A)
    (hloc : ∀ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 →
      totalQuotientToAtPrime A p z ∈ Set.range
        (algebraMap (Localization.AtPrime p.asIdeal)
          (FractionRing (Localization.AtPrime p.asIdeal)))) :
    z ∈ Set.range (algebraMap A (FractionRing A)) := by
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors A) z
  have ha : a ∈ Ideal.span {b.val} := by
    by_contra ha
    let I : Ideal A := Ideal.span {b.val}
    have hq : Ideal.Quotient.mk I a ≠ 0 := by
      exact fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp h)
    obtain ⟨p, hp, hsurv⟩ := exists_associatedPrime_localized_ne_zero A (A ⧸ I)
      (Ideal.Quotient.mk I a) hq
    have hht := associatedPrime_quotient_height_le_one A hS b.val b.property p hp
    obtain ⟨x, hx⟩ := hloc p hht
    let S := Localization.AtPrime p.asIdeal
    have hx' : algebraMap S (FractionRing S) x =
        IsLocalization.mk' (FractionRing S) (algebraMap A S a)
          ⟨algebraMap A S b.val, nonZeroDivisor_atPrime A p b.val b.property⟩ := by
      simpa only [totalQuotientToAtPrime, Specs.totalQuotientToAtPrimeValue,
        IsLocalization.map_mk'] using hx
    have he : x * algebraMap A S b.val = algebraMap A S a := by
      apply IsFractionRing.injective S (FractionRing S)
      simpa only [map_mul] using (IsLocalization.eq_mk'_iff_mul_eq.mp hx')
    have hmem : algebraMap A S a ∈ I.map (algebraMap A S) := by
      dsimp [I]
      rw [Ideal.map_span, Set.image_singleton]
      apply Ideal.mem_span_singleton.mpr
      exact ⟨x, by simpa only [mul_comm] using he.symm⟩
    obtain ⟨s, hs, hsa⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.asIdeal.primeCompl S I a).mp hmem
    apply hsurv
    change LocalizedModule.mkLinearMap p.asIdeal.primeCompl (A ⧸ I)
      (Ideal.Quotient.mk I a) = 0
    apply (IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (A ⧸ I))).mpr
    refine ⟨⟨s, hs⟩, ?_⟩
    change Ideal.Quotient.mk I (s * a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hsa
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨c, ?_⟩
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [← map_mul]
  congr 1
  exact (mul_comm c b.val).trans hc.symm

end AdvCommAlg.Normality
