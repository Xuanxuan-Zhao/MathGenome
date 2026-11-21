import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.SerreCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.ReducednessCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.NormalityAndIntegralClosure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.NormalLocalDepth
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.CodimensionOneMembership
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.RegularLocalLowDimension

/-! Serre's criterion SN-09. The reverse implication first establishes
reducedness, then detects integral total fractions in codimension one.
Neither direction assumes that the ambient ring is a domain or nonzero. -/
universe u
namespace AdvCommAlg.Normality

variable (A : Type u) [CommRing A] [IsNoetherianRing A]

/-- The ring specialization of `(S_k)` uses the ring itself at each prime. -/
private theorem ringSerreCondition_iff_local_depth (k : ℕ) :
    CohenMacaulay.RingSerreCondition A k ↔
      ∀ p : PrimeSpectrum A,
        min (k : WithBot ℕ∞) (ringKrullDim (Localization.AtPrime p.asIdeal)) ≤
          (IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime p.asIdeal)) : WithBot ℕ∞) := by
  have he (p : PrimeSpectrum A) :
      (LocalizedModule.AtPrime p.asIdeal A) ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime p.asIdeal :=
    (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl A)
      (Algebra.linearMap A (Localization.AtPrime p.asIdeal))).extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
  constructor
  · intro h p
    have : Nontrivial (LocalizedModule.AtPrime p.asIdeal A) := (he p).toEquiv.nontrivial
    have hp := h p (by
      change Nontrivial (LocalizedModule.AtPrime p.asIdeal A)
      infer_instance)
    rwa [Module.supportDim_eq_of_equiv (he p), Module.supportDim_self_eq_ringKrullDim,
      IsLocalRing.depth_eq_of_linearEquiv (he p)] at hp
  · intro h p _
    rw [Module.supportDim_eq_of_equiv (he p), Module.supportDim_self_eq_ringKrullDim,
      IsLocalRing.depth_eq_of_linearEquiv (he p)]
    exact h p

/-- A Noetherian ring is normal exactly when it satisfies `(R₁)` and `(S₂)`.
This includes reducible normal rings and the zero ring. -/
theorem serreCriterion :
    IsNormal A ↔ RegularInCodimension A 1 ∧ CohenMacaulay.RingSerreCondition A 2 := by
  constructor
  · intro hn
    constructor
    · intro p hp
      let S := Localization.AtPrime p.asIdeal
      have : IsDomain S := (hn p).1
      have : IsIntegrallyClosed S := (hn p).2
      have hd : ringKrullDim S ≤ 1 := by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal S]
        exact WithBot.coe_le_coe.mpr hp
      by_cases hz : ringKrullDim S = 0
      · have : Ring.KrullDimLE 0 S := Ring.krullDimLE_iff.mpr hz.le
        let : Field S := (Ring.KrullDimLE.isField_of_isReduced (R := S)).toField
        infer_instance
      · have hdim : ringKrullDim S = 1 := by
          apply le_antisymm hd
          apply le_of_not_gt
          intro hlt
          apply hz
          apply le_antisymm ?_ (ringKrullDim_nonneg_of_nontrivial (R := S))
          exact ENat.WithBot.lt_add_one_iff.mp (by simpa using hlt)
        exact (dimension_one_dvr_equivalences S hdim).1.mp inferInstance
    · apply (ringSerreCondition_iff_local_depth A 2).mpr
      intro p
      let S := Localization.AtPrime p.asIdeal
      have : IsDomain S := (hn p).1
      have : IsIntegrallyClosed S := (hn p).2
      have h := normal_local_depth_lower_bound S
      rw [Depth.depth_eq_libraryDepth (R := S) (ModuleCat.of S S)] at h
      exact h
  · rintro ⟨hR, hS⟩
    have hR0 : RegularInCodimension A 0 := by
      intro p hp
      exact hR p (hp.trans (by norm_num))
    have hS1 : CohenMacaulay.RingSerreCondition A 1 := by
      apply (ringSerreCondition_iff_local_depth A 1).mpr
      intro p
      exact (min_le_min_right _ (by norm_num : (1 : WithBot ℕ∞) ≤ 2)).trans
        ((ringSerreCondition_iff_local_depth A 2).mp hS p)
    have : IsReduced A :=
      (isReduced_iff_regularInCodimension_zero_and_serreCondition_one A).mpr ⟨hR0, hS1⟩
    apply isNormal_of_integral_totalQuotient A
    intro z hz
    apply codimensionOne_membership A hS z
    intro p hp
    let S := Localization.AtPrime p.asIdeal
    have : IsRegularLocalRing S := hR p hp
    have hd : ringKrullDim S ≤ 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal S]
      exact WithBot.coe_le_coe.mpr hp
    have : IsIntegrallyClosed S := (regularLocal_low_dimension_integrallyClosed S hd).2
    apply (isIntegrallyClosed_iff (FractionRing S)).mp inferInstance
    exact hz.map_of_comp_eq (algebraMap A S) (totalQuotientToAtPrime A p)
      (by ext a; exact (totalQuotientToAtPrime_algebraMap A p a).symm)

end AdvCommAlg.Normality
