import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.AssociatedPrimeDetection
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.ReducednessCriterion
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.KrullDimension.Zero

/-! The reducedness criterion SN-03.

For the forward `(S₁)` implication we use an equivalent algebraic proof:
in a reduced ring a prime annihilator `ann(x)` cannot contain `x`.
Consequently every prime contained in `ann(x)` equals it, so every associated
prime is minimal. SN-02 then supplies the full localized depth inequality.
For the converse we detect a putative nonzero nilpotent at an associated
prime, whose localization is a field by `(S₁)` and `(R₀)`.
-/
universe u
namespace AdvCommAlg.Normality

variable (A : Type u) [CommRing A] [IsNoetherianRing A]

/-- Reduced minimal-prime localizations are fields. -/
theorem isField_localization_minimalPrime [IsReduced A] (p : PrimeSpectrum A)
    (hp : p.asIdeal ∈ minimalPrimes A) : IsField (Localization.AtPrime p.asIdeal) := by
  have : Ring.KrullDimLE 0 (Localization.AtPrime p.asIdeal) :=
    Ring.KrullDimLE.of_isLocalization p.asIdeal hp _
  exact Ring.KrullDimLE.isField_of_isReduced

theorem regularInCodimension_zero_of_isReduced [IsReduced A] :
    RegularInCodimension A 0 := by
  intro p hp
  have hmin : p.asIdeal ∈ minimalPrimes A :=
    Ideal.height_eq_zero_iff.mp (le_antisymm hp bot_le)
  let := (isField_localization_minimalPrime A p hmin).toField
  infer_instance

theorem ringSerreCondition_one_of_isReduced [IsReduced A] :
    CohenMacaulay.RingSerreCondition A 1 := by
  apply (serreCondition_one_iff_associatedPrimes_minimal A A).mpr
  intro p hp
  obtain ⟨hprime, x, hx⟩ := isAssociatedPrime_iff.mp hp
  have hxnot : x ∉ p.asIdeal := by
    intro hxp
    have hxx : x * x = 0 := by
      simpa only [hx, Submodule.mem_colon_singleton, Submodule.mem_bot,
        smul_eq_mul] using hxp
    have hxzero : x = 0 := (show IsNilpotent x from ⟨2, by simpa [pow_two] using hxx⟩).eq_zero
    apply hprime.ne_top
    rw [hx, hxzero, Submodule.colon_singleton_zero]
  refine ⟨CohenMacaulay.mem_support_of_associatedPrime A A p hp, ?_⟩
  intro q _ hqp a ha
  have hax : a * x = 0 := by
    simpa only [hx, Submodule.mem_colon_singleton, Submodule.mem_bot,
      smul_eq_mul] using ha
  exact (q.isPrime.mem_or_mem (hax ▸ q.asIdeal.zero_mem)).resolve_right
    (fun hxq => hxnot (hqp hxq))

/-- Every positive-dimensional localization of a reduced Noetherian ring has positive depth. -/
theorem depth_pos_localization_of_isReduced [IsReduced A] (p : PrimeSpectrum A)
    (hd : 0 < ringKrullDim (Localization.AtPrime p.asIdeal)) :
    0 < IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal)) := by
  let S := Localization.AtPrime p.asIdeal
  have hann : Module.annihilator S S = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  apply bot_lt_iff_ne_bot.mpr
  intro hz
  have hass := (CohenMacaulay.depth_eq_zero_iff_maximal_associated S S).mp hz
  have heq := (CohenMacaulay.serreCondition_one_iff_associatedPrimes_eq_minimalPrimes S S).mp
    (ringSerreCondition_one_of_isReduced S)
  have hmin : IsLocalRing.maximalIdeal S ∈ minimalPrimes S := by
    change IsLocalRing.maximalIdeal S ∈ (⊥ : Ideal S).minimalPrimes
    rw [← hann, ← heq]
    exact hass
  have hh := Ideal.height_eq_zero_iff.mpr hmin
  have he : ringKrullDim S = 0 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hh]
    rfl
  exact (ne_of_gt hd) he

/-- A zero-dimensional regular local ring has zero maximal ideal, hence is a field. -/
lemma isField_localization_minimalPrime_of_regularInCodimension_zero
    (hR : RegularInCodimension A 0) (p : PrimeSpectrum A)
    (hp : p.asIdeal ∈ minimalPrimes A) : IsField (Localization.AtPrime p.asIdeal) := by
  have hh : p.asIdeal.height = 0 := Ideal.height_eq_zero_iff.mpr hp
  have := hR p (by simp [hh])
  apply IsLocalRing.isField_iff_maximalIdeal_eq.mpr
  apply (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp
  have hdim : ringKrullDim (Localization.AtPrime p.asIdeal) = 0 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal, hh]
    rfl
  have he := IsRegularLocalRing.spanFinrank_maximalIdeal (R := Localization.AtPrime p.asIdeal)
  rw [hdim] at he
  exact_mod_cast he

/-- A commutative Noetherian ring is reduced exactly when it satisfies `(R₀)` and `(S₁)`.
No nontriviality assumption is imposed on `A`. -/
theorem isReduced_iff_regularInCodimension_zero_and_serreCondition_one :
    IsReduced A ↔ RegularInCodimension A 0 ∧ CohenMacaulay.RingSerreCondition A 1 := by
  constructor
  · intro h
    let := h
    exact ⟨regularInCodimension_zero_of_isReduced A, ringSerreCondition_one_of_isReduced A⟩
  · rintro ⟨hR, hS⟩
    constructor
    intro x hx
    by_contra hxzero
    obtain ⟨p, hp, hxp⟩ := exists_associatedPrime_localized_ne_zero A A x hxzero
    have hmin := (serreCondition_one_iff_associatedPrimes_minimal A A).mp hS p hp
    have hmin' : p.asIdeal ∈ minimalPrimes A := by
      refine ⟨⟨p.isPrime, bot_le⟩, ?_⟩
      intro q hq hqp
      apply hmin.2 (y := ⟨q, hq.1⟩) _ hqp
      apply Module.mem_support_iff_of_finite.mpr
      rw [Module.annihilator_eq_bot.mpr (inferInstance : FaithfulSMul A A)]
      exact bot_le
    let := (isField_localization_minimalPrime_of_regularInCodimension_zero A hR p hmin').toField
    have hz : algebraMap A (Localization.AtPrime p.asIdeal) x = 0 :=
      (hx.map (algebraMap A (Localization.AtPrime p.asIdeal))).eq_zero
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl _ x).mp hz
    apply hxp
    change LocalizedModule.mkLinearMap p.asIdeal.primeCompl A x = 0
    apply (IsLocalizedModule.eq_zero_iff p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl A)).mpr
    exact ⟨s, hs⟩

end AdvCommAlg.Normality
