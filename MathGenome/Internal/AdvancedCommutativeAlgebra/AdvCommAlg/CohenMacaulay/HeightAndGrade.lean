import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.LocalDetection
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.HeightAndGrade

/-! The ideal-height and quotient-dimension assertions in CM-07. -/
universe u
namespace AdvCommAlg.CohenMacaulay
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The module localization of the ring is its ring localization, with the
canonical localized scalar action. -/
noncomputable def localizedSelfEquiv (p : PrimeSpectrum R) :
    LocalizedModule.AtPrime p.asIdeal R ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal :=
  (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl R)
    (Algebra.linearMap R (Localization.AtPrime p.asIdeal))).extendScalarsOfIsLocalization
      p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)

omit [IsNoetherianRing R] in
lemma self_mem_support (p : PrimeSpectrum R) : p ∈ Module.support R R := by
  have hAnn : Module.annihilator R R = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
  rw [Module.support_eq_zeroLocus, hAnn]
  change (⊥ : Ideal R) ≤ p.asIdeal
  exact bot_le

lemma localized_depth_eq_height (hCM : CohenMacaulayRing R) (p : PrimeSpectrum R) :
    Depth.depth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal R) =
      p.asIdeal.height := by
  apply WithBot.coe_inj.mp
  rw [Depth.depth_eq_libraryDepth (ModuleCat.of _ _),
    IsLocalRing.depth_eq_of_linearEquiv (localizedSelfEquiv p),
    (cohenMacaulayAt_iff_depth_eq R p).mp (hCM p),
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal)]

/-- Grade equals height for every proper ideal of a Noetherian CM ring. -/
theorem grade_eq_height (hCM : CohenMacaulayRing R) (I : Ideal R) (hI : I ≠ ⊤) :
    Depth.grade I R = I.height := by
  apply le_antisymm (Depth.grade_le_height I hI)
  rw [Depth.grade_eq_iInf_localDepth R I]
  refine le_iInf fun p => le_iInf fun hIp => le_iInf fun _hp => ?_
  rw [localized_depth_eq_height hCM p]
  exact Ideal.height_mono hIp

omit [IsNoetherianRing R] in
/-- Passing to the closed subset of primes containing an ideal leaves every
upper interval unchanged, so quotient dimension is the supremum of coheights. -/
lemma quotient_dimension_eq_iSup_coheight (I : Ideal R) (hI : I ≠ ⊤) :
    ringKrullDim (R ⧸ I) =
      ((⨆ p : PrimeSpectrum.zeroLocus (R := R) (I : Set R), Order.coheight p.1) : ℕ∞) := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hI
  let : Nonempty (PrimeSpectrum.zeroLocus (R := R) (I : Set R)) := ⟨⟨⟨p, hp.isPrime⟩, hp.le⟩⟩
  rw [ringKrullDim_quotient, Order.krullDim_eq_iSup_coheight_of_nonempty]
  congr 1
  apply iSup_congr
  intro p
  apply Order.coheight_eq_of_strictMono (fun a : PrimeSpectrum.zeroLocus (R := R) (I : Set R) => a.1)
    (fun _ _ h => h)
  intro a b hab
  exact ⟨⟨b, (show I ≤ a.1.asIdeal from a.2).trans hab.le⟩, hab, rfl⟩

section Local
variable [IsLocalRing R]

lemma localCohenMacaulay_self_of_ring (hCM : CohenMacaulayRing R) :
    LocalCohenMacaulay R R := by
  apply (localCohenMacaulay_self_iff R).mpr
  rw [← Depth.depth_eq_libraryDepth (ModuleCat.of R R), Depth.depth_eq_grade,
    grade_eq_height hCM _ (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
  exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim

/-- The CM local dimension formula at a prime, expressed using ideal height. -/
lemma prime_height_add_quotient_dimension (hCM : CohenMacaulayRing R) (p : PrimeSpectrum R) :
    (p.asIdeal.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p.asIdeal) = ringKrullDim R := by
  have h := dimension_eq_localized_add_dim R (localCohenMacaulay_self_of_ring hCM)
    p (self_mem_support p)
  rw [dimension, Module.supportDim_self_eq_ringKrullDim] at h
  rw [dimension, Module.supportDim_eq_of_equiv (localizedSelfEquiv p),
    Module.supportDim_self_eq_ringKrullDim,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal)] at h
  exact h.symm

/-- In a local Noetherian CM ring, height and quotient dimension add to the
ring dimension for every proper ideal. No primality or generator bound is assumed. -/
theorem height_add_quotient_dimension (hCM : CohenMacaulayRing R)
    (I : Ideal R) (hI : I ≠ ⊤) :
    (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I) = ringKrullDim R := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top hI)
  obtain ⟨p, hp, hIp, hph⟩ := Ideal.exists_isPrime_height_eq hn.symm
  let := hp
  let P : PrimeSpectrum.zeroLocus (R := R) (I : Set R) := ⟨⟨p, hp⟩, hIp⟩
  let : Nonempty (PrimeSpectrum.zeroLocus (R := R) (I : Set R)) := ⟨P⟩
  have coheight_dim (q : PrimeSpectrum R) :
      (Order.coheight q : WithBot ℕ∞) = ringKrullDim (R ⧸ q.asIdeal) := by
    rw [Order.coheight_eq_krullDim_Ici, ringKrullDim_quotient]
    rfl
  have prime_eq (q : PrimeSpectrum R) :
      (q.asIdeal.height : WithBot ℕ∞) + (Order.coheight q : WithBot ℕ∞) =
        ringKrullDim R := by
    rw [coheight_dim]
    exact prime_height_add_quotient_dimension hCM q
  rw [quotient_dimension_eq_iSup_coheight I hI, ← WithBot.coe_add]
  apply le_antisymm
  · rw [ENat.add_iSup, WithBot.coe_iSup (OrderTop.bddAbove _)]
    apply iSup_le
    intro q
    rw [WithBot.coe_add]
    exact (add_le_add (WithBot.coe_le_coe.mpr (Ideal.height_mono q.2)) le_rfl).trans
      (prime_eq q.1).le
  · calc
      ringKrullDim R = (p.height : WithBot ℕ∞) + (Order.coheight P.1 : WithBot ℕ∞) :=
        (prime_eq P.1).symm
      _ = ((I.height + Order.coheight P.1 : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add, hph, hn]
      _ ≤ _ := WithBot.coe_le_coe.mpr (add_le_add le_rfl (le_iSup (fun q : PrimeSpectrum.zeroLocus (R := R) (I : Set R) =>
        Order.coheight q.1) P))

end Local
end AdvCommAlg.CohenMacaulay
