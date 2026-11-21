import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.CodimensionOneMembership
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Normality.NormalLocalDepth
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.HeightOneIntersection

universe u v
namespace AdvCommAlg.Normality

noncomputable abbrev atPrimeToFractionField := Specs.atPrimeToFractionFieldValue

/-- The canonical map really embeds the prime localization. -/
theorem atPrimeToFractionField_injective
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (p : PrimeSpectrum A) : Function.Injective (atPrimeToFractionField A K p) :=
  (IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A) K).injective.comp
    (IsFractionRing.injective (Localization.AtPrime p.asIdeal) (FractionRing A))

/-- On A the embedding is the prescribed fraction-field map. -/
theorem atPrimeToFractionField_algebraMap
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (p : PrimeSpectrum A) (a : A) :
    atPrimeToFractionField A K p (algebraMap A (Localization.AtPrime p.asIdeal) a) =
      algebraMap A K a := by
  change (IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A) K)
    (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing A)
      (algebraMap A (Localization.AtPrime p.asIdeal) a)) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact AlgEquiv.commutes _ a

/-- Local normality gives S₂ at every prime, using SN-07. -/
theorem normal_serreCondition_two (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hN : IsNormal A) : CohenMacaulay.RingSerreCondition A 2 := by
  intro p hp
  let S := Localization.AtPrime p.asIdeal
  have : IsDomain S := (hN p).1
  have : IsIntegrallyClosed S := (hN p).2
  let e : (LocalizedModule.AtPrime p.asIdeal A) ≃ₗ[S] S :=
    (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl A)
      (Algebra.linearMap A S)).extendScalarsOfIsLocalization p.asIdeal.primeCompl S
  rw [Module.supportDim_eq_of_equiv e, Module.supportDim_self_eq_ringKrullDim,
    IsLocalRing.depth_eq_of_linearEquiv e, ← Depth.depth_eq_libraryDepth]
  exact normal_local_depth_lower_bound S

/-- The two canonical maps into the localized total quotient ring agree. -/
lemma totalQuotientToAtPrime_fractionMap (A : Type u) [CommRing A] [IsDomain A]
    (p : PrimeSpectrum A) (x : Localization.AtPrime p.asIdeal) :
    totalQuotientToAtPrime A p
        (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing A) x) =
      algebraMap (Localization.AtPrime p.asIdeal)
        (FractionRing (Localization.AtPrime p.asIdeal)) x := by
  have he : (totalQuotientToAtPrime A p).comp
        (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing A)) =
      algebraMap (Localization.AtPrime p.asIdeal)
        (FractionRing (Localization.AtPrime p.asIdeal)) := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    ext a
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
      totalQuotientToAtPrime_algebraMap]
  exact RingHom.congr_fun he x

/-- In a domain the unique height-zero prime places no restriction on a fraction. -/
lemma mem_atPrime_range_of_height_zero (A : Type u) [CommRing A] [IsDomain A]
    (p : PrimeSpectrum A) (hp : p.asIdeal.height = 0) (z : FractionRing A) :
    z ∈ (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing A)).range := by
  have hp0 : p.asIdeal = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp hp
  obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors A) z
  have hb : b.val ∈ p.asIdeal.primeCompl := by
    change b.val ∉ p.asIdeal
    rw [hp0, Ideal.mem_bot]
    exact mem_nonZeroDivisors_iff_ne_zero.mp b.property
  refine ⟨IsLocalization.mk' (Localization.AtPrime p.asIdeal) a ⟨b.val, hb⟩, ?_⟩
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [IsScalarTower.algebraMap_apply A (Localization.AtPrime p.asIdeal) (FractionRing A),
    ← map_mul, IsLocalization.mk'_spec]
  rw [← IsScalarTower.algebraMap_apply]

/-- SN-08: a positive-dimensional Noetherian normal domain is the intersection
of its height-one localizations inside any chosen fraction field. -/
theorem heightOne_intersection
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (hN : IsNormal A) (_hd : 0 < ringKrullDim A) :
    (algebraMap A K).range =
      ⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
        (atPrimeToFractionField A K p).range := by
  let e := IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A) K
  ext z
  simp only [Subring.mem_iInf, RingHom.mem_range]
  constructor
  · rintro ⟨a, rfl⟩ p _
    exact ⟨algebraMap A (Localization.AtPrime p.asIdeal) a,
      atPrimeToFractionField_algebraMap A K p a⟩
  · intro hz
    have hloc : ∀ p : PrimeSpectrum A, p.asIdeal.height ≤ 1 →
        totalQuotientToAtPrime A p (e.symm z) ∈ Set.range
          (algebraMap (Localization.AtPrime p.asIdeal)
            (FractionRing (Localization.AtPrime p.asIdeal))) := by
      intro p hp
      have hmem : e.symm z ∈
          (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing A)).range := by
        by_cases hp0 : p.asIdeal.height = 0
        · exact mem_atPrime_range_of_height_zero A p hp0 _
        · have hp1 : p.asIdeal.height = 1 :=
            le_antisymm hp (Order.one_le_iff_ne_zero.mpr hp0)
          obtain ⟨x, hx⟩ := hz p hp1
          change e (algebraMap (Localization.AtPrime p.asIdeal) (FractionRing A) x) = z at hx
          refine ⟨x, ?_⟩
          exact e.injective (by simpa only [AlgEquiv.apply_symm_apply] using hx)
      obtain ⟨x, hx⟩ := hmem
      exact ⟨x, by rw [← hx, totalQuotientToAtPrime_fractionMap]⟩
    obtain ⟨a, ha⟩ := codimensionOne_membership A (normal_serreCondition_two A hN)
      (e.symm z) hloc
    refine ⟨a, ?_⟩
    have hh := congrArg e ha
    simpa only [AlgEquiv.commutes, AlgEquiv.apply_symm_apply] using hh

end AdvCommAlg.Normality
