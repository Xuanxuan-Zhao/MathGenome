import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ZeroTest
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.DimensionBounds
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.SerreDepthConditions

/-! Serre's depth conditions, with the support and zero-module conventions
of CM-11 and the all-prime convention of chapter 8. -/
universe u
open scoped Pointwise
namespace AdvCommAlg.CohenMacaulay

noncomputable def SerreCondition : Specs.SerreConditionType.{u} := Specs.SerreConditionValue
noncomputable def RingSerreCondition : Specs.RingSerreConditionType.{u} :=
  fun R _ _ k => SerreCondition R R k
noncomputable def NoEmbeddedAssociatedPrimes : Specs.NoEmbeddedAssociatedPrimesType.{u} :=
  Specs.NoEmbeddedAssociatedPrimesValue

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem serreCondition_of_subsingleton [Subsingleton M] (k : ℕ) : SerreCondition R M k := by
  intro p hp
  simp [Module.support_eq_empty] at hp

private lemma dimension_le_depth_of_forall_min {d : WithBot ℕ∞} {e : ℕ∞}
    (h : ∀ k : ℕ, min (k : WithBot ℕ∞) d ≤ (e : WithBot ℕ∞)) : d ≤ e := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    apply WithBot.coe_le_coe.mpr
    apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    have hh := h n
    have hn' : (n : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast hn
    rw [min_eq_left hn'] at hh
    exact_mod_cast hh

theorem cohenMacaulay_iff_forall_serreCondition :
    IsCohenMacaulay R M ↔ ∀ k : ℕ, SerreCondition R M k := by
  constructor
  · intro h k p hp
    have : Nontrivial (LocalizedModule.AtPrime p.asIdeal M) := hp
    have he := (localCohenMacaulay_iff_depth_eq _ _).mp (h p hp)
    exact (min_le_right _ _).trans (le_of_eq he.symm)
  · intro h p hp
    have : Nontrivial (LocalizedModule.AtPrime p.asIdeal M) := hp
    apply (localCohenMacaulay_iff_depth_eq _ _).mpr
    apply le_antisymm
    · rw [← Depth.depth_eq_libraryDepth]
      exact Depth.depth_le_supportDim _
    · exact dimension_le_depth_of_forall_min (fun k => h k p hp)

/-- Every associated prime belongs to the support. -/
lemma mem_support_of_associatedPrime (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ associatedPrimes R M) : p ∈ Module.support R M := by
  apply Module.mem_support_iff_of_finite.mpr
  exact Submodule.annihilator_top.symm.le.trans hp.annihilator_le

/-- Every support prime contains an associated prime, by taking a minimal
prime over the annihilator. -/
lemma exists_associatedPrime_le_of_mem_support (p : PrimeSpectrum R)
    (hp : p ∈ Module.support R M) :
    ∃ q : PrimeSpectrum R, q.asIdeal ∈ associatedPrimes R M ∧ q ≤ p := by
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le
    (Module.mem_support_iff_of_finite.mp hp)
  exact ⟨⟨q, hq.isPrime⟩,
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hq, hqp⟩

/-- Support under prime localization is the inverse image under contraction. -/
lemma mem_support_localizedModule_iff (p : PrimeSpectrum R)
    (q : PrimeSpectrum (Localization.AtPrime p.asIdeal)) :
    q ∈ Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) ↔
      PrimeSpectrum.comap (algebraMap R (Localization.AtPrime p.asIdeal)) q ∈
        Module.support R M := by
  let S := Localization.AtPrime p.asIdeal
  let N := LocalizedModule.AtPrime p.asIdeal M
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso S p.asIdeal
  have he (t : PrimeSpectrum S) :
      (e t).val = PrimeSpectrum.comap (algebraMap R S) t := rfl
  have hass (t : PrimeSpectrum S) :
      (PrimeSpectrum.comap (algebraMap R S) t).asIdeal ∈ associatedPrimes R M ↔
        t.asIdeal ∈ associatedPrimes S N := by
    have h := Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
      p.asIdeal.primeCompl S (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    exact Set.ext_iff.mp h t.asIdeal
  constructor
  · intro hq
    obtain ⟨t, ht, htq⟩ := exists_associatedPrime_le_of_mem_support S N q hq
    exact Module.mem_support_mono (Ideal.comap_mono htq)
      (mem_support_of_associatedPrime R M _ ((hass t).mpr ht))
  · intro hq
    obtain ⟨t, ht, htq⟩ := exists_associatedPrime_le_of_mem_support R M _ hq
    have htp : t ≤ p := htq.trans (e q).property
    let t' : PrimeSpectrum S := e.symm ⟨t, htp⟩
    have het : (e t').val = t := congrArg Subtype.val (e.apply_symm_apply ⟨t, htp⟩)
    have ht' : t'.asIdeal ∈ associatedPrimes S N := by
      apply (hass t').mp
      rw [← he, het]
      exact ht
    apply Module.mem_support_mono _ (mem_support_of_associatedPrime S N t' ht')
    apply e.le_iff_le.mp
    change (e t').val ≤ (e q).val
    rw [het, he q]
    exact htq

/-- Local support dimension zero detects precisely the minimal support primes. -/
lemma localized_supportDim_eq_zero_iff_minimal (p : PrimeSpectrum R)
    (hp : p ∈ Module.support R M) :
    Module.supportDim (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) = 0 ↔
      Minimal (fun q => q ∈ Module.support R M) p := by
  let S := Localization.AtPrime p.asIdeal
  let N := LocalizedModule.AtPrime p.asIdeal M
  have : Nontrivial N := hp
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso S p.asIdeal
  have he (t : PrimeSpectrum S) :
      (e t).val = PrimeSpectrum.comap (algebraMap R S) t := rfl
  have htop : PrimeSpectrum.comap (algebraMap R S) (IsLocalRing.closedPoint S) = p := by
    apply PrimeSpectrum.ext
    exact Localization.AtPrime.under_maximalIdeal
  constructor
  · intro hd
    refine ⟨hp, ?_⟩
    intro q hq hqp
    let q' := e.symm ⟨q, hqp⟩
    have hqq : PrimeSpectrum.comap (algebraMap R S) q' = q := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨q, hqp⟩)
    have hqs : q' ∈ Module.support S N := by
      apply (mem_support_localizedModule_iff R M p q').mpr
      rwa [hqq]
    have heq : q' = IsLocalRing.closedPoint S := by
      rw [support_of_supportDim_eq_zero S N hd, PrimeSpectrum.zeroLocus_eq_singleton] at hqs
      exact hqs
    have : q = p := by rw [← hqq, heq, htop]
    exact this.symm.le
  · intro hmin
    have hsub : Subsingleton (Module.support S N) := by
      constructor
      intro a b
      apply Subtype.ext
      apply e.injective
      apply Subtype.ext
      have ha := (mem_support_localizedModule_iff R M p a.val).mp a.property
      have hb := (mem_support_localizedModule_iff R M p b.val).mp b.property
      exact (le_antisymm (e a.val).property (hmin.2 ha (e a.val).property)).trans
        (le_antisymm (e b.val).property (hmin.2 hb (e b.val).property)).symm
    have : Nonempty (Module.support S N) :=
      ⟨⟨IsLocalRing.closedPoint S, IsLocalRing.closedPoint_mem_support S N⟩⟩
    exact Order.krullDim_eq_zero

/-- For a nonzero finite local module, depth zero is equivalent to the
maximal ideal being associated. -/
lemma depth_eq_zero_iff_maximal_associated [IsLocalRing R] [Nontrivial M] :
    IsLocalRing.depth (ModuleCat.of R M) = 0 ↔
      IsLocalRing.maximalIdeal R ∈ associatedPrimes R M := by
  rw [← Depth.depth_eq_libraryDepth]
  have hproper : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  rw [Depth.depth_eq_grade, Depth.grade_zero_iff_exists_associatedPrime _ _ hproper]
  constructor
  · rintro ⟨q, hq, hle⟩
    have : q = IsLocalRing.maximalIdeal R :=
      le_antisymm (IsLocalRing.le_maximalIdeal hq.isPrime.ne_top) hle
    rwa [this] at hq
  · intro h
    exact ⟨_, h, le_rfl⟩

/-- Associated primes are exactly the support points where the localized
module has depth zero. -/
lemma localized_depth_eq_zero_iff_associated (p : PrimeSpectrum R)
    (hp : p ∈ Module.support R M) :
    IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M)) = 0 ↔
        p.asIdeal ∈ associatedPrimes R M := by
  have : Nontrivial (LocalizedModule.AtPrime p.asIdeal M) := hp
  rw [depth_eq_zero_iff_maximal_associated]
  have h := Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
  have hh := Set.ext_iff.mp h (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
  simpa only [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal] using hh.symm

private lemma min_one_le_depth_iff {d : WithBot ℕ∞} {e : ℕ∞} (hd : 0 ≤ d) :
    min 1 d ≤ (e : WithBot ℕ∞) ↔ (e = 0 → d = 0) := by
  rw [min_le_iff]
  constructor
  · rintro (h | h) he
    · subst e
      have hbad : ¬ (1 : WithBot ℕ∞) ≤ 0 := by decide
      exact (hbad h).elim
    · exact le_antisymm (by simpa [he] using h) hd
  · intro h
    by_cases he : e = 0
    · right
      simp [h he, he]
    · left
      exact_mod_cast Order.one_le_iff_ne_zero.mpr he

theorem serreCondition_one_iff_noEmbeddedAssociatedPrimes :
    SerreCondition R M 1 ↔ NoEmbeddedAssociatedPrimes R M := by
  constructor
  · intro hs p hass
    have hp := mem_support_of_associatedPrime R M p hass
    have : Nontrivial (LocalizedModule.AtPrime p.asIdeal M) := hp
    have hd : (0 : WithBot ℕ∞) ≤ Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) := by
      apply Order.krullDim_nonneg_iff.mpr
      exact Module.nonempty_support_of_nontrivial.to_subtype
    apply (localized_supportDim_eq_zero_iff_minimal R M p hp).mp
    exact (min_one_le_depth_iff hd).mp (hs p hp)
      ((localized_depth_eq_zero_iff_associated R M p hp).mpr hass)
  · intro h p hp
    have : Nontrivial (LocalizedModule.AtPrime p.asIdeal M) := hp
    have hd : (0 : WithBot ℕ∞) ≤ Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) := by
      apply Order.krullDim_nonneg_iff.mpr
      exact Module.nonempty_support_of_nontrivial.to_subtype
    apply (min_one_le_depth_iff hd).mpr
    intro hz
    apply (localized_supportDim_eq_zero_iff_minimal R M p hp).mpr
    exact h p ((localized_depth_eq_zero_iff_associated R M p hp).mp hz)

theorem serreCondition_one_iff_associatedPrimes_eq_minimalPrimes :
    SerreCondition R M 1 ↔
      associatedPrimes R M = (Module.annihilator R M).minimalPrimes := by
  rw [serreCondition_one_iff_noEmbeddedAssociatedPrimes]
  constructor
  · intro h
    apply Set.Subset.antisymm _
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M)
    intro p hp
    let pp : PrimeSpectrum R := ⟨p, hp.isPrime⟩
    have hm := h pp hp
    refine ⟨⟨hp.isPrime, Module.mem_support_iff_of_finite.mp hm.1⟩, ?_⟩
    intro q hq hqp
    exact hm.2 (Module.mem_support_iff_of_finite.mpr hq.2 :
      (⟨q, hq.1⟩ : PrimeSpectrum R) ∈ Module.support R M) hqp
  · intro h p hp
    have hm : p.asIdeal ∈ (Module.annihilator R M).minimalPrimes := by rwa [← h]
    refine ⟨mem_support_of_associatedPrime R M p hp, ?_⟩
    intro q hq hqp
    exact hm.2 ⟨q.isPrime, Module.mem_support_iff_of_finite.mp hq⟩ hqp

end AdvCommAlg.CohenMacaulay
