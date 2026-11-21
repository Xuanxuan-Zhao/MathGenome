import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.RegularQuotient
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.LocalDetection
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Localization.Ideal

/-! Local detection of grade and its consequences, DP-06. -/
universe u
open scoped Pointwise
open RingTheory.Sequence
namespace AdvCommAlg.Depth
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]

omit [IsNoetherianRing R] in
lemma grade_le_localDepth (I : Ideal R) (p : PrimeSpectrum R)
    (hIp : I ≤ p.asIdeal) (hp : p ∈ Module.support R M) :
    grade I M ≤ depth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
  let S := Localization.AtPrime p.asIdeal
  let N := LocalizedModule.AtPrime p.asIdeal M
  let : Nontrivial N := hp
  have hproper : IsLocalRing.maximalIdeal S • (⊤ : Submodule S N) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm
  have hI : I • (⊤ : Submodule R M) ≠ ⊤ := by
    intro he
    have hsupp : p ∈ Module.support R (M ⧸ (I • ⊤ : Submodule R M)) := by
      rw [Module.support_quotient]
      exact ⟨hp, hIp⟩
    have : Subsingleton (M ⧸ (I • ⊤ : Submodule R M)) :=
      Submodule.Quotient.subsingleton_iff.mpr he
    simp [Module.support_eq_empty] at hsupp
  rw [grade_of_smul_ne_top I M hI, depth_eq_grade,
    grade_of_smul_ne_top _ _ hproper]
  apply sSup_le
  rintro _ ⟨xs, hx, hmem, rfl⟩
  have hreg := RegularSequence.regular_localizedModule M p.asIdeal xs
    (Ideal.span_le.mpr fun a ha => hIp (hmem a ha)) hx
  apply le_sSup
  refine ⟨xs.map (algebraMap R S), hreg, ?_, by simp⟩
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p.asIdeal b).mpr (hIp (hmem b hb))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- A proper ideal action remains proper after quotienting by elements of the ideal. -/
lemma ideal_smul_listQuotient_ne_top (I : Ideal R)
    (hI : I • (⊤ : Submodule R M) ≠ ⊤) (xs : List R) (hmem : ∀ x ∈ xs, x ∈ I) :
    I • (⊤ : Submodule R (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M))) ≠ ⊤ := by
  intro he
  apply hI
  have h := congrArg (Submodule.comap (Submodule.mkQ
    (Ideal.ofList xs • (⊤ : Submodule R M)))) he
  have hle : Ideal.ofList xs • (⊤ : Submodule R M) ≤ I • ⊤ :=
    Submodule.smul_mono_left (Ideal.span_le.mpr hmem)
  simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
    sup_eq_left.mpr hle] using h

/-- A maximal regular list has the same length as the depth at a suitable prime. -/
lemma exists_localDepth_eq_grade (I : Ideal R) (hI : I • (⊤ : Submodule R M) ≠ ⊤) :
    ∃ p : PrimeSpectrum R, I ≤ p.asIdeal ∧ p ∈ Module.support R M ∧
      depth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) = grade I M := by
  let : Nontrivial M := by
    by_contra h
    have := not_nontrivial_iff_subsingleton.mp h
    exact hI (Subsingleton.elim _ _)
  obtain ⟨xs, hmax⟩ := exists_maximalRegular_extension I M hI [] (IsRegular.nil R M)
    (by simp)
  simp only [List.nil_append] at hmax
  let K : Submodule R M := Ideal.ofList xs • ⊤
  let Q := M ⧸ K
  have hQI : I • (⊤ : Submodule R Q) ≠ ⊤ := ideal_smul_listQuotient_ne_top M I hI xs hmax.2.1
  have hQzero : grade I Q = 0 := by
    rw [grade_quotient_regular M I hI xs hmax.1 hmax.2.1,
      ← maximalRegular_length_eq_grade I M hI xs hmax]
    simp
  obtain ⟨p, hp, hIp⟩ := (grade_zero_iff_exists_associatedPrime I Q hQI).mp hQzero
  let : p.IsPrime := hp.isPrime
  let pp : PrimeSpectrum R := ⟨p, inferInstance⟩
  have hpQ : pp ∈ Module.support R Q := by
    rw [Module.support_eq_zeroLocus]
    exact le_of_eq_of_le Submodule.annihilator_top.symm hp.annihilator_le
  have hpM : pp ∈ Module.support R M :=
    Module.support_subset_of_surjective (Submodule.mkQ K) (Submodule.mkQ_surjective K) hpQ
  let S := Localization.AtPrime p
  let N := LocalizedModule.AtPrime p M
  let f := LocalizedModule.mkLinearMap p.primeCompl M
  let : Nontrivial N := hpM
  let ys := xs.map (algebraMap R S)
  have hK : K.localized' S p.primeCompl f =
      (Ideal.ofList ys • ⊤ : Submodule S N) := by
    simp only [K, Submodule.localized'_smul, Ideal.localized'_eq_map,
      Submodule.localized'_top, ys, Ideal.map_ofList]
  have hass : IsLocalRing.maximalIdeal S ∈ associatedPrimes S
      (N ⧸ (Ideal.ofList ys • ⊤ : Submodule S N)) := by
    have h := Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      p.primeCompl (K.toLocalizedQuotient' S p.primeCompl f) (IsLocalRing.maximalIdeal S)
      (by simpa [S, Localization.AtPrime.under_maximalIdeal] using hp)
    change IsLocalRing.maximalIdeal S ∈ associatedPrimes S
      (N ⧸ K.localized' S p.primeCompl f) at h
    rw [hK] at h
    exact h
  let L := N ⧸ (Ideal.ofList ys • ⊤ : Submodule S N)
  let : Nontrivial L := by
    by_contra h
    have := not_nontrivial_iff_subsingleton.mp h
    exact not_isAssociatedPrime_of_subsingleton hass
  have hmL : IsLocalRing.maximalIdeal S • (⊤ : Submodule S L) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm
  have hzL : grade (IsLocalRing.maximalIdeal S) L = 0 :=
    (grade_zero_iff_exists_associatedPrime _ L hmL).mpr ⟨_, hass, le_rfl⟩
  have hys : MaximalRegular (IsLocalRing.maximalIdeal S) N ys := by
    refine ⟨RegularSequence.regular_localizedModule M p xs (Ideal.span_le.mpr hmax.2.1 |>.trans hIp)
      hmax.1, ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p b).mpr (hIp (hmax.2.1 b hb))
    · intro a ha hext
      have hr := ((regular_append_iff N ys [a]).mp hext).2.toIsWeaklyRegular
      exact (grade_zero_iff_no_regular _ L hmL).mp hzL a ha
        ((isWeaklyRegular_singleton_iff L a).mp hr)
  have hmN : IsLocalRing.maximalIdeal S • (⊤ : Submodule S N) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm
  refine ⟨pp, hIp, hpM, ?_⟩
  change grade (IsLocalRing.maximalIdeal S) N = grade I M
  rw [← maximalRegular_length_eq_grade _ N hmN ys hys,
    ← maximalRegular_length_eq_grade I M hI xs hmax]
  simp [ys]

/-- Grade is detected by local depths, including the empty-index case. -/
theorem grade_eq_iInf_localDepth (I : Ideal R) :
    grade I M = ⨅ (p : PrimeSpectrum R) (_ : I ≤ p.asIdeal)
      (_ : p ∈ Module.support R M),
      depth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
  apply le_antisymm
  · exact le_iInf fun p => le_iInf fun hIp => le_iInf fun hp => grade_le_localDepth M I p hIp hp
  · by_cases hI : I • (⊤ : Submodule R M) = ⊤
    · rw [grade_of_smul_eq_top I M hI]
      exact le_top
    · obtain ⟨p, hIp, hp, he⟩ := exists_localDepth_eq_grade M I hI
      exact iInf_le_of_le p (iInf_le_of_le hIp (iInf_le_of_le hp he.le))

/-- Replacing an ideal by its radical preserves grade. -/
theorem grade_radical (I : Ideal R) : grade I.radical M = grade I M := by
  simp_rw [grade_eq_iInf_localDepth M, Ideal.IsPrime.radical_le_iff inferInstance]

/-- Grade of a product is the minimum of the two grades. -/
theorem grade_mul (I J : Ideal R) :
    grade (I * J) M = min (grade I M) (grade J M) := by
  simp_rw [grade_eq_iInf_localDepth M, Ideal.IsPrime.mul_le inferInstance, iInf_or]
  exact iInf_inf_eq

/-- Grade of an intersection is the minimum of the two grades. -/
theorem grade_inf (I J : Ideal R) :
    grade (I ⊓ J) M = min (grade I M) (grade J M) := by
  simp_rw [grade_eq_iInf_localDepth M, Ideal.IsPrime.inf_le inferInstance, iInf_or]
  exact iInf_inf_eq

/-- Grade of a proper ideal of the ring is at most its height. -/
theorem grade_le_height (I : Ideal R) (_hI : I ≠ ⊤) : grade I R ≤ I.height := by
  rw [Ideal.height_eq_inf_minimalPrimes]
  apply le_iInf₂
  intro p hp
  let : p.IsPrime := hp.isPrime
  let S := Localization.AtPrime p
  let N := LocalizedModule.AtPrime p R
  have hpR : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ Module.support R R := by
    have hAnn : Module.annihilator R R = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
    rw [Module.support_eq_zeroLocus, hAnn]
    change (⊥ : Ideal R) ≤ p
    exact bot_le
  let : Nontrivial N := hpR
  have hdim : (depth S N : WithBot ℕ∞) ≤ (p.height : WithBot ℕ∞) := by
    calc
      (depth S N : WithBot ℕ∞) ≤ Module.supportDim S N := depth_le_supportDim N
      _ ≤ ringKrullDim S := Module.supportDim_le_ringKrullDim S N
      _ = (p.height : WithBot ℕ∞) := IsLocalization.AtPrime.ringKrullDim_eq_height p S
  exact (grade_le_localDepth R I ⟨p, inferInstance⟩ hp.le hpR).trans
    (WithBot.coe_le_coe.mp hdim)

end AdvCommAlg.Depth
