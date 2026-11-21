import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.FiniteColength
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

namespace P103.Ch06.FiniteColength

universe u v
open P103.Specs.Ch06.FiniteColength
open P103.Specs.Ch05.AssociatedPrimesInterface
open IsLocalRing

theorem support_quotient : support_quotientType.{u,v} := by
  intro R _ M _ _ _ Q
  change Module.support R _ = _
  rw [Module.support_quotient, Module.support_eq_zeroLocus,
    PrimeSpectrum.zeroLocus_sup, Set.inter_comm]

theorem quotient_nontrivial : quotient_nontrivialType.{u,v} := by
  intro R _ _ _ M _ _ _ _ Q hQ
  rw [Submodule.Quotient.nontrivial_iff]
  exact (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (hQ.trans (maximalIdeal_le_jacobson _))).symm

/-- Descending powers stabilize in an Artinian module. Nakayama then makes
that stable submodule zero. This also applies to the zero module. -/
theorem finite_length_power (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    ∃ n : ℕ, (maximalIdeal R) ^ n ≤ Module.annihilator R M := by
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
  have := hN
  have := hA
  let f : ℕ →o (Submodule R M)ᵒᵈ :=
    ⟨fun n => OrderDual.toDual ((maximalIdeal R) ^ n • (⊤ : Submodule R M)),
      fun _ _ hab => Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  have heq : (maximalIdeal R) ^ n • (⊤ : Submodule R M) =
      maximalIdeal R • ((maximalIdeal R) ^ n • ⊤) := by
    have heq' : (maximalIdeal R) ^ n • (⊤ : Submodule R M) =
        (maximalIdeal R) ^ (n + 1) • ⊤ := hn (n + 1) (Nat.le_succ n)
    simpa only [pow_succ', Submodule.mul_smul] using heq'
  have hz := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R)
    ((maximalIdeal R) ^ n • (⊤ : Submodule R M)) (IsNoetherian.noetherian _) heq.le
    (maximalIdeal_le_jacobson _)
  exact ⟨n, by rwa [← Submodule.annihilator_top, Submodule.le_annihilator_iff]⟩

/-- Closed sets in the prime spectrum determine radicals. -/
theorem zeroLocus_eq_closedPoint_iff (R : Type u) [CommRing R] [IsLocalRing R]
    (I : Ideal R) :
    PrimeSpectrum.zeroLocus (I : Set R) = {closedPoint R} ↔
      I.radical = maximalIdeal R := by
  change PrimeSpectrum.zeroLocus (I : Set R) =
    {⟨maximalIdeal R, inferInstance⟩} ↔ _
  rw [← PrimeSpectrum.zeroLocus_eq_singleton (maximalIdeal R),
    PrimeSpectrum.zeroLocus_eq_iff,
    (inferInstance : (maximalIdeal R).IsPrime).radical]

/-- A finite module supported at the closed point is a finite module over
its Artinian annihilator quotient. Restriction of scalars preserves the
submodule lattice because the quotient map is surjective. -/
theorem finite_length_of_support_singleton (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type v) [AddCommGroup M]
    [Module R M] [Module.Finite R M]
    (hs : Module.support R M = {closedPoint R}) : IsFiniteLength R M := by
  let A := Module.annihilator R M
  have hd : Ring.KrullDimLE 0 (R ⧸ A) := by
    apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
    intro J hJ
    have hp : (⟨J, hJ.isPrime⟩ : PrimeSpectrum R) ∈ Module.support R M :=
      Module.mem_support_iff_of_finite.mpr hJ.1.2
    rw [hs, Set.mem_singleton_iff] at hp
    have he : J = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hp
    rw [he]
    infer_instance
  have := hd
  have : IsArtinianRing (R ⧸ A) :=
    isArtinianRing_iff_krullDimLE_zero.mpr hd
  let hT := Module.isTorsionBySet_annihilator R M
  let := hT.module
  have : Module.Finite (R ⧸ A) M := Module.Finite.of_restrictScalars_finite R (R ⧸ A) M
  have ha : IsArtinian (R ⧸ A) M := inferInstance
  have : IsArtinian R M :=
    (hT.semilinearMap.isArtinian_iff_of_bijective Function.bijective_id).mpr ha
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

theorem support_singleton_iff_finite_length :
    support_singleton_iff_finite_lengthType.{u,v} := by
  intro R _ _ _ M _ _ _ _
  change Module.support R M = _ ↔ _
  refine ⟨finite_length_of_support_singleton R M, ?_⟩
  intro h
  obtain ⟨n, hn⟩ := finite_length_power R M h
  rw [Module.support_eq_zeroLocus, zeroLocus_eq_closedPoint_iff]
  apply le_antisymm
  · exact (inferInstance : (maximalIdeal R).IsPrime).radical_le_iff.mpr
      (Module.annihilator_le_of_mem_support (closedPoint_mem_support R M))
  · intro r hr
    exact ⟨n, hn (Ideal.pow_mem_pow hr n)⟩

theorem maximalIdeal_pow_annihilates : maximalIdeal_pow_annihilatesType.{u,v} := by
  intro R _ _ _ M _ _ _ _ hs
  obtain ⟨n, hn⟩ := finite_length_power R M
    ((support_singleton_iff_finite_length R M).mp hs)
  exact ⟨n + 1, Nat.zero_lt_succ _, (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn⟩

theorem finite_colength_iff : finite_colength_iffType.{u,v} := by
  intro R _ _ _ M _ _ _ _ Q hQ
  have := quotient_nontrivial R M Q hQ
  rw [← support_singleton_iff_finite_length R (M ⧸ (Q • (⊤ : Submodule R M))),
    support_quotient R M Q, zeroLocus_eq_closedPoint_iff]

theorem zero_module : zero_moduleType.{u,v} := by
  intro R _ M _ _ _
  refine ⟨.of_subsingleton, ?_, ?_, ?_⟩
  · simp
  · simp [P103.Specs.Ch02.FiniteLength.lengthValue]
  · exact Module.support_eq_empty

theorem top_quotient : top_quotientType.{u,v} := by
  intro R _ M _ _
  dsimp only
  have : Subsingleton (M ⧸ ((⊤ : Ideal R) • (⊤ : Submodule R M))) := by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.top_smul]
  exact ⟨inferInstance, zero_module R _⟩

end P103.Ch06.FiniteColength
