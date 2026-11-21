import MathGenome.Internal.Specs.D07.Ch22.LocalizationUniversal
import MathGenome.Internal.D07.Ch22.LocalizationConstruction
import MathGenome.Internal.D07.Ch22.LocalizationUniversalAwayPolynomialQuotient
import MathGenome.Internal.D07.Ch08.FractionUniversal

/-! K07.22.localization_universal: universal maps, kernels, exceptional cases,
the domain specialization, and the concrete zero-divisor example. -/

universe u v

namespace D07.Ch22.LocalizationUniversal

open Specs.D07.Ch22.LocalizationUniversal

theorem extensionUnique : ExtensionUnique.{u, v} := by
  intro R A _ _ S f hf
  refine ⟨IsLocalization.lift hf, IsLocalization.lift_comp hf, ?_⟩
  intro g hg
  exact IsLocalization.ringHom_ext S (hg.trans (IsLocalization.lift_comp hf).symm)

theorem fractionFormula : FractionFormula.{u, v} := by
  intro R A _ _ S f g hg a s t ht
  have hbase (r : R) : g (algebraMap R (Localization S) r) = f r :=
    RingHom.congr_fun hg r
  have hmul : g (Localization.mk a s) * f s = f a := by
    rw [← hbase s, ← map_mul, Localization.mk_eq_mk',
      IsLocalization.mk'_spec, hbase a]
  calc
    g (Localization.mk a s) =
        (g (Localization.mk a s) * (t : A)) * ↑(t⁻¹) := by simp [mul_assoc]
    _ = f a * ↑(t⁻¹) := by rw [ht, hmul]

theorem extensionCriterion : ExtensionCriterion.{u, v} := by
  intro R A _ _ S f
  constructor
  · rintro ⟨g, hg⟩ s
    have h := (IsLocalization.map_units (Localization S) s).map g
    change IsUnit ((g.comp (algebraMap R (Localization S))) s) at h
    rwa [hg] at h
  · intro hf
    obtain ⟨g, hg, _⟩ := extensionUnique R A S f hf
    exact ⟨g, hg⟩

theorem kernelFormula : KernelFormula.{u} := by
  intro R _ S a
  exact IsLocalization.map_eq_zero_iff S (Localization S) a

theorem zeroRingIff : ZeroRingIff.{u} := by
  intro R _ S
  exact IsLocalization.subsingleton_iff

theorem nonzeroIff : NonzeroIff.{u} := by
  intro R _ S
  rw [← not_subsingleton_iff_nontrivial, zeroRingIff R S]

theorem injectiveIff : InjectiveIff.{u} := by
  intro R _ S
  constructor
  · intro hi s a b hab
    apply hi
    exact (IsLocalization.eq_iff_exists S (Localization S)).mpr ⟨s, hab⟩
  · intro hs a b hab
    obtain ⟨s, hsab⟩ := (IsLocalization.eq_iff_exists S (Localization S)).mp hab
    exact hs s hsab

theorem zeroBaseRing : ZeroBaseRing.{u} := by
  intro R _ _ S
  have hzero : (0 : R) ∈ S := by
    rw [Subsingleton.elim (0 : R) 1]
    exact S.one_mem
  exact ⟨hzero, (zeroRingIff R S).mpr hzero⟩

theorem fractionFieldRecovery : FractionFieldRecovery.{u, v} := by
  intro R _ _
  refine ⟨fun _ => mem_nonZeroDivisors_iff_ne_zero, ⟨RingEquiv.refl _, fun _ => rfl⟩,
    ?_, IsFractionRing.injective R (FractionRing R), ?_⟩
  · exact Field.toIsField _
  · intro A _ f hf
    exact extensionUnique R A (nonZeroDivisors R) f
      (fun b => hf b (mem_nonZeroDivisors_iff_ne_zero.mp b.2))

theorem fractionFieldEmbedding : FractionFieldEmbedding.{u, v} := by
  intro R K _ _ _ f hf
  obtain ⟨g, hg, huniq⟩ := D07.Ch08.FractionUniversal.fieldExtensionUnique R K f hf
  exact ⟨g, hg, D07.Ch08.FractionUniversal.fieldExtensionInjective R K f hf g hg, huniq⟩

open Polynomial

theorem zeroDivisorExample : ZeroDivisorExample.{u} := by
  intro k _ _
  let ev₀ : MvPolynomial (Fin 2) k →+* Polynomial k :=
    MvPolynomial.eval₂Hom C (fun i => if i = 0 then 0 else X)
  have hkill : CrossingIdeal k ≤ RingHom.ker ev₀ := by
    rw [Ideal.span_le]
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    simp [ev₀]
  let ev : CrossingRing k →+* Polynomial k := Ideal.Quotient.lift _ ev₀ hkill
  have hx : ev (crossingX k) = 0 := by
    change ev₀ (MvPolynomial.X 0) = 0
    simp [ev₀]
  have hy : ev (crossingY k) = X := by
    change ev₀ (MvPolynomial.X 1) = X
    simp [ev₀]
  have hyne : crossingY k ≠ 0 := by
    intro h
    have : (X : Polynomial k) = 0 := by rw [← hy, h, map_zero]
    exact Polynomial.X_ne_zero this
  have hxy : crossingX k * crossingY k = 0 := by
    rw [crossingX, crossingY, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hloc : Specs.D07.Ch22.LocalizationConstruction.LocalizationMapValue
      (CrossingRing k) (Submonoid.powers (crossingX k)) (crossingY k) = 0 := by
    apply (kernelFormula (CrossingRing k) (Submonoid.powers (crossingX k)) _).mpr
    exact ⟨⟨crossingX k, Submonoid.mem_powers _⟩, hxy⟩
  refine ⟨⟨ev, hx, hy, ?_⟩, hyne, hxy, hloc, ?_⟩
  · intro a
    change ev₀ (MvPolynomial.C a) = C a
    simp [ev₀]
  · intro hi
    apply hyne
    apply hi
    simpa only [map_zero] using hloc

theorem principalPresentation : PrincipalPresentation.{u} := by
  exact ⟨fun R _ f => ⟨LocalizationUniversalAwayPolynomialQuotient.presentationEquiv R f⟩,
    LocalizationUniversalAwayPolynomialQuotient.nilpotentCase,
    LocalizationUniversalAwayPolynomialQuotient.zeroRingCase⟩

end D07.Ch22.LocalizationUniversal
