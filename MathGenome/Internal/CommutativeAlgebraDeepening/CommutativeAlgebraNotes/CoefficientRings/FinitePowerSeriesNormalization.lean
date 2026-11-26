import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoefficientRings.FinitePowerSeriesNormalization
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.AdicFiniteGeneration
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CoefficientField
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingExistence
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CohenRingMap
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.PowerSeriesEvaluation
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.SupportAndParameters
import MathGenome.Internal.AlgebraCore.P103.Ch04.IntegralDimension
import Mathlib.RingTheory.Finiteness.NilpotentKer

namespace CommutativeAlgebraNotes.CoefficientRings

open IsLocalRing
open scoped Pointwise

open Specs.CommutativeAlgebraNotes.CoefficientRings.FinitePowerSeriesNormalization
  (IsFiniteNormalization EqualCharacteristic MixedCharacteristic MixedCharacteristicWitness Normalization)

private theorem finiteClosedFiber {S B : Type*} [CommRing S] [CommRing B]
    [IsLocalRing S] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra S B] [IsLocalHom (algebraMap S B)]
    (hres : Function.Surjective (ResidueField.map (algebraMap S B)))
    (hJ : (extendedMaximalIdeal S B).radical = maximalIdeal B) :
    let := closedFiberAlgebra S B
    Module.Finite (ResidueField S) (B ⧸ extendedMaximalIdeal S B) := by
  let J := extendedMaximalIdeal S B
  let := closedFiberAlgebra S B
  have hle : J ≤ maximalIdeal B := hJ ▸ Ideal.le_radical
  let π : (B ⧸ J) →ₐ[ResidueField S] ResidueField B :=
    { Ideal.Quotient.factor hle with
      commutes' := by
        intro a
        obtain ⟨s, rfl⟩ := residue_surjective a
        rfl }
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective hle
  have hfinite : Module.Finite (ResidueField S) (ResidueField B) :=
    Module.Finite.of_surjective (Algebra.linearMap (ResidueField S) (ResidueField B)) hres
  refine Module.finite_of_surjective_of_ker_le_nilradical π hπ ?_ (IsNoetherian.noetherian _)
  change RingHom.ker (Ideal.Quotient.factor hle) ≤ nilradical (B ⧸ J)
  rw [Ideal.Quotient.factor_ker]
  intro b hb
  obtain ⟨a, ha, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hb
  obtain ⟨n, hn⟩ := show a ∈ J.radical by rwa [hJ]
  refine ⟨n, ?_⟩
  change Ideal.Quotient.mk J a ^ n = 0
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact hn

private theorem injective_of_finite_of_dimension {S B : Type*} [CommRing S] [IsDomain S]
    [CommRing B] (F : S →+* B) (hfinite : F.Finite) (d : ℕ)
    (hS : ringKrullDim S = (d : WithBot ℕ∞))
    (hB : ringKrullDim B = (d : WithBot ℕ∞)) : Function.Injective F := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro a ha
  by_contra hne
  have hdim := P103.Ch04.IntegralDimension.dimension_eq S B F hfinite.to_isIntegral
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr hne)
  have hker : Ideal.span {a} ≤ RingHom.ker F :=
    by rwa [Ideal.span_singleton_le_iff_mem]
  have h : ringKrullDim B + 1 ≤ ringKrullDim S := by
    rw [hdim]
    calc
      _ ≤ ringKrullDim (S ⧸ Ideal.span {a}) + 1 :=
        add_le_add_left
          (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hker)) 1
      _ ≤ _ := hle
  rw [hB, hS, ← Nat.cast_one, ← Nat.cast_add] at h
  exact (Nat.not_succ_le_self d) (by exact_mod_cast h)

private theorem finiteNormalization {S B : Type*} [CommRing S]
    [IsDomain S] [IsRegularLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B]
    (F : S →+* B) [IsLocalHom F] (d : ℕ)
    (hS : ringKrullDim S = (d : WithBot ℕ∞))
    (hB : ringKrullDim B = (d : WithBot ℕ∞))
    (hres : Function.Bijective (ResidueField.map F))
    (hJ : ((maximalIdeal S).map F).radical = maximalIdeal B) :
    IsFiniteNormalization d F := by
  let : Algebra S B := F.toAlgebra
  have : IsLocalHom (algebraMap S B) := ‹IsLocalHom F›
  have hfinite : Module.Finite S B :=
    finiteOfFiniteClosedFiber hJ (finiteClosedFiber hres.surjective hJ)
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, hS,
    injective_of_finite_of_dimension F hfinite d hS hB, hres, hfinite, hJ⟩

/-- Finite normalization by a power-series ring over the residue field. -/
theorem finitePowerSeriesNormalization_equal : EqualCharacteristic := by
  intro B _ _ _ _ _ d hd hchar
  classical
  obtain ⟨n, x, hn, hxm, hxr⟩ := P103.Ch06.SystemsParameters.local_ring_parameters B
  have hnd : n = d := by exact_mod_cast hn.symm.trans hd
  subst n
  obtain ⟨σ, hσ, _⟩ := exists_coefficientField B hchar
  have hres : Function.Bijective (ResidueField.map σ) := by
    refine ⟨(ResidueField.map σ).injective, fun a => ⟨residue _ a, ?_⟩⟩
    exact RingHom.congr_fun hσ a
  obtain ⟨F, hF, _, hC, hX, hresF, hres_apply, hJ⟩ :=
    PowerSeriesEvaluation.evaluation (ResidueField B) B σ hres d x hxm
  have := hF
  obtain ⟨hdom, hregular, hcomplete, _, hS, _⟩ :=
    CompleteRegularPowerSeries.overField (ResidueField B) d
  have := hdom
  have := hregular
  have := hcomplete
  rw [maximalIdeal_eq_bot, Ideal.map_bot, bot_sup_eq] at hJ
  refine ⟨σ, x, F, hσ, hxm, hxr, hC, hX, ?_,
    finiteNormalization F d hS hd hresF (hJ ▸ hxr)⟩
  intro f
  rw [← ResidueField.map_residue, hres_apply, ResidueField.map_residue]
  exact RingHom.congr_fun hσ _

private theorem quotient_dimension {B : Type*} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] {a : B} (ha : a ∈ maximalIdeal B)
    (hreg : Function.Injective (fun b : B => a * b)) :
    ringKrullDim (B ⧸ Ideal.span {a}) + 1 = ringKrullDim B := by
  have h := (AdvCommAlg.CohenMacaulay.dimension_quotient_regular B B a ha hreg).2
  change Module.supportDim B (QuotSMulTop a B) + 1 = Module.supportDim B B at h
  have he : Ideal.span {a} = a • (⊤ : Ideal B) := by
    simp [← Submodule.ideal_span_singleton_smul]
  have eq := Module.supportDim_eq_of_equiv
    (Ideal.quotientEquivAlgOfEq B he).toLinearEquiv
  rw [← Module.supportDim_quotient_eq_ringKrullDim, eq, h,
    Module.supportDim_self_eq_ringKrullDim]

/-- Finite normalization by a power-series ring over a Cohen DVR. -/
theorem finitePowerSeriesNormalization_mixed : MixedCharacteristic := by
  intro B _ _ _ _ _ _ d p hd hp _
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : B) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hreg : Function.Injective (fun b : B => (p : B) * b) :=
    fun _ _ h => mul_left_cancel₀ hp0 h
  have hpm : (p : B) ∈ maximalIdeal B := (residue_eq_zero_iff _).mp (by
    rw [map_natCast, CharP.cast_eq_zero])
  let I : Ideal B := Ideal.span {(p : B)}
  let Q := B ⧸ I
  have hI : I ≤ maximalIdeal B := by rwa [Ideal.span_singleton_le_iff_mem]
  have : Nontrivial Q :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hI)
  let q : B →+* Q := Ideal.Quotient.mk I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have : IsLocalHom q := IsLocalHom.of_surjective q hq
  have hQ : IsLocalRing Q := IsLocalRing.of_surjective q hq
  obtain ⟨n, y, hdimQ, hym, hyr⟩ := P103.Ch06.SystemsParameters.local_ring_parameters Q
  have hdrop := quotient_dimension hpm hreg
  change ringKrullDim Q + 1 = ringKrullDim B at hdrop
  rw [hdimQ, hd, ← Nat.cast_one, ← Nat.cast_add] at hdrop
  have hdn : n + 1 = d := by exact_mod_cast hdrop
  subst d
  choose x hx using fun i => hq (y i)
  have hxm : ∀ i, x i ∈ maximalIdeal B := by
    intro i
    rw [← maximalIdeal_comap q]
    change q (x i) ∈ maximalIdeal Q
    rw [hx]
    exact hym i
  have hxy : q ∘ x = y := funext hx
  have hmap : (Ideal.span (Set.range x)).map q = Ideal.span (Set.range y) := by
    rw [Ideal.map_span, ← Set.range_comp, hxy]
  have hrad : (Ideal.span (Set.range x) ⊔ I).radical = maximalIdeal B := by
    apply (P103.Ch06.SystemsParameters.radical_map_quotient_iff B I _).mp
    rw [hmap]
    exact hyr
  obtain ⟨Λ, hring, hdom, hdvr, hchar, hcomplete, hgen, ⟨e⟩⟩ :=
    cohenRingExistence p hp (ResidueField B)
  let := hring
  let := hdom
  let := hdvr
  let := hcomplete
  let e' := (Ideal.quotEquivOfEq hgen.symm).trans e
  obtain ⟨φ, hφlocal, _, hφ, hker, _⟩ := cohenRingMap B Λ p hgen.symm e'
  have := hφlocal
  have hφres : (residue B).comp φ = e.toRingHom.comp (residue Λ) := by
    apply RingHom.ext
    intro a
    change residue B (φ a) = e (residue Λ a)
    calc
      _ = e' (Ideal.Quotient.mk _ a) := RingHom.congr_fun hφ a
      _ = _ := by
        change e (Ideal.quotEquivOfEq hgen.symm (Ideal.Quotient.mk _ a)) = e (residue Λ a)
        rw [Ideal.quotEquivOfEq_mk]
        rfl
  have hres : Function.Bijective (ResidueField.map φ) := by
    refine ⟨(ResidueField.map φ).injective, fun b => ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective b
    obtain ⟨a, rfl⟩ := residue_surjective a
    exact ⟨residue Λ a, RingHom.congr_fun hφres a⟩
  obtain ⟨F, hF, _, hC, hX, hresF, hres_apply, hJ⟩ :=
    PowerSeriesEvaluation.evaluation Λ B φ hres n x hxm
  have := hF
  have hirr := (IsDiscreteValuationRing.irreducible_iff_uniformizer (p : Λ)).mpr hgen
  obtain ⟨hSdom, hregular, hScomplete, _, hS, _⟩ :=
    CompleteRegularPowerSeries.overCompleteDVR Λ (p : Λ) hirr n
  have := hSdom
  have := hregular
  have := hScomplete
  have hJrad : ((maximalIdeal (MvPowerSeries (Fin n) Λ)).map F).radical = maximalIdeal B := by
    rw [hJ, hgen, Ideal.map_span, Set.image_singleton, map_natCast, sup_comm]
    exact hrad
  have hφinj : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    exact hker (fun ⟨k, hk⟩ => (pow_ne_zero k hp0) hk)
  have hFres (f : MvPowerSeries (Fin n) Λ) :
      residue B (F f) = e (residue Λ (MvPowerSeries.constantCoeff f)) := by
    rw [← ResidueField.map_residue, hres_apply, ResidueField.map_residue]
    exact RingHom.congr_fun hφres _
  have hyr' : (Ideal.span (Set.range (q ∘ x))).radical = maximalIdeal Q := hxy ▸ hyr
  simp only [MixedCharacteristicWitness, Nat.add_sub_cancel]
  exact ⟨hQ, hp0, hreg, hdimQ, Λ, hring, hdom, hdvr, hchar, hcomplete, hgen,
    e, φ, x, F, hφinj, hφres, hxm, hyr', hC, hX, hFres,
    finiteNormalization F (n + 1) hS hd hresF hJrad⟩

/-- Every complete Noetherian local domain has a finite normalization of one
of the two stated power-series forms. -/
theorem finitePowerSeriesNormalization : Normalization := by
  intro B _ _ _ _ _
  obtain ⟨d, _, hd, _⟩ := P103.Ch06.SystemsParameters.local_ring_parameters B
  refine ⟨d, hd, ?_⟩
  by_cases hchar : ringChar (ResidueField B) = ringChar B
  · exact Or.inl ⟨hchar, finitePowerSeriesNormalization_equal B d hd hchar⟩
  · right
    have hdiv : ringChar (ResidueField B) ∣ ringChar B := ringChar.dvd (by
      rw [← map_natCast (residue B), CharP.cast_eq_zero, map_zero])
    have hzero : ringChar B = 0 := by
      rcases CharP.char_is_prime_or_zero B (ringChar B) with hprime | hzero
      · exact False.elim (hchar ((Nat.dvd_prime hprime).mp hdiv |>.resolve_left
          CharP.ringChar_ne_one))
      · exact hzero
    have : CharZero B := (CharP.ringChar_zero_iff_CharZero (R := B)).mp hzero
    let p := ringChar (ResidueField B)
    have hp : p.Prime :=
      (CharP.char_is_prime_or_zero (ResidueField B) p).resolve_right (hzero ▸ hchar)
    exact ⟨p, hp, inferInstance, ringChar.charP _, finitePowerSeriesNormalization_mixed B d p hd hp⟩

end CommutativeAlgebraNotes.CoefficientRings
