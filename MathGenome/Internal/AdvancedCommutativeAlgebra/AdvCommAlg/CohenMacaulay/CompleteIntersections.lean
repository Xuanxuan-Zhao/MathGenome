import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.HeightAndGrade
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularParameters
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularLocalStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.QuotientsAndScalars
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.RingHom.Surjective
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.CompleteIntersections

/-! Forward complete-intersection and unmixedness assertions of CM-09.

The height of the localized generated ideal equals the displayed list length:
height is bounded below by contraction and above by Krull's height theorem.
The CM dimension criterion then proves regularity in every local ring over I.
Regular quotients are CM, and localization of the quotient is identified with
the quotient of the local ring. At an associated prime the local quotient has
dimension zero, so the dimension drop gives height exactly the list length.
This also proves minimality, without a positive-height assumption.
-/

universe u
open scoped Pointwise
open RingTheory.Sequence
namespace AdvCommAlg.CohenMacaulay
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

lemma cohenMacaulayRing_of_local [IsLocalRing R] (hCM : LocalCohenMacaulay R R) :
    CohenMacaulayRing R := by
  intro p
  have h := localCohenMacaulay_atPrime R hCM p (self_mem_support p)
  exact (localCohenMacaulay_congr (localizedSelfEquiv p)).mp h

lemma height_ofList_le_length (x : List R) (hx : Ideal.ofList x ≠ ⊤) :
    (Ideal.ofList x).height ≤ x.length := by
  classical
  have he : Ideal.ofList x = Ideal.span (x.toFinset : Set R) := by
    apply congrArg Ideal.span
    ext a
    exact List.mem_toFinset.symm
  rw [he] at hx ⊢
  exact (Ideal.height_span_le_card_of_span_ne_top hx).trans
    (by exact_mod_cast List.toFinset_card_le x)

lemma height_map_eq_length (I : Ideal R) (x : List R)
    (hgen : Ideal.ofList x = I) (hheight : I.height = x.length)
    (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    (I.map (algebraMap R (Localization.AtPrime p.asIdeal))).height = x.length := by
  let f := algebraMap R (Localization.AtPrime p.asIdeal)
  have hproper : I.map f ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    rw [Ideal.map_le_iff_le_comap]
    change I ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).under R
    rw [Localization.AtPrime.under_maximalIdeal]
    exact hIp
  apply le_antisymm
  · have he : Ideal.ofList (x.map f) = I.map f := by rw [← Ideal.map_ofList, hgen]
    simpa only [List.length_map, he] using height_ofList_le_length (x.map f) (he.symm ▸ hproper)
  · rw [← hheight, ← IsLocalization.height_under p.asIdeal.primeCompl (I.map f)]
    exact Ideal.height_mono Ideal.le_comap_map

lemma regular_of_height_eq_length [IsLocalRing R]
    (hCM : LocalCohenMacaulay R R) (x : List R)
    (hxm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R)
    (hheight : (Ideal.ofList x).height = x.length) : IsRegular R x := by
  have hI : Ideal.ofList x ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (Ideal.span_le.mpr hxm)
  apply (regular_iff_dimension R hCM x hxm).mpr
  have he : Ideal.ofList x • (⊤ : Submodule R R) = Ideal.ofList x := by
    change Ideal.ofList x * ⊤ = _
    exact Ideal.mul_top _
  rw [he, dimension, dimension, Module.supportDim_self_eq_ringKrullDim,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Ideal.annihilator_quotient]
  rw [add_comm]
  have h := height_add_quotient_dimension (cohenMacaulayRing_of_local hCM) (Ideal.ofList x) hI
  rw [hheight] at h
  exact_mod_cast h

/-- Displayed height-many generators are regular at every prime containing the ideal. -/
theorem completeIntersection_regular_atPrime (hCM : CohenMacaulayRing R)
    (I : Ideal R) (x : List R) (hgen : Ideal.ofList x = I)
    (hheight : I.height = x.length) (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    IsRegular (Localization.AtPrime p.asIdeal)
      (x.map (algebraMap R (Localization.AtPrime p.asIdeal))) := by
  apply regular_of_height_eq_length (hCM p)
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p.asIdeal b).mpr
    exact hIp (hgen ▸ Ideal.subset_span hb)
  · rw [← Ideal.map_ofList, hgen, List.length_map]
    exact height_map_eq_length I x hgen hheight p hIp

/-- Localization commutes with the ring quotient, as a module over the local ring. -/
noncomputable def quotientLocalizationEquiv (I : Ideal R) (p : PrimeSpectrum R) :
    LocalizedModule.AtPrime p.asIdeal (R ⧸ I) ≃ₗ[Localization.AtPrime p.asIdeal]
      (Localization.AtPrime p.asIdeal ⧸ I.map (algebraMap R (Localization.AtPrime p.asIdeal))) := by
  let A := Localization.AtPrime p.asIdeal
  let f := Algebra.linearMap R A
  have he : I.localized' A p.asIdeal.primeCompl f = I.map (algebraMap R A) := by
    rw [Submodule.localized'_eq_span]
    rfl
  exact (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (R ⧸ I))
    (I.toLocalizedQuotient' A p.asIdeal.primeCompl f)).extendScalarsOfIsLocalization
      p.asIdeal.primeCompl A ≪≫ₗ Submodule.quotEquivOfEq _ _ he

lemma completeIntersection_local_quotient (hCM : CohenMacaulayRing R)
    (I : Ideal R) (x : List R) (hgen : Ideal.ofList x = I)
    (hheight : I.height = x.length) (p : PrimeSpectrum R) (hIp : I ≤ p.asIdeal) :
    LocalCohenMacaulay (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⧸ I.map (algebraMap R (Localization.AtPrime p.asIdeal))) := by
  let A := Localization.AtPrime p.asIdeal
  let y := x.map (algebraMap R A)
  have hym : ∀ a ∈ y, a ∈ IsLocalRing.maximalIdeal A := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A p.asIdeal b).mpr
      (hIp (hgen ▸ Ideal.subset_span hb))
  have hreg := completeIntersection_regular_atPrime hCM I x hgen hheight p hIp
  have h := cohenMacaulay_quotient_of_regular A (hCM p) y hym hreg
  have he : Ideal.ofList y • (⊤ : Submodule A A) = I.map (algebraMap R A) := by
    change Ideal.ofList y * ⊤ = _
    rw [Ideal.mul_top, ← Ideal.map_ofList, hgen]
  rw [he] at h
  exact h

/-- The quotient is Cohen–Macaulay as an R-module. -/
theorem completeIntersection_cohenMacaulay_module (hCM : CohenMacaulayRing R)
    (I : Ideal R) (x : List R) (hgen : Ideal.ofList x = I)
    (hheight : I.height = x.length) : IsCohenMacaulay R (R ⧸ I) := by
  intro p hp
  have hIp : I ≤ p.asIdeal := by
    simpa only [Ideal.annihilator_quotient] using Module.mem_support_iff_of_finite.mp hp
  let e := quotientLocalizationEquiv I p
  letI : Nontrivial (LocalizedModule.AtPrime p.asIdeal (R ⧸ I)) := hp
  haveI : Nontrivial (Localization.AtPrime p.asIdeal ⧸
      I.map (algebraMap R (Localization.AtPrime p.asIdeal))) := e.symm.toEquiv.nontrivial
  exact (localCohenMacaulay_congr e).mpr
    (completeIntersection_local_quotient hCM I x hgen hheight p hIp)

/-- Associated primes of the quotient have the common height of I. -/
theorem completeIntersection_associated_height (hCM : CohenMacaulayRing R)
    (I : Ideal R) (x : List R) (hgen : Ideal.ofList x = I)
    (hheight : I.height = x.length) (p : Ideal R)
    (hp : p ∈ associatedPrimes R (R ⧸ I)) :
    p ∈ I.minimalPrimes ∧ p.height = x.length := by
  letI := hp.isPrime
  let P : PrimeSpectrum R := ⟨p, hp.isPrime⟩
  let A := Localization.AtPrime p
  let Q := LocalizedModule.AtPrime p (R ⧸ I)
  have hIp : I ≤ p := by
    simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient] using hp.annihilator_le
  have hs : P ∈ Module.support R (R ⧸ I) := by
    apply Module.mem_support_iff_of_finite.mpr
    simpa only [Ideal.annihilator_quotient] using hIp
  letI : Nontrivial Q := hs
  have hCMQ := completeIntersection_cohenMacaulay_module hCM I x hgen hheight P hs
  have hass := Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hp
  have hdim := dim_quotient_eq_dimension_of_associatedPrime hCMQ
    (IsLocalRing.maximalIdeal A) hass
  have hzero : dimension A Q = 0 := by
    rw [← hdim]
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
    exact ringKrullDim_eq_zero_of_field _
  have hreg := completeIntersection_regular_atPrime hCM I x hgen hheight P hIp
  have hdrop := Module.supportDim_add_length_eq_supportDim_of_isRegular
    (x.map (algebraMap R A)) hreg
  have he : Ideal.ofList (x.map (algebraMap R A)) • (⊤ : Submodule A A) =
      I.map (algebraMap R A) := by
    change (Ideal.ofList (x.map (algebraMap R A)) : Ideal A) * ⊤ = _
    rw [Ideal.mul_top, ← Ideal.map_ofList, hgen]
  rw [he, ← Module.supportDim_eq_of_equiv (quotientLocalizationEquiv I P),
    List.length_map, Module.supportDim_self_eq_ringKrullDim] at hdrop
  change dimension A Q + x.length = ringKrullDim A at hdrop
  rw [hzero, zero_add, IsLocalization.AtPrime.ringKrullDim_eq_height p A] at hdrop
  have hph : p.height = x.length := by exact_mod_cast hdrop.symm
  exact ⟨Ideal.mem_minimalPrimes_of_height_le hIp (by rw [hph, hheight]), hph⟩

/-- Arbitrary regular sequences in a regular local ring give CM quotient rings. -/
theorem regularLocal_quotient_cohenMacaulay [IsRegularLocalRing R] (x : List R)
    (hxm : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) (hx : IsRegular R x) :
    CohenMacaulayRing (R ⧸ Ideal.ofList x) := by
  letI := Depth.regularQuotientLocalRing x hxm
  apply cohenMacaulayRing_of_local
  apply (localCohenMacaulay_of_surjective_iff (R ⧸ Ideal.ofList x)
    Ideal.Quotient.mk_surjective).mp
  have h := cohenMacaulay_quotient_of_regular R (regularLocal_cohenMacaulay R) x hxm hx
  have he : Ideal.ofList x • (⊤ : Submodule R R) = Ideal.ofList x := by
    change Ideal.ofList x * ⊤ = _
    exact Ideal.mul_top _
  rwa [he] at h

/-- The global module condition for a quotient implies the ring condition. -/
lemma cohenMacaulayRing_quotient_of_module (I : Ideal R)
    (hCM : IsCohenMacaulay R (R ⧸ I)) : CohenMacaulayRing (R ⧸ I) := by
  intro q
  let p := q.asIdeal.comap (Ideal.Quotient.mk I)
  letI : p.IsPrime := Ideal.comap_isPrime _ _
  let A := Localization.AtPrime p
  let B := Localization.AtPrime q.asIdeal
  let g : A →+* B := Localization.localRingHom p q.asIdeal (Ideal.Quotient.mk I) rfl
  letI : Algebra A B := g.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R B r = g (algebraMap R A r)
    rw [Localization.localRingHom_to_map]
    rfl
  have hg : Function.Surjective (algebraMap A B) :=
    RingHom.surjective_localRingHom_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective q.asIdeal
  letI : Module.Finite A B := finite_restrictScalars_of_surjective (R := A) (S := B) B hg
  have hmap : Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl = q.asIdeal.primeCompl := by
    exact Submonoid.map_comap_eq_of_surjective
      (show Function.Surjective (Ideal.Quotient.mk I) from Ideal.Quotient.mk_surjective)
      q.asIdeal.primeCompl
  letI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl) B :=
    hmap.symm ▸ Localization.isLocalization
  let f : (R ⧸ I) →ₗ[R] B := (Algebra.linearMap (R ⧸ I) B).restrictScalars R
  letI : IsLocalizedModule p.primeCompl f :=
    IsLocalizedModule.restrictScalars p.primeCompl (Algebra.linearMap (R ⧸ I) B)
  let e := (IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl (R ⧸ I)) f).extendScalarsOfIsLocalization
      p.primeCompl A
  letI : Nontrivial (LocalizedModule.AtPrime p (R ⧸ I)) := e.toEquiv.nontrivial
  have h := hCM (⟨p, inferInstance⟩ : PrimeSpectrum R)
    (Module.mem_support_iff.mpr inferInstance)
  have hB : LocalCohenMacaulay A B := (localCohenMacaulay_congr e).mp h
  exact (localCohenMacaulay_of_surjective_iff B hg).mp hB

/-- Quotients by height-many generators of a CM ring are CM rings. -/
theorem completeIntersection_cohenMacaulay (hCM : CohenMacaulayRing R)
    (I : Ideal R) (x : List R) (hgen : Ideal.ofList x = I)
    (hheight : I.height = x.length) : CohenMacaulayRing (R ⧸ I) :=
  cohenMacaulayRing_quotient_of_module I
    (completeIntersection_cohenMacaulay_module hCM I x hgen hheight)

/-- Associated primes of the quotient ring, pulled back to R, are minimal over I
and all have the displayed number of generators as their height. -/
theorem completeIntersection_unmixed (hCM : CohenMacaulayRing R)
    (I : Ideal R) (x : List R) (hgen : Ideal.ofList x = I)
    (hheight : I.height = x.length) (q : Ideal (R ⧸ I))
    (hq : q ∈ associatedPrimes (R ⧸ I) (R ⧸ I)) :
    q.comap (Ideal.Quotient.mk I) ∈ I.minimalPrimes ∧
      (q.comap (Ideal.Quotient.mk I)).height = x.length := by
  obtain ⟨hqprime, a, ha⟩ := isAssociatedPrime_iff.mp hq
  have hp : q.comap (Ideal.Quotient.mk I) ∈ associatedPrimes R (R ⧸ I) := by
    apply isAssociatedPrime_iff.mpr
    refine ⟨hqprime.comap _, a, ?_⟩
    ext r
    simp only [Ideal.mem_comap, ha, Submodule.mem_colon_singleton, Submodule.mem_bot]
    rfl
  exact completeIntersection_associated_height hCM I x hgen hheight _ hp

end AdvCommAlg.CohenMacaulay
