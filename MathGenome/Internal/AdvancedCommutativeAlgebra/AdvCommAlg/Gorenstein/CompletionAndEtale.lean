import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.FlatLocalMaps
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.FlatUnramifiedCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.LocalResidueFields
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.CompletionAndEtale
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

noncomputable section
set_option linter.style.haveILetI false
universe u
open CategoryTheory
namespace AdvCommAlg.Gorenstein

/-- A field is self-injective, hence has finite self-injective dimension.
`IsField` preserves the given commutative ring structure. -/
lemma localGorenstein_of_isField (K : Type u) [CommRing K]
    [IsNoetherianRing K] [IsLocalRing K] (hK : IsField K) : LocalGorenstein K := by
  letI := hK.toField
  letI : Module.Injective K K := Module.injective_of_isSemisimpleRing K K
  letI : Injective (ModuleCat.of K K) := Module.injective_object_of_injective_module K K
  exact (finiteInjectiveDimension_iff_exists_bound K K).mpr
    ⟨0, inferInstance⟩

/-- The flat-local criterion specializes to a field closed fiber. -/
lemma flatLocal_gorenstein_iff_of_isField (R S : Type u)
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (hF : IsField (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))) :
    LocalGorenstein S ↔ LocalGorenstein R := by
  letI := CohenMacaulay.Specs.closedFiberLocalRing R S
  exact (flatLocal_gorenstein R S).trans
    (and_iff_left (localGorenstein_of_isField _ hF))

/-- Completion is faithfully flat and local, with a field closed fiber. -/
theorem completion_applicability :
    CompletionAndEtaleSpecs.completion_applicabilityType.{u} := by
  intro R _ _ _
  let S := AdicCompletion (IsLocalRing.maximalIdeal R) R
  have hF : IsField (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
    rw [← AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.Quotient.maximal_ideal_iff_isField_quotient _ |>.mp inferInstance
  exact ⟨CohenMacaulay.completion_faithfullyFlat R, inferInstance, hF⟩

/-- A Noetherian local ring is Gorenstein exactly when its maximal-ideal
adic completion is Gorenstein. Noetherianness of the completion is proved. -/
theorem completion_gorenstein_iff :
    CompletionAndEtaleSpecs.completion_gorensteinType.{u} := by
  intro R _ _ _
  letI := CohenMacaulay.Specs.completionNoetherian R
  exact (flatLocal_gorenstein_iff_of_isField R _ (completion_applicability R).2.2).symm

section Etale
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [IsNoetherianRing A] [IsNoetherianRing B]

/-- At an étale prime the stalk map is flat and local and its closed fiber
is the residue field of the target stalk. -/
lemma etale_stalk_criterion (h : Etale.Etale A B) (q : PrimeSpectrum B) :
    LocalGorenstein (Localization.AtPrime q.asIdeal) ↔
      LocalGorenstein (Localization.AtPrime (q.asIdeal.under A)) := by
  letI : Algebra.Etale A B := h
  have hflat := (Etale.etale_iff_finitePresentation_flat_subsingleton_omega A B).mp h |>.2.1
  letI := hflat
  let p := q.asIdeal.under A
  letI := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  let R := Localization.AtPrime p
  let S := Localization.AtPrime q.asIdeal
  have hloc : IsLocalHom (algebraMap R S) := by
    rw [Localization.AtPrime.algebraMap_eq]
    exact Localization.isLocalHom_localRingHom _ _ _ _
  letI := hloc
  have hq : Etale.IsEtaleAt A B q :=
    ⟨1, q.asIdeal.one_notMem,
      show Algebra.Etale A (Localization.Away (1 : B)) from inferInstance⟩
  have hJ : (IsLocalRing.maximalIdeal R).map (algebraMap R S) =
      IsLocalRing.maximalIdeal S := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p R, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
    exact Etale.contracted_prime_map A B q hq
  apply flatLocal_gorenstein_iff_of_isField R S
  rw [hJ]
  exact Ideal.Quotient.maximal_ideal_iff_isField_quotient _ |>.mp inferInstance

end Etale

theorem etale_stalk_gorenstein_iff :
    CompletionAndEtaleSpecs.etale_stalk_gorensteinType.{u} := by
  intro A B _ _ _ _ _ h q
  exact etale_stalk_criterion A B h q

/-- Prime-local Gorensteinness ascends along every étale map, also for zero rings. -/
theorem etale_gorenstein_ascent : CompletionAndEtaleSpecs.etale_ascentType.{u} := by
  intro A B _ _ _ _ _ h hA q
  exact (etale_stalk_criterion A B h q).mpr (hA (PrimeSpectrum.comap (algebraMap A B) q))

/-- Faithful flatness supplies a prime above every base prime, so the stalk
criterion gives descent. No nonzero assumption is imposed on the global rings. -/
theorem etale_gorenstein_descent : CompletionAndEtaleSpecs.etale_descentType.{u} := by
  intro A B _ _ _ _ _ h hff hB p
  letI := hff
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) p
  have h := (etale_stalk_criterion A B h q).mp (hB q)
  change Specs.LocalGorensteinValue
    (Localization.AtPrime (PrimeSpectrum.comap (algebraMap A B) q).asIdeal) at h
  rw [hq] at h
  exact h

end AdvCommAlg.Gorenstein
