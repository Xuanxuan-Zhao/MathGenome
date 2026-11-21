import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.StandardAndPointwiseDefinitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.LocalResidueFields

namespace AdvCommAlg.Etale

universe u v

/-- Finiteness is needed only on the displayed principal neighborhood. -/
theorem local_essFiniteType (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B)
    (h : IsEtaleAt A B q) : Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) := by
  obtain ⟨b, hb, he⟩ := h
  let : Algebra.Etale A (Localization.Away b) := he
  have hle : Submonoid.powers b ≤ q.asIdeal.primeCompl := by
    simpa [Submonoid.powers_le, Ideal.primeCompl] using hb
  let : Algebra (Localization.Away b) (Localization.AtPrime q.asIdeal) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  have : IsScalarTower B (Localization.Away b) (Localization.AtPrime q.asIdeal) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  have : IsScalarTower A (Localization.Away b) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply A B (Localization.Away b),
        ← IsScalarTower.algebraMap_apply B (Localization.Away b),
        ← IsScalarTower.algebraMap_apply A B]
  have : IsLocalization (q.asIdeal.primeCompl.map (algebraMap B (Localization.Away b)))
      (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hle
  have : Algebra.EssFiniteType (Localization.Away b) (Localization.AtPrime q.asIdeal) :=
    Algebra.EssFiniteType.of_isLocalization _
      (q.asIdeal.primeCompl.map (algebraMap B (Localization.Away b)))
  exact Algebra.EssFiniteType.comp A (Localization.Away b) _

/-- Formal unramifiedness passes from the principal neighborhood to the stalk. -/
theorem local_formallyUnramified (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B)
    (h : IsEtaleAt A B q) : Algebra.FormallyUnramified A (Localization.AtPrime q.asIdeal) := by
  obtain ⟨b, hb, he⟩ := h
  let : Algebra.Etale A (Localization.Away b) := he
  exact (Algebra.basicOpen_subset_unramifiedLocus_iff.mpr
    (inferInstance : Algebra.FormallyUnramified A (Localization.Away b))) hb

/-- The extended contracted prime is the maximal ideal of the stalk. -/
theorem contracted_prime_map (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (q : PrimeSpectrum B)
    (h : IsEtaleAt A B q) :
    (q.asIdeal.under A).map (algebraMap A (Localization.AtPrime q.asIdeal)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) := by
  let p := q.asIdeal.under A
  let := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  have := local_essFiniteType A B q h
  have := local_formallyUnramified A B q h
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    Algebra.EssFiniteType.of_comp A _ _
  have hm := Algebra.FormallyUnramified.map_maximalIdeal
    (R := Localization.AtPrime p) (S := Localization.AtPrime q.asIdeal)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p),
    Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hm
  exact hm

theorem prime_extension_eq :
    Specs.AdvCommAlg.Etale.LocalResidueFields.primeExtensionEquality.{u,v} := by
  intro A B _ _ _ q h
  rw [Localization.AtPrime.map_eq_maximalIdeal,
    contracted_prime_map A B q h]

theorem finite_separable_residueFields :
    Specs.AdvCommAlg.Etale.LocalResidueFields.finiteSeparableResidueFields.{u,v} := by
  intro A B _ _ _ q h
  let p := q.asIdeal.under A
  let := Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  have := local_essFiniteType A B q h
  have := local_formallyUnramified A B q h
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    Algebra.EssFiniteType.of_comp A _ _
  exact ⟨inferInstance, inferInstance⟩

theorem local_fiber_identification :
    Specs.AdvCommAlg.Etale.LocalResidueFields.localFiberIdentification.{u,v} := by
  intro A B _ _ _ q h
  refine ⟨Ideal.quotientEquivAlgOfEq (Localization.AtPrime q.asIdeal)
    (contracted_prime_map A B q h), ?_⟩
  intro x
  rfl

end AdvCommAlg.Etale
