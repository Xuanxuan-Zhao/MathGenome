import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.StandardAndPointwiseDefinitions

/-! ET-06: standard étale algebras and étale principal neighborhoods.
The quotient model is `AdjoinRoot f = A[X]/(f)` and its localization
inverts the image of `g`. The comparison with Mathlib clears denominators
in that quotient; it does not require monicity or nontriviality.
-/
namespace AdvCommAlg.Etale

universe u v
open Polynomial
open Specs.AdvCommAlg.Etale.StandardAndPointwise

/-- The source's standard form, retaining the monicity requirement. -/
abbrev StandardEtale : Specs.AdvCommAlg.FormalLifting.propertyType.{u,v} :=
  standardEtaleValue

/-- Étale on a principal neighborhood of the given prime. -/
abbrev IsEtaleAt : atPrimeType.{u,v} := isEtaleAtValue

/-- The primes admitting an étale principal neighborhood. -/
abbrev etaleLocus : locusType.{u,v} := etaleLocusValue

theorem derivative_unit_iff : derivativeUnitIff.{u} := by
  intro A _ f g
  change IsUnit (algebraMap (AdjoinRoot f) (LocalizedQuotient f g)
    (AdjoinRoot.mk f f.derivative)) ↔ _
  rw [IsLocalization.algebraMap_isUnit_iff (Submonoid.powers (AdjoinRoot.mk f g))]
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, a, ha⟩
    obtain ⟨p₁, rfl⟩ := AdjoinRoot.mk_surjective a
    have hz : AdjoinRoot.mk f (g ^ n - f.derivative * p₁) = 0 := by
      simpa only [map_sub, map_mul, map_pow, sub_eq_zero] using ha
    obtain ⟨p₂, hp₂⟩ := AdjoinRoot.mk_eq_zero.mp hz
    exact ⟨p₁, p₂, n, by rw [← hp₂]; ring⟩
  · rintro ⟨p₁, p₂, n, h⟩
    refine ⟨_, ⟨n, rfl⟩, AdjoinRoot.mk f p₁, ?_⟩
    have := congrArg (AdjoinRoot.mk f) h
    simpa using this.symm

theorem standardEtale_iff : standardEtaleIff.{u,v} := by
  intro A B _ _ _
  constructor
  · rintro ⟨f, hf, g, hunit, ⟨e⟩⟩
    let P : StandardEtalePair A := ⟨f, hf, g, (derivative_unit_iff A f g).mp hunit⟩
    exact Algebra.IsStandardEtale.of_equiv (P.equivAwayAdjoinRoot.trans e.symm)
  · intro h
    obtain ⟨P⟩ := h.nonempty_standardEtalePresentation
    refine ⟨P.f, P.monic_f, P.g, (derivative_unit_iff A P.f P.g).mpr P.cond,
      ⟨P.equivRing.trans P.P.equivAwayAdjoinRoot⟩⟩

theorem standardEtalePresentation_iff : standardEtalePresentationIff.{u,v} := by
  intro A B _ _ _
  rw [standardEtale_iff A B]
  exact ⟨fun h => h.nonempty_standardEtalePresentation, fun h => ⟨h⟩⟩

theorem etaleLocus_eq_union : locusEqUnion.{u,v} := by
  intro A B _ _ _
  ext q
  simp only [etaleLocusValue, isEtaleAtValue, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨b, hb, he⟩
    exact ⟨b, he, hb⟩
  · rintro ⟨b, he, hb⟩
    exact ⟨b, hb, he⟩

end AdvCommAlg.Etale
