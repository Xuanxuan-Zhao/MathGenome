import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExcellenceDefinitions
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Order.UpperLower.Basic

/-! Permanence of J-2 and universal catenarity under finite type and localization. -/

universe u v

namespace CommutativeAlgebraNotes.Excellence

section Localization
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]

include M in
/-- The regular locus of a localization is the inverse image of the regular locus. -/
theorem regularLocus_eq_preimage_of_isLocalization :
    regularLocus S = PrimeSpectrum.comap (algebraMap R S) ⁻¹' regularLocus R := by
  ext p
  let q := PrimeSpectrum.comap (algebraMap R S) p
  change IsRegularLocalRing (Localization.AtPrime p.asIdeal) ↔
    IsRegularLocalRing (Localization.AtPrime q.asIdeal)
  let T := Localization.AtPrime p.asIdeal
  let : IsLocalization.AtPrime T q.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M T p.asIdeal
  let e := IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) T
  exact ⟨fun hp => IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv,
    fun hq => IsRegularLocalRing.of_ringEquiv e.toRingEquiv⟩

include M in
/-- Contraction takes saturated prime chains to saturated prime chains, since
every prime below a surviving prime also avoids the denominators. -/
theorem Catenary.of_isLocalization (h : Catenary R) : Catenary S := by
  let e : PrimeSpectrum S ↪o PrimeSpectrum R :=
    OrderEmbedding.ofMapLEIff (PrimeSpectrum.comap (algebraMap R S))
      (fun _ _ => IsLocalization.under_le_under_iff M S)
  have hlower : IsLowerSet (Set.range e) := by
    change IsLowerSet (Set.range (PrimeSpectrum.comap (algebraMap R S)))
    rw [PrimeSpectrum.localization_comap_range S M]
    intro p q hpq hq
    exact hq.mono_right hpq
  let f : SetRel.Hom
      {(p, q) : PrimeSpectrum S × PrimeSpectrum S | p ⋖ q}
      {(p, q) : PrimeSpectrum R × PrimeSpectrum R | p ⋖ q} :=
    ⟨e, fun hcover => hcover.image e hlower.ordConnected⟩
  intro p q hpq c d hcp hcq hdp hdq
  exact h (e p) (e q) (e.monotone hpq) (c.map f) (d.map f)
    (congrArg e hcp) (congrArg e hcq) (congrArg e hdp) (congrArg e hdq)

end Localization

section Permanence
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]

theorem J2.of_finiteType [Algebra.FiniteType R S] (h : J2 R) :
    letI := Algebra.FiniteType.isNoetherianRing R S
    J2 S := by
  intro B _ _ _
  let : Algebra R B := Algebra.compHom B (algebraMap R S)
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FiniteType R B := Algebra.FiniteType.trans inferInstance ‹Algebra.FiniteType S B›
  exact h.isOpen_regularLocus B

theorem UniversallyCatenary.of_finiteType [Algebra.FiniteType R S] (h : UniversallyCatenary R) :
    letI := Algebra.FiniteType.isNoetherianRing R S
    UniversallyCatenary S := by
  intro B _ _ _
  let : Algebra R B := Algebra.compHom B (algebraMap R S)
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FiniteType R B := Algebra.FiniteType.trans inferInstance ‹Algebra.FiniteType S B›
  exact h.catenary B

/-- J-2 passes to an essentially finite-type algebra. A finite-type algebra over
it is a localization of a finite-type algebra over the original base. -/
theorem J2.of_essFiniteType [Algebra.EssFiniteType R S] (h : J2 R) :
    letI := Algebra.EssFiniteType.isNoetherianRing R S
    J2 S := by
  intro B _ _ _
  let : Algebra R B := Algebra.compHom B (algebraMap R S)
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  have hB : Algebra.EssFiniteType R B := Algebra.EssFiniteType.comp R S B
  obtain ⟨B₀, M, hfinite, hloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra R B).mp hB
  change IsOpen (regularLocus B)
  rw [regularLocus_eq_preimage_of_isLocalization M]
  exact (h.isOpen_regularLocus B₀).preimage (PrimeSpectrum.continuous_comap (algebraMap B₀ B))

theorem UniversallyCatenary.of_essFiniteType [Algebra.EssFiniteType R S]
    (h : UniversallyCatenary R) :
    letI := Algebra.EssFiniteType.isNoetherianRing R S
    UniversallyCatenary S := by
  intro B _ _ _
  let : Algebra R B := Algebra.compHom B (algebraMap R S)
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  have hB : Algebra.EssFiniteType R B := Algebra.EssFiniteType.comp R S B
  obtain ⟨B₀, M, hfinite, hloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra R B).mp hB
  exact Catenary.of_isLocalization M (h.catenary B₀)

theorem J2.of_isLocalization (M : Submonoid R) [IsLocalization M S] (h : J2 R) :
    letI := IsLocalization.isNoetherianRing M S (inferInstance : IsNoetherianRing R)
    J2 S :=
  letI := Algebra.EssFiniteType.of_isLocalization S M
  h.of_essFiniteType

theorem UniversallyCatenary.of_isLocalization (M : Submonoid R) [IsLocalization M S]
    (h : UniversallyCatenary R) :
    letI := IsLocalization.isNoetherianRing M S (inferInstance : IsNoetherianRing R)
    UniversallyCatenary S :=
  letI := Algebra.EssFiniteType.of_isLocalization S M
  h.of_essFiniteType

end Permanence

end CommutativeAlgebraNotes.Excellence
