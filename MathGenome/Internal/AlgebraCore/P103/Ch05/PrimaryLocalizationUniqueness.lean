import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.PrimaryLocalizationUniqueness
import MathGenome.Internal.AlgebraCore.P103.Ch05.PrimaryDecomposition
import MathGenome.Internal.AlgebraCore.P103.Ch05.PrimarySubmodules
import MathGenome.Internal.AlgebraCore.P103.Ch04.ModuleLocalization

namespace P103.Ch05.PrimaryLocalizationUniqueness

universe u v
open P103.Specs.Ch05.PrimaryLocalizationUniqueness
open P103.Specs.Ch05.PrimaryDecomposition
open P103.Specs.Ch05.PrimarySubmodules
open P103.Specs.Ch05.AssociatedPrimesInterface

noncomputable def contraction : ContractionType.{u,v} := contractionValue

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Membership in the contraction is the usual saturation criterion. -/
theorem mem_contraction_iff (S : Submonoid R) (N : Submodule R M) (m : M) :
    m ∈ contractionValue R M S N ↔ ∃ a : S, (a : R) • m ∈ N := by
  change (∃ n ∈ N, ∃ t : S,
    IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) n t =
      LocalizedModule.mkLinearMap S M m) ↔ _
  constructor
  · rintro ⟨n, hn, t, ht⟩
    rw [IsLocalizedModule.mk'_eq_iff, ← LinearMap.map_smul_of_tower] at ht
    obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists S
      (LocalizedModule.mkLinearMap S M)).mp ht
    refine ⟨a * t, ?_⟩
    change (a : R) • n = (a : R) • (t : R) • m at ha
    have h := N.smul_mem (a : R) hn
    rw [ha] at h
    simpa only [Submonoid.coe_mul, mul_smul] using h
  · rintro ⟨a, ha⟩
    exact ⟨(a : R) • m, ha, a, IsLocalizedModule.mk'_cancel _ m a⟩

/-- On a primary quotient, an avoided scalar cannot kill a nonzero class. -/
theorem primary_contraction_of_disjoint (S : Submonoid R) (Q : Submodule R M)
    (hQ : primaryValue R M Q)
    (hd : Disjoint (radicalValue R M Q : Set R) (S : Set R)) :
    contractionValue R M S Q = Q := by
  ext m
  rw [mem_contraction_iff]
  constructor
  · rintro ⟨a, ha⟩
    have hnot : (a : R) ∉ radicalValue R M Q :=
      fun h => Set.disjoint_left.mp hd h a.property
    have hinj := PrimarySubmodules.injective_of_not_mem_radical R M Q hQ (a : R) hnot
    apply (Submodule.Quotient.mk_eq_zero Q).mp
    apply hinj
    simpa using (Submodule.Quotient.mk_eq_zero Q).mpr ha
  · intro hm
    exact ⟨1, by simpa using hm⟩

/-- A radical element from S has a power that annihilates the whole quotient. -/
theorem primary_contraction_of_not_disjoint (S : Submonoid R) (Q : Submodule R M)
    (hd : ¬ Disjoint (radicalValue R M Q : Set R) (S : Set R)) :
    contractionValue R M S Q = ⊤ := by
  apply top_unique
  intro m _
  rw [mem_contraction_iff]
  obtain ⟨a, ha, has⟩ := Set.not_disjoint_iff.mp hd
  obtain ⟨n, _, hn⟩ := (PrimarySubmodules.mem_radical_iff_nilpotent R M Q a).mp ha
  refine ⟨⟨a ^ n, S.pow_mem has n⟩, ?_⟩
  exact (Submodule.Quotient.mk_eq_zero Q).mp (hn (Submodule.Quotient.mk m))

/-- Localize the finite intersection and contract each primary factor. -/
theorem localizationFormula : localizationFormulaType.{u,v} := by
  intro R _ _ M _ _ _ N s h S
  ext m
  change LocalizedModule.mkLinearMap S M m ∈ N.localized S ↔ _
  rw [← h.intersection]
  rw [P103.Ch04.ModuleLocalization.finiteIntersections
    R S M (Submodule R M) s (fun Q => Q)]
  simp only [Submodule.mem_iInf]
  constructor
  · intro hm Q hQs hd
    have hmQ : m ∈ contractionValue R M S Q := hm Q hQs
    rwa [primary_contraction_of_disjoint S Q (h.primary Q hQs) hd] at hmQ
  · intro hm Q hQs
    change m ∈ contractionValue R M S Q
    by_cases hd : Disjoint (radicalValue R M Q : Set R) (S : Set R)
    · rw [primary_contraction_of_disjoint S Q (h.primary Q hQs) hd]
      exact hm Q hQs hd
    · rw [primary_contraction_of_not_disjoint S Q hd]
      exact Submodule.mem_top

theorem emptyIntersection : emptyIntersectionType.{u,v} := by
  intro R _ _ M _ _ _ N s h S hS
  rw [localizationFormula R M N s h S]
  apply top_unique
  intro m _
  simp only [Submodule.mem_iInf]
  intro Q hQ hd
  exact (hS Q hQ hd).elim

/-- Avoiding the complement of a prime is exactly containment in it. -/
theorem disjoint_primeCompl_iff (I : Ideal R) (p : PrimeSpectrum R) :
    Disjoint (I : Set R) (p.asIdeal.primeCompl : Set R) ↔ I ≤ p.asIdeal := by
  constructor
  · intro hd r hr
    by_contra hnot
    exact Set.disjoint_left.mp hd hr hnot
  · intro hle
    exact Set.disjoint_left.mpr (fun r hr hnot => hnot (hle hr))

theorem minimalComponent : minimalComponentType.{u,v} := by
  intro R _ _ M _ _ _ N s h p hp
  have hass := PrimaryDecomposition.associatedPrimes_eq_radicals R M N s h
  have hex : ∃ Q ∈ s, radicalValue R M Q = p.asIdeal := by
    have hmem := hp.1
    rw [hass] at hmem
    exact hmem
  refine ⟨hex, ?_⟩
  intro Q hQ hrad
  rw [localizationFormula R M N s h p.asIdeal.primeCompl]
  apply le_antisymm
  · refine le_iInf fun P => le_iInf fun hP => le_iInf fun hd => ?_
    have hmem : radicalValue R M P ∈ associatedPrimesValue R (M ⧸ N) := by
      rw [hass]
      exact Set.mem_image_of_mem _ hP
    have hradP : radicalValue R M P = p.asIdeal :=
      hp.eq_of_le hmem ((disjoint_primeCompl_iff _ p).mp hd)
    have heq : P = Q := by
      by_contra hne
      exact h.distinct hP hQ hne (hradP.trans hrad.symm)
    rw [heq]
  · apply iInf_le_of_le Q
    apply iInf_le_of_le hQ
    apply iInf_le_of_le ((disjoint_primeCompl_iff _ p).mpr (le_of_eq hrad))
    exact le_rfl

theorem minimalComponentUnique : minimalComponentUniqueType.{u,v} := by
  intro R _ _ M _ _ _ N s t hs ht p hp Q hQ P hP hradQ hradP
  exact ((minimalComponent R M N s hs p hp).2 Q hQ hradQ).trans
    ((minimalComponent R M N t ht p hp).2 P hP hradP).symm

end P103.Ch05.PrimaryLocalizationUniqueness
