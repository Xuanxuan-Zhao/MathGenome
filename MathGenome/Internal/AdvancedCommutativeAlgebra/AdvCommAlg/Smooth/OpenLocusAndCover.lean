import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.LocusDefinitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.TargetLocality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.LocalStandardCover
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Permanence
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.OpenLocusAndCover

/-! Openness and the global equivalences in SM-07. Finite presentation is
descended by target locality, rather than assumed for the global assertions. -/
namespace AdvCommAlg.Smooth

universe u v

open Specs.AdvCommAlg.Smooth.OpenLocusAndCover

/-- The smooth locus is the union of its smooth principal neighborhoods. -/
theorem smoothLocus_isOpen : locusOpen.{u,v} := by
  intro A B _ _ _
  have heq : smoothLocus A B =
      ⋃ (g : B) (_ : Smooth A (Localization.Away g)),
        (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum B)) := by
    ext q
    simp [smoothLocus, IsSmoothAt, and_comm]
  change IsOpen (smoothLocus A B)
  rw [heq]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => PrimeSpectrum.isOpen_basicOpen

/-- Reindex a finite set of charts by Fin n for the target-locality interface. -/
private theorem smooth_of_finset_cover (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] (s : Finset B)
    (hspan : Ideal.span (s : Set B) = ⊤)
    (hs : ∀ g ∈ s, Smooth A (Localization.Away g)) : Smooth A B := by
  classical
  let g : Fin s.card → B := fun i => (s.equivFin.symm i).val
  have hrange : Set.range g = (s : Set B) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).property
    · intro hx
      refine ⟨s.equivFin ⟨x, hx⟩, ?_⟩
      simp [g]
  apply smooth_of_finite_principal_cover A B s.card g
  · rw [hrange]
    exact hspan
  · intro i
    exact hs _ (s.equivFin.symm i).property

/-- Smoothness can be tested at all primes using the neighborhood definition. -/
theorem smooth_iff_forall_isSmoothAt : smoothIffEveryPrime.{u,v} := by
  intro A B _ _ _
  change Smooth A B ↔ ∀ q : PrimeSpectrum B, IsSmoothAt A B q
  constructor
  · intro h q
    refine ⟨1, Ideal.one_notMem q.asIdeal, ?_⟩
    exact smooth_target_localization A B (Localization.Away (1 : B)) 1 h
  · intro h
    let S : Set B := {g | Smooth A (Localization.Away g)}
    have hspan : Ideal.span S = ⊤ := by
      apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
      rw [PrimeSpectrum.zeroLocus_span]
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      obtain ⟨g, hg, hgs⟩ := h q
      exact hg ((PrimeSpectrum.mem_zeroLocus q S).mp hq hgs)
    obtain ⟨s, hs, hsp⟩ := (Ideal.span_eq_top_iff_finite S).mp hspan
    exact smooth_of_finset_cover A B s hsp (fun g hg => hs hg)

/-- Smoothness is equivalent to a finite standard smooth principal cover. -/
theorem smooth_iff_exists_finite_standardSmooth_cover :
    smoothIffFiniteStandardCover.{u,v} := by
  intro A B _ _ _
  constructor
  · exact exists_finite_standardSmooth_cover A B
  · rintro ⟨s, hspan, hs⟩
    apply smooth_of_finset_cover A B s hspan
    intro g hg
    let : Algebra.IsStandardSmooth A (Localization.Away g) := hs g hg
    exact (inferInstance : Algebra.Smooth A (Localization.Away g))

/-- This finiteness conclusion also holds without a prior finiteness assumption. -/
theorem finitePresentation_of_forall_isSmoothAt : finitePresentationOfEveryPrime.{u,v} := by
  intro A B _ _ _ h
  exact ((smooth_iff_forall_isSmoothAt A B).mpr h).finitePresentation

end AdvCommAlg.Smooth
