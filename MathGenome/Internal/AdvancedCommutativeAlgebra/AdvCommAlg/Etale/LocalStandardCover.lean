import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.LocalStandardCover
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.OpenLocus
import Mathlib.RingTheory.Unramified.LocalStructure

/-! Local monic one-variable presentations and finite standard étale covers
(ET-09). The Mathlib local structure theorem applies to the prime-local
étale predicate; the upstream comparison uses precisely the source's
principal-neighborhood convention. -/
namespace AdvCommAlg.Etale

universe u v

open Specs.AdvCommAlg.Etale
open Specs.AdvCommAlg.Etale.StandardAndPointwise
open Specs.AdvCommAlg.Etale.LocalStandardCover

theorem exists_standard_etale_neighborhood : localStandardNeighborhood.{u,v} := by
  intro A B _ _ _ _ q hq
  let : Algebra.IsEtaleAt A q.asIdeal :=
    (neighborhood_iff_isEtaleAt A B q).mp hq
  obtain ⟨b, hb, hstandard⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := A) q.asIdeal
  exact ⟨b, hb, (standardEtale_iff A (Localization.Away b)).mpr hstandard⟩

theorem exists_finite_standard_etale_cover : finiteStandardCover.{u,v} := by
  intro A B _ _ _ h
  classical
  let : Algebra.Etale A B := h
  let S : Set B := {b | standardEtaleValue A (Localization.Away b)}
  have hcover : (⨆ b ∈ S, PrimeSpectrum.basicOpen b) = ⊤ := by
    apply top_unique
    intro q _
    have hq : isEtaleAtValue A B q :=
      (neighborhood_iff_isEtaleAt A B q).mpr inferInstance
    obtain ⟨b, hb, hstandard⟩ := exists_standard_etale_neighborhood A B q hq
    simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨b, hstandard, hb⟩
  have hspan : Ideal.span S = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp hcover
  obtain ⟨s, hs, hstop⟩ := (Ideal.span_eq_top_iff_finite S).mp hspan
  exact ⟨s, hstop, fun b hb => hs hb⟩

theorem empty_standard_etale_cover : emptyStandardCover.{u,v} := by
  intro A B _ _ _ _
  constructor
  · exact Subsingleton.elim _ _
  · simp

end AdvCommAlg.Etale
