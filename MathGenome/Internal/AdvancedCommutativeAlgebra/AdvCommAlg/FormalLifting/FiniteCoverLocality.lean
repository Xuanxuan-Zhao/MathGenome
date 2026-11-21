import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.FiniteCoverLocality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.UnramifiedLocality
import Mathlib.RingTheory.Smooth.Locus

/-! FL-10: finite principal covers.

For smoothness we use the cotangent proof of the smooth-locus criterion.
Mathlib identifies the smooth locus with the intersection of the complement
of the support of H¹ and the free locus of Ω. For a finitely presented
algebra, Ω is finitely presented; its local freeness detects projectivity.
Localization of H¹ detects its vanishing. Thus covering the spectrum by
smooth principal opens gives global formal smoothness, equivalently the
square-zero lifting property by FL-01. This is a local-to-global argument
on the cotangent modules, valid also for an empty spectrum.
-/
namespace AdvCommAlg.FormalLifting.FiniteCoverLocality

universe u v

open Specs.AdvCommAlg.FormalLifting.FiniteCoverLocality

/-- The formal smoothness criterion on a finite principal cover. -/
theorem formallySmooth_iff_finite_principal_cover :
    smoothFinitePrincipalCover.{u,v} := by
  intro A B _ _ _ _ n b hspan
  change FormallySmooth A B ↔ _
  constructor
  · intro h i
    exact smooth_target_localization A B (Localization.Away (b i))
      (Submonoid.powers (b i)) h
  · intro h
    apply (formallySmooth_iff A B).mpr
    apply Algebra.smoothLocus_eq_univ_iff.mp
    apply Set.eq_univ_of_forall
    intro q
    classical
    have hex : ∃ i, b i ∉ q.asIdeal := by
      by_contra! hall
      have hle : Ideal.span (Set.range b) ≤ q.asIdeal :=
        Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
      exact q.isPrime.ne_top (top_unique (hspan ▸ hle))
    obtain ⟨i, hi⟩ := hex
    exact (Algebra.basicOpen_subset_smoothLocus_iff.mpr
      ((formallySmooth_iff A (Localization.Away (b i))).mp (h i))) hi

/-- Formal unramifiedness needs no finiteness hypothesis. -/
theorem formallyUnramified_iff_finite_principal_cover :
    unramifiedFinitePrincipalCover.{u,v} :=
  AdvCommAlg.FormalLifting.formallyUnramified_iff_finite_principal_cover

private theorem etale_iff_smooth_and_unramified
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    FormallyEtale A B ↔ FormallySmooth A B ∧ FormallyUnramified A B := by
  constructor
  · intro h
    exact ⟨fun N hN => (h N hN).2, fun N hN => (h N hN).1⟩
  · rintro ⟨hS, hU⟩
    exact fun N hN => ⟨hU N hN, hS N hN⟩

/-- Formal étaleness is the conjunction of existence and uniqueness. -/
theorem formallyEtale_iff_finite_principal_cover :
    etaleFinitePrincipalCover.{u,v} := by
  intro A B _ _ _ _ n b hspan
  change FormallyEtale A B ↔ _
  constructor
  · intro h i
    exact etale_target_localization A B (Localization.Away (b i))
      (Submonoid.powers (b i)) h
  · intro h
    apply (etale_iff_smooth_and_unramified A B).mpr
    constructor
    · apply (formallySmooth_iff_finite_principal_cover A B n b hspan).mpr
      intro i
      exact ((etale_iff_smooth_and_unramified A (Localization.Away (b i))).mp (h i)).1
    · apply (formallyUnramified_iff_finite_principal_cover A B n b hspan).mpr
      intro i
      exact ((etale_iff_smooth_and_unramified A (Localization.Away (b i))).mp (h i)).2

end AdvCommAlg.FormalLifting.FiniteCoverLocality
