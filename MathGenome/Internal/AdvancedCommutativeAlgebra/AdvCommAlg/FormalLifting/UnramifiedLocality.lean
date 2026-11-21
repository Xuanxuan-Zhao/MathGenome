import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Localization
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.UnramifiedLocality
import Mathlib.RingTheory.Unramified.Locus

/-! FL-10: formal unramifiedness is local on the target without any finiteness
assumption. Mathlib's prime-local criterion uses vanishing of the localized
Kähler differential module; FL-01 identifies it with uniqueness of square-zero
lifts. Every prime misses a member of a family generating the unit ideal,
so the principal-cover assertion follows from the same criterion.
-/
namespace AdvCommAlg.FormalLifting

universe u v

/-- Prime-local detection for the square-zero lifting definition, including
the zero ring, whose spectrum is empty. -/
theorem formallyUnramified_iff_prime_localizations :
    Specs.AdvCommAlg.FormalLifting.UnramifiedLocality.primeLocalizations.{u,v} := by
  intro A B _ _ _
  refine (formallyUnramified_iff A B).trans ?_
  refine Algebra.formallyUnramified_iff_forall.trans ?_
  exact forall_congr' fun q =>
    (formallyUnramified_iff A (Localization.AtPrime q.asIdeal)).symm

/-- Finite principal covers detect formal unramifiedness. There is no
nonempty-family assumption: the empty cover handles the zero target ring. -/
theorem formallyUnramified_iff_finite_principal_cover :
    Specs.AdvCommAlg.FormalLifting.UnramifiedLocality.finitePrincipalCover.{u,v} := by
  intro A B _ _ _ n b hspan
  change FormallyUnramified A B ↔ _
  constructor
  · intro h i
    exact unramified_target_localization A B (Localization.Away (b i))
      (Submonoid.powers (b i)) h
  · intro h
    apply (formallyUnramified_iff_prime_localizations A B).mpr
    intro q
    classical
    have hex : ∃ i, b i ∉ q.asIdeal := by
      by_contra! hall
      have hle : Ideal.span (Set.range b) ≤ q.asIdeal :=
        Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hall i)
      exact q.isPrime.ne_top (top_unique (hspan ▸ hle))
    obtain ⟨i, hi⟩ := hex
    apply (formallyUnramified_iff A (Localization.AtPrime q.asIdeal)).mpr
    exact (Algebra.basicOpen_subset_unramifiedLocus_iff.mpr
      ((formallyUnramified_iff A (Localization.Away (b i))).mp (h i))) hi

end AdvCommAlg.FormalLifting
