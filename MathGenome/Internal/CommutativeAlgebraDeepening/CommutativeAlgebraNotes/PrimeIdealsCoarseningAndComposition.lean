import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PrimeIdealsCoarseningAndComposition
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoarseningAndResidueValuations
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompositionOfValuations

namespace CommutativeAlgebraNotes.PrimeIdealsCoarseningAndComposition

open ValuationPrimesAndConvexSubgroups (prime_convex_correspondence rank_eq_iSup_length)
open CoarseningAndResidueValuations (coarsening residue_valuation extreme_primes)
open Specs.CommutativeAlgebraNotes.CoarseningAndResidueValuations (Associated)
open Specs.CommutativeAlgebraNotes.PrimeIdealsCoarseningAndComposition
  (PrimeIdealsCoarseningCompositionAndRank)

universe u

/-- Prime ideals, coarsening, and composition of valuation rings, with the rank formula. -/
theorem prime_ideals_coarsening_and_composition :
    PrimeIdealsCoarseningCompositionAndRank.{u} := by
  refine ⟨?_, CompositionOfValuations.composition⟩
  intro K _ V
  obtain ⟨e, hprime, hconvex, hbot, hmax⟩ := prime_convex_correspondence V
  obtain ⟨⟨hlocalBot, _⟩, hlocalMax, hsurj, _⟩ := extreme_primes V
  refine ⟨e, hprime, hconvex, ?_, ⟨hbot, hlocalBot, hmax, hlocalMax, hsurj⟩,
    rank_eq_iSup_length V⟩
  intro P
  let H := e (OrderDual.toDual P)
  have hassoc : Associated V P H := fun g hg ↦
    ⟨fun h ↦ (hprime P g).mp ⟨hg, h⟩, fun h ↦ ((hprime P g).mpr h).2⟩
  exact ⟨coarsening V P H hassoc, residue_valuation V P H hassoc⟩

end CommutativeAlgebraNotes.PrimeIdealsCoarseningAndComposition
