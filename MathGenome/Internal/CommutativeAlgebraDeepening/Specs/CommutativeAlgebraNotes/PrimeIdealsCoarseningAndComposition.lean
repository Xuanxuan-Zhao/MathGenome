import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CoarseningAndResidueValuations
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompositionOfValuations

namespace Specs.CommutativeAlgebraNotes.PrimeIdealsCoarseningAndComposition

open OrderedValuationGroups (valueGroup)
open ValuationPrimesAndConvexSubgroups (convexAddSubgroup PrimeValues ringValue valuationRank)
open CoarseningAndResidueValuations (IsCoarsening HasResidueValuation residueMap)

universe u

/-- Theorem 5.19 and the rank formula. The localization and residue identifications
use the subgroup assigned to each prime by the order-reversing correspondence. -/
def PrimeIdealsCoarseningCompositionAndRank : Prop :=
  (∀ {K : Type u} [Field K] (V : ValuationSubring K),
    ∃ e : (PrimeSpectrum V)ᵒᵈ ≃o convexAddSubgroup (valueGroup V),
      (∀ (P : PrimeSpectrum V) (g : valueGroup V),
        (0 ≤ g ∧ g ∈ (e (OrderDual.toDual P)).1) ↔ PrimeValues V P g) ∧
      (∀ (H : convexAddSubgroup (valueGroup V)) (x : V),
        x ∈ (OrderDual.ofDual (e.symm H)).asIdeal ↔
          x = 0 ∨ ∃ hx : x ≠ 0, 0 ≤ ringValue V x hx ∧ ringValue V x hx ∉ H.1) ∧
      (∀ P : PrimeSpectrum V,
        IsCoarsening V P (e (OrderDual.toDual P)) ∧
          HasResidueValuation V P (e (OrderDual.toDual P))) ∧
      (let O : PrimeSpectrum V := ⊥
       let M : PrimeSpectrum V := ⟨IsLocalRing.maximalIdeal V, inferInstance⟩
       (e (OrderDual.toDual O)).1 = ⊤ ∧ V.ofPrime O.asIdeal = ⊤ ∧
         (e (OrderDual.toDual M)).1 = ⊥ ∧ V.ofPrime M.asIdeal = V ∧
           Function.Surjective (residueMap V M)) ∧
      valuationRank V = ⨆ c : LTSeries (convexAddSubgroup (valueGroup V)),
        (c.length : WithBot ℕ∞)) ∧
  _root_.CommutativeAlgebraNotes.CompositionOfValuations.Spec.Composition.{u}

end Specs.CommutativeAlgebraNotes.PrimeIdealsCoarseningAndComposition
