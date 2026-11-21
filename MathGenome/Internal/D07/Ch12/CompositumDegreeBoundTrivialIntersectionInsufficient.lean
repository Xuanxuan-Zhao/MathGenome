import MathGenome.Internal.Specs.D07.Ch12.CompositumDegreeBoundTrivialIntersectionInsufficient
import MathGenome.Internal.D07.Ch14.CubicSplittingExample

namespace D07.Ch12.CompositumDegreeBoundTrivialIntersectionInsufficient

open IntermediateField
open Specs.D07.Ch14.CubicSplittingExample
open Specs.D07.Ch12.CompositumDegreeBoundTrivialIntersectionInsufficient

/-- The upstream cubic fields intersect in Q but have compositum degree six.
Linear disjointness would instead force degree nine. -/
theorem cubic_counterexample : CubicCounterexample := by
  intro ζ hζ
  have hL := Ch14.CubicSplittingExample.degreeSix ζ hζ
  have hE := Ch14.CubicSplittingExample.cubicDegrees ζ hζ 0
  have hF := Ch14.CubicSplittingExample.cubicDegrees ζ hζ 1
  have hsup := Ch14.CubicSplittingExample.compositum ζ hζ
  have hdegree : Module.finrank ℚ ↥(cubicField ζ 0 ⊔ cubicField ζ 1) = 6 := by
    rw [hsup, (topEquiv.toLinearEquiv).finrank_eq, hL.2.1]
  have hlt : Module.finrank ℚ ↥(cubicField ζ 0 ⊔ cubicField ζ 1) <
      Module.finrank ℚ (cubicField ζ 0) * Module.finrank ℚ (cubicField ζ 1) := by
    rw [hdegree, hE.2, hF.2]
    decide
  obtain ⟨ρ, _, _⟩ := Ch14.CubicSplittingExample.galoisGroupAndAlternatingFixedField ζ hζ
  refine ⟨hL.1, Ch14.CubicSplittingExample.splittingField ζ hζ, hL.2.2, ⟨ρ⟩,
    ?_, hE.1, hF.1, hE.2, hF.2,
    Ch14.CubicSplittingExample.intersections ζ hζ 0 1 (by decide), hsup,
    hL.2.1, hdegree, hlt, ?_⟩
  · intro heq
    have hinj := (Ch14.CubicSplittingExample.cubicClassification ζ hζ).1
    exact (by decide : (0 : Fin 3) ≠ 1) (hinj heq)
  · intro hdisjoint
    exact (ne_of_lt hlt) hdisjoint.finrank_sup

/-- Instantiate a primitive root explicitly to obtain an unconditional example. -/
theorem exists_cubic_counterexample : ExistsCubicCounterexample := by
  let ζ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hζ : IsPrimitiveRoot ζ 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
  exact ⟨ζ, hζ, cubic_counterexample ζ hζ⟩

end D07.Ch12.CompositumDegreeBoundTrivialIntersectionInsufficient
