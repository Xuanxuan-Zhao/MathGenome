import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.QuadraticContinuedFractions

/-! The reduced quotient and predecessor assertions of
`paper.tex`, Lemma `lem:nt-reduced-step` (2415–2424, 2434–2444).
The separate surd recurrence is allocated to E08_SurdRecurrence. -/
namespace P203Specs

/-- The quotient is reduced, with the intrinsic other-root conjugate formula. -/
def ReducedStep : Prop :=
  ∀ y : ℝ, ReducedQuadratic y →
    1 ≤ ⌊y⌋ ∧ ReducedQuadratic (continuedFractionStep y) ∧
      quadraticConjugate (continuedFractionStep y) =
        1 / (quadraticConjugate y - (⌊y⌋ : ℝ))

/-- The explicit predecessor has the indicated digit and is the unique reduced
predecessor among all real numbers, not just among represented surd states. -/
def ReducedPredecessor : Prop :=
  ∀ z : ℝ, ReducedQuadratic z →
    let a : ℤ := ⌊-1 / quadraticConjugate z⌋
    let y : ℝ := (a : ℝ) + 1 / z
    1 ≤ a ∧ ⌊y⌋ = a ∧ ReducedQuadratic y ∧ continuedFractionStep y = z ∧
      quadraticConjugate y = (a : ℝ) + 1 / quadraticConjugate z ∧
      ∀ w : ℝ, ReducedQuadratic w → continuedFractionStep w = z → w = y

end P203Specs
