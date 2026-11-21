import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.InvariantProbability
import Mathlib.Dynamics.Ergodic.EmpiricalMeasure

/-!
Existence of an invariant Borel probability on a nonempty compact metric space.

We specialize Mathlib's Krylov–Bogolyubov theorem, whose hypotheses are
nonemptiness, compactness, the Hausdorff property, the Borel measurable
structure, and continuity of the self-map. A metric space is Hausdorff.
Its conclusion supplies an actual regular probability measure and the
pushforward equality, hence preservation for every Borel set. No
invertibility or extra dynamical hypothesis is required.
-/

open MeasureTheory

namespace D13Unified.Ch19

/-- `paper.tex`, Theorem `d13:19:invariant-probability`. -/
theorem invariant_probability : Specs.D13Unified.Ch19.InvariantProbability := by
  intro K _ _ _ _ _ T hT
  obtain ⟨ν, hν, _, hprob⟩ := exists_measurePreserving_probabilityMeasure hT
  exact ⟨⟨ν, hprob⟩, hν⟩

end D13Unified.Ch19
