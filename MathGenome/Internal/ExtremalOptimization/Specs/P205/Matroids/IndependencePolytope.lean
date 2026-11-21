import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matroids.Models
import Mathlib.Analysis.Convex.Hull

/-! The first assertion of Theorem 9.4 (W46), on the actual finite ground.
No total-rank equality or restriction on linear objectives is imposed. -/
namespace Specs.P205.Matroids
open _root_.P205.Matroids
universe u

def IndependencePolytope : Prop :=
  ∀ {α : Type u} (M : Matroid α) [M.Finite],
    convexHull ℝ (independentIndicatorsValue M) = rankInequalitiesValue M

end Specs.P205.Matroids
