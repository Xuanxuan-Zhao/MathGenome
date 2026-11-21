import MathGenome.Internal.ExtremalOptimization.Specs.P205.Polyhedra.ActiveRows

/-! The general convex-set midpoint characterization preceding W32. -/
namespace P205.Convex.Expected

/-- Only convexity is assumed; membership is included in `MidpointExtreme`. -/
def midpointExtremeIffMemExtremePoints : Prop :=
  ∀ {n : ℕ} (P : Set (P205.Polyhedra.Coordinate n))
    (x : P205.Polyhedra.Coordinate n), Convex ℝ P →
      (P205.Polyhedra.MidpointExtreme P x ↔ x ∈ P.extremePoints ℝ)

/-- In particular, both endpoints of any strict convex decomposition equal the point. -/
def eqOfMidpointExtremeConvexCombination : Prop :=
  ∀ {n : ℕ} (P : Set (P205.Polyhedra.Coordinate n))
    (x y z : P205.Polyhedra.Coordinate n) (t : ℝ),
    Convex ℝ P → P205.Polyhedra.MidpointExtreme P x →
    y ∈ P → z ∈ P → 0 < t → t < 1 →
    t • y + (1 - t) • z = x → y = x ∧ z = x

end P205.Convex.Expected
