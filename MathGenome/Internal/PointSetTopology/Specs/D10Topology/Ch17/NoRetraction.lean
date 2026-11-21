import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent statement of paper.tex, d10:17:no-retraction.
The ball and sphere are subtypes of Euclidean space with their induced
topologies. The map in the identity condition is the standard inclusion of
the unit sphere into the closed unit ball. -/
namespace Specs.D10Topology.Ch17.NoRetraction

def no_retraction_ball_sphere : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ¬ ∃ r : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ ≤ 1} →
        {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1},
      Continuous r ∧
        ∀ y : {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1},
          r ⟨y.val, y.property.le⟩ = y

end Specs.D10Topology.Ch17.NoRetraction
