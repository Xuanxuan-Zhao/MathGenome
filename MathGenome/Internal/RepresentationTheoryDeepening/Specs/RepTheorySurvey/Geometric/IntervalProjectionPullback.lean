import Mathlib.Topology.UnitInterval
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SheafModels

open CategoryTheory

namespace RepTheorySurvey.Geometric.IntervalProjectionPullback.Expected

/-- Inverse image along the second projection from the product with `[0, 1]` is
fully faithful on the bounded-below derived category of rational sheaves. -/
def IntervalProjectionFullyFaithful : Prop :=
  ∀ X : TopCat.{0},
    let p : TopCat.of (unitInterval × X) ⟶ X := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
    Nonempty ((Analytic.boundedBelowInverseImage p).FullyFaithful)

end RepTheorySurvey.Geometric.IntervalProjectionPullback.Expected
