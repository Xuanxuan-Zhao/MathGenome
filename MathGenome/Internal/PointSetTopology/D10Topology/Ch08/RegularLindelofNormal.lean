import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.RegularLindelofNormal
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityImplications

/-!
Theorem d10:08:regular-lindelof-normal of paper.tex.
Mathlib's regular-Lindelöf normality theorem has precisely the paper's
separation conventions: neither regularity nor normality includes T1.
The second assertion adds the given T1 condition to obtain the paper's T4.
-/

universe u

namespace D10Topology.Ch08

variable {X : Type u} [t : TopologicalSpace X]

/-- Every regular Lindelöf space is normal, without separation assumptions. -/
theorem regular_lindelof_normal (hR : Ch07.Regular X) (hL : Lindelof t) :
    Ch07.Normal X := by
  let : RegularSpace X := hR
  let : LindelofSpace X := hL
  exact NormalSpace.of_regularSpace_lindelofSpace

/-- A regular second countable T1 space is T4 in the paper's convention. -/
theorem regular_secondCountable_t1_t4 (hR : Ch07.Regular X)
    (hS : SecondCountable t) (h1 : Ch07.T1 X) : Ch07.T4 X := by
  let : SecondCountableTopology X := hS
  exact ⟨regular_lindelof_normal hR secondCountable_lindelof, h1⟩

end D10Topology.Ch08
