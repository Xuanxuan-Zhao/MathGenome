import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.LocalConnectedness
import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.SineCurveClosure
import Mathlib.Topology.Instances.Rat

/-! Independent statements for `paper.tex`, d10:06:local-limitations.
Bool has its standard discrete two-point topology. The rational topology is
the topology induced by its inclusion in the usual real line. The sine curve
is exactly the upstream graph on (0,1] together with the whole vertical
segment, with the induced topology of the real plane. -/

open Set Topology

namespace D10Topology.Ch06.LocalCounterexamplesData

/-- The point (0,0) in the exact sine-curve subspace. -/
def sineOrigin : SineCurveData.curve :=
  ⟨(0, 0), Or.inr ⟨rfl, neg_nonpos.mpr zero_le_one, zero_le_one⟩⟩

end D10Topology.Ch06.LocalCounterexamplesData

namespace Specs.D10Topology.Ch06.LocalConnectednessCounterexamples
open _root_.D10Topology.Ch06
open ConnectednessData LocalConnectednessData ComponentsPathsData LocalCounterexamplesData

def twoPoint_locallyConnected : Prop := LocallyConnected Bool

def twoPoint_disconnected : Prop := ¬ Connected Bool

/-- A concrete neighborhood has no connected neighborhood refinement;
the candidate refinements are not assumed open. -/
def sineCurve_connectedNeighborhood_obstruction : Prop :=
  ∃ N : Set SineCurveData.curve, N ∈ 𝓝 sineOrigin ∧
    ∀ V : Set SineCurveData.curve, V ∈ 𝓝 sineOrigin → V ⊆ N → ¬ ConnectedSubset V

def sineCurve_not_locallyConnectedAt_origin : Prop :=
  ¬ LocallyConnectedAt sineOrigin

def sineCurve_connected_not_locallyConnected : Prop :=
  ConnectedSubset SineCurveData.curve ∧ ¬ LocallyConnected SineCurveData.curve

/-- Includes the empty connected subset, without asserting it is a singleton. -/
def rational_connected_subsingleton : Prop :=
  ∀ A : Set ℚ, ConnectedSubset A → A.Subsingleton

def rational_connected_singleton : Prop :=
  ∀ A : Set ℚ, A.Nonempty → ConnectedSubset A → ∃ q : ℚ, A = {q}

def rational_component_singleton : Prop :=
  ∀ q : ℚ, Component q = {q}

def rational_not_discrete : Prop := ¬ DiscreteTopology ℚ

def rational_not_locallyConnected : Prop := ¬ LocallyConnected ℚ

def real_locallyConnected : Prop := LocallyConnected ℝ

/-- The inclusion is an actual embedding for the topologies in the claims. -/
def locallyConnected_not_hereditary : Prop :=
  LocallyConnected ℝ ∧ IsEmbedding ((↑) : ℚ → ℝ) ∧ ¬ LocallyConnected ℚ

end Specs.D10Topology.Ch06.LocalConnectednessCounterexamples
