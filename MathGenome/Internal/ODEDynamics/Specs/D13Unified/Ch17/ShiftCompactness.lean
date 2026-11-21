import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ShiftSpaces
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
Full statements of paper.tex, Lemma `d13:17:shift-compactness`.
The spaces and their native product topologies are the canonical upstream
objects. The upstream `metricPlus_existsStatement` and `metric_existsStatement`
identify these topologies with those of the exact distances in the paper.
No isolated points is expressed directly: every neighborhood of every point
contains a different point. Total disconnectedness is stated both as the
standard class and as the source's assertion about all connected subsets.
-/
namespace Specs.D13Unified.Ch17.ShiftCompactness

open Set Topology
open Specs.D13Unified.Ch17.ShiftSpaces

def compactPlusStatement : Prop := CompactSpace OneSided
def compactStatement : Prop := CompactSpace TwoSided

def noIsolatedPointsPlusStatement : Prop :=
  ∀ s : OneSided, ∀ U ∈ 𝓝 s, ∃ t ∈ U, t ≠ s

def noIsolatedPointsStatement : Prop :=
  ∀ s : TwoSided, ∀ U ∈ 𝓝 s, ∃ t ∈ U, t ≠ s

def totallyDisconnectedPlusStatement : Prop := TotallyDisconnectedSpace OneSided
def totallyDisconnectedStatement : Prop := TotallyDisconnectedSpace TwoSided

def connected_subsingletonPlusStatement : Prop :=
  ∀ C : Set OneSided, IsConnected C → C.Subsingleton

def connected_subsingletonStatement : Prop :=
  ∀ C : Set TwoSided, IsConnected C → C.Subsingleton

end Specs.D13Unified.Ch17.ShiftCompactness
