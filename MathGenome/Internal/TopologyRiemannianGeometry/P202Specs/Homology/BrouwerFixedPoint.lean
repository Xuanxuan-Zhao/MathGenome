import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellStructures

/-!
Independent statements for the no-retraction and fixed-point conclusions of
paper.tex, Proposition `prop:p202-degree`, lines 1682–1705.
The parameter n ranges over all natural numbers: n = 0 is the closed interval
and its two-point boundary. Disks and spheres use the shared Euclidean objects
and their induced topologies.
-/
namespace P202Specs.BrouwerFixedPoint

/-- There is no continuous map from the closed (n+1)-disk to its boundary
whose restriction along the standard boundary inclusion is the identity. -/
def noRetraction_type : Prop :=
  ∀ n : ℕ, ¬ ∃ r : P202.Cellular.Disk (n+1) → P202.Cellular.Sphere (n+1),
    Continuous r ∧ ∀ y, r (P202.Cellular.boundaryInclusion (n+1) y) = y

/-- Every continuous self-map of the closed (n+1)-disk has a fixed point. -/
def fixedPoint_type : Prop :=
  ∀ (n : ℕ) (f : P202.Cellular.Disk (n+1) → P202.Cellular.Disk (n+1)),
    Continuous f → ∃ x, f x = x

end P202Specs.BrouwerFixedPoint
