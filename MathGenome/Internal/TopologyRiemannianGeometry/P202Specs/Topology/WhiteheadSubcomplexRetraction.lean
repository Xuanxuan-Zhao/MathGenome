import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.HomotopyExtension
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.WhiteheadDiskReplacement

/-!
The inclusion case of Whitehead's theorem, paper.tex, lines 977–1003.
The subcomplex has its actual subspace topology. The hypothesis includes all
path components and every positive homotopy group at every basepoint. There
is no connectedness, finiteness, dimension, or local finiteness assumption.
-/

universe u
namespace P202Specs.Topology.WhiteheadSubcomplexRetraction
open P202.Cellular

/-- A retraction together with a homotopy from the identity to its composite
with the inclusion, fixing the subcomplex pointwise throughout. -/
def strongDeformationRetraction : Prop :=
  ∀ {Y : Type u} [TopologicalSpace Y] [CWStructure Y] (A : Subcomplex Y),
    IsWeakHomotopyEquivalenceInclusion A.carrier →
    ∃ (r : C(Y, A)) (H : C(Y × Interval, Y)),
      (∀ a : A, r a.val = a) ∧
      (∀ y, H (y, 0) = y) ∧
      (∀ y, H (y, 1) = (r y).val) ∧
      (∀ (a : A) t, H (a.val, t) = a.val)

end P202Specs.Topology.WhiteheadSubcomplexRetraction
