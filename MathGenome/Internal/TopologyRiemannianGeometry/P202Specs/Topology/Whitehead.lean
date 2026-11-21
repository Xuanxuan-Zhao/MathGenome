import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellularApproximation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.WhiteheadSubcomplexRetraction

/-! Independent specification of `thm:p202-whitehead`, paper.tex 977–1023.
The map is arbitrary, the spaces may be disconnected or empty, and the
positive homotopy-group hypothesis is imposed at every source basepoint. -/

universe u v
namespace P202Specs.Topology

/-- Bijectivity on components and on the actual induced positive homotopy
groups. The natural number `n` indexes the positive dimension `n + 1`. -/
def IsWeakHomotopyEquivalence {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) : Prop :=
  Function.Bijective (componentMap f) ∧
    ∀ (n : ℕ) (x : X), Function.Bijective
      (higherInduced n (⟨f, rfl⟩ : PointedMap X Y x (f x)))

/-- The given map, rather than just the two spaces, has a homotopy inverse. -/
def HasHomotopyInverse {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) : Prop :=
  ∃ g : C(Y, X),
    (g.comp f).Homotopic (ContinuousMap.id X) ∧
    (f.comp g).Homotopic (ContinuousMap.id Y)

namespace Whitehead

/-- Whitehead's theorem with its original hypotheses and full conclusion.
There is no cellularity assumption on `f`. -/
def whitehead : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [P202.Cellular.CWStructure X] [P202.Cellular.CWStructure Y] (f : C(X, Y)),
    IsWeakHomotopyEquivalence f → HasHomotopyInverse f

end Whitehead
end P202Specs.Topology
