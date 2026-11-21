import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CoveringLifting
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.VanKampen
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! The unit circle is the actual unit sphere in ℂ. The n-sphere below is the
unit sphere in Euclidean (n+1)-space, with its subspace topology. Integers are
written multiplicatively only when they are the codomain of a group homomorphism.
The fundamental groups retain the first-path-first convention of §1.1. -/
namespace P202Specs.Topology.BasicFundamentalGroups
open scoped unitInterval
universe u v
noncomputable section

/-- The covering in the source, with one turn per unit interval. -/
def circleCover : C(ℝ, Circle) :=
  ⟨fun t => Circle.exp (2 * Real.pi * t), Circle.exp.continuous.comp (by fun_prop)⟩

abbrev Sphere (n : ℕ) := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- The pointed coordinate projection of an arbitrary product. -/
def coordinate {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (x : ∀ i, X i) (i : ι) : PointedMap (∀ i, X i) (X i) x (x i) :=
  ⟨⟨fun y => y i, continuous_apply i⟩, rfl⟩

def first (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) : PointedMap (X × Y) X (x,y) x :=
  ⟨⟨Prod.fst, continuous_fst⟩, rfl⟩
def second (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) : PointedMap (X × Y) Y (x,y) y :=
  ⟨⟨Prod.snd, continuous_snd⟩, rfl⟩

namespace Expected

def circleCovering : Prop :=
  Covering circleCover ∧ ∀ t : ℝ,
    (circleCover t : ℂ) = Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

/-- In particular, the integer endpoint is independent of the representative
loop and of its lift. The equivalence asserts both injectivity and surjectivity. -/
def windingNumber : Prop :=
  ∃ e : Pi1 Circle 1 ≃* Multiplicative ℤ,
    ∀ (a : SourcePath (1 : Circle) 1) (L : C(unitInterval, ℝ)),
      (∀ t, circleCover (L t) = a t) → L 0 = 0 →
      ((e (loopClass a)).toAdd : ℝ) = L 1

/-- Arbitrary products, including the empty product. -/
def product : Prop :=
  ∀ (ι : Type u) (X : ι → Type v) [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i),
    ∃ e : Pi1 (∀ i, X i) x ≃* (∀ i, Pi1 (X i) (x i)),
      ∀ a i, e a i = (coordinate X x i).induced a

/-- Binary products also allow different universes for the two factors. -/
def binaryProduct : Prop :=
  ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y), ∃ e : Pi1 (X × Y) (x,y) ≃* (Pi1 X x × Pi1 Y y),
      ∀ a, (e a).1 = (first X Y x y).induced a ∧
        (e a).2 = (second X Y x y).induced a

def spheres : Prop :=
  ∀ n : ℕ, 2 ≤ n → PathConnectedSpace (Sphere n) ∧ SimplyConnectedSpace (Sphere n)

end Expected
end
end P202Specs.Topology.BasicFundamentalGroups
