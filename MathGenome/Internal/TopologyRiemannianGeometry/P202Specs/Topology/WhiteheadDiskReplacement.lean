import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.HigherHomotopy

/-!
The disk replacement lemma, paper.tex 924–975. All spaces carry their given
topologies; the subspace carries the induced topology. No CW or separation
assumption is made. The disk and its boundary are the upstream Euclidean models.
-/
namespace P202Specs.Topology

universe u
noncomputable section

variable {Y : Type u} [TopologicalSpace Y]

/-- The actual inclusion of a subspace. -/
def subspaceInclusion (A : Set Y) : C(A, Y) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Its pointed version at each point of the subspace. -/
def pointedSubspaceInclusion {A : Set Y} (x : A) : PointedMap A Y x x.val :=
  ⟨subspaceInclusion A, rfl⟩

/-- Exactly the component and positive homotopy-group hypotheses of disk
replacement. Bijectivity is imposed on the induced homomorphisms themselves,
so it expresses that the inclusion induces isomorphisms. -/
def IsWeakHomotopyEquivalenceInclusion (A : Set Y) : Prop :=
  Function.Bijective (componentMap (subspaceInclusion A)) ∧
    ∀ (n : ℕ) (x : A), Function.Bijective (higherInduced n (pointedSubspaceInclusion x))

namespace ExpectedDiskReplacement

/-- Full disk replacement, including the empty boundary in dimension zero. -/
def diskReplacement : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (A : Set Y),
    IsWeakHomotopyEquivalenceInclusion A → ∀ n : ℕ, RelativeDiskCondition n A

/-- Dimension zero needs only surjectivity on path components. -/
def zero : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (A : Set Y),
    Function.Surjective (componentMap (subspaceInclusion A)) → RelativeDiskCondition 0 A

/-- The path form of dimension one, with its endpoints individually fixed. -/
def pathReplacement : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (A : Set Y),
    Function.Injective (componentMap (subspaceInclusion A)) →
    (∀ x : A, Function.Surjective (pointedSubspaceInclusion x).induced) →
    ∀ (x y : A) (p : Path x.val y.val),
      ∃ q : Path x y, Nonempty (p.Homotopy (q.map continuous_subtype_val))

/-- The literal Euclidean one-disk conclusion. -/
def one : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (A : Set Y),
    IsWeakHomotopyEquivalenceInclusion A → RelativeDiskCondition 1 A

/-- Surjectivity supplies a boundary-fixed representative lift for cubes whose
whole boundary already has the chosen constant value. -/
def basedCubeLift : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (A : Set Y),
    IsWeakHomotopyEquivalenceInclusion A →
    ∀ (n : ℕ) (x : A) (a : CubeMap (n + 1) x.val),
      ∃ b : CubeMap (n + 1) x,
        Nonempty (CubeHomotopy a (cubeMap (pointedSubspaceInclusion x) b))

/-- Injectivity reflects boundary-fixed null homotopies of based cubes. -/
def basedCubeNull : Prop :=
  ∀ (Y : Type u) [TopologicalSpace Y] (A : Set Y),
    IsWeakHomotopyEquivalenceInclusion A →
    ∀ (n : ℕ) (x : A) (a : CubeMap (n + 1) x),
      Nonempty (CubeHomotopy (cubeMap (pointedSubspaceInclusion x) a) GenLoop.const) →
      Nonempty (CubeHomotopy a GenLoop.const)

end ExpectedDiskReplacement
end
end P202Specs.Topology
