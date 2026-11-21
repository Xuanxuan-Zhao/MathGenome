import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.HomotopyExtension

/-!
Theorem `thm:p202-cellular-approx` and its skeletal consequences,
paper.tex 843–896. All products have their ordinary product topology.
The source and target universe levels are independent.
-/

noncomputable section
open Set
open P202.Cellular
universe u v

namespace P202.Cellular

/-- Preservation of every nonnegative skeleton. The negative skeleton is empty. -/
def IsCellular {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CellStructure X] [CellStructure Y] (f : X → Y) : Prop :=
  ∀ n : ℕ, MapsTo f (skeleton X (n : ℤ)) (skeleton Y (n : ℤ))

/-- Cellularity on the specified subcomplex, using the ambient skeleta. -/
def IsCellularOn {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CWStructure X] [CellStructure Y] (f : X → Y) (A : Subcomplex X) : Prop :=
  ∀ n : ℕ, MapsTo f (A.carrier ∩ skeleton X (n : ℤ)) (skeleton Y (n : ℤ))

/-- Dimension at most `n`, including zero-dimensional and empty complexes. -/
def HasDimensionLE (X : Type u) [TopologicalSpace X] [CellStructure X] (n : ℕ) : Prop :=
  skeleton X (n : ℤ) = univ

/-- The parts of a cylinder fixed during a relative deformation of a homotopy.
Time is first, as in `ContinuousMap.Homotopy`. -/
def cylinderRelativeSet {X : Type u} [TopologicalSpace X] [CWStructure X]
    (A : Subcomplex X) : Set (Interval × X) :=
  {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 ∈ A.carrier}

end P202.Cellular

namespace P202Specs.Topology.CellularApproximation

/-- Relative cellular approximation, without a dimension or finiteness bound. -/
def cellularApproximation : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CWStructure X] [CWStructure Y] (A : Subcomplex X) (f : C(X, Y)),
    IsCellularOn f A →
    ∃ g : C(X, Y), IsCellular g ∧ Nonempty (f.HomotopyRel g A.carrier)

/-- A relative map from a complex of dimension at most `n` can be moved into
the target `n`-skeleton. The relative hypothesis is exactly the main theorem's. -/
def mapIntoSkeleton : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CWStructure X] [CWStructure Y] (n : ℕ) (A : Subcomplex X) (f : C(X, Y)),
    HasDimensionLE X n → IsCellularOn f A →
    ∃ g : C(X, Y), range g ⊆ skeleton Y (n : ℤ) ∧
      Nonempty (f.HomotopyRel g A.carrier)

/-- Based cellular approximation at vertices. A cellular based map must
send its source vertex to a target vertex, as explicitly required here. -/
def basedCellularApproximation : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CWStructure X] [CWStructure Y] (f : C(X, Y)) (x₀ : X) (y₀ : Y),
    x₀ ∈ skeleton X 0 → y₀ ∈ skeleton Y 0 → f x₀ = y₀ →
    ∃ g : C(X, Y), IsCellular g ∧ g x₀ = y₀ ∧
      Nonempty (f.HomotopyRel g {x₀})

def basedMapIntoSkeleton : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CWStructure X] [CWStructure Y] (n : ℕ) (f : C(X, Y)) (x₀ : X) (y₀ : Y),
    HasDimensionLE X n →
    x₀ ∈ skeleton X 0 → y₀ ∈ skeleton Y 0 → f x₀ = y₀ →
    ∃ g : C(X, Y), range g ⊆ skeleton Y (n : ℤ) ∧ g x₀ = y₀ ∧
      Nonempty (f.HomotopyRel g {x₀})

/-- A homotopy between cellular maps can be deformed into the next skeleton,
relative to the ends and a subcomplex on which it was stationary. The extra
homotopy witnesses the deformation of the given cylinder map itself. -/
def homotopyIntoSkeleton : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CWStructure X] [CWStructure Y] (n : ℕ) (A : Subcomplex X)
    (f₀ f₁ : C(X, Y)) (H : f₀.Homotopy f₁),
    HasDimensionLE X n → IsCellular f₀ → IsCellular f₁ →
    (∀ t (a : A), H (t, a.1) = f₀ a.1) →
    ∃ K : f₀.Homotopy f₁,
      (∀ t (a : A), K (t, a.1) = f₀ a.1) ∧
      range K ⊆ skeleton Y ((n + 1 : ℕ) : ℤ) ∧
      Nonempty (H.toContinuousMap.HomotopyRel K.toContinuousMap (cylinderRelativeSet A))

/-- The based specialization fixes the entire basepoint line as well as
both end maps, including when `n = 0`. -/
def basedHomotopyIntoSkeleton : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [CWStructure X] [CWStructure Y] (n : ℕ) (f₀ f₁ : C(X, Y))
    (H : f₀.Homotopy f₁) (x₀ : X) (y₀ : Y),
    HasDimensionLE X n → IsCellular f₀ → IsCellular f₁ →
    x₀ ∈ skeleton X 0 → (∀ t, H (t, x₀) = y₀) →
    ∃ K : f₀.Homotopy f₁,
      (∀ t, K (t, x₀) = y₀) ∧ range K ⊆ skeleton Y ((n + 1 : ℕ) : ℤ) ∧
      Nonempty (H.toContinuousMap.HomotopyRel K.toContinuousMap
        {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 = x₀})

end P202Specs.Topology.CellularApproximation
