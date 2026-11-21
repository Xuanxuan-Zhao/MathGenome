import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexGeometry.Foundations
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Topology.Algebra.Module.FiniteDimension

open Set
open scoped Pointwise
noncomputable section
universe u
namespace VariationalNotes.ConvexGeometry.Specs

/-- The definition in §v01-06; it is meaningful even without closedness or nonemptiness. -/
def recession {E : Type u} [AddCommGroup E] [Module ℝ E] (C : Set E) : Set E :=
  {d | ∀ x ∈ C, ∀ t : ℝ, 0 ≤ t → x + t • d ∈ C}

def recessionType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → Set E

def lineality {E : Type u} [AddCommGroup E] [Module ℝ E] (C : Set E) : Set E :=
  recession C ∩ -recession C

def linealityType : Type (u+1) :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E], Set E → Set E

/-- Closedness and the zero-containing convex-cone convention of the manuscript. -/
def recession_closed_convex_cone : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E],
    ∀ C : Set E, C.Nonempty → IsClosed C → Convex ℝ C →
      IsClosed (recession C) ∧ Convex ℝ (recession C) ∧ IsCone (recession C)

def recession_iff_ray : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E],
    ∀ C : Set E, C.Nonempty → IsClosed C → Convex ℝ C → ∀ d : E,
      d ∈ recession C ↔ ∃ x₀ ∈ C, ∀ t : ℝ, 0 ≤ t → x₀ + t • d ∈ C

/-- Von Neumann boundedness is the intrinsic boundedness of a topological vector space.
In finite dimension it agrees with boundedness in any compatible norm. -/
def unbounded_iff_recession_nonzero : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E]
    [FiniteDimensional ℝ E],
    ∀ C : Set E, C.Nonempty → IsClosed C → Convex ℝ C →
      (¬ Bornology.IsVonNBounded ℝ C ↔ ∃ d ∈ recession C, d ≠ 0)

end VariationalNotes.ConvexGeometry.Specs
