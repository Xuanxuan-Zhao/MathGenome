import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Independent statements of paper.tex, Proposition `prop:v03-03-01`.
The ambient representative `J` is only constrained on `C`. Its epigraph on
`C` expresses convexity of the extended objective, with `WithTop ℝ`
excluding minus infinity. Properness is likewise relative to `C`.
-/
noncomputable section
open Set
universe u
namespace VariationalNotes.Existence.Specs

/-- A finite local minimum relative to a convex feasible set is global.
No closedness, completeness, or existence of a minimizer is assumed. -/
def localMin_isMin : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (C : Set E) (J : E → WithTop ℝ), Convex ℝ C →
    (∃ z ∈ C, J z < ⊤) →
    Convex ℝ {p : E × ℝ | p.1 ∈ C ∧ J p.1 ≤ (p.2 : WithTop ℝ)} →
    ∀ x ∈ C, J x < ⊤ → IsLocalMinOn J C x → IsMinOn J C x

/-- Strict convexity is required only between distinct finite-value points.
Properness ensures that every global minimizer has finite value. -/
def minimizer_unique : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E]
    (C : Set E) (J : E → WithTop ℝ), Convex ℝ C →
    (∃ z ∈ C, J z < ⊤) →
    Convex ℝ {p : E × ℝ | p.1 ∈ C ∧ J p.1 ≤ (p.2 : WithTop ℝ)} →
    (∀ x ∈ C, ∀ y ∈ C, ∀ r s : ℝ, J x = (r : WithTop ℝ) →
      J y = (s : WithTop ℝ) → x ≠ y →
      ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
        J (a • x + b • y) < ((a * r + b * s : ℝ) : WithTop ℝ)) →
    ∀ x ∈ C, ∀ y ∈ C, IsMinOn J C x → IsMinOn J C y → x = y

/-- The first-order variational inequality for an objective agreeing on `C`
with a differentiable convex real function on an open convex neighborhood.
The finite-dimensional inner product space formulation includes all Euclidean
spaces, including dimension zero. -/
def isMin_iff_gradient_nonneg : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (C U : Set E) (J : E → WithTop ℝ) (g : E → ℝ),
    Convex ℝ C → IsOpen U → Convex ℝ U → C ⊆ U → ConvexOn ℝ U g →
    (∀ z ∈ U, DifferentiableAt ℝ g z) →
    (∀ z ∈ C, J z = (g z : WithTop ℝ)) →
    ∀ x ∈ C, IsMinOn J C x ↔
      ∀ y ∈ C, 0 ≤ inner ℝ (gradient g x) (y - x)

end VariationalNotes.Existence.Specs
