import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24Faces
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Topology.Instances.Matrix

/-!
Independent statements for `fa2:p1:birkhoff-von-neumann`, paper.tex:5491–5520.
Matrices have real nonnegative entries and unit row and column sums. Convexity
and extreme points use real coefficients and the shared manuscript definition.
The ambient topology is the usual finite product topology. Every natural size,
including zero, is included. No decomposition certificate is assumed.
-/

namespace ExpandedFA.P1.BirkhoffVonNeumannSpec

/-- The manuscript's set of doubly stochastic matrices. -/
def stochasticSet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {M | (∀ i j, 0 ≤ M i j) ∧
    (∀ i, ∑ j, M i j = 1) ∧ (∀ j, ∑ i, M i j = 1)}

/-- One entry equal to one in each row, in the column selected by the permutation. -/
def permutationMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if σ i = j then 1 else 0

/-- An explicit finite real convex combination, indexed by all permutations. -/
def Decomposition : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ), M ∈ stochasticSet n →
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧ (∑ σ, w σ = 1) ∧
      (∑ σ, w σ • permutationMatrix σ) = M

/-- Equality with the ordinary (finite-combination) convex hull, without closure. -/
def ConvexHullEquality : Prop :=
  ∀ n : ℕ, stochasticSet n = convexHull ℝ (Set.range (@permutationMatrix n))

/-- The stochastic matrices form a compact convex set in the given matrix topology. -/
def CompactConvex : Prop :=
  ∀ n : ℕ, IsCompact (stochasticSet n) ∧ Convex ℝ (stochasticSet n)

/-- The extreme points are precisely the permutation matrices. -/
def ExtremePoints : Prop :=
  ∀ n : ℕ, C24FacesSpec.extremePoints (stochasticSet n) =
    Set.range (@permutationMatrix n)

end ExpandedFA.P1.BirkhoffVonNeumannSpec
