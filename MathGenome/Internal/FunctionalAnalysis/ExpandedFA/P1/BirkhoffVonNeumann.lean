import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BirkhoffVonNeumann
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24Faces
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Topology

/-!
Birkhoff–von Neumann for finite real matrices (paper.tex:5491–5520).
Mathlib's Hall-matching proof gives finite coefficients directly, as well as
the native extreme-point characterization. The bridges below identify its
objects with the entrywise manuscript definitions and its extreme points with
the shared project definition. Compactness follows from the convex hull of the
finite set of permutation matrices. All steps retain the empty-matrix case.
-/

namespace ExpandedFA.P1

open BirkhoffVonNeumannSpec

private theorem stochasticSet_eq (n : ℕ) :
    stochasticSet n = (doublyStochastic ℝ (Fin n) : Set (Matrix (Fin n) (Fin n) ℝ)) := by
  ext M
  exact mem_doublyStochastic_iff_sum.symm

private theorem permutationMatrix_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permutationMatrix σ = σ.permMatrix ℝ := by
  ext i j
  simp [permutationMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

/-- Every doubly stochastic matrix is a finite convex combination of permutations. -/
theorem birkhoff_von_neumann : BirkhoffVonNeumannSpec.Decomposition := by
  intro n M hM
  rw [stochasticSet_eq] at hM
  simpa only [permutationMatrix_eq] using exists_eq_sum_perm_of_mem_doublyStochastic hM

/-- The hull is the ordinary convex hull, with no topological closure needed. -/
theorem stochastic_eq_convexHull_permutations : BirkhoffVonNeumannSpec.ConvexHullEquality := by
  intro n
  simpa only [stochasticSet_eq, Set.range, permutationMatrix_eq] using
    (doublyStochastic_eq_convexHull_permMatrix (R := ℝ) (n := Fin n))

/-- Compactness and convexity in the finite product topology of real entries. -/
theorem stochastic_compact_convex : BirkhoffVonNeumannSpec.CompactConvex := by
  intro n
  constructor
  · rw [stochastic_eq_convexHull_permutations n]
    exact (Set.finite_range _).isCompact_convexHull ℝ
  · rw [stochasticSet_eq]
    exact convex_doublyStochastic

/-- Permutation matrices, and only these, are extreme. -/
theorem stochastic_extremePoints : BirkhoffVonNeumannSpec.ExtremePoints := by
  intro n
  change extremePoints (stochasticSet n) = _
  rw [extremePoints_eq_native, stochasticSet_eq]
  simpa only [Set.range, permutationMatrix_eq] using
    (extremePoints_doublyStochastic (R := ℝ) (n := Fin n))

end ExpandedFA.P1
