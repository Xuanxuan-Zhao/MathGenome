import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic

/-! The Euclidean closed convex sets in the example following strong separation,
`paper.tex`, lines 1163–1169. The strict positive-coordinate condition is retained. -/
namespace ExpandedFA.P1.ClosedConvexNoGap

/-- The real Euclidean plane, with its usual Euclidean distance. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def point (s t : ℝ) : Plane := WithLp.toLp 2 ![s, t]

/-- The epigraph of the reciprocal on the strictly positive half-line. -/
def A : Set Plane := {x | 0 < x 0 ∧ 1 / x 0 ≤ x 1}

/-- The entire vertical axis. -/
def B : Set Plane := {x | x 0 = 0}

/-- The set of all mutual Euclidean distances (not Hausdorff distance). -/
def mutualDistances : Set ℝ := {r | ∃ c ∈ A, ∃ d ∈ B, r = dist c d}

end ExpandedFA.P1.ClosedConvexNoGap

namespace ExpandedFA.P1.ClosedConvexNoGap.Spec
open _root_.ExpandedFA.P1.ClosedConvexNoGap
open Filter

def geometry_type : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ IsClosed A ∧ IsClosed B ∧
    Convex ℝ A ∧ Convex ℝ B

def zero_distance_type : Prop :=
  sInf mutualDistances = 0 ∧
    ∀ ε : ℝ, 0 < ε → ∃ c ∈ A, ∃ d ∈ B, dist c d < ε

/-- Either one-sided bound on the full vertical line kills its coefficient. -/
def vertical_coefficient_type : Prop :=
  ∀ h : Plane →L[ℝ] ℝ,
    ((∃ M : ℝ, ∀ d ∈ B, h d ≤ M) ∨ (∃ M : ℝ, ∀ d ∈ B, M ≤ h d)) →
      h (point 0 1) = 0 ∧ ∀ d ∈ B, h d = 0

/-- A concrete family in A whose functional values tend to the common B-value. -/
def approaching_values_type : Prop :=
  ∀ h : Plane →L[ℝ] ℝ,
    ((∃ M : ℝ, ∀ d ∈ B, h d ≤ M) ∨ (∃ M : ℝ, ∀ d ∈ B, M ≤ h d)) →
      (∀ n : ℕ, point (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ∈ A) ∧
      ∀ d ∈ B,
        Tendsto (fun n : ℕ => h (point (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)))
          atTop (nhds (h d))

def no_positive_gap_type : Prop :=
  ¬ ∃ (h : Plane →L[ℝ] ℝ) (δ : ℝ), 0 < δ ∧
      ∀ c ∈ A, ∀ d ∈ B, h c + δ ≤ h d

def no_positive_gap_reverse_type : Prop :=
  ¬ ∃ (h : Plane →L[ℝ] ℝ) (δ : ℝ), 0 < δ ∧
      ∀ c ∈ A, ∀ d ∈ B, h d + δ ≤ h c

end ExpandedFA.P1.ClosedConvexNoGap.Spec
