import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.IndexOperationsHomotopy
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.DiskCauchyFormula
import Mathlib.Analysis.Convex.Basic

/-! Practical index computations, paper.tex:1004–1039.
These statements use the canonical integral-based path index. The crossing set
counts all parameter times, with two-sided derivatives away from the corners.
Explicit traversals and their existence specify the rectangle and half-disk
boundaries without any general Jordan separation assumption. -/
noncomputable section
open Set Metric

namespace Specs.D12Complex.Ch04.IndexComputations
open _root_.D12Complex

def circle_index_interior_type : Prop :=
  ∀ (c a : ℂ) (r : ℝ), 0 < r → ‖a - c‖ < r →
    (Ch04.DiskCauchyFormula.circlePath_value c r).index a = 1

def circle_index_exterior_type : Prop :=
  ∀ (c a : ℂ) (r : ℝ), 0 < r → r < ‖a - c‖ →
    (Ch04.DiskCauchyFormula.circlePath_value c r).index a = 0

/-- A useful exterior computation that requires only the indicated convex set,
not an arbitrary Jordan curve's interior or any separation theorem. -/
def closed_path_index_zero_of_convex_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (K : Set ℂ) (a : ℂ),
    γ.IsClosed → Convex ℝ K → γ.trace ⊆ K → a ∉ K → γ.index a = 0

/-- The empty-crossing case: the entire trace misses a closed ray.
No differentiability, transversality, or positive duration beyond the canonical
piecewise C1 path hypotheses is added. -/
def closed_path_index_zero_of_avoids_ray_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (a η : ℂ), γ.IsClosed → η ≠ 0 →
    (∀ t ∈ Icc γ.path.a γ.path.b,
      ¬ ∃ s : ℝ, 0 ≤ s ∧ γ t - a = (s : ℂ) * η) → γ.index a = 0

/-- The source crossing statement with its crossing set empty. Closedness and
the start-point condition handle the two endpoints, including a=b. -/
def path_index_empty_ray_crossings_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (a η : ℂ),
    γ.IsClosed → a ∉ γ.trace → ‖η‖ = 1 →
    (¬ ∃ s : ℝ, 0 ≤ s ∧ γ γ.path.a - a = (s : ℂ) * η) →
    (∀ t ∈ Ioo γ.path.a γ.path.b,
      ¬ ∃ s : ℝ, 0 < s ∧ γ t - a = (s : ℂ) * η) →
    γ.index a = ∑ t ∈ (∅ : Finset ℝ),
      (if 0 < (deriv γ t / η).im then (1 : ℂ) else -1)

/-- Every meeting with the positive open ray is counted, not merely a selected
subset of meetings. One C1 partition has all these times in its open pieces,
so ordinary real derivatives at them have their intended two-sided meaning.
The finite set may be empty, and the parameter interval may be degenerate. -/
def path_index_signed_ray_crossings_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (a η : ℂ) (S : Finset ℝ),
    γ.IsClosed → a ∉ γ.trace → ‖η‖ = 1 →
    (¬ ∃ s : ℝ, 0 ≤ s ∧ γ γ.path.a - a = (s : ℂ) * η) →
    (∀ t : ℝ, t ∈ S ↔ t ∈ Ioo γ.path.a γ.path.b ∧
      ∃ s : ℝ, 0 < s ∧ γ t - a = (s : ℂ) * η) →
    (∃ P : C1Partition γ.path, ∀ t ∈ S,
      ∃ i : Fin P.count, t ∈ Ioo (P.node i.castSucc) (P.node i.succ)) →
    (∀ t ∈ S, (deriv γ t / η).im ≠ 0) →
    γ.index a = ∑ t ∈ S, (if 0 < (deriv γ t / η).im then (1 : ℂ) else -1)

/-- The four directed sides of an explicit positive rectangle, using unit
length parameter intervals. `c` is its lower left corner in the η-coordinate. -/
def rectangle_traversal (γ : PiecewiseC1Path) (c η : ℂ) (w h : ℝ) : Prop :=
  γ.path.a = 0 ∧ γ.path.b = 4 ∧
  (∀ t ∈ Icc (0 : ℝ) 1, γ t = c + ((w * t : ℝ) : ℂ) * η) ∧
  (∀ t ∈ Icc (1 : ℝ) 2,
    γ t = c + ((w : ℂ) + ((h * (t - 1) : ℝ) : ℂ) * Complex.I) * η) ∧
  (∀ t ∈ Icc (2 : ℝ) 3,
    γ t = c + (((w * (3 - t) : ℝ) : ℂ) + (h : ℂ) * Complex.I) * η) ∧
  (∀ t ∈ Icc (3 : ℝ) 4,
    γ t = c + ((h * (4 - t) : ℝ) : ℂ) * Complex.I * η)

def rectangle_boundary_exists_type : Prop :=
  ∀ (c η : ℂ) (w h : ℝ), ‖η‖ = 1 → 0 < w → 0 < h →
    ∃ γ : PiecewiseC1Path, rectangle_traversal γ c η w h

def rectangle_index_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (c η a : ℂ) (w h : ℝ),
    ‖η‖ = 1 → 0 < w → 0 < h → rectangle_traversal γ c η w h →
    (0 < ((a - c) / η).re ∧ ((a - c) / η).re < w ∧
      0 < ((a - c) / η).im ∧ ((a - c) / η).im < h → γ.index a = 1) ∧
    (¬ (0 ≤ ((a - c) / η).re ∧ ((a - c) / η).re ≤ w ∧
      0 ≤ ((a - c) / η).im ∧ ((a - c) / η).im ≤ h) → γ.index a = 0)

/-- Diameter from left to right, then the upper semicircle from right to left.
The η-coordinate gives an arbitrary translated and rotated upper half-disk. -/
def half_disk_traversal (γ : PiecewiseC1Path) (c η : ℂ) (r : ℝ) : Prop :=
  γ.path.a = 0 ∧ γ.path.b = 2 ∧
  (∀ t ∈ Icc (0 : ℝ) 1, γ t = c + ((r * (2 * t - 1) : ℝ) : ℂ) * η) ∧
  (∀ t ∈ Icc (1 : ℝ) 2,
    γ t = c + (r : ℂ) *
      Complex.exp (((Real.pi * (t - 1) : ℝ) : ℂ) * Complex.I) * η)

def half_disk_boundary_exists_type : Prop :=
  ∀ (c η : ℂ) (r : ℝ), ‖η‖ = 1 → 0 < r →
    ∃ γ : PiecewiseC1Path, half_disk_traversal γ c η r

def half_disk_index_type : Prop :=
  ∀ (γ : PiecewiseC1Path) (c η a : ℂ) (r : ℝ),
    ‖η‖ = 1 → 0 < r → half_disk_traversal γ c η r →
    (‖a - c‖ < r ∧ 0 < ((a - c) / η).im → γ.index a = 1) ∧
    (r < ‖a - c‖ ∨ ((a - c) / η).im < 0 → γ.index a = 0)

end Specs.D12Complex.Ch04.IndexComputations
