import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
Independent specification of `paper.tex:19270–19316`, fa2:p4:besicovitch.
The plane is represented by real coordinate pairs. Length and unit directions
use the Euclidean quadratic form explicitly, not the product's maximum norm.
The product of the two standard real volumes is planar Lebesgue area.
-/
noncomputable section
open Set MeasureTheory

namespace ExpandedFA.PartIV.Besicovitch

abbrev BinarySequence := ℕ → Fin 2

/-- The coefficient of the (n+1)-st binary digit (our indices begin at zero). -/
def weight (n : ℕ) : ℝ := ((2 : ℝ) ^ (n + 1))⁻¹

/-- The ordinate in the source's binary-series construction. -/
def height (c : ℕ → ℝ) (a : BinarySequence) (x : ℝ) : ℝ :=
  ∑' n, (a n : ℝ) * weight n * (x - c n)

/-- The concrete base set, for a specified sequence of centers. -/
def baseSet (c : ℕ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ ∃ a : BinarySequence, height c a p.1 = p.2}

/-- Arbitrarily long blocks whose entries are uniformly close to any given x.
This slightly more flexible condition suffices for the paper's fiber argument. -/
def HasApproximationBlocks (c : ℕ → ℝ) : Prop :=
  ∀ x ∈ Icc (0 : ℝ) 1, ∀ ε > (0 : ℝ), ∀ r : ℕ,
    ∃ N : ℕ, ∀ k < r, |x - c (N + k)| ≤ ε

/-- Exact unit Euclidean segments, in every direction. Quantifying over both
orientations is equivalent to the source's unoriented-direction assertion,
since a segment can be parametrized starting at either endpoint. -/
def ContainsUnitSegments (K : Set (ℝ × ℝ)) : Prop :=
  ∀ v : ℝ × ℝ, v.1 ^ 2 + v.2 ^ 2 = 1 →
    ∃ p : ℝ × ℝ, ∀ t ∈ Icc (0 : ℝ) 1, p + t • v ∈ K

namespace Spec

def CompactNullUnitSegments : Prop :=
  ∃ K : Set (ℝ × ℝ), IsCompact K ∧ volume K = 0 ∧ ContainsUnitSegments K

def BaseCompact : Prop :=
  ∀ c : ℕ → ℝ, (∀ n, c n ∈ Icc (0 : ℝ) 1) → IsCompact (baseSet c)

def BaseSlopes : Prop :=
  ∀ c : ℕ → ℝ, (∀ n, c n ∈ Icc (0 : ℝ) 1) →
    ∀ m ∈ Icc (0 : ℝ) 1, ∃ b : ℝ,
      ∀ x ∈ Icc (0 : ℝ) 1, (x, m * x + b) ∈ baseSet c

def BaseFibersNull : Prop :=
  ∀ c : ℕ → ℝ, (∀ n, c n ∈ Icc (0 : ℝ) 1) → HasApproximationBlocks c →
    ∀ x : ℝ, volume {y : ℝ | (x, y) ∈ baseSet c} = 0

def ApproximationBlocksExist : Prop :=
  ∃ c : ℕ → ℝ, (∀ n, c n ∈ Icc (0 : ℝ) 1) ∧ HasApproximationBlocks c

end Spec
end ExpandedFA.PartIV.Besicovitch
