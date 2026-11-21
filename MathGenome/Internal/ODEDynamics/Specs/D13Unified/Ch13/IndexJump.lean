import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.IndexOperationsHomotopy

/-! Independent statements for paper.tex, d13:13:index-jump.
The plane is ℂ with its standard orientation. All paths, integrals and path
indices below are the canonical D12 objects. No separation property is assumed.
-/
noncomputable section
open Classical
open Set Filter
open scoped Topology

namespace D13Unified.Ch13.IndexJump
open D12Complex

/-- A cyclic traversal, cut at `s`. The tail and head of the original path
occupy one unit interval each. This handles an arc crossing the original
parameter endpoints without imposing a restriction on the original basepoint. -/
def cutTraversal (γ : PiecewiseC1Path) (s t : ℝ) : ℂ :=
  if t ≤ 1 then γ (s + (γ.path.b - s) * t)
  else γ (γ.path.a + (s - γ.path.a) * (t - 1))

/-- The left side of an oriented chord inside the given open disc. The point
`c` is on the chord, and need not be the centre `o` of the disc. -/
def leftSide (o : ℂ) (r : ℝ) (c η : ℂ) : Set ℂ :=
  {p | ‖p - o‖ < r ∧ 0 < ((p - c) / η).im}

/-- The right side uses the same fixed direction as `leftSide`. -/
def rightSide (o : ℂ) (r : ℝ) (c η : ℂ) : Set ℂ :=
  {p | ‖p - o‖ < r ∧ ((p - c) / η).im < 0}

/-- Exactly one positive traversal of a straight chord, with all remaining
portions outside the open disc. A monotone coordinate allows zero speed and
pauses, but forbids backtracking or an additional traversal. The conditions are
on the actual cyclic parametrization, not merely on its set of image points.
There are no assumptions about the winding index or the curve complement. -/
structure SingleStraightArc (γ : PiecewiseC1Path) (o : ℂ) (r : ℝ) (c η : ℂ) where
  radius_pos : 0 < r
  direction_unit : ‖η‖ = 1
  centre_on_chord : ‖c - o‖ < r
  cut : ℝ
  cut_mem : cut ∈ Icc γ.path.a γ.path.b
  finish : ℝ
  finish_pos : 0 < finish
  finish_lt : finish < 2
  coordinate : ℝ → ℝ
  coordinate_continuous : ContinuousOn coordinate (Icc 0 finish)
  coordinate_monotone : MonotoneOn coordinate (Icc 0 finish)
  first_neg : coordinate 0 < 0
  last_pos : 0 < coordinate finish
  first_boundary : ‖c + (coordinate 0 : ℂ) * η - o‖ = r
  last_boundary : ‖c + (coordinate finish : ℂ) * η - o‖ = r
  arc_eq : ∀ t ∈ Icc 0 finish, cutTraversal γ cut t = c + (coordinate t : ℂ) * η
  rest_outside : ∀ t ∈ Icc finish 2, r ≤ ‖cutTraversal γ cut t - o‖

/-- Integer representative of the canonical path index; the fallback only
makes this a total function. The bridge theorem specifies all meaningful uses. -/
def integerIndex (γ : PiecewiseC1Path) (p : ℂ) : ℤ :=
  if h : ∃ n : ℤ, γ.index p = (n : ℂ) then Classical.choose h else 0

end D13Unified.Ch13.IndexJump

namespace Specs.D13Unified.Ch13.IndexJump
open _root_.D13Unified.Ch13.IndexJump _root_.D12Complex

/-- The integer used in the jump is exactly the canonical contour/path index. -/
def index_bridge_type : Prop :=
  ∀ (γ : PiecewiseC1Path), γ.IsClosed → ∀ p : ℂ, p ∉ γ.trace →
    (integerIndex γ p : ℂ) = γ.index p ∧
    γ.index p = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      γ.integral (fun z => 1 / (z - p))

def index_locally_constant_type : Prop :=
  ∀ (γ : PiecewiseC1Path), γ.IsClosed → ∀ p : ℂ, p ∉ γ.trace →
    ∀ᶠ q in 𝓝 p, q ∉ γ.trace ∧ integerIndex γ q = integerIndex γ p

/-- Full straight-edge jump, for arbitrary points of the two open half-discs.
Off-trace conclusions are included, rather than presumed from a picture. -/
def index_jump_type : Prop :=
  ∀ (γ : PiecewiseC1Path), γ.IsClosed → ∀ (o : ℂ) (r : ℝ) (c η : ℂ),
    SingleStraightArc γ o r c η →
    ∀ p ∈ leftSide o r c η, ∀ q ∈ rightSide o r c η,
      p ∉ γ.trace ∧ q ∉ γ.trace ∧ integerIndex γ p = integerIndex γ q + 1

/-- Reversing traversal negates the jump for the fixed original left/right
sides. Equivalently, exchanging those sides for direction -η restores +1. -/
def index_jump_reversal_type : Prop :=
  ∀ (γ δ : PiecewiseC1Path), γ.IsClosed →
    δ.path.a = γ.path.a → δ.path.b = γ.path.b →
    EqOn δ (fun t => γ (γ.path.a + γ.path.b - t)) (Icc δ.path.a δ.path.b) →
    ∀ (o : ℂ) (r : ℝ) (c η : ℂ), SingleStraightArc γ o r c η →
    ∀ p ∈ leftSide o r c η, ∀ q ∈ rightSide o r c η,
      p ∉ δ.trace ∧ q ∉ δ.trace ∧ integerIndex δ p = integerIndex δ q - 1

end Specs.D13Unified.Ch13.IndexJump
