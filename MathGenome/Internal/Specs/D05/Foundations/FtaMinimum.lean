import MathGenome.Internal.Specs.D05.Foundations.FormalPolynomials
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
Independent statements for the first paragraph of the proof of the fundamental
theorem of algebra, paper.tex:403–410. Polynomials remain formal coefficient
objects. Positive natural degree expresses nonconstancy. The source filter in
`coercivity` expresses precisely that the absolute value of the input tends to
infinity, in every complex direction.
-/

namespace D05.Specs.FtaMinimum

open Filter

/-- Reverse triangle inequality with the entire lower-degree coefficient sum.
This estimate also holds for constant and zero polynomials. -/
def lowerBound : Prop := ∀ (p : Polynomial ℂ) (z : ℂ),
  ‖p.leadingCoeff‖ * ‖z‖ ^ p.natDegree -
      ∑ j ∈ Finset.range p.natDegree, ‖p.coeff j‖ * ‖z‖ ^ j ≤ ‖p.eval z‖

/-- The lower-degree sum is at most `C * |z|^(n-1)` for `|z| ≥ 1`,
with the explicit coefficient constant used in the paper. -/
def lowerDegreeBound : Prop := ∀ (p : Polynomial ℂ) (z : ℂ),
  1 ≤ ‖z‖ →
  (∑ j ∈ Finset.range p.natDegree, ‖p.coeff j‖ * ‖z‖ ^ j) ≤
    (∑ j ∈ Finset.range p.natDegree, ‖p.coeff j‖) * ‖z‖ ^ (p.natDegree - 1)

def coercivity : Prop := ∀ (p : Polynomial ℂ), 0 < p.natDegree →
  Tendsto (fun z : ℂ => ‖p.eval z‖)
    (comap (fun z : ℂ => ‖z‖) atTop) atTop

/-- A closed disk containing zero, outside which the value is strictly
larger than the value at zero. -/
def outsideDisk : Prop := ∀ (p : Polynomial ℂ), 0 < p.natDegree →
  ∃ R : ℝ, 1 ≤ R ∧ ∀ z : ℂ, R < ‖z‖ → ‖p.eval 0‖ < ‖p.eval z‖

/-- Minimum attainment, without asserting that the minimum is zero. -/
def globalMinimum : Prop := ∀ (p : Polynomial ℂ), 0 < p.natDegree →
  ∃ z₀ : ℂ, ∀ z : ℂ, ‖p.eval z₀‖ ≤ ‖p.eval z‖

end D05.Specs.FtaMinimum
