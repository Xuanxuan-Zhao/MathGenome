import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.PowerSeriesCalculus
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Independent interface for paper.tex:1242–1268, d12:05-01.
`Metric.eball a R` represents B(a,R) for an extended radius, including R = ∞.
Real partials are the real Fréchet differential evaluated on the coordinate
vectors 1 and i. The slice theorem asserts existence of the corresponding
one-dimensional derivatives; no regularity of f' is assumed.
-/
noncomputable section
open Filter
open scoped Topology NNReal ENNReal ContDiff

namespace D12Complex.Taylor

def coefficients (f : ℂ → ℂ) (a : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f a / (n.factorial : ℂ)

def partialX (f : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ f z 1

def partialY (f : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ f z Complex.I

def mixedPartial (p q : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (partialX^[p]) ((partialY^[q]) f)

end D12Complex.Taylor

namespace Specs.D12Complex.Ch05.TaylorSmoothness
open _root_.D12Complex _root_.D12Complex.Taylor
open _root_.D12Complex.PowerSeriesCalculus

def coefficients_type := (ℂ → ℂ) → ℂ → ℕ → ℂ
def coefficients_value : coefficients_type :=
  fun f a n => iteratedDeriv n f a / (n.factorial : ℂ)
def partialX_type := (ℂ → ℂ) → ℂ → ℂ
def partialX_value : partialX_type := fun f z => fderiv ℝ f z 1
def partialY_type := (ℂ → ℂ) → ℂ → ℂ
def partialY_value : partialY_type := fun f z => fderiv ℝ f z Complex.I
def mixedPartial_type := ℕ → ℕ → (ℂ → ℂ) → ℂ → ℂ
def mixedPartial_value : mixedPartial_type :=
  fun p q f => (Taylor.partialX^[p]) ((Taylor.partialY^[q]) f)

/-- Taylor representation throughout the original open disk. -/
def taylor_hasSum_type : Prop :=
  ∀ (a : ℂ) (R : ℝ≥0∞) (f : ℂ → ℂ), 0 < R →
    HolomorphicOn (Metric.eball a R) f → ∀ z ∈ Metric.eball a R,
    HasSum (fun n => coefficients f a n * (z - a)^n) (f z)

/-- The Taylor radius is at least the given disk radius; equality is not asserted. -/
def taylor_radius_lowerBound_type : Prop :=
  ∀ (a : ℂ) (R : ℝ≥0∞) (f : ℂ → ℂ), 0 < R →
    HolomorphicOn (Metric.eball a R) f → R ≤ powerSeriesRadius (coefficients f a)

/-- Normal convergence of every formal derivative, to the actual derivative.
The first and third conclusions also give absolute uniform convergence. -/
def taylor_uniform_derivatives_type : Prop :=
  ∀ (a : ℂ) (R : ℝ≥0∞) (f : ℂ → ℂ), 0 < R →
    HolomorphicOn (Metric.eball a R) f → ∀ (k : ℕ) (r : ℝ),
    0 ≤ r → ENNReal.ofReal r < R →
    Summable (fun n => ‖iteratedCoefficients (coefficients f a) k n‖ * r^n) ∧
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N,
        iteratedCoefficients (coefficients f a) k n * (z - a)^n)
      (iteratedDeriv k f) atTop (Metric.closedBall a r) ∧
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N,
        ‖iteratedCoefficients (coefficients f a) k n * (z - a)^n‖)
      (fun z => ∑' n, ‖iteratedCoefficients (coefficients f a) k n * (z - a)^n‖)
      atTop (Metric.closedBall a r)

/-- Real C∞ regularity on arbitrary open sets, including empty/disconnected ones. -/
def holomorphic_real_smooth_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f → ContDiffOn ℝ ∞ f U

/-- Actual real coordinate slice derivatives and their values. -/
def holomorphic_coordinate_derivatives_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f → ∀ z ∈ U,
    HasDerivAt (fun t : ℝ => f (z + (t : ℂ))) (deriv f z) 0 ∧
    HasDerivAt (fun t : ℝ => f (z + (t : ℂ) * Complex.I))
      (Complex.I * deriv f z) 0 ∧
    Taylor.partialX f z = deriv f z ∧ Taylor.partialY f z = Complex.I * deriv f z

/-- All mixed partials, with their continuity and existence on the same open set.
For each p,q their holomorphy also guarantees existence of the next real partials. -/
def holomorphic_mixed_partials_type : Prop :=
  ∀ (U : Set ℂ) (f : ℂ → ℂ), HolomorphicOn U f → ∀ p q : ℕ,
    (∀ z ∈ U, mixedPartial p q f z = Complex.I^q * iteratedDeriv (p+q) f z) ∧
    ContinuousOn (mixedPartial p q f) U ∧ HolomorphicOn U (mixedPartial p q f)

end Specs.D12Complex.Ch05.TaylorSmoothness
