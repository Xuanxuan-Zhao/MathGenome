import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.TaylorSmoothness

/-! Independent statements for paper.tex:1270–1286 (d12:05-02).
The coefficients are the canonical actual Taylor coefficients. The extended
outer radius allows both finite disks and the whole plane. Every inner radius
is strictly positive and strictly smaller than the outer radius.

The first three statements hold for any upper bound on the circle. The last
statement obtains an attained circle maximum and all three estimates with
that same maximum; thus boundedness is a conclusion, not an added assumption.
The finite sum includes exactly the indices 0 through N.
-/

noncomputable section
open Set Metric
open scoped ENNReal

namespace Specs.D12Complex.Ch05.TaylorRemainderBounds
open _root_.D12Complex _root_.D12Complex.Taylor

def coefficient_bound_type : Prop :=
  ∀ (a : ℂ) (R : ℝ≥0∞) (f : ℂ → ℂ) (r M : ℝ),
    HolomorphicOn (eball a R) f → 0 < r → ENNReal.ofReal r < R →
    (∀ w ∈ sphere a r, ‖f w‖ ≤ M) → ∀ n : ℕ,
      ‖coefficients f a n‖ ≤ M / r ^ n

def derivative_bound_type : Prop :=
  ∀ (a : ℂ) (R : ℝ≥0∞) (f : ℂ → ℂ) (r M : ℝ),
    HolomorphicOn (eball a R) f → 0 < r → ENNReal.ofReal r < R →
    (∀ w ∈ sphere a r, ‖f w‖ ≤ M) → ∀ k : ℕ,
      ‖iteratedDeriv k f a‖ ≤ (k.factorial : ℝ) * M / r ^ k

def remainder_bound_type : Prop :=
  ∀ (a : ℂ) (R : ℝ≥0∞) (f : ℂ → ℂ) (r M : ℝ),
    HolomorphicOn (eball a R) f → 0 < r → ENNReal.ofReal r < R →
    (∀ w ∈ sphere a r, ‖f w‖ ≤ M) → ∀ (N : ℕ) (z : ℂ), ‖z - a‖ < r →
      ‖f z - ∑ n ∈ Finset.range (N + 1), coefficients f a n * (z - a) ^ n‖ ≤
        M * (‖z - a‖ / r) ^ (N + 1) / (1 - ‖z - a‖ / r)

def bounds_at_circle_maximum_type : Prop :=
  ∀ (a : ℂ) (R : ℝ≥0∞) (f : ℂ → ℂ) (r : ℝ),
    HolomorphicOn (eball a R) f → 0 < r → ENNReal.ofReal r < R →
    ∃ b ∈ sphere a r, (∀ w ∈ sphere a r, ‖f w‖ ≤ ‖f b‖) ∧
      (∀ n : ℕ, ‖coefficients f a n‖ ≤ ‖f b‖ / r ^ n) ∧
      (∀ k : ℕ, ‖iteratedDeriv k f a‖ ≤ (k.factorial : ℝ) * ‖f b‖ / r ^ k) ∧
      (∀ (N : ℕ) (z : ℂ), ‖z - a‖ < r →
        ‖f z - ∑ n ∈ Finset.range (N + 1), coefficients f a n * (z - a) ^ n‖ ≤
          ‖f b‖ * (‖z - a‖ / r) ^ (N + 1) / (1 - ‖z - a‖ / r))

end Specs.D12Complex.Ch05.TaylorRemainderBounds
