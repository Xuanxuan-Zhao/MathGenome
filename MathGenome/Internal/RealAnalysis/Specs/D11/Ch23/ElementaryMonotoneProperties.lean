import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.ElementaryIntegral
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Independent statements of paper.tex:6195–6197.
All functions are actual finite real functions on an arbitrary, possibly empty,
domain. Nonnegative series are interpreted in the extended nonnegative reals,
so the comparison includes divergent pointwise series and infinite scalar sums.
No Stone truncation or constant unit is needed for these assertions. -/

universe u
open Filter Topology

namespace D11.Ch23.Specs

/-- Increasing pointwise convergence inside the lattice gives increasing
convergence of the elementary integrals. -/
def ElementaryMonotoneConvergence : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)), IsVectorLattice V →
    ∀ (L : V →ₗ[ℝ] ℝ), IsElementaryIntegral V L →
    ∀ (f : V) (s : ℕ → V),
      (∀ x, 0 ≤ (f : X → ℝ) x) →
      (∀ n x, 0 ≤ (s n : X → ℝ) x) →
      (∀ x, Monotone (fun n => (s n : X → ℝ) x)) →
      (∀ x, Tendsto (fun n => (s n : X → ℝ) x) atTop (𝓝 ((f : X → ℝ) x))) →
      Monotone (fun n => L (s n)) ∧
        Tendsto (fun n => L (s n)) atTop (𝓝 (L f))

/-- Equality of nonnegative pointwise series is preserved by L. In particular,
the scalar series on the right is finite because L f is real-valued. -/
def ElementarySeriesEquality : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)), IsVectorLattice V →
    ∀ (L : V →ₗ[ℝ] ℝ), IsElementaryIntegral V L →
    ∀ (f : V) (s : ℕ → V),
      (∀ x, 0 ≤ (f : X → ℝ) x) →
      (∀ n x, 0 ≤ (s n : X → ℝ) x) →
      (∀ x, ENNReal.ofReal ((f : X → ℝ) x) =
        ∑' n, ENNReal.ofReal ((s n : X → ℝ) x)) →
      ENNReal.ofReal (L f) = ∑' n, ENNReal.ofReal (L (s n))

/-- Comparison of nonnegative series, with infinite right sides allowed. -/
def ElementarySeriesComparison : Prop :=
  ∀ {X : Type u} (V : Submodule ℝ (X → ℝ)), IsVectorLattice V →
    ∀ (L : V →ₗ[ℝ] ℝ), IsElementaryIntegral V L →
    ∀ (f : V) (s : ℕ → V),
      (∀ x, 0 ≤ (f : X → ℝ) x) →
      (∀ n x, 0 ≤ (s n : X → ℝ) x) →
      (∀ x, ENNReal.ofReal ((f : X → ℝ) x) ≤
        ∑' n, ENNReal.ofReal ((s n : X → ℝ) x)) →
      ENNReal.ofReal (L f) ≤ ∑' n, ENNReal.ofReal (L (s n))

end D11.Ch23.Specs
