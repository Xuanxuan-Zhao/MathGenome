import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Independent statements of polynomial approximation on a compact real interval.
The domain is the interval subtype, so continuity is required only on that interval.
There is no strict endpoint inequality; singleton and empty intervals are included. -/

namespace Specs.ExpandedFA.Approximation.IntervalPolynomials

open Filter

def RealUniformLimit : Prop :=
  ∀ (a b : ℝ) (f : C(Set.Icc a b, ℝ)),
    ∃ p : ℕ → Polynomial ℝ,
      TendstoUniformly (fun n (x : Set.Icc a b) => (p n).eval (x : ℝ)) f atTop

def ComplexUniformLimit : Prop :=
  ∀ (a b : ℝ) (f : C(Set.Icc a b, ℂ)),
    ∃ p : ℕ → Polynomial ℂ,
      TendstoUniformly (fun n (x : Set.Icc a b) => (p n).eval (x : ℂ)) f atTop

/-- On a degenerate interval the constant polynomial already equals the function. -/
def RealSingleton : Prop :=
  ∀ (a : ℝ) (f : C(Set.Icc a a, ℝ)),
    ∀ x : Set.Icc a a,
      (Polynomial.C (f ⟨a, le_rfl, le_rfl⟩)).eval (x : ℝ) = f x

def ComplexSingleton : Prop :=
  ∀ (a : ℝ) (f : C(Set.Icc a a, ℂ)),
    ∀ x : Set.Icc a a,
      (Polynomial.C (f ⟨a, le_rfl, le_rfl⟩)).eval (x : ℂ) = f x

end Specs.ExpandedFA.Approximation.IntervalPolynomials
