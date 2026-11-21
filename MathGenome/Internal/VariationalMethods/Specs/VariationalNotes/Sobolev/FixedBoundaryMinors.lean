import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.Minors
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Independent statement of paper.tex, Proposition `prop:fixed-trace-minors`.
The order is n+1, and existence of an increasing index enforces the upper
bound by min(m,d). Boundary equality means precisely the closure-defined
zero-boundary condition, on an arbitrary bounded open set. -/
noncomputable section
open MeasureTheory TopologicalSpace

namespace VariationalNotes.Sobolev.FixedBoundaryMinors.Expected
open Minors

/-- Equality of every component of the integral of the vector of minors.
The finite exponent satisfies p≥n+1, including equality and order one. -/
def FixedBoundaryIntegrals : Prop :=
  ∀ {d m n : ℕ} (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (p : Exponent), (n+1 : ℕ) ≤ p.real →
    ∀ (u v : W1p Ω m p), u - v ∈ zeroSubmodule Ω m p →
    ∀ a : Index m d (n+1),
      (∫ x, minor a (gradient Ω m p u x) ∂domainMeasure Ω) =
        ∫ x, minor a (gradient Ω m p v x) ∂domainMeasure Ω

end VariationalNotes.Sobolev.FixedBoundaryMinors.Expected
