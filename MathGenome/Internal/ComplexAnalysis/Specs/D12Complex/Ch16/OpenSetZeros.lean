import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.LocallyFinsupp

/-! D12.16.05, paper.tex:2808–2819. Effective divisors are natural-valued
functions supported in the stated open set, locally finite there, using
Mathlib's `Function.locallyFinsuppWithin`. No connectedness or nonemptiness
of the open set, and no enumeration or convergence certificate, is assumed. -/
noncomputable section
open Set

namespace Specs.D12Complex.Ch16.OpenSetZeros
open _root_.D12Complex

def Realizes_type := (Ω : Set ℂ) → Function.locallyFinsuppWithin Ω ℕ → (ℂ → ℂ) → Prop
def Realizes_value : Realizes_type := fun Ω d f =>
  HolomorphicOn Ω f ∧
  (∀ z ∈ Ω, analyticOrderAt f z = (d z : ℕ∞)) ∧
  (∀ z ∈ Ω, f z = 0 ↔ d z ≠ 0) ∧
  ∀ a ∈ Ω, ∃ z ∈ connectedComponentIn Ω a, f z ≠ 0

/-- The entire prescribed divisor is realized, with finite orders at every point
and nontriviality on every component. Includes empty and disconnected sets. -/
def open_set_prescribed_zeros_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → ∀ d : Function.locallyFinsuppWithin Ω ℕ,
    ∃ f : ℂ → ℂ, Realizes_value Ω d f

end Specs.D12Complex.Ch16.OpenSetZeros
