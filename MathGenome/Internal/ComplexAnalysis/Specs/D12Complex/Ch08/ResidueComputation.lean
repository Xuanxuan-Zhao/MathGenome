import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.Residue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Independent statements for the two computation formulas in
paper.tex:1909–1924, `d12:08-01-formulas`. The coordinate-invariance
assertion belongs to the separate ResidueCoordinate goal.

All functions are total representatives of local functions. Equalities on a
punctured neighborhood impose no value at the singular point. In the first
formula `g` is the holomorphic extension of `(z-a)^m * f z`; neither an exact
pole nor a nonzero extension value is required. In the second formula the
numerator is allowed to vanish at the center.
-/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch08.ResidueComputation
open _root_.D12Complex _root_.D12Complex.Residue

/-- The residue at a pole of order at most m, including a removable point,
computed using any holomorphic extension of the multiplied function. -/
def residue_pole_formula_type : Prop :=
  ∀ (f g : ℂ → ℂ) (a : ℂ) (m : ℕ) (U : Set ℂ),
    1 ≤ m → a ∈ U → HolomorphicOn U g →
    (∀ᶠ z in 𝓝[≠] a, g z = (z - a)^m * f z) →
    residue f a = ((m - 1).factorial : ℂ)⁻¹ * iteratedDeriv (m - 1) g a

/-- The simple-denominator-zero formula for a quotient germ, including the
case p(a)=0. The equality with the quotient is required only near a. -/
def residue_simple_quotient_type : Prop :=
  ∀ (f p q : ℂ → ℂ) (a : ℂ) (U : Set ℂ),
    a ∈ U → HolomorphicOn U p → HolomorphicOn U q →
    q a = 0 → deriv q a ≠ 0 →
    (∀ᶠ z in 𝓝[≠] a, f z = p z / q z) →
    residue f a = p a / deriv q a

end Specs.D12Complex.Ch08.ResidueComputation
