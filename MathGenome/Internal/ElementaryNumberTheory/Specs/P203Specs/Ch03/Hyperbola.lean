import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch03.Convolution
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Real.Sqrt

/-! Chapter 3 conventions and Theorem 3.5 (`nt:C05`), paper.tex.
`Ioc 0 ⌊t⌋₊` contains exactly the positive integers at most the real bound t.
Values at positive integers are those of the shared positive-domain model;
the value of its zero extension at zero never contributes to these sums. -/
namespace P203Specs

noncomputable def summatory {R : Type*} [CommRing R]
    (f : PositiveFunction R) (t : ℝ) : R :=
  ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, zeroExtend f n

namespace Hyperbola

noncomputable def Formula {R : Type*} [CommRing R]
    (f g : PositiveFunction R) (x : ℝ) (U V : ℕ) : Prop :=
  summatory (positiveConvolution f g) x =
    (∑ u ∈ Finset.Ioc 0 U, zeroExtend f u * summatory g (x / (u : ℝ))) +
    (∑ v ∈ Finset.Ioc 0 V, zeroExtend g v * summatory f (x / (v : ℝ))) -
    summatory f (U : ℝ) * summatory g (V : ℝ)

/-- The general identity includes U=0 and V=0. -/
def Identity : Prop :=
  ∀ (R : Type*) [CommRing R] (f g : PositiveFunction R) (x : ℝ) (U V : ℕ),
    (U : ℝ) * (V : ℝ) ≤ x →
    x < ((U : ℝ) + 1) * ((V : ℝ) + 1) → Formula f g x U V

/-- The symmetric cutoff is valid for every x≥0, including x=0. -/
def SymmetricIdentity : Prop :=
  ∀ (R : Type*) [CommRing R] (f g : PositiveFunction R) (x : ℝ), 0 ≤ x →
    Formula f g x ⌊Real.sqrt x⌋₊ ⌊Real.sqrt x⌋₊

end Hyperbola
end P203Specs
