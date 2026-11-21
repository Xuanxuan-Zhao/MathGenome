import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.CyclicParameters
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SingularityGrowth
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Laurent
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Polynomial.CauchyBound

/-! D12.21.05, paper.tex:3643–3664. The assertions apply to every
holomorphic parameter satisfying the original fiber equation, hence in
particular to each W in `cyclicModel`. No property at the missing center
is part of the hypotheses. The representative's value at zero is ignored.
The natural number h is the cycle length, including length one.
-/
noncomputable section
open Filter Bornology
open scoped Topology

namespace Specs.D12Complex.Ch21.AlgebraicGrowth
open _root_.D12Complex _root_.D12Complex.AlgebraicCovering

/-- Meromorphy, the quantitative pole-order alternative, and an actual
convergent Laurent series on the entire original parameter disk. -/
def finiteTail (W : ℂ → ℂ) (r : ℝ) (m : ℕ) : Prop :=
  MeromorphicAt W 0 ∧
  (RemovableSingularityAt W 0 ∨ ∃ k : ℕ, k ≤ m ∧ PoleOfOrderAt W 0 k) ∧
  ∃ a : ℤ → ℂ,
    Laurent.HasLaurentSeriesOn W 0 0 (ENNReal.ofReal r) a ∧
    ∀ n : ℤ, n < -(m : ℤ) → a n = 0

/-- Cauchy's root estimate, with the finite maximum represented by sup
in the nonnegative reals. Positive degree ensures the index set is nonempty. -/
def root_bound_type : Prop :=
  ∀ (d : ℕ) (b : ℕ → ℂ) (w : ℂ), 0 < d →
    w ^ d + ∑ j ∈ Finset.range d, b j * w ^ j = 0 →
    ‖w‖₊ ≤ 1 + (Finset.range d).sup (fun j => ‖b j‖₊)

/-- Exact growth at a finite point of leading-coefficient order k. This
stronger local form does not require c to be exceptional or P irreducible. -/
def finite_growth_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)), P ≠ 0 →
  ∀ (c : ℂ) (k : ℕ),
    Specs.D12Complex.Ch05.LocalZeroFactorization.HasFiniteOrder_value
      (fun z => P.leadingCoeff.eval z) c k →
  ∀ (h : ℕ), 0 < h → ∀ (r : ℝ), 0 < r → ∀ (W : ℂ → ℂ),
    HolomorphicOn (puncturedDisk 0 r) W →
    (∀ t ∈ puncturedDisk 0 r, (fiber P (c + t ^ h)).eval (W t) = 0) →
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝[≠] (0 : ℂ),
      ‖W t‖ ≤ C * (‖t‖ ^ (h * k))⁻¹) ∧ finiteTail W r (h * k)

/-- Every nonzero leading polynomial has such a finite order. Thus no
order factorization or growth certificate must be supplied by a cyclic parameter. -/
def finite_parameter_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)), P ≠ 0 → ∀ (c : ℂ),
  ∀ (h : ℕ), 0 < h → ∀ (r : ℝ), 0 < r → ∀ (W : ℂ → ℂ),
    HolomorphicOn (puncturedDisk 0 r) W →
    (∀ t ∈ puncturedDisk 0 r, (fiber P (c + t ^ h)).eval (W t) = 0) →
    ∃ k : ℕ,
      Specs.D12Complex.Ch05.LocalZeroFactorization.HasFiniteOrder_value
        (fun z => P.leadingCoeff.eval z) c k ∧
      (∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝[≠] (0 : ℂ),
        ‖W t‖ ≤ C * (‖t‖ ^ (h * k))⁻¹) ∧ finiteTail W r (h * k)

/-- With nonvanishing leading coefficient the parameter itself is bounded
and extends holomorphically; all its negative Laurent coefficients vanish. -/
def nonvanishing_parameter_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)) (c : ℂ), P.leadingCoeff.eval c ≠ 0 →
  ∀ (h : ℕ), 0 < h → ∀ (r : ℝ), 0 < r → ∀ (W : ℂ → ℂ),
    HolomorphicOn (puncturedDisk 0 r) W →
    (∀ t ∈ puncturedDisk 0 r, (fiber P (c + t ^ h)).eval (W t) = 0) →
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖W t‖ ≤ C) ∧
    RemovableSingularityAt W 0 ∧ finiteTail W r 0

/-- One natural exponent controls all the rational coefficients at infinity. -/
def infinity_coefficients_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)), P ≠ 0 →
    ∃ L : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ z in cobounded ℂ, ∀ j < P.natDegree,
        ‖(P.coeff j).eval z / P.leadingCoeff.eval z‖ ≤ C * ‖z‖ ^ L

/-- At infinity z=t^(-h), with the same exponent L controlling both
coefficient ratios and the pole order of W. -/
def infinity_parameter_type : Prop :=
  ∀ (P : Polynomial (Polynomial ℂ)), P ≠ 0 →
    ∃ L : ℕ,
      (∃ C : ℝ, 0 < C ∧ ∀ᶠ z in cobounded ℂ, ∀ j < P.natDegree,
        ‖(P.coeff j).eval z / P.leadingCoeff.eval z‖ ≤ C * ‖z‖ ^ L) ∧
      ∀ (h : ℕ), 0 < h → ∀ (r : ℝ), 0 < r → ∀ (W : ℂ → ℂ),
        HolomorphicOn (puncturedDisk 0 r) W →
        (∀ t ∈ puncturedDisk 0 r, (fiber P (t ^ h)⁻¹).eval (W t) = 0) →
        (∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝[≠] (0 : ℂ),
          ‖W t‖ ≤ C * (‖t‖ ^ (h * L))⁻¹) ∧ finiteTail W r (h * L)

end Specs.D12Complex.Ch21.AlgebraicGrowth
