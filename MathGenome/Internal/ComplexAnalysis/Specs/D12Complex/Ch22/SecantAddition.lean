import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TorusCubicBiholomorphism
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.DivisorSumConstraint
import Mathlib.Data.Finsupp.Multiset

/-! The generic secant assertion of paper.tex:4070–4094. Intersection
multiplicity is the vanishing order of the line pulled back through the
biholomorphism Φ. The complete degree-three divisor below allows the third
intersection to coincide with either of the first two. The polynomial identity
also records the algebraic intersection multiplicities in the affine line.
Scalar formulas are asserted only away from poles and with nonzero secant
denominator. The last statement expresses the identity in each meromorphic
variable, including punctured germs at exceptional arguments. -/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch22.SecantAddition
open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)

/-- Pullback of the affine line `y = m*x+b`. -/
def linePullback (ω₁ ω₂ m b t : ℂ) : ℂ :=
  deriv (weierstrassP ω₁ ω₂) t - m * weierstrassP ω₁ ω₂ t - b

/-- The secant expression, used only with its displayed domain conditions or
as a meromorphic germ. Its totalized values at indeterminate arguments carry
no asserted pointwise meaning. -/
def additionExpression (ω₁ ω₂ z w : ℂ) : ℂ :=
  -weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ w +
    ((deriv (weierstrassP ω₁ ω₂) z - deriv (weierstrassP ω₁ ω₂) w) /
      (weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ w)) ^ 2 / 4

end Specs.D12Complex.Ch22.SecantAddition

namespace Specs.D12Complex.Ch22.SecantAddition
open _root_.D12Complex
open _root_.D12Complex.TorusSurface _root_.D12Complex.CubicFiniteCharts
open _root_.D12Complex.TorusCubicLocalMap
open WeierstrassSeries (weierstrassP)
open WeierstrassEquations (g₂ g₃)

def linePullback_type := ℂ → ℂ → ℂ → ℂ → ℂ → ℂ
def linePullback_value : linePullback_type := fun ω₁ ω₂ m b t =>
  deriv (weierstrassP ω₁ ω₂) t - m * weierstrassP ω₁ ω₂ t - b

def additionExpression_type := ℂ → ℂ → ℂ → ℂ → ℂ
def additionExpression_value : additionExpression_type := fun ω₁ ω₂ z w =>
  -weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ w +
    ((deriv (weierstrassP ω₁ ω₂) z - deriv (weierstrassP ω₁ ω₂) w) /
      (weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ w)) ^ 2 / 4

/-- The complete intersection divisor of the nonvertical secant. -/
def secant_intersections_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ z w : ℂ,
    z ∉ lattice ω₁ ω₂ → w ∉ lattice ω₁ ω₂ →
    weierstrassP ω₁ ω₂ z ≠ weierstrassP ω₁ ω₂ w →
    let m := (deriv (weierstrassP ω₁ ω₂) z - deriv (weierstrassP ω₁ ω₂) w) /
      (weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ w)
    let b := deriv (weierstrassP ω₁ ω₂) z - m * weierstrassP ω₁ ω₂ z
    z + w ∉ lattice ω₁ ω₂ ∧
    (∀ a : ℂ, meromorphicOrderAt (linePullback ω₁ ω₂ m b) a ≠ ⊤ ∧
      (meromorphicOrderAt (linePullback ω₁ ω₂ m b) a).untop₀.toNat =
        (Finsupp.single (projection ω₁ ω₂ z) 1 +
          Finsupp.single (projection ω₁ ω₂ w) 1 +
          Finsupp.single (-projection ω₁ ω₂ z - projection ω₁ ω₂ w) 1 :
            Torus ω₁ ω₂ →₀ ℕ)
            (projection ω₁ ω₂ a)) ∧
    phi ω₁ ω₂ (-projection ω₁ ω₂ z - projection ω₁ ω₂ w) =
      affinePoint (weierstrassP ω₁ ω₂ (z + w))
        (-deriv (weierstrassP ω₁ ω₂) (z + w)) ∧
    deriv (weierstrassP ω₁ ω₂) (z + w) =
      -deriv (weierstrassP ω₁ ω₂) z +
        m * (weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ (z + w)) ∧
    (∀ x : ℂ,
      4 * x ^ 3 - g₂ ω₁ ω₂ * x - g₃ ω₁ ω₂ - (m * x + b) ^ 2 =
        4 * (x - weierstrassP ω₁ ω₂ z) * (x - weierstrassP ω₁ ω₂ w) *
          (x - weierstrassP ω₁ ω₂ (z + w))) ∧
    phi ω₁ ω₂ (projection ω₁ ω₂ z + projection ω₁ ω₂ w) =
      affinePoint (weierstrassP ω₁ ω₂ (z + w))
        (-deriv (weierstrassP ω₁ ω₂) z +
          m * (weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ (z + w)))

/-- The pointwise formula keeps precisely the finite, nonvertical domain. The
finiteness of the sum is a conclusion, rather than an extra hypothesis. -/
def addition_formula_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ z w : ℂ,
    z ∉ lattice ω₁ ω₂ → w ∉ lattice ω₁ ω₂ →
    weierstrassP ω₁ ω₂ z ≠ weierstrassP ω₁ ω₂ w →
    z + w ∉ lattice ω₁ ω₂ ∧
    weierstrassP ω₁ ω₂ (z + w) = additionExpression ω₁ ω₂ z w

/-- For each finite fixed argument, both sides are meromorphic in the other
argument and have equal punctured germs everywhere. The two clauses cover
both variables; they assign no scalar value to a pole or a zero denominator. -/
def meromorphic_identity_type : Prop := ∀ ω₁ ω₂ : ℂ,
  ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im → ∀ w : ℂ, w ∉ lattice ω₁ ω₂ →
    (Meromorphic (fun z => weierstrassP ω₁ ω₂ (z + w)) ∧
      Meromorphic (fun z => additionExpression ω₁ ω₂ z w) ∧
      ∀ a : ℂ, (fun z => weierstrassP ω₁ ω₂ (z + w)) =ᶠ[𝓝[≠] a]
        (fun z => additionExpression ω₁ ω₂ z w)) ∧
    (Meromorphic (fun z => weierstrassP ω₁ ω₂ (w + z)) ∧
      Meromorphic (fun z => additionExpression ω₁ ω₂ w z) ∧
      ∀ a : ℂ, (fun z => weierstrassP ω₁ ω₂ (w + z)) =ᶠ[𝓝[≠] a]
        (fun z => additionExpression ω₁ ω₂ w z))

end Specs.D12Complex.Ch22.SecantAddition
