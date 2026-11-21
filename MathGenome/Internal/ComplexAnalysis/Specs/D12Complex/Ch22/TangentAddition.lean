import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TorusCubicBiholomorphism
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.DivisorSumConstraint
import Mathlib.Algebra.Polynomial.Roots

/-! The diagonal case of paper.tex, D12.22.09 (4102–4110).
The intersection divisor is measured by the local orders of the actual line
equation pulled back through the upstream biholomorphism. Thus its coefficients
are analytic intersection multiplicities on the literal cubic. Coincident
summands are added, so the flex case retains multiplicity three. -/
noncomputable section
open scoped Classical

namespace Specs.D12Complex.Ch22.TangentAddition
open _root_.D12Complex _root_.D12Complex.TorusSurface
open _root_.D12Complex.CubicFiniteCharts _root_.D12Complex.TorusCubicLocalMap
open WeierstrassSeries (weierstrassP)
open WeierstrassEquations (g₂ g₃)

/-- The genuine homogeneous line, including its point at infinity. -/
def projective_line_type : Prop := ∀ m b : ℂ,
  (∀ x y : ℂ,
    (∃ v : _root_.D12Complex.ProjectivePlaneTopology.HomogeneousVector,
      _root_.D12Complex.ProjectivePlaneTopology.projection v = affinePoint x y ∧
      v.val 2 - m*v.val 1 - b*v.val 0 = 0) ↔ y-m*x-b = 0) ∧
  ¬ ∃ v : _root_.D12Complex.ProjectivePlaneTopology.HomogeneousVector,
    _root_.D12Complex.ProjectivePlaneTopology.projection v = _root_.D12Complex.CubicInfinityChart.O ∧
    v.val 2 - m*v.val 1 - b*v.val 0 = 0

def tangent_slope_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ z : ℂ, z ∉ lattice ω₁ ω₂ → deriv (weierstrassP ω₁ ω₂) z ≠ 0 →
    (12 * weierstrassP ω₁ ω₂ z ^ 2 - g₂ ω₁ ω₂) /
        (2 * deriv (weierstrassP ω₁ ω₂) z) =
      deriv (deriv (weierstrassP ω₁ ω₂)) z / deriv (weierstrassP ω₁ ω₂) z

/-- All intersections, their local orders, total degree, and the third class.
The last equivalence identifies the support using the literal finite chart.
The only cubic point outside that chart is O, and the nonvertical line does
not pass through O. No abstract elliptic-curve group law is assumed. -/
def tangent_intersections_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ z : ℂ, z ∉ lattice ω₁ ω₂ → deriv (weierstrassP ω₁ ω₂) z ≠ 0 →
  let x := weierstrassP ω₁ ω₂ z
  let y := deriv (weierstrassP ω₁ ω₂) z
  let m := (12 * x ^ 2 - g₂ ω₁ ω₂) / (2 * y)
  let f := fun w => deriv (weierstrassP ω₁ ω₂) w - m * weierstrassP ω₁ ω₂ w - (y - m*x)
  let t := projection ω₁ ω₂ z
  ∃ Z : Torus ω₁ ω₂ →₀ ℕ,
    (∀ w : ℂ, meromorphicOrderAt f w ≠ ⊤ ∧
      Z (projection ω₁ ω₂ w) = (meromorphicOrderAt f w).untop₀.toNat) ∧
    Z.sum (fun _ n => n) = 3 ∧
    Z = Finsupp.single t 2 + Finsupp.single (-(t+t)) 1 ∧
    (meromorphicOrderAt f z = if -(t+t) = t then (3 : ℤ) else (2 : ℤ)) ∧
    ∀ w : ℂ, w ∉ lattice ω₁ ω₂ →
      (deriv (weierstrassP ω₁ ω₂) w = m * weierstrassP ω₁ ω₂ w + (y-m*x) ↔
        projection ω₁ ω₂ w = t ∨ projection ω₁ ω₂ w = -(t+t))

def tangent_polynomial_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ z : ℂ, z ∉ lattice ω₁ ω₂ → deriv (weierstrassP ω₁ ω₂) z ≠ 0 →
  let x := weierstrassP ω₁ ω₂ z
  let y := deriv (weierstrassP ω₁ ω₂) z
  let m := (12 * x ^ 2 - g₂ ω₁ ω₂) / (2 * y)
  let R : Polynomial ℂ := 4 * Polynomial.X ^ 3 - Polynomial.C (g₂ ω₁ ω₂) * Polynomial.X -
    Polynomial.C (g₃ ω₁ ω₂) -
      (Polynomial.C y + Polynomial.C m * (Polynomial.X - Polynomial.C x)) ^ 2
  R = 4 * (Polynomial.X - Polynomial.C x) ^ 2 *
      (Polynomial.X - Polynomial.C (-2*x + m^2/4)) ∧
  R.roots = ({x} + {x} + {-2*x+m^2/4} : Multiset ℂ) ∧
  R.rootMultiplicity x = if -2*x+m^2/4 = x then 3 else 2

/-- The third point and its reflection are the images of -2t and 2t.
Both coordinates are asserted for every original nonvertical tangent; finiteness
of the doubled point is a conclusion, not an added hypothesis. -/
def tangent_doubling_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ z : ℂ, z ∉ lattice ω₁ ω₂ → deriv (weierstrassP ω₁ ω₂) z ≠ 0 →
  let x := weierstrassP ω₁ ω₂ z
  let y := deriv (weierstrassP ω₁ ω₂) z
  let m := (12*x^2-g₂ ω₁ ω₂)/(2*y)
  let x₂ := -2*x+m^2/4
  let y₂ := -y+m*(x-x₂)
  let t := projection ω₁ ω₂ z
  2*z ∉ lattice ω₁ ω₂ ∧
    weierstrassP ω₁ ω₂ (2*z) = x₂ ∧ deriv (weierstrassP ω₁ ω₂) (2*z) = y₂ ∧
    phi ω₁ ω₂ (-(t+t)) = affinePoint x₂ (-y₂) ∧
    phi ω₁ ω₂ (t+t) = affinePoint x₂ y₂

/-- Support in the literal projective cubic, with no affine-chart omission. -/
def tangent_projective_intersections_type : Prop :=
  ∀ ω₁ ω₂ : ℂ, ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ z : ℂ, z ∉ lattice ω₁ ω₂ → deriv (weierstrassP ω₁ ω₂) z ≠ 0 →
  let x := weierstrassP ω₁ ω₂ z
  let y := deriv (weierstrassP ω₁ ω₂) z
  let m := (12*x^2-g₂ ω₁ ω₂)/(2*y)
  let b := y-m*x
  let t := projection ω₁ ω₂ z
  ∀ u : Torus ω₁ ω₂,
    (∃ v : _root_.D12Complex.ProjectivePlaneTopology.HomogeneousVector,
      _root_.D12Complex.ProjectivePlaneTopology.projection v = phi ω₁ ω₂ u ∧
      v.val 2 - m*v.val 1 - b*v.val 0 = 0) ↔ u=t ∨ u=-(t+t)

end Specs.D12Complex.Ch22.TangentAddition
