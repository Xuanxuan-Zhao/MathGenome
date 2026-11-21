import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.ModelCoverings
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.Surfaces
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.IndexOperationsHomotopy
import Mathlib.Topology.Homotopy.Path

/-! Independent obligations for the loop and cyclic-monodromy argument in
paper.tex:3488–3504. No classification or lifting certificate is assumed. -/
noncomputable section
open unitInterval

namespace D12Complex.Ch20.PuncturedDiskLoops

abbrev Disk (r : ℝ) := {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < r}

/-- A normalized logarithmic lift, with the indicated integral endpoint change.
This is a predicate on an arbitrary continuous loop, not an extra hypothesis
in the existence theorem. -/
def HasWinding {r : ℝ} {b : Disk r} (γ : Path b b) (k : ℤ) : Prop :=
  ∃ L : C(I, ℂ), L 0 = Complex.log (b : ℂ) ∧
    (∀ t, Complex.exp (L t) = (γ t : ℂ)) ∧
    L 1 = Complex.log (b : ℂ) + k * ModelCoverings.period

/-- Constant base modulus and linear argument increase `2πk`. -/
def circleValue {r : ℝ} (b : Disk r) (k : ℤ) (t : I) : ℂ :=
  (b : ℂ) * Complex.exp ((t : ℝ) * (k : ℂ) * ModelCoverings.period)

/-- The endpoint relation is defined by actual continuous path lifts. -/
def LiftEndpoint {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) {b : B} (γ : Path b b) (x y : p ⁻¹' {b}) : Prop :=
  ∃ Γ : Path (x : E) (y : E), ∀ t, p (Γ t) = γ t

end D12Complex.Ch20.PuncturedDiskLoops

namespace Specs.D12Complex.Ch20.PuncturedDiskLoops
open _root_.D12Complex _root_.D12Complex.Ch20
open _root_.D12Complex.Ch20.PuncturedDiskLoops
universe u

/-- Every continuous loop admits a normalized logarithmic lift and a unique
integer change. -/
def logarithmic_lift : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ (b : Disk r) (γ : Path b b), ∃! k : ℤ, HasWinding γ k

/-- Its imaginary part is an actual continuous argument, with change `2πk`. -/
def argument_lift : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ (b : Disk r) (γ : Path b b) (k : ℤ),
    HasWinding γ k → ∃ θ : C(I, ℝ), θ 0 = Complex.arg (b : ℂ) ∧
      (∀ t, (γ t : ℂ) = (‖(γ t : ℂ)‖ : ℂ) *
        Complex.exp ((θ t : ℂ) * Complex.I)) ∧
      θ 1 - θ 0 = 2 * Real.pi * k

/-- The normal form is a based loop in the same punctured disk, and its
homotopy fixes both endpoints. -/
def normal_form : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ (b : Disk r) (γ : Path b b) (k : ℤ),
    HasWinding γ k → ∃ η : Path b b,
      (∀ t, (η t : ℂ) = circleValue b k t) ∧ γ.Homotopic η

def classification : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ (b : Disk r) (γ δ : Path b b) (k l : ℤ),
    HasWinding γ k → HasWinding δ l → (γ.Homotopic δ ↔ k = l)

/-- Includes arbitrary compact parameter intervals and the degenerate interval.
The equality with a unit-interval traversal is explicit. -/
def integral_index : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ (b : Disk r) (γ : Path b b)
    (c : PiecewiseC1Path) (k : ℤ),
    (∀ t : I, (γ t : ℂ) = c (c.path.a + (c.path.b - c.path.a) * (t : ℝ))) →
    HasWinding γ k → c.index 0 = (k : ℂ)

/-- Every closed piecewise C1 path in the punctured disk admits the continuous
loop representation above and has integral index equal to its winding integer. -/
def contour_winding : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ c : PiecewiseC1Path, c.IsClosed →
    (∀ z ∈ c.trace, 0 < ‖z‖ ∧ ‖z‖ < r) →
    ∃ (b : Disk r) (γ : Path b b) (k : ℤ),
      (∀ t : I, (γ t : ℂ) = c (c.path.a + (c.path.b - c.path.a) * (t : ℝ))) ∧
      HasWinding γ k ∧ c.index 0 = (k : ℂ)

/-- A stronger purely topological covering assertion: no holomorphic regularity
of the covering projection is needed. The Riemann surface hypothesis retains
all source-space hypotheses of the paper. Bijectivity of the orbit enumeration
and `τ^m=1` express one full m-cycle, including the one-sheeted case.
The generator may be any representative with winding one. -/
def cyclic_monodromy : Prop :=
  ∀ {r : ℝ}, 0 < r → ∀ {E : Type u} [TopologicalSpace E],
    Surfaces.RiemannSurface E → ∀ (p : E → Disk r), IsCovering p →
    ∀ m : ℕ, 0 < m → (∀ b, Nat.card (p ⁻¹' {b}) = m) →
    ∀ (b : Disk r) (η : Path b b),
    HasWinding η 1 →
    ∃ τ : Equiv.Perm (p ⁻¹' {b}),
      (∀ x y, τ x = y ↔ LiftEndpoint p η x y) ∧
      τ ^ m = 1 ∧
      ∀ x, Function.Bijective (fun i : Fin m => (τ ^ i.val) x)

end Specs.D12Complex.Ch20.PuncturedDiskLoops
