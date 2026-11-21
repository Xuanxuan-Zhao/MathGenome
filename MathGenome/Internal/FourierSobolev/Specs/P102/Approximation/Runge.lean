import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.RationalInfinity

/-!
Independent statement of P1-02, Theorem 1.12 (paper.tex:510–583).
The canonical sphere is the one-point compactification of ℂ. `extension`
fills the meromorphic quotient in both finite and reciprocal coordinates,
so removable cancellations are filled and infinity is tested as a pole too.
No connectedness of V, nonemptiness of K, or restriction on the size of A
is imposed. The supremum of the empty error set in ℝ is zero.
-/
noncomputable section

namespace Specs.P102.Approximation.Runge
open _root_.D12Complex
open Specs.D12Complex.Ch07.RationalInfinity.Objects

/-- On an open set, Mathlib complex differentiability on the set is exactly
MathGenome's weak holomorphy; no continuity of the derivative is required. -/
def holomorphicOn_iff_differentiableOn_type : Prop :=
  ∀ (V : Set ℂ) (f : ℂ → ℂ), IsOpen V →
    (HolomorphicOn V f ↔ DifferentiableOn ℂ f V)

/-- Uniform rational approximation with all actual spherical poles in A.
The finiteness clause ensures that `finiteCoordinate` is used only at finite
values. Both the pointwise bound and the strict uniform bound are explicit. -/
def runge_spherical_poles_type : Prop :=
  ∀ (K V : Set ℂ) (f : ℂ → ℂ) (A : Set RiemannSphere),
    IsCompact K → IsOpen V → K ⊆ V → DifferentiableOn ℂ f V →
    A ⊆ (sphereFinite '' K)ᶜ →
    (∀ p ∈ (sphereFinite '' K)ᶜ,
      (connectedComponentIn (sphereFinite '' K)ᶜ p ∩ A).Nonempty) →
    ∀ ε : ℝ, 0 < ε → ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
      (∀ p : RiemannSphere, extension P Q p = sphereInfty → p ∈ A) ∧
      (∀ z ∈ K, extension P Q (sphereFinite z) =
        sphereFinite (finiteCoordinate (extension P Q (sphereFinite z)))) ∧
      (∀ z ∈ K, ‖f z - finiteCoordinate (extension P Q (sphereFinite z))‖ < ε) ∧
      sSup ((fun z => ‖f z - finiteCoordinate (extension P Q (sphereFinite z))‖) '' K) < ε

end Specs.P102.Approximation.Runge
