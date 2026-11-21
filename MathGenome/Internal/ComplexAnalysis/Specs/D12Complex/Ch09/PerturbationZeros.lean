import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch09.Rouche
import Mathlib.Analysis.Analytic.Polynomial

/-! Independent statements for the perturbation assertions of
paper.tex:2295–2300 (D12.09.04). The monic total-root count is allocated
separately. Polynomial perturbations vary all coefficients up to a fixed
degree bound, including the leading coefficient. Finite families may be
empty; the conclusions in particular apply to chosen disjoint disks.
-/
noncomputable section
open Set
open scoped BigOperators

namespace Specs.D12Complex.Ch09.PerturbationZeros
open _root_.D12Complex

def cycle_sup_min_type : Prop :=
  ∀ (Ω : Set ℂ) (Γ : IntegralCycle) (f g : ℂ → ℂ),
    HolomorphicOn Ω f → HolomorphicOn Ω g → Γ.trace ⊆ Ω →
    (∀ a, Γ.index a ≠ 0 → a ∈ Ω) →
    sSup ((fun z => ‖g z - f z‖) '' Γ.trace) <
      sInf ((fun z => ‖f z‖) '' Γ.trace) →
    (∀ a, Γ.index a ≠ 0 →
      Ch05.LocalZeroFactorization.HasFiniteOrder_value f a (analyticOrderNatAt f a) ∧
      Ch05.LocalZeroFactorization.HasFiniteOrder_value g a (analyticOrderNatAt g a)) ∧
    (Function.support (fun a => Γ.index a * (analyticOrderNatAt f a : ℂ))).Finite ∧
    (Function.support (fun a => Γ.index a * (analyticOrderNatAt g a : ℂ))).Finite ∧
    (∑ᶠ a, Γ.index a * (analyticOrderNatAt f a : ℂ)) =
      ∑ᶠ a, Γ.index a * (analyticOrderNatAt g a : ℂ)

/-- Positive perturbation threshold, including the empty counting cycle. -/
def cycle_uniform_type : Prop :=
  ∀ (Ω : Set ℂ) (Γ : IntegralCycle) (f : ℂ → ℂ),
    HolomorphicOn Ω f → Γ.trace ⊆ Ω →
    (∀ a, Γ.index a ≠ 0 → a ∈ Ω) → (∀ z ∈ Γ.trace, f z ≠ 0) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : ℂ → ℂ, HolomorphicOn Ω g →
      (∀ z ∈ Γ.trace, ‖g z - f z‖ < ε) →
      (∀ a, Γ.index a ≠ 0 →
        Ch05.LocalZeroFactorization.HasFiniteOrder_value f a (analyticOrderNatAt f a) ∧
        Ch05.LocalZeroFactorization.HasFiniteOrder_value g a (analyticOrderNatAt g a)) ∧
      (Function.support (fun a => Γ.index a * (analyticOrderNatAt f a : ℂ))).Finite ∧
      (Function.support (fun a => Γ.index a * (analyticOrderNatAt g a : ℂ))).Finite ∧
      (∑ᶠ a, Γ.index a * (analyticOrderNatAt f a : ℂ)) =
        ∑ᶠ a, Γ.index a * (analyticOrderNatAt g a : ℂ)

/-- The disk is closed in the holomorphy neighborhood. Isolation on that
closed disk also excludes boundary zeros. The finite set enumerates its
interior zeros, and the boundary of every admitted perturbation is zero-free. -/
def isolating_disk_type : Prop :=
  ∀ (Ω : Set ℂ) (c : ℂ) (r : ℝ) (f : ℂ → ℂ) (m : ℕ),
    0 < r → HolomorphicOn Ω f → Metric.closedBall c r ⊆ Ω →
    Ch05.LocalZeroFactorization.HasFiniteOrder_value f c m → f c = 0 →
    (∀ z ∈ Metric.closedBall c r, f z = 0 → z = c) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ (U : Set ℂ) (g : ℂ → ℂ),
      HolomorphicOn U g → Metric.closedBall c r ⊆ U →
      (∀ z ∈ Metric.sphere c r, ‖g z - f z‖ < ε) →
      (∀ a ∈ Metric.ball c r,
        Ch05.LocalZeroFactorization.HasFiniteOrder_value g a (analyticOrderNatAt g a)) ∧
      (∀ z ∈ Metric.sphere c r, g z ≠ 0) ∧
      ∃ t : Finset ℂ,
        (∀ a, a ∈ t ↔ a ∈ Metric.ball c r ∧ g a = 0) ∧
        (∑ a ∈ t, analyticOrderNatAt g a) = m

/-- The same algebraic multiplicity is also the analytic multiplicity used
in the contour counts. The zero polynomial is excluded for the finite order. -/
def polynomial_multiplicity_type : Prop :=
  ∀ (P : Polynomial ℂ), P ≠ 0 → ∀ a : ℂ,
    Ch05.LocalZeroFactorization.HasFiniteOrder_value (fun z => P.eval z) a
      (P.rootMultiplicity a) ∧
    analyticOrderNatAt (fun z => P.eval z) a = P.rootMultiplicity a

/-- Simultaneous stability on any finite family of isolating disks.
No disjointness is needed for this stronger form. The sums use actual
polynomial root multiplicities, as well as exact enumeration of the zeros. -/
def polynomial_disks_type : Prop :=
  ∀ (P : Polynomial ℂ) (N k : ℕ) (c : Fin k → ℂ) (r : Fin k → ℝ),
    P ≠ 0 → P.natDegree ≤ N → (∀ i, 0 < r i) →
    (∀ i, P.eval (c i) = 0) →
    (∀ i, ∀ z ∈ Metric.closedBall (c i) (r i), P.eval z = 0 → z = c i) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Polynomial ℂ, Q.natDegree ≤ N →
      (∀ j ≤ N, ‖Q.coeff j - P.coeff j‖ < δ) → ∀ i,
      (∀ z ∈ Metric.sphere (c i) (r i), Q.eval z ≠ 0) ∧
      ∃ t : Finset ℂ,
        (∀ a, a ∈ t ↔ a ∈ Metric.ball (c i) (r i) ∧ Q.eval a = 0) ∧
        (∑ a ∈ t, Q.rootMultiplicity a) = P.rootMultiplicity (c i)

/-- A simple chosen root yields exactly one simple root in its disk. -/
def simple_polynomial_disks_type : Prop :=
  ∀ (P : Polynomial ℂ) (N k : ℕ) (c : Fin k → ℂ) (r : Fin k → ℝ),
    P ≠ 0 → P.natDegree ≤ N → (∀ i, 0 < r i) →
    (∀ i, P.eval (c i) = 0) → (∀ i, P.rootMultiplicity (c i) = 1) →
    (∀ i, ∀ z ∈ Metric.closedBall (c i) (r i), P.eval z = 0 → z = c i) →
    ∃ δ : ℝ, 0 < δ ∧ ∀ Q : Polynomial ℂ, Q.natDegree ≤ N →
      (∀ j ≤ N, ‖Q.coeff j - P.coeff j‖ < δ) → ∀ i,
      ∃ a : ℂ, a ∈ Metric.ball (c i) (r i) ∧ Q.eval a = 0 ∧
        Q.rootMultiplicity a = 1 ∧
        ∀ b ∈ Metric.ball (c i) (r i), Q.eval b = 0 → b = a

end Specs.D12Complex.Ch09.PerturbationZeros
