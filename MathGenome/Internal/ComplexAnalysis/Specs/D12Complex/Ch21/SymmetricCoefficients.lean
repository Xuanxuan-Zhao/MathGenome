import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.LocalQuotientsArithmetic
import Mathlib.RingTheory.Polynomial.Vieta

/-! The symmetric-coefficient stage of paper.tex:3666–3687.

A continuation-invariant finite system has a well-defined multiset of values
at each ordinary point. `AnalyticMultiset` records only this consequence and
its local holomorphic enumerations; no labels are chosen globally and repeated
branches retain their multiplicities. The theorem below needs no stronger
path hypothesis. `CyclicPowerGrowth` records the given finite cyclic parameters,
their actual holomorphic branches and their bounds, together with coverage of
all branch values. Neither descent of the bounds nor meromorphy of a symmetric
coefficient is assumed. All source charts are centered at zero.
-/
noncomputable section
open Set Filter
open scoped Topology Classical
namespace D12Complex.SymmetricCoefficientData

/-- Centered finite coordinate, or the reciprocal coordinate at infinity. -/
def parameter (p : RiemannSphere) (u : ℂ) : RiemannSphere :=
  if p = sphereInfty then infinityParametrization u
  else sphereFinite (finiteCoordinate p + u)

/-- The coefficient of w^(d-k), including its Vieta sign. -/
def coefficient (B : RiemannSphere → Multiset ℂ) (k : ℕ) (p : RiemannSphere) : ℂ :=
  (-1) ^ k * (B p).esymm k

/-- A local enumeration is by actual holomorphic functions on a whole disk. -/
def LocallyEnumerated (d : ℕ) (B : RiemannSphere → Multiset ℂ)
    (p : RiemannSphere) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ f : Fin d → ℂ → ℂ,
    (∀ i, HolomorphicOn (Metric.ball 0 r) (f i)) ∧
    ∀ u ∈ Metric.ball 0 r,
      B (parameter p u) = Finset.univ.val.map (fun i => f i u)

/-- The finite-valued analytic multiset off a finite exceptional set. -/
def AnalyticMultiset (E : Finset RiemannSphere) (d : ℕ)
    (B : RiemannSphere → Multiset ℂ) : Prop :=
  1 ≤ d ∧ ∀ p ∉ E, (B p).card = d ∧ LocallyEnumerated d B p

/-- Finitely many local cycles, of positive lengths h, have z-c=t^h
(or z=t^(-h) at infinity). Every nearby value belongs to one of these cycles.
The parameter disk can always be reduced to radius at most one. -/
def CyclicPowerGrowth (B : RiemannSphere → Multiset ℂ) (p : RiemannSphere) : Prop :=
  ∃ (m : ℕ) (h : Fin m → ℕ) (W : Fin m → ℂ → ℂ)
    (C : Fin m → ℝ) (N : Fin m → ℕ) (δ ρ : ℝ),
    0 < δ ∧ δ ≤ 1 ∧ 0 < ρ ∧
    (∀ i, 1 ≤ h i ∧ 0 < C i ∧ HolomorphicOn (puncturedDisk 0 δ) (W i) ∧
      ∀ t ∈ puncturedDisk 0 δ, ‖W i t‖ ≤ C i * (‖t‖ ^ N i)⁻¹) ∧
    ∀ u ∈ puncturedDisk 0 ρ, ∀ v ∈ B (parameter p u),
      ∃ (i : Fin m) (t : ℂ), t ∈ puncturedDisk 0 δ ∧
        t ^ h i = u ∧ W i t = v

end D12Complex.SymmetricCoefficientData

namespace Specs.D12Complex.Ch21.SymmetricCoefficients
open _root_.D12Complex _root_.D12Complex.SymmetricCoefficientData
open Specs.D12Complex.Ch07.LocalQuotientsArithmetic.Objects

def parameter_type := RiemannSphere → ℂ → RiemannSphere
def parameter_value : parameter_type := parameter

def coefficient_type := (RiemannSphere → Multiset ℂ) → ℕ → RiemannSphere → ℂ
def coefficient_value : coefficient_type := coefficient

def LocallyEnumerated_type := ℕ → (RiemannSphere → Multiset ℂ) → RiemannSphere → Prop
def LocallyEnumerated_value : LocallyEnumerated_type := LocallyEnumerated

def AnalyticMultiset_type := Finset RiemannSphere → ℕ → (RiemannSphere → Multiset ℂ) → Prop
def AnalyticMultiset_value : AnalyticMultiset_type := AnalyticMultiset

def CyclicPowerGrowth_type := (RiemannSphere → Multiset ℂ) → RiemannSphere → Prop
def CyclicPowerGrowth_value : CyclicPowerGrowth_type := CyclicPowerGrowth

/-- Precisely the coefficients of the product of linear factors; this also
identifies the sign, multiplicities, and the monic leading coefficient. -/
def product_expansion_type : Prop :=
  ∀ (B : RiemannSphere → Multiset ℂ) (p : RiemannSphere),
    ((B p).map fun v => Polynomial.X - Polynomial.C v).prod =
      ∑ k ∈ Finset.range ((B p).card + 1),
        Polynomial.C (coefficient B k p) * Polynomial.X ^ ((B p).card - k)

/-- Canonical coefficients agree with every local enumeration and are
holomorphic in each ordinary chart, so the local coefficients glue. -/
def holomorphic_coefficients_type : Prop :=
  ∀ (d : ℕ) (B : RiemannSphere → Multiset ℂ) (p : RiemannSphere),
    LocallyEnumerated d B p → ∀ k : ℕ,
      ∃ r : ℝ, 0 < r ∧
        HolomorphicOn (Metric.ball 0 r) (fun u => coefficient B k (parameter p u))

/-- Bounds descend from the finite cyclic parameters, without assuming a
single-valued labeling of the branches. -/
def common_power_bound_type : Prop :=
  ∀ (B : RiemannSphere → Multiset ℂ) (p : RiemannSphere),
    CyclicPowerGrowth B p → ∃ (C : ℝ) (N : ℕ) (r : ℝ),
      0 < C ∧ 0 < r ∧ r ≤ 1 ∧
      ∀ u ∈ puncturedDisk 0 r, ∀ v ∈ B (parameter p u),
        ‖v‖ ≤ C * (‖u‖ ^ N)⁻¹

/-- Full conclusion of the assigned stage: holomorphic gluing, meromorphic
extension in every finite chart and at infinity, and one rational function for
each coefficient. Filled germs retain all cancellations. Values assigned to B
at exceptional points have no effect on these germs. -/
def rational_coefficients_type : Prop :=
  ∀ (E : Finset RiemannSphere) (d : ℕ) (B : RiemannSphere → Multiset ℂ),
    AnalyticMultiset E d B → (∀ p ∈ E, CyclicPowerGrowth B p) →
    ∀ k : ℕ,
      (∀ p ∉ E, ∃ r : ℝ, 0 < r ∧
        HolomorphicOn (Metric.ball 0 r) (fun u => coefficient B k (parameter p u))) ∧
      (∀ p, MeromorphicAt (fun u => coefficient B k (parameter p u)) 0) ∧
      ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
        (∀ a : ℂ,
          fill (fun z => coefficient B k (sphereFinite z)) a =
            fill (fun z => P.eval z / Q.eval z) a) ∧
        fill (fun u => coefficient B k (parameter sphereInfty u)) 0 =
          fill (fun u => P.eval u⁻¹ / Q.eval u⁻¹) 0

/-- The rational representatives take the original coefficient values at every
ordinary point, including source infinity when it is not exceptional. -/
def rational_values_type : Prop :=
  ∀ (E : Finset RiemannSphere) (d : ℕ) (B : RiemannSphere → Multiset ℂ),
    AnalyticMultiset E d B → (∀ p ∈ E, CyclicPowerGrowth B p) →
    ∀ k : ℕ, ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
      (∀ a : ℂ, sphereFinite a ∉ E →
        sphereFinite (coefficient B k (sphereFinite a)) =
          fill (fun z => P.eval z / Q.eval z) a) ∧
      (sphereInfty ∉ E → sphereFinite (coefficient B k sphereInfty) =
        fill (fun u => P.eval u⁻¹ / Q.eval u⁻¹) 0)

end Specs.D12Complex.Ch21.SymmetricCoefficients
