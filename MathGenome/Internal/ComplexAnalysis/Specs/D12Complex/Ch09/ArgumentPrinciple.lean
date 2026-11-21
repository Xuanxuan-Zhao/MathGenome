import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch09.LogarithmicDerivative
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.ResidueCycle
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.GreenRegionIndex
import Mathlib.Algebra.BigOperators.Fin

/-! Independent statements for paper.tex:2264–2284, D12.09.02.
The default in `order` is used only at zero-index points; finite orders on
every relevant component are asserted by the argument principle itself.
The image-cycle statement retains the full interval parametrizations and
uses pushforward of integer chains, including cancellation of equal images.
-/
noncomputable section
open Set
open scoped BigOperators

namespace Specs.D12Complex.Ch09.ArgumentPrinciple.Objects
open _root_.D12Complex

def order (F : ℂ → RiemannSphere) (a : ℂ) : ℤ :=
  (scalarSignedOrder F a).getD 0

def weightedOrder (F : ℂ → RiemannSphere) (Γ : IntegralCycle) (a : ℂ) : ℂ :=
  Γ.index a * (order F a : ℂ)

end Specs.D12Complex.Ch09.ArgumentPrinciple.Objects

namespace Specs.D12Complex.Ch09.ArgumentPrinciple
open _root_.D12Complex Objects

def order_type := (ℂ → RiemannSphere) → ℂ → ℤ
def order_value : order_type := fun F a => (scalarSignedOrder F a).getD 0
def weightedOrder_type := (ℂ → RiemannSphere) → IntegralCycle → ℂ → ℂ
def weightedOrder_value : weightedOrder_type :=
  fun F Γ a => Γ.index a * ((scalarSignedOrder F a).getD 0 : ℂ)

def argument_principle_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere) (Γ : IntegralCycle),
    ScalarMeromorphicOn Ω F →
    Γ.trace ⊆ Ω →
    (∀ z ∈ Γ.trace, F z ≠ sphereFinite 0 ∧ F z ≠ sphereInfty) →
    (∀ w, w ∉ Ω → Γ.index w = 0) →
    (∀ a ∈ Ω, Γ.index a ≠ 0 →
      ¬ EqOn F (fun _ => sphereFinite 0) (connectedComponentIn Ω a)) →
    (∀ a ∈ Ω, Γ.index a ≠ 0 → ∃ m : ℤ, scalarSignedOrder F a = some m) ∧
    (Function.support (weightedOrder F Γ)).Finite ∧
    Γ.integral (Ch09.LogarithmicDerivative.Objects.coefficient F) /
      (2 * Real.pi * Complex.I : ℂ) = ∑ᶠ a, weightedOrder F Γ a

def image_index_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere) (Γ : IntegralCycle),
    ScalarMeromorphicOn Ω F → Γ.trace ⊆ Ω →
    (∀ z ∈ Γ.trace, F z ≠ sphereFinite 0 ∧ F z ≠ sphereInfty) →
    ∃ p : PiecewiseC1Path → PiecewiseC1Path,
      (∀ γ ∈ Γ.chain.support,
        (p γ).path.a = γ.path.a ∧ (p γ).path.b = γ.path.b ∧
        ∀ t, p γ t = scalarFinitePart F (γ t)) ∧
      ∃ Δ : IntegralCycle, Δ.chain = Γ.chain.mapDomain p ∧
        0 ∉ Δ.trace ∧
        Γ.integral (Ch09.LogarithmicDerivative.Objects.coefficient F) /
          (2 * Real.pi * Complex.I : ℂ) = Δ.index 0

/-- These are the source zero and pole multiplicities, rather than just the
positive and negative parts of an unrelated integer-valued function. -/
def order_classification_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℂ → RiemannSphere), ScalarMeromorphicOn Ω F →
    ∀ a ∈ Ω, ∀ m : ℤ, scalarSignedOrder F a = some m →
    (F a = sphereFinite 0 ↔ 0 < m) ∧
    (F a = sphereInfty ↔ m < 0) ∧
    (F a ≠ sphereInfty →
      Ch05.LocalZeroFactorization.HasFiniteOrder_value (scalarFinitePart F) a m.toNat) ∧
    (F a = sphereInfty → PoleOfOrderAt (scalarFinitePart F) a (-m).toNat)

/-- The region and full positive boundary are supplied with their actual
Green geometry. No Jordan separation or interior construction is assumed.
The two finite natural sums count zeros and poles with multiplicity. -/
def region_count_type : Prop :=
  ∀ (D Ω : Set ℂ) (F : ℂ → RiemannSphere) (Γ : IntegralCycle),
    GreenRegionIndex.SpecifiedGreenRegularRegion D Γ →
    ScalarMeromorphicOn Ω F → closure D ⊆ Ω →
    (∀ z ∈ frontier D, F z ≠ sphereFinite 0 ∧ F z ≠ sphereInfty) →
    (∀ a ∈ D, ∃ m : ℤ, scalarSignedOrder F a = some m) ∧
    ∃ s : Finset ℂ,
      (∀ a, a ∈ s ↔ a ∈ D ∧ (F a = sphereFinite 0 ∨ F a = sphereInfty)) ∧
      Γ.integral (Ch09.LogarithmicDerivative.Objects.coefficient F) /
        (2 * Real.pi * Complex.I : ℂ) =
        ((∑ a ∈ s, (order F a).toNat : ℕ) : ℂ) -
        ((∑ a ∈ s, (-(order F a)).toNat : ℕ) : ℂ)

end Specs.D12Complex.Ch09.ArgumentPrinciple
