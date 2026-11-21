import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.DivisorDegree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The lattice sum assertion of paper.tex, d12:22-03.
Multisets list all zero and pole classes with exact multiplicities. Their entries
are arbitrary plane representatives; they need not belong to a chosen cell and
repeated entries are allowed. Orders and the torus are the upstream objects. -/
noncomputable section
open Set
open scoped Classical

namespace D12Complex.DivisorSumConstraint
open TorusSurface

/-- Equality of counts in the literal quotient specifies both complete lists. -/
def DivisorLists (ω₁ ω₂ : ℂ) (F : ℂ → RiemannSphere)
    (a b : Multiset ℂ) : Prop :=
  ∀ z : ℂ,
    (a.map (projection ω₁ ω₂)).count (projection ω₁ ω₂ z) =
      (meromorphicOrderAt (scalarFinitePart F) z).untop₀.toNat ∧
    (b.map (projection ω₁ ω₂)).count (projection ω₁ ω₂ z) =
      (-(meromorphicOrderAt (scalarFinitePart F) z).untop₀).toNat

end D12Complex.DivisorSumConstraint

namespace Specs.D12Complex.Ch22.DivisorSumConstraint
open _root_.D12Complex _root_.D12Complex.TorusSurface

def DivisorLists_type := ℂ → ℂ → (ℂ → RiemannSphere) → Multiset ℂ → Multiset ℂ → Prop

def DivisorLists_value : DivisorLists_type := fun ω₁ ω₂ F a b =>
  ∀ z : ℂ,
    (a.map (projection ω₁ ω₂)).count (projection ω₁ ω₂ z) =
      (meromorphicOrderAt (scalarFinitePart F) z).untop₀.toNat ∧
    (b.map (projection ω₁ ω₂)).count (projection ω₁ ω₂ z) =
      (-(meromorphicOrderAt (scalarFinitePart F) z).untop₀).toNat

/-- For every nonconstant scalar meromorphic periodic function and every pair
of complete lists, the difference of sums is in the original period lattice. -/
def divisor_sum_constraint_type : Prop :=
  ∀ (ω₁ ω₂ : ℂ), ω₁ ≠ 0 → 0 < (ω₂ / ω₁).im →
  ∀ F : ℂ → RiemannSphere, ScalarMeromorphicOn univ F → Periodic ω₁ ω₂ F →
  (¬ ∃ c : ℂ, ∀ z, F z = sphereFinite c) →
  ∀ a b : Multiset ℂ, _root_.D12Complex.DivisorSumConstraint.DivisorLists ω₁ ω₂ F a b →
    a.sum - b.sum ∈ lattice ω₁ ω₂

end Specs.D12Complex.Ch22.DivisorSumConstraint
