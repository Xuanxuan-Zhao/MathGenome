import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.HolomorphicLimits
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.ENat

/-! Independent statements for the holomorphic part of D12.16.01,
paper.tex:2771–2776. Factors may have zeros. Suprema are real suprema;
for the empty compact set the supremum is zero. On nonempty compact sets,
holomorphy guarantees that these suprema are finite.
-/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch16.HolomorphicProducts
open _root_.D12Complex

def NormalProductCondition_type := Set ℂ → (ℕ → ℂ → ℂ) → Prop

def NormalProductCondition_value : NormalProductCondition_type := fun Ω u =>
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    Summable (fun n => sSup ((fun z => ‖u n z - 1‖) '' K))

/-- Ordered products include exactly indices 0,...,n-1. The asserted limit
is the pointwise infinite product, so no unspecified limit is used later. -/
def holomorphic_product_limit_type : Prop :=
  ∀ (Ω : Set ℂ) (u : ℕ → ℂ → ℂ), IsOpen Ω →
    (∀ n, HolomorphicOn Ω (u n)) → NormalProductCondition_value Ω u →
    TendstoLocallyUniformlyOn (fun n z => ∏ k ∈ Finset.range n, u k z)
      (fun z => ∏' k, u k z) atTop Ω ∧
    HolomorphicOn Ω (fun z => ∏' k, u k z)

/-- Every shifted product also converges and is holomorphic on the full open set. -/
def holomorphic_tail_limit_type : Prop :=
  ∀ (Ω : Set ℂ) (u : ℕ → ℂ → ℂ), IsOpen Ω →
    (∀ n, HolomorphicOn Ω (u n)) → NormalProductCondition_value Ω u →
    ∀ N : ℕ,
    TendstoLocallyUniformlyOn (fun n z => ∏ k ∈ Finset.range n, u (k + N) z)
      (fun z => ∏' k, u (k + N) z) atTop Ω ∧
    HolomorphicOn Ω (fun z => ∏' k, u (k + N) z)

/-- The same index works at every point of the compact set, for every later
starting index. This applies in particular to compact neighborhoods in Ω. -/
def tail_nonvanishing_on_compact_type : Prop :=
  ∀ (Ω : Set ℂ) (u : ℕ → ℂ → ℂ), IsOpen Ω →
    (∀ n, HolomorphicOn Ω (u n)) → NormalProductCondition_value Ω u →
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ N : ℕ,
      ∀ M : ℕ, N ≤ M → ∀ z ∈ K,
        (∀ n : ℕ, M ≤ n → u n z ≠ 0) ∧ (∏' k, u (k + M) z) ≠ 0

/-- Splitting off the prefix is valid even if that prefix vanishes. -/
def product_prefix_tail_type : Prop :=
  ∀ (Ω : Set ℂ) (u : ℕ → ℂ → ℂ), IsOpen Ω →
    (∀ n, HolomorphicOn Ω (u n)) → NormalProductCondition_value Ω u →
    ∀ N : ℕ, ∀ z ∈ Ω,
      (∏' k, u k z) = (∏ k ∈ Finset.range N, u k z) * (∏' k, u (k + N) z)

/-- On the actual connected component of a, every factor and the limit have
finite local order, and all orders beyond N vanish. Thus the displayed finite
sum is the sum of all factor orders, including factors nonzero at a (order 0).
The order used is exactly the canonical local zero order of Chapter 5. -/
def product_order_on_component_type : Prop :=
  ∀ (Ω : Set ℂ) (u : ℕ → ℂ → ℂ), IsOpen Ω →
    (∀ n, HolomorphicOn Ω (u n)) → NormalProductCondition_value Ω u →
    ∀ a ∈ Ω,
      (∀ n : ℕ, ∃ z ∈ connectedComponentIn Ω a, u n z ≠ 0) →
      (∀ n : ℕ, analyticOrderAt (u n) a ≠ ⊤) ∧
      ∃ N : ℕ, (∀ n : ℕ, N ≤ n → analyticOrderAt (u n) a = 0) ∧
        analyticOrderAt (fun z => ∏' k, u k z) a =
          ∑ k ∈ Finset.range N, analyticOrderAt (u k) a ∧
        analyticOrderAt (fun z => ∏' k, u k z) a ≠ ⊤

/-- The order formula also as an infinite sum, with explicitly finite support. -/
def product_order_sum_on_component_type : Prop :=
  ∀ (Ω : Set ℂ) (u : ℕ → ℂ → ℂ), IsOpen Ω →
    (∀ n, HolomorphicOn Ω (u n)) → NormalProductCondition_value Ω u →
    ∀ a ∈ Ω,
      (∀ n : ℕ, ∃ z ∈ connectedComponentIn Ω a, u n z ≠ 0) →
      {n : ℕ | analyticOrderAt (u n) a ≠ 0}.Finite ∧
      analyticOrderAt (fun z => ∏' k, u k z) a = ∑' n, analyticOrderAt (u n) a ∧
      analyticOrderAt (fun z => ∏' k, u k z) a ≠ ⊤

/-- Exact zeros, without any connectedness or global nonzero-factor assumption. -/
def product_eq_zero_iff_type : Prop :=
  ∀ (Ω : Set ℂ) (u : ℕ → ℂ → ℂ), NormalProductCondition_value Ω u →
    ∀ z ∈ Ω, ((∏' k, u k z) = 0 ↔ ∃ n : ℕ, u n z = 0)

/-- Any identically zero factor makes the product zero on that component.
The stronger statement holds on any subset, without connectedness. -/
def product_zero_of_zero_factor_type : Prop :=
  ∀ (u : ℕ → ℂ → ℂ) (S : Set ℂ) (n : ℕ),
    (∀ z ∈ S, u n z = 0) → ∀ z ∈ S, (∏' k, u k z) = 0

end Specs.D12Complex.Ch16.HolomorphicProducts
