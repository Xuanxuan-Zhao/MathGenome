import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! Independent statements of Hurwitz's theorem, paper.tex:2303–2308.
The zero sets are enumerated exactly, and the counts use the ordinary local
analytic multiplicity. Finite-order witnesses exclude the identically zero
germ before the natural-valued multiplicity is used. Convergence is stated
as uniform convergence on every compact subset of the original domain.
-/
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace Specs.D12Complex.Ch09.Hurwitz
open _root_.D12Complex

/-- Every admissible disk has eventually the same finite multiplicity count.
The circle may surround several zeros; in particular this covers every
isolating circle from the source. -/
def circle_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    IsDomain Ω → (∀ n, HolomorphicOn Ω (F n)) → HolomorphicOn Ω f →
    (∀ K : Set ℂ, K ⊆ Ω → IsCompact K → TendstoUniformlyOn F f atTop K) →
    ¬ EqOn f (fun _ => 0) Ω →
    ∀ (c : ℂ) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ Ω →
      (∀ z ∈ Metric.sphere c r, f z ≠ 0) →
      ∀ᶠ n in atTop,
        (∀ a ∈ Metric.ball c r,
          Ch05.LocalZeroFactorization.HasFiniteOrder_value f a (analyticOrderNatAt f a) ∧
          Ch05.LocalZeroFactorization.HasFiniteOrder_value (F n) a
            (analyticOrderNatAt (F n) a)) ∧
        ∃ s t : Finset ℂ,
          (∀ a, a ∈ s ↔ a ∈ Metric.ball c r ∧ f a = 0) ∧
          (∀ a, a ∈ t ↔ a ∈ Metric.ball c r ∧ F n a = 0) ∧
          (∑ a ∈ s, analyticOrderNatAt f a) =
            ∑ a ∈ t, analyticOrderNatAt (F n) a

/-- The identically zero alternative is retained, without a nonzero-limit
hypothesis. Values outside Ω are unrestricted. -/
def zero_free_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    IsDomain Ω → (∀ n, HolomorphicOn Ω (F n)) → HolomorphicOn Ω f →
    (∀ K : Set ℂ, K ⊆ Ω → IsCompact K → TendstoUniformlyOn F f atTop K) →
    (∀ n, ∀ z ∈ Ω, F n z ≠ 0) →
    (∀ z ∈ Ω, f z ≠ 0) ∨ EqOn f (fun _ => 0) Ω

end Specs.D12Complex.Ch09.Hurwitz
