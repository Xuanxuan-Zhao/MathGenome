import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! Independent statements for paper.tex:2311–2316 (D12.09.06).
Functions are total representatives, with injectivity and constancy required
only on the original domain. Local uniform convergence means uniform
convergence on every compact subset, as in the upstream Hurwitz interface.
-/

noncomputable section
open Set Filter

namespace Specs.D12Complex.Ch09.UnivalentLimits
open _root_.D12Complex

/-- A locally uniform holomorphic limit of injective holomorphic functions
on a domain is injective or constant there. -/
def injective_or_constant_type : Prop :=
  ∀ (Ω : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ),
    IsDomain Ω → (∀ n, HolomorphicOn Ω (F n)) → HolomorphicOn Ω f →
    (∀ K : Set ℂ, K ⊆ Ω → IsCompact K → TendstoUniformlyOn F f atTop K) →
    (∀ n, InjOn (F n) Ω) →
    InjOn f Ω ∨ ∃ c : ℂ, EqOn f (fun _ => c) Ω

/-- The sequence z/(n+1), indexing the source's z/n for n ≥ 1, shows
that the constant alternative is necessary on every positive-radius disk. -/
def scaling_example_type : Prop :=
  ∀ (a : ℂ) (r : ℝ), 0 < r →
    (∀ n : ℕ,
      HolomorphicOn (Metric.ball a r) (fun z => z / (↑(n + 1) : ℂ)) ∧
      InjOn (fun z => z / (↑(n + 1) : ℂ)) (Metric.ball a r)) ∧
    (∀ K : Set ℂ, K ⊆ Metric.ball a r → IsCompact K →
      TendstoUniformlyOn (fun (n : ℕ) z => z / (↑(n + 1) : ℂ))
        (fun _ => 0) atTop K) ∧
    (∃ c : ℂ, EqOn (fun _ : ℂ => 0) (fun _ => c) (Metric.ball a r)) ∧
    ¬ InjOn (fun _ : ℂ => 0) (Metric.ball a r)

end Specs.D12Complex.Ch09.UnivalentLimits
