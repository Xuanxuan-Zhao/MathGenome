import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! The normalized planar Riemann mapping theorem, paper.tex:2486–2491
(D12.12.01). Domains are explicitly nonempty, open and connected; simple
connectivity is the topological predicate on their induced spaces. Maps use
the shared weak holomorphy and biholomorphism predicates. Uniqueness is on
Ω because total representatives can have arbitrary values outside Ω.
No boundary extension is included. -/

noncomputable section

namespace Specs.D12Complex.Ch12.RiemannMapping
open _root_.D12Complex

/-- Every pointed, nonempty, simply connected proper plane domain has exactly
one biholomorphism to the open unit disk taking its basepoint to zero with
strictly positive real derivative. -/
def normalized_riemann_mapping_type : Prop :=
  ∀ Ω : Set ℂ, IsDomain Ω → IsSimplyConnected Ω → Ω ≠ Set.univ →
    ∀ z₀ ∈ Ω, ∃ F : ℂ → ℂ,
      (IsBiholomorphism Ω (Metric.ball 0 1) F ∧ F z₀ = 0 ∧
        ∃ t : ℝ, 0 < t ∧ deriv F z₀ = (t : ℂ)) ∧
      ∀ G : ℂ → ℂ,
        (IsBiholomorphism Ω (Metric.ball 0 1) G ∧ G z₀ = 0 ∧
          ∃ t : ℝ, 0 < t ∧ deriv G z₀ = (t : ℂ)) →
        Set.EqOn G F Ω

end Specs.D12Complex.Ch12.RiemannMapping
