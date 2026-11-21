import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.SupSpace

/-!
Independent specification of K03.16.complete (paper.tex:3823–3831).

The objects and norms are the canonical continuous maps from SupSpace.
`CompactSpace K` is compactness of the real subtype, equivalent to `IsCompact K`
by the upstream interface. No nonemptiness assumption is imposed, so the empty
compact set is included. The first two statements spell out norm Cauchyness and
norm convergence; the last two give the equivalent metric formulation.
No continuity or existence of a limit is assumed.
-/

namespace Specs.SingleVariableAnalysis.Ch16.Complete

open scoped Topology

def realSupSpaceComplete : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℝ)),
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m ≥ N, ∀ n ≥ N, ‖F n - F m‖ < ε) →
    ∃ f : C(K, ℝ),
      Filter.Tendsto (fun n => ‖F n - f‖) Filter.atTop (𝓝 0)

def complexSupSpaceComplete : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℂ)),
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m ≥ N, ∀ n ≥ N, ‖F n - F m‖ < ε) →
    ∃ f : C(K, ℂ),
      Filter.Tendsto (fun n => ‖F n - f‖) Filter.atTop (𝓝 0)

def realSupSpaceCauchySeqConverges : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℝ)),
    CauchySeq F → ∃ f : C(K, ℝ), Filter.Tendsto F Filter.atTop (𝓝 f)

def complexSupSpaceCauchySeqConverges : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (F : ℕ → C(K, ℂ)),
    CauchySeq F → ∃ f : C(K, ℂ), Filter.Tendsto F Filter.atTop (𝓝 f)

end Specs.SingleVariableAnalysis.Ch16.Complete
