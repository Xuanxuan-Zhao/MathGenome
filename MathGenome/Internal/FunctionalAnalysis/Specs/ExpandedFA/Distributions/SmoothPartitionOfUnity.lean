import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.TestFunctionLFTopology

/-! Independent specification of paper.tex:17187, `fa2:p4:partition-unity`.
The original cover has an arbitrary index type; only the resulting refinement
is required to be countable. Local finiteness is on the open domain, including
near every point of that domain, rather than at its excluded boundary. -/

open Set TopologicalSpace

universe u

namespace Specs.ExpandedFA.Distributions.SmoothPartitionOfUnity
open _root_.ExpandedFA.Distributions

/-- A countable smooth partition on Ω, subordinate to the given open cover.
The bundled real test functions are globally smooth, have compact topological
support contained in Ω, and hence are in particular smooth functions on Ω.
Subordination concerns the full topological support. -/
def partitionUnityType : Prop :=
  ∀ (d : ℕ) (Ω : Opens (Domain d)) (ι : Type u) (U : ι → Set (Domain d)),
    (∀ i, IsOpen (U i)) → (Ω : Set (Domain d)) ⊆ ⋃ i, U i →
    ∃ (κ : Type), Countable κ ∧ ∃ φ : κ → Tests ℝ Ω,
      (∀ k x, 0 ≤ φ k x) ∧
      LocallyFinite (fun k => (Subtype.val : Ω → Domain d) ⁻¹' tsupport (φ k)) ∧
      (∀ x ∈ Ω, ∑ᶠ k, φ k x = 1) ∧
      (∀ k, ∃ i, tsupport (φ k) ⊆ U i)

end Specs.ExpandedFA.Distributions.SmoothPartitionOfUnity
