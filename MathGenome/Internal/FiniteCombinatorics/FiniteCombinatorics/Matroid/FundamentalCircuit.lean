import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ForwardPresentations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.FundamentalCircuit

/-! Fundamental circuits: paper.tex, W68, first paragraph.
We use the same Mathlib matroid, circuits and closure as the shared foundation.
The library's fundamental circuit applies to arbitrary independent sets,
including when the added element is a loop. -/

namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u}

/-- The unique circuit in `I + e`, together with its exchange criterion. -/
theorem fundamentalCircuit :
    ∀ (M : _root_.Matroid α) [M.Finite] (I : Set α) (e : α),
      M.Indep I → e ∈ M.closure I \ I →
        ∃ C : Set α, M.IsCircuit C ∧ C ⊆ insert e I ∧
          (∀ D : Set α, M.IsCircuit D → D ⊆ insert e I → D = C) ∧
          ∀ f ∈ I, M.Indep (insert e (I \ {f})) ↔ f ∈ C := by
  intro M _ I e hI he
  refine ⟨M.fundCircuit e I, hI.fundCircuit_isCircuit he.1 he.2,
    M.fundCircuit_subset_insert e I, ?_, ?_⟩
  · intro D hD hDI
    exact hD.eq_fundCircuit_of_subset hI hDI
  · intro f hf
    have hef : e ≠ f := by
      rintro rfl
      exact he.2 hf
    rw [insert_sdiff_singleton_comm hef]
    exact (hI.mem_fundCircuit_iff he.1 he.2).symm

end FiniteCombinatorics.Matroid
