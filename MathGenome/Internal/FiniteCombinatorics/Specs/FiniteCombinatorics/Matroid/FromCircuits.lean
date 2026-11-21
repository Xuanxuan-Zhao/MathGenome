import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.Foundation
import Mathlib.Combinatorics.Matroid.Circuit

namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u}

/-- The hereditary system containing precisely the sets avoiding designated circuits. -/
def circuitSystem (E : Set α) (hE : E.Finite) (C : Set (Set α))
    (hC : Expected.CircuitPresentation E C) : IndependenceSystem E where
  finite_ground := hE
  Indep := Expected.CircuitIndependent E C
  empty_indep := ⟨empty_subset E, fun D hD h =>
    (hC.1 D hD).2.ne_empty (subset_empty_iff.mp h)⟩
  hereditary := fun {_ _} hJ hIJ => ⟨hIJ.trans hJ.1, fun D hD hDI => hJ.2 D hD (hDI.trans hIJ)⟩
  subset_ground := fun {_} h => h.1

namespace Expected

/-- Augmentation is a conclusion, with no exchange certificate among the hypotheses. -/
def circuitAugmentation : Prop :=
  ∀ {α : Type u} (E : Set α) (hE : E.Finite) (C : Set (Set α))
    (hC : CircuitPresentation E C), Augmentation (circuitSystem E hE C hC)

/-- A finite matroid on the same ambient type, recovering both independence and circuits. -/
def matroidFromCircuits : Prop :=
  ∀ {α : Type u} (E : Set α), E.Finite → ∀ (C : Set (Set α)),
    CircuitPresentation E C → ∃ M : _root_.Matroid α,
      M.E = E ∧ M.Finite ∧
      (∀ I, M.Indep I ↔ CircuitIndependent E C I) ∧
      (∀ D, M.IsCircuit D ↔ D ∈ C)

end Expected
end FiniteCombinatorics.Matroid
