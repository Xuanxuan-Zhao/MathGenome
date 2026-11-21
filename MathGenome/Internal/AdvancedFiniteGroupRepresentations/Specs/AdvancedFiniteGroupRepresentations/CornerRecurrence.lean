import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StandardTableaux
import Mathlib.Data.Fintype.BigOperators

/-! FR-B06 (Corner recurrence), source lines 679–696.
The counts are the cardinalities of the upstream standard-tableau types.
The positive-size statement covers exactly the nonempty diagrams. -/
noncomputable section
namespace Specs.AdvancedFiniteGroupRepresentations

instance cornerRemovableCellFinite {n : ℕ} (p : Partition n) : Finite (RemovableCell p) := by
  apply Finite.of_injective (fun c : RemovableCell p => (⟨c.val, c.property.1⟩ : Cell p))
  intro a b h
  exact Subtype.ext (congrArg (fun x : Cell p => x.val) h)

def cornerRecurrence_emptyType : Prop := standardTableauCount emptyPartition = 1

def cornerRecurrenceType : Prop :=
  ∀ {n : ℕ} (p : Partition n), 0 < n →
    letI := Fintype.ofFinite (RemovableCell p)
    standardTableauCount p = ∑ c : RemovableCell p, standardTableauCount (deleteCell p c)

end Specs.AdvancedFiniteGroupRepresentations
