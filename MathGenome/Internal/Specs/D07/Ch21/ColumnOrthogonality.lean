import MathGenome.Internal.Specs.D07.Ch21.CharacterCompleteness
import MathGenome.Internal.Specs.D07.Ch05.ConjugacyCounting

/-!
K07.21.column_orthogonality, paper.tex:6445–6464.
The chosen family consists of actual representations, is nonrepeating, and
exhausts all irreducible types in the upstream sense. No finite-dimensional
hypothesis on its carriers is imposed. The sum uses trace characters and
complex conjugation, and applies to every pair of group elements.
-/
namespace Specs.D07.Ch21.ColumnOrthogonality

universe u r v
noncomputable section

/-- The second orthogonality relation for any complete irreducible family.
Finite dimension of every carrier is part of the conclusion. -/
def SecondOrthogonality : Prop := by
  classical
  exact ∀ (G : Type u) [Group G] [Fintype G] (I : Type r) [Fintype I]
    (V : I → Type v) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)),
    (∀ i, Representation.IsIrreducible (ρ i)) →
    (∀ i j, i ≠ j → ¬ Nonempty ((ρ i).Equiv (ρ j))) →
    RegularDecomposition.IsComplete ρ →
    (∀ i, Module.Finite ℂ (V i)) ∧
    ∀ g h : G,
      (∑ i, LinearMap.trace ℂ (V i) (ρ i g) *
        starRingEnd ℂ (LinearMap.trace ℂ (V i) (ρ i h))) =
      if IsConj g h then (Nat.card (Subgroup.centralizer {g}) : ℂ) else 0

end
end Specs.D07.Ch21.ColumnOrthogonality
