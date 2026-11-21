import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.TutteDefinition

namespace FiniteCombinatorics.Matroid.Expected
open Set
universe u v

/-- W77: the subset-rank polynomial is multiplicative for disjoint indexed sums. -/
def tutteDirectSum : Prop :=
  ∀ {α : Type u} {β : Type v} (M : _root_.Matroid α) (N : _root_.Matroid β)
    [M.Finite] [N.Finite], tutte (directSum M N) = tutte M * tutte N

/-- W77: count the actual canonical bases, among all subsets of the finite ground. -/
noncomputable def tutteOneOne : Prop := by
  classical
  exact ∀ {α : Type u} (M : _root_.Matroid α) [M.Finite],
    tutteEvaluate M 1 1 =
      ((M.ground_finite.toFinset.powerset.filter
        (fun (A : Finset α) => M.IsBase (A : Set α))).card : ℤ)

end FiniteCombinatorics.Matroid.Expected
