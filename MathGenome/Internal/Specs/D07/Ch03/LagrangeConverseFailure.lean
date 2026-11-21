import MathGenome.Internal.Specs.D07.Ch02.AlternatingGroups

/-!
Independent specification of `K07.03.lagrange_converse_failure`,
paper.tex:648–656 (Example `ex:A4-no-six`).

`A₄` is the canonical alternating subgroup of permutations of `Fin 4`,
with the same sign and permutation convention as the upstream entry.
The second statement quantifies over every subgroup of this group.
-/

namespace Specs.D07.Ch03.LagrangeConverseFailure

/-- The alternating group on four letters has twelve elements. -/
def AlternatingFourOrder : Prop := by
  classical
  exact Nat.card (alternatingGroup (Fin 4)) = 12

/-- No subgroup of the alternating group on four letters has six elements. -/
def NoSubgroupOrderSix : Prop := by
  classical
  exact ∀ H : Subgroup (alternatingGroup (Fin 4)), Nat.card H ≠ 6

end Specs.D07.Ch03.LagrangeConverseFailure
