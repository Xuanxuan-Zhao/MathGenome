import MathGenome.Internal.ExtremalOptimization.Specs.P205.Ramsey.ThreeThree
import MathGenome.Internal.ExtremalOptimization.P205.Ramsey.GraphNumbers

namespace P205.Ramsey

/-- The five-cycle counterexample on five vertices. -/
def fiveCycleColor : Specs.FiveCycleColorType := Specs.fiveCycleColorValue

theorem five_cycle_color_edges : Specs.FiveCycleColorEdges := by
  unfold Specs.FiveCycleColorEdges Specs.fiveCycleColorValue
  decide

theorem five_cycle_no_triangle : Specs.FiveCycleNoTriangle := by
  unfold Specs.FiveCycleNoTriangle ColoredClique Specs.fiveCycleColorValue
  decide

theorem ramsey_three_three_upper : Specs.RamseyThreeThreeUpper := by
  have h := ramsey_number_binomial 3 3 (by decide) (by decide)
  exact h

theorem ramsey_three_three_lower : Specs.RamseyThreeThreeLower := by
  have hbad : ¬ GraphRamseyProperty 3 3 5 := by
    intro h
    rcases h (Fin 5) Finset.univ (by decide) fiveCycleColor with
      ⟨t, _, ht, hc⟩ | ⟨t, _, ht, hc⟩
    · exact (five_cycle_no_triangle t ht).1 hc
    · exact (five_cycle_no_triangle t ht).2 hc
  have hnot : ¬ Specs.ramseyNumberValue 3 3 ≤ 5 := by
    intro h
    exact hbad ((ramsey_number_threshold 3 3 5 (by decide) (by decide) (by decide)).2 h)
  exact Nat.lt_of_not_ge hnot

theorem ramsey_three_three : Specs.RamseyThreeThree := by
  have hu := ramsey_three_three_upper
  have hl := ramsey_three_three_lower
  change Specs.ramseyNumberValue 3 3 ≤ 6 at hu
  change 5 < Specs.ramseyNumberValue 3 3 at hl
  change Specs.ramseyNumberValue 3 3 = 6
  omega

end P205.Ramsey
