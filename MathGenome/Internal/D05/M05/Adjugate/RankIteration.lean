import MathGenome.Internal.Specs.D05.M05.Adjugate.RankIteration
import MathGenome.Internal.D05.M05.Adjugate.RankCases

/-!
Ranks, determinant, and iteration of the adjugate (paper.tex:846–876).
The rank branches reuse the upstream minor/kernel proofs. The two algebraic
formulas are transported along the proved determinant and cofactor-adjugate
bridges. Mathlib proves them by universal polynomial identities, so neither
transport requires a nonzero determinant or an infinite-field hypothesis.
-/

namespace D05.M05.Adjugate.RankIteration

open _root_.D05.M05

theorem full_rank : Specs.D05.M05.Adjugate.RankIteration.full_rank :=
  RankCases.full_rank

theorem corank_one : Specs.D05.M05.Adjugate.RankIteration.corank_one :=
  RankCases.corank_one

theorem corank_at_least_two :
    Specs.D05.M05.Adjugate.RankIteration.corank_at_least_two := by
  intro K _ n _ A hA
  exact RankCases.corank_at_least_two (by omega) A (by omega)

theorem det_adjugate : Specs.D05.M05.Adjugate.RankIteration.det_adjugate := by
  intro K _ n _ A
  rw [Adjugate.matrix_adjugate_bridge, DetDefinition.matrix_det_bridge,
    DetDefinition.matrix_det_bridge]
  simpa only [Fintype.card_fin] using Matrix.det_adjugate A

theorem adjugate_adjugate :
    Specs.D05.M05.Adjugate.RankIteration.adjugate_adjugate := by
  intro K _ n hn A
  rw [Adjugate.matrix_adjugate_bridge, Adjugate.matrix_adjugate_bridge,
    DetDefinition.matrix_det_bridge]
  have hcard : Fintype.card (Fin n) ≠ 1 := by
    simp only [Fintype.card_fin]
    omega
  simpa only [Fintype.card_fin] using Matrix.adjugate_adjugate A hcard

end D05.M05.Adjugate.RankIteration
