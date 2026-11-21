import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.CantorSets
import MathGenome.Internal.RealAnalysis.D11.Ch03.CantorSet
import MathGenome.Internal.RealAnalysis.D11.Ch03.FatCantor

/-! Assembly of paper.tex:1025–1030 from the canonical middle-thirds
construction and the prescribed-positive-mass nowhere-dense construction.
-/

namespace D11.Ch03.CantorSets

/-- The complete Cantor-sets proposition for the fixed middle-thirds set
and every real prescribed mass strictly between zero and one. -/
theorem cantor_sets : Specs.D11.Ch03.CantorSets.cantor_sets :=
  ⟨⟨CantorSet.C_subset, CantorSet.C_compact, CantorSet.C_perfect,
      CantorSet.C_nowhere_dense, CantorSet.C_cardinality,
      CantorSet.C_lebesgue_null⟩,
    FatCantor.exists_fatCantor⟩

end D11.Ch03.CantorSets
