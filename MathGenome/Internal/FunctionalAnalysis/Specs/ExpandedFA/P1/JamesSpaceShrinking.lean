import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesSpaceBanachBasis
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DualBasisBasicity

/-! Shrinking for the real cyclic-variation James space, paper.tex:4542–4557.
The models fix the original sequence operations and exact norm. No block
estimate is assumed in the shrinking conclusion. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ExpandedFA.P1.JamesShrinkingSpec

/-- A stronger upper square estimate, valid even for nonsuccessive disjoint
supports. In particular it gives an ℓ² estimate for normalized successive blocks. -/
def DisjointBlockEstimate : Prop :=
  ∀ m : JamesBanachBasisSpec.BanachBasisModel,
    letI := m.toBanachModel.toNormedModel.group
    letI := m.toBanachModel.toNormedModel.scalars
    ∀ (n : ℕ) (u : Fin n → JamesBanachBasisSpec.Sequence),
      (∀ i j, i ≠ j → ∀ k, (u i).val k = 0 ∨ (u j).val k = 0) →
      ‖∑ i, u i‖ ^ 2 ≤ 2 * ∑ i, ‖u i‖ ^ 2

/-- The prescribed coordinate basis is shrinking, with its native continuous
coordinates identified with the actual sequence entries. All normalized,
monotone Banach basis models of the prescribed norm are covered. -/
def ShrinkingConclusion : Prop :=
  Nonempty JamesBanachBasisSpec.BanachBasisModel ∧
  ∀ m : JamesBanachBasisSpec.BanachBasisModel,
    letI := m.toBanachModel.toNormedModel.group
    letI := m.toBanachModel.toNormedModel.scalars
    ∃ b : SchauderBasis ℝ JamesBanachBasisSpec.Sequence,
      b.basis = m.e ∧ (∀ i x, b.coord i x = x.val i) ∧
      DualBasisBasicity.Spec.IsShrinking b

end ExpandedFA.P1.JamesShrinkingSpec
