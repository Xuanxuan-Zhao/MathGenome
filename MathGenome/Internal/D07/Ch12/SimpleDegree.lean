import MathGenome.Internal.Specs.D07.Ch12.SimpleDegree
import MathGenome.Internal.D07.Ch12.PowerBasis
import MathGenome.Internal.D07.Ch12.FiniteAlgebraic

/-!
K07.12.simple_degree, paper.tex:3615–3621.
Counting the upstream power basis proves the cardinal degree formula and its
finiteness consequence. Conversely, apply finite-implies-algebraic inside the
generated field, then map its generator into L through the canonical inclusion.
The degree-one assertion uses the dimension-one characterization of the bottom
intermediate field, whose carrier is exactly the image of the chosen base map.
-/

universe u v

namespace D07.Ch12.SimpleDegree

open Specs.D07.Ch12.SimpleDegree

theorem simple_degree : DegreeEqualsMinpolyDegree.{u, v} := by
  intro K L _ _ _ α hα
  obtain ⟨_, b, _⟩ := PowerBasis.powerBasisExists K L α hα
  simpa only [Fintype.card_fin] using rank_eq_card_basis b

theorem algebraic_iff_finite_simple_extension :
    AlgebraicIffFiniteSimpleExtension.{u, v} := by
  intro K L _ _ _ α
  constructor
  · intro hα
    exact ⟨(minpoly K α).natDegree, simple_degree K L α hα⟩
  · intro hfinite
    have halg := FiniteAlgebraic.finite_extension_is_algebraic K
      (IntermediateField.adjoin K {α}) hfinite
    let a : IntermediateField.adjoin K {α} :=
      ⟨α, IntermediateField.mem_adjoin_simple_self K α⟩
    exact (halg.isAlgebraic a).algHom (IntermediateField.adjoin K {α}).val

theorem simple_degree_one_iff_mem_base : SimpleDegreeOneIffMemBase.{u, v} := by
  intro K L _ _ _ α
  exact IntermediateField.rank_adjoin_simple_eq_one_iff.trans IntermediateField.mem_bot

end D07.Ch12.SimpleDegree
