import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.GermSpaceCountability
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.GermTopology
import Mathlib.Analysis.Real.Cardinality

/-! Entire constant functions give uncountably many pairwise disjoint,
nonempty open sections in the canonical germ topology. -/

noncomputable section

namespace D12Complex.GermSpaceCountability

open GermTopology Set

/-- An entire constant function, viewed as a function element. -/
private def constantElement (c : ℂ) : FunctionElement where
  domain := Set.univ
  isDomain := ⟨Set.univ_nonempty, isOpen_univ, isPreconnected_univ⟩
  toFun := fun _ => c
  holomorphic := ⟨isOpen_univ, fun _ _ => differentiableAt_const c⟩

private lemma constant_sections_disjoint :
    Pairwise (fun c d : ℂ => Disjoint
      (basicSet Set.univ (constantElement c))
      (basicSet Set.univ (constantElement d))) := by
  intro c d hne
  apply Set.disjoint_left.mpr
  intro p hp hq
  obtain ⟨hc, hp⟩ := hp
  obtain ⟨hd, hq⟩ := hq
  have hcd := congrArg HolomorphicGerm.value (hp.symm.trans hq)
  change c = d at hcd
  exact hne hcd

private lemma constant_section_nonempty (c : ℂ) :
    (basicSet Set.univ (constantElement c)).Nonempty := by
  refine ⟨⟨⟨0, Set.mem_univ 0⟩,
    (constantElement c).germAt 0 (Set.mem_univ 0)⟩, ?_⟩
  exact ⟨Set.mem_univ 0, rfl⟩

/-- The full space of all holomorphic germs over ℂ fails second countability. -/
theorem fullSpace_not_secondCountable :
    Specs.D12Complex.Ch20.GermSpaceCountability.fullSpace_not_secondCountable_type := by
  intro h
  have : Countable ℂ := constant_sections_disjoint.countable_of_isOpen_disjoint
    (fun c => isOpen_basicSet (constantElement c) (Set.subset_univ _))
    constant_section_nonempty
  have : Countable ℝ := Function.Injective.countable Complex.ofReal_injective
  exact Cardinal.not_countable_real Set.countable_univ

end D12Complex.GermSpaceCountability
