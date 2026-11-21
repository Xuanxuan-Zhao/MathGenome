import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Equivalence
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.EquivalenceReplacement

/-!
Replacement of products and quotients, and the cancellation counterexample
from K03.02.equivalence_replacement (paper.tex:457–463).

The Mathlib product and quotient laws apply to its error-based equivalence.
The upstream bridge is used together with separate proofs of nonvanishing,
so the manuscript's stronger ratio relation is preserved. In the example,
(x + x²)/x = 1 + x on the punctured neighborhood of zero.
-/

namespace SingleVariableAnalysis

open Filter
open scoped Topology
universe u v

theorem scalarEquivalent_mul {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (f F g G : X → K)
    (hf : ScalarEquivalent l f F) (hg : ScalarEquivalent l g G) :
    ScalarEquivalent l (fun x => f x * g x) (fun x => F x * G x) := by
  apply (scalarEquivalent_iff_isEquivalent l _ _).mpr
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hg.1] with x hF hG
    exact mul_ne_zero hF hG
  · exact ((scalarEquivalent_iff_isEquivalent l f F).mp hf).2.mul
      ((scalarEquivalent_iff_isEquivalent l g G).mp hg).2

/-- Both actual quotient denominators are nonzero on a common tail. -/
theorem scalarEquivalent_div {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (f F g G : X → K)
    (hf : ScalarEquivalent l f F) (hg : ScalarEquivalent l g G) :
    (∀ᶠ x in l, g x ≠ 0 ∧ G x ≠ 0) ∧
    ScalarEquivalent l (fun x => f x / g x) (fun x => F x / G x) := by
  refine ⟨(scalarEquivalent_eventually_ne_zero l g G hg).and hg.1, ?_⟩
  apply (scalarEquivalent_iff_isEquivalent l _ _).mpr
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hg.1] with x hF hG
    exact div_ne_zero hF hG
  · exact ((scalarEquivalent_iff_isEquivalent l f F).mp hf).2.div
      ((scalarEquivalent_iff_isEquivalent l g G).mp hg).2

private theorem real_eventually_ne_zero_at_zero :
    ∀ᶠ x : ℝ in PuncturedDomainFilter Set.univ 0, x ≠ 0 := by
  have hmem : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.univ \ {0}), x ∈ Set.univ \ {0} :=
    self_mem_nhdsWithin
  exact hmem.mono (fun _ hx => hx.2)

theorem real_add_sq_equivalent_self :
    ScalarEquivalent (PuncturedDomainFilter Set.univ 0)
      (fun x : ℝ => x + x ^ 2) (fun x => x) := by
  refine ⟨real_eventually_ne_zero_at_zero, ?_⟩
  have hx : Tendsto (fun x : ℝ => x) (PuncturedDomainFilter Set.univ 0) (𝓝 0) :=
    nhdsWithin_le_nhds
  have hlim : Tendsto (fun x : ℝ => 1 + x)
      (PuncturedDomainFilter Set.univ 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.add hx
  apply hlim.congr'
  filter_upwards [real_eventually_ne_zero_at_zero] with x hx
  field_simp

theorem real_self_equivalent_at_zero :
    ScalarEquivalent (PuncturedDomainFilter Set.univ 0)
      (fun x : ℝ => x) (fun x => x) := by
  exact scalarEquivalent_refl _ _ real_eventually_ne_zero_at_zero

theorem real_subtraction_replacement_counterexample :
    (∀ x : ℝ, (x + x ^ 2) - x = x ^ 2 ∧ x - x = 0) ∧
      (¬ ScalarEquivalent (PuncturedDomainFilter Set.univ 0)
        (fun x : ℝ => x ^ 2) (fun _ => 0)) ∧
      (¬ ScalarEquivalent (PuncturedDomainFilter Set.univ 0)
        (fun x : ℝ => (x + x ^ 2) - x) (fun x => x - x)) := by
  have hnontrivial : (PuncturedDomainFilter (Set.univ : Set ℝ) 0).NeBot := by
    simpa only [PuncturedDomainFilter, ← Set.compl_eq_univ_sdiff] using
      (inferInstance : (𝓝[≠] (0 : ℝ)).NeBot)
  have hzero (f : ℝ → ℝ) :
      ¬ ScalarEquivalent (PuncturedDomainFilter Set.univ 0) f (fun _ => 0) := by
    intro h
    have hfalse : ∀ᶠ _ : ℝ in PuncturedDomainFilter Set.univ 0, False := by
      simpa only [ne_eq, not_true_eq_false] using h.1
    exact hnontrivial.ne (eventually_false_iff_eq_bot.mp hfalse)
  refine ⟨fun x => ⟨by ring, sub_self x⟩, hzero _, ?_⟩
  simpa only [sub_self] using hzero (fun x : ℝ => (x + x ^ 2) - x)

end SingleVariableAnalysis
