import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.Injective
import MathGenome.Internal.AlgebraCore.P103.Ch01.HomTensorExactness
import MathGenome.Internal.AlgebraCore.P103.Ch01.SplitSequences

namespace P103.Ch02.Injective

open P103.Specs.Ch02.Injective

universe u

theorem extension_iff_injective : extension_iff_injectiveType.{u} := by
  intro R E _ _ _
  constructor
  · intro h
    constructor
    intro U M _ _ _ _ i hi f
    obtain ⟨g, hg⟩ := h U M i hi f
    exact ⟨g, LinearMap.congr_fun hg⟩
  · intro h U M _ _ _ _ i hi f
    obtain ⟨g, hg⟩ := h.out i hi f
    exact ⟨g, LinearMap.ext hg⟩

theorem baerCriterion : baerCriterionType.{u} := by
  intro R E _ _ _
  constructor
  · intro h I f
    exact h I R I.subtype Subtype.val_injective f
  · intro h
    apply (extension_iff_injective R E).mpr
    apply Module.Baer.injective
    intro I f
    obtain ⟨g, hg⟩ := h I f
    exact ⟨g, fun x hx => LinearMap.congr_fun hg ⟨x, hx⟩⟩

theorem homExact_iff : homExact_iffType.{u} := by
  intro R E _ _ _
  constructor
  · intro h A B C _ _ _ _ _ _ i p hi he hp
    obtain ⟨hinj, hex⟩ := P103.HomTensorExactness.homContravariant R A B C E i p he hp
    refine ⟨hinj, hex, ?_⟩
    intro f
    exact h A B i hi f
  · intro h U M _ _ _ _ i hi f
    obtain ⟨g, hg⟩ := (h U M (M ⧸ LinearMap.range i) i
      (LinearMap.range i).mkQ hi (LinearMap.exact_map_mkQ_range i)
      (LinearMap.range i).mkQ_surjective).2.2 f
    exact ⟨g, hg⟩

/-- The pushout construction used in the converse splitting implication.
The relation is (f(u), -i(u)); no commutativity of R is used. -/
theorem extension_of_splits (R E : Type u) [Ring R] [AddCommGroup E] [Module R E]
    (h : Splits R E) : Extension R E := by
  intro U M _ _ _ _ i hi f
  let d : U →ₗ[R] E × M := f.prod (-i)
  let D : Submodule R (E × M) := LinearMap.range d
  let j : E →ₗ[R] ((E × M) ⧸ D) := D.mkQ.comp (LinearMap.inl R E M)
  let k : M →ₗ[R] ((E × M) ⧸ D) := D.mkQ.comp (LinearMap.inr R E M)
  have hj : Function.Injective j := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro e he
      have he' : (e, (0 : M)) ∈ D := (Submodule.Quotient.mk_eq_zero D).mp he
      obtain ⟨a, ha⟩ := he'
      have hia : i a = 0 := by
        have := congrArg Prod.snd ha
        change -i a = 0 at this
        exact neg_eq_zero.mp this
      have ha0 : a = 0 := hi (hia.trans (map_zero i).symm)
      have hfe := congrArg Prod.fst ha
      change f a = e at hfe
      simpa [ha0] using hfe.symm
    · exact bot_le
  let q := (LinearMap.range j).mkQ
  have he := LinearMap.exact_map_mkQ_range j
  obtain ⟨s, hs⟩ := h _ _ j q hj he (LinearMap.range j).mkQ_surjective
  obtain ⟨r, hr⟩ :=
    (P103.Ch01.SplitSequences.section_iff_retraction R E _ _ j q hj
      (LinearMap.range j).mkQ_surjective he).mp ⟨s, hs⟩
  refine ⟨r.comp k, ?_⟩
  ext a
  have hrel : j (f a) = k (i a) := by
    apply (Submodule.Quotient.eq D).mpr
    change (f a, (0 : M)) - (0, i a) ∈ D
    exact ⟨a, by simp [d]⟩
  change r (k (i a)) = f a
  rw [← hrel]
  exact LinearMap.congr_fun hr (f a)

theorem splits_iff : splits_iffType.{u} := by
  intro R E _ _ _
  constructor
  · intro h B C _ _ _ _ i p hi he hp
    obtain ⟨r, hr⟩ := h E B i hi LinearMap.id
    exact (P103.Ch01.SplitSequences.section_iff_retraction R E B C i p hi hp he).mpr
      ⟨r, hr⟩
  · exact extension_of_splits R E

theorem rightModuleCriterion : rightModuleCriterionType.{u} := by
  intro R E _ _ _
  exact ⟨extension_iff_injective Rᵐᵒᵖ E, baerCriterion Rᵐᵒᵖ E,
    homExact_iff Rᵐᵒᵖ E, splits_iff Rᵐᵒᵖ E⟩

end P103.Ch02.Injective
