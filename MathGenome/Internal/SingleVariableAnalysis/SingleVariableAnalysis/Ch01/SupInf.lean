import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SupInf
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch01.Scalar
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

/-!
# Suprema and infima

The real supremum and infimum have proof arguments restricting them to nonempty
sets bounded in the appropriate direction. The infimum is constructed exactly
as minus the supremum of the negative image. The extended operations are the
canonical complete-lattice bounds on `EReal`; finite compatibility, empty sets
and unbounded real sets are treated separately below.
-/

namespace SingleVariableAnalysis

noncomputable def realSupremum (A : Set ℝ) (_ : A.Nonempty) (_ : BddAbove A) : ℝ :=
  sSup A

noncomputable def realInfimum (A : Set ℝ) (_ : A.Nonempty) (_ : BddBelow A) : ℝ :=
  -sSup ((fun x : ℝ => -x) '' A)

noncomputable def extendedSupremum (A : Set EReal) : EReal := sSup A

noncomputable def extendedInfimum (A : Set EReal) : EReal := sInf A

theorem real_supremum_isLUB (A : Set ℝ) (hne : A.Nonempty) (hb : BddAbove A) :
    IsLUB A (realSupremum A hne hb) :=
  isLUB_csSup hne hb

theorem real_infimum_eq_csInf (A : Set ℝ) (hne : A.Nonempty) (hb : BddBelow A) :
    realInfimum A hne hb = sInf A := by
  simp only [realInfimum, Set.image_neg_eq_neg, csSup_neg hne hb, neg_neg]

theorem real_infimum_isGLB (A : Set ℝ) (hne : A.Nonempty) (hb : BddBelow A) :
    IsGLB A (realInfimum A hne hb) := by
  rw [real_infimum_eq_csInf A hne hb]
  exact isGLB_csInf hne hb

/-- A smaller number cannot be an upper bound of a set with the given LUB. -/
theorem real_supremum_approx (A : Set ℝ) (hne : A.Nonempty) (hb : BddAbove A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ A, realSupremum A hne hb - ε < a ∧ a ≤ realSupremum A hne hb :=
  (real_supremum_isLUB A hne hb).exists_between (sub_lt_self _ hε)

theorem real_infimum_approx (A : Set ℝ) (hne : A.Nonempty) (hb : BddBelow A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ A, realInfimum A hne hb ≤ a ∧ a < realInfimum A hne hb + ε :=
  (real_infimum_isGLB A hne hb).exists_between (lt_add_of_pos_right _ hε)

theorem real_no_supremum_empty (s : ℝ) : ¬ IsLUB (∅ : Set ℝ) s := by
  intro h
  have hle : s ≤ s - 1 := h.2 (by simp)
  exact (not_le_of_gt (sub_lt_self s zero_lt_one)) hle

theorem real_no_infimum_empty (t : ℝ) : ¬ IsGLB (∅ : Set ℝ) t := by
  intro h
  have hle : t + 1 ≤ t := h.2 (by simp)
  exact (not_le_of_gt (lt_add_of_pos_right t zero_lt_one)) hle

theorem extended_supremum_isLUB (A : Set EReal) : IsLUB A (extendedSupremum A) :=
  isLUB_sSup A

theorem extended_infimum_isGLB (A : Set EReal) : IsGLB A (extendedInfimum A) :=
  isGLB_sInf A

theorem extended_supremum_empty : extendedSupremum ∅ = ⊥ := sSup_empty

theorem extended_infimum_empty : extendedInfimum ∅ = ⊤ := sInf_empty

/-- Coercion preserves the finite supremum, with the required real hypotheses. -/
theorem extended_supremum_of_real (A : Set ℝ) (hne : A.Nonempty) (hb : BddAbove A) :
    extendedSupremum (Real.toEReal '' A) = (realSupremum A hne hb : EReal) := by
  change sSup (Real.toEReal '' A) = ((sSup A : ℝ) : EReal)
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨a, ha, rfl⟩
    exact EReal.coe_le_coe (le_csSup hb ha)
  · have hu : ∀ a ∈ A, (a : EReal) ≤ sSup (Real.toEReal '' A) :=
      fun a ha => le_sSup (Set.mem_image_of_mem Real.toEReal ha)
    cases h : sSup (Real.toEReal '' A) with
    | bot =>
      obtain ⟨a, ha⟩ := hne
      exact False.elim ((EReal.coe_ne_bot a) (le_bot_iff.mp (h ▸ hu a ha)))
    | coe b =>
      exact EReal.coe_le_coe (csSup_le hne fun a ha =>
        EReal.coe_le_coe_iff.mp (h ▸ hu a ha))
    | top => exact le_top

/-- The extended infimum agrees with the constructed real infimum. -/
theorem extended_infimum_of_real (A : Set ℝ) (hne : A.Nonempty) (hb : BddBelow A) :
    extendedInfimum (Real.toEReal '' A) = (realInfimum A hne hb : EReal) := by
  rw [real_infimum_eq_csInf A hne hb]
  change sInf (Real.toEReal '' A) = ((sInf A : ℝ) : EReal)
  apply le_antisymm
  · have hl : ∀ a ∈ A, sInf (Real.toEReal '' A) ≤ (a : EReal) :=
      fun a ha => sInf_le (Set.mem_image_of_mem Real.toEReal ha)
    cases h : sInf (Real.toEReal '' A) with
    | bot => exact bot_le
    | coe b =>
      exact EReal.coe_le_coe (le_csInf hne fun a ha =>
        EReal.coe_le_coe_iff.mp (h ▸ hl a ha))
    | top =>
      obtain ⟨a, ha⟩ := hne
      exact False.elim ((EReal.coe_ne_top a) (top_le_iff.mp (h ▸ hl a ha)))
  · refine le_sInf ?_
    rintro _ ⟨a, ha, rfl⟩
    exact EReal.coe_le_coe (csInf_le hb ha)

theorem extended_supremum_unbounded (A : Set ℝ) (hb : ¬ BddAbove A) :
    extendedSupremum (Real.toEReal '' A) = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).2
  intro b
  obtain ⟨a, ha, hba⟩ := not_bddAbove_iff.mp hb b
  exact (EReal.coe_lt_coe hba).trans_le
    (le_sSup (Set.mem_image_of_mem Real.toEReal ha))

theorem extended_infimum_unbounded (A : Set ℝ) (hb : ¬ BddBelow A) :
    extendedInfimum (Real.toEReal '' A) = ⊥ := by
  apply (EReal.eq_bot_iff_forall_lt _).2
  intro b
  obtain ⟨a, ha, hab⟩ := not_bddBelow_iff.mp hb b
  exact (sInf_le (Set.mem_image_of_mem Real.toEReal ha)).trans_lt
    (EReal.coe_lt_coe hab)

end SingleVariableAnalysis
