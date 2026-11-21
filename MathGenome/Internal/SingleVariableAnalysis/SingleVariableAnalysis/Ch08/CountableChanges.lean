import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.CountableChanges
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Dirichlet
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.ZeroCovers
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Linearity

/-! Countable modifications can destroy Riemann integrability. When both
integrals already exist, tags outside the exceptional set identify their
values, using only the shared Darboux/tagged-sum bridge.
-/
namespace SingleVariableAnalysis.Riemann
open scoped BigOperators

/-- A length-zero set cannot contain any closed nondegenerate interval. -/
theorem exists_point_outside_lengthZero {E : Set ℝ} (hE : LengthZero E)
    {c d : ℝ} (hcd : c < d) : ∃ x ∈ Set.Icc c d, x ∉ E := by
  by_contra! h
  exact not_lengthZero_of_contains_Icc E c d hcd h hE

/-- Each closed partition cell has a tag outside the exceptional set. -/
theorem exists_tagging_outside_lengthZero {E : Set ℝ} (hE : LengthZero E)
    {a b : ℝ} (P : Partition a b) :
    ∃ ξ : Tagging P, ∀ i, (ξ i : ℝ) ∉ E := by
  classical
  have hex (i : Fin P.n) : ∃ x : {x // x ∈ cell P i}, (x : ℝ) ∉ E := by
    obtain ⟨x, hx, hnot⟩ := exists_point_outside_lengthZero hE
      (P.strictMono (Fin.castSucc_lt_succ (i := i)))
    exact ⟨⟨x, hx⟩, hnot⟩
  exact ⟨fun i => (hex i).choose, fun i => (hex i).choose_spec⟩

/-- Limits of tagged sums agree if the functions agree off a length-zero set.
Only one tagging per partition is needed, since the two limits control all tags. -/
theorem fineTaggedLimits_eq_off_lengthZero
    {V : Type*} [NormedAddCommGroup V] [Module ℝ V]
    {f g : ℝ → V} {a b : ℝ} (hab : a ≤ b)
    {E : Set ℝ} (hE : LengthZero E)
    (hfg : ∀ x ∈ Set.Icc a b, x ∉ E → f x = g x)
    {I J : V} (hf : FineTaggedLimit f a b I) (hg : FineTaggedLimit g a b J) :
    I = J := by
  by_contra hne
  have hp : 0 < ‖I - J‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨δf, hδf, hcf⟩ := hf (‖I - J‖ / 2) (half_pos hp)
  obtain ⟨δg, hδg, hcg⟩ := hg (‖I - J‖ / 2) (half_pos hp)
  obtain ⟨P, hP⟩ := exists_fine_partition hab (min δf δg) (lt_min hδf hδg)
  obtain ⟨ξ, hξ⟩ := exists_tagging_outside_lengthZero hE P
  have hs : taggedSum P ξ f = taggedSum P ξ g := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hfg (ξ i) (cell_subset_interval P i (ξ i).property) (hξ i)]
  have hi := hcf P ξ (hP.trans_le (min_le_left _ _))
  have hj := hcg P ξ (hP.trans_le (min_le_right _ _))
  change ‖taggedSum P ξ f - I‖ < ‖I - J‖ / 2 at hi
  change ‖taggedSum P ξ g - J‖ < ‖I - J‖ / 2 at hj
  have ht := norm_sub_le_norm_sub_add_norm_sub I (taggedSum P ξ f) J
  rw [norm_sub_rev I (taggedSum P ξ f)] at ht
  rw [hs] at ht hi
  linarith

theorem countable_modification_counterexample :
    Specs.SingleVariableAnalysis.Ch08.CountableChanges.modificationCounterexample := by
  classical
  let E : Set ℝ := {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ q : ℚ, (q : ℝ) = x}
  have hc : E.Countable := by
    apply (Set.countable_range (fun q : ℚ => (q : ℝ))).mono
    rintro x ⟨_, q, hq⟩
    exact ⟨q, hq⟩
  refine ⟨hc, lengthZero_countable E hc, ?_, ?_, dirichlet_bounded,
    real_zero_value (by norm_num), dirichlet_not_integrable⟩
  · intro x
    change (if x ∈ E then (1 : ℝ) else 0) ≠ 0 ↔ x ∈ E
    split_ifs <;> simp_all
  · exact boundedOnInterval_of_abs (M := 0) (by simp)

theorem realIntegral_eq_off_lengthZero :
    Specs.SingleVariableAnalysis.Ch08.CountableChanges.realIntegralEqOffLengthZero := by
  intro f g a b E hE hf hg hfg
  change RealIntegrable f a b at hf
  change RealIntegrable g a b at hg
  exact fineTaggedLimits_eq_off_lengthZero hf.ordered hE hfg
    ((real_tagged_equivalence f hf.ordered hf.bounded _).mp ⟨hf, rfl⟩)
    ((real_tagged_equivalence g hg.ordered hg.bounded _).mp ⟨hg, rfl⟩)

theorem complexIntegral_eq_off_lengthZero :
    Specs.SingleVariableAnalysis.Ch08.CountableChanges.complexIntegralEqOffLengthZero := by
  intro f g a b E hE hf hg hfg
  apply Complex.ext
  · rw [(complexIntegral_components f hf).1, (complexIntegral_components g hg).1]
    exact realIntegral_eq_off_lengthZero _ _ a b E hE hf.1 hg.1
      (fun x hx hnot => congrArg Complex.re (hfg x hx hnot))
  · rw [(complexIntegral_components f hf).2, (complexIntegral_components g hg).2]
    exact realIntegral_eq_off_lengthZero _ _ a b E hE hf.2 hg.2
      (fun x hx hnot => congrArg Complex.im (hfg x hx hnot))

end SingleVariableAnalysis.Riemann
