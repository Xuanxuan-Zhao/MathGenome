import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesBalancedAttainment
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.EberleinSmulian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesBlockLemma
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.JamesWitness
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

universe u
namespace ExpandedFA.P1.JamesBalancedAttainment
open Set Filter TopologicalSpace
open scoped Topology BigOperators
open JamesBlockObjects JamesBlockLemma
noncomputable section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A noncompact weakly closed set contains a norm-separable, weakly closed
noncompact subset. We use the separable closed span of a sequence witnessing
failure of relative sequential compactness. -/
lemma separable_noncompact_subset (A : Set E)
    (hclosed : @IsClosed E (Spec.weakTopology E) A)
    (hnc : ¬ @IsCompact E (Spec.weakTopology E) A) :
    ∃ A₀ : Set E, A₀ ⊆ A ∧ A₀.Nonempty ∧ IsSeparable A₀ ∧
      @IsClosed E (Spec.weakTopology E) A₀ ∧
      ¬ @IsCompact E (Spec.weakTopology E) A₀ := by
  classical
  have hnseq : ¬ EberleinSmulian.Spec.HasWeaklyConvergentSubsequences ℝ E A := by
    intro hs
    have hc := (EberleinSmulian.relative_equivalences ℝ E A).1.mpr hs
    rw [@IsClosed.closure_eq E (Spec.weakTopology E) A hclosed] at hc
    exact hnc hc
  simp only [EberleinSmulian.Spec.HasWeaklyConvergentSubsequences,
    WeakSequentialRelativeCompact.Spec.HasWeaklyConvergentSubsequences,
    not_forall, not_exists, not_and] at hnseq
  obtain ⟨s, hs, hnosub⟩ := hnseq
  let Y : Submodule ℝ E := (Submodule.span ℝ (range s)).topologicalClosure
  have hYs : ∀ n, s n ∈ Y := fun n =>
    (Submodule.span ℝ (range s)).le_topologicalClosure
      (Submodule.subset_span (mem_range_self n))
  have hYsep : IsSeparable (Y : Set E) := by
    rw [show (Y : Set E) = closure (Submodule.span ℝ (range s) : Set E) from
      Submodule.topologicalClosure_coe _]
    exact (countable_range s).isSeparable.span.closure
  have hYclosed := C12ConvexClosure.isWeaklyClosed_of_isClosed_submodule ℝ E Y
    (Submodule.isClosed_topologicalClosure _)
  have hAc : @IsClosed E (Spec.weakTopology E) (A ∩ (Y : Set E)) :=
    @IsClosed.inter E A (Y : Set E) (Spec.weakTopology E) hclosed hYclosed
  refine ⟨A ∩ (Y : Set E), inter_subset_left, ⟨s 0, hs 0, hYs 0⟩,
    hYsep.mono inter_subset_right, hAc, ?_⟩
  intro hc
  have hsubs := EberleinSmulian.compact_implies_subsequences ℝ E
    (A ∩ (Y : Set E)) (by rwa [@IsClosed.closure_eq E (Spec.weakTopology E) _ hAc])
  obtain ⟨x, r, hr, hc⟩ := hsubs s (fun n => ⟨hs n, hYs n⟩)
  exact hnosub x r hr hc

/-- Pointwise convergence on a subset forces every limsup-dominated linear
functional to vanish there. -/
lemma L_vanishes {f : ℕ → E →L[ℝ] ℝ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {A₀ : Set E} (hzero : ∀ x ∈ A₀, Tendsto (fun n => f n x) atTop (𝓝 0))
    {w : E →L[ℝ] ℝ} (hw : w ∈ L f) {x : E} (hx : x ∈ A₀) : w x = 0 := by
  have hh := L_bounds f ⟨1, hf⟩ w hw x
  rw [(hzero x hx).liminf_eq, (hzero x hx).limsup_eq] at hh
  exact le_antisymm hh.2 hh.1

/-- The witness on A₀ gives the separation hypothesis for the block lemma on A,
even though the block lemma's set need not be separable. -/
lemma witness_separates {A A₀ : Set E} (hA : A.Nonempty)
    (hunit : A ⊆ Metric.closedBall (0 : E) 1) (hne : A₀.Nonempty) (hsub : A₀ ⊆ A)
    {θ : ℝ} {f : ℕ → E →L[ℝ] ℝ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hzero : ∀ x ∈ A₀, Tendsto (fun n => f n x) atTop (𝓝 0))
    (hsep : ∀ h ∈ convexHull ℝ (range f), θ ≤ sSup ((fun x => ‖h x‖) '' A₀)) :
    ∀ h ∈ convexHull ℝ (range f), ∀ w ∈ L f, θ ≤ normOn A (h - w) := by
  intro h hh w hw
  apply (hsep h hh).trans
  apply csSup_le (hne.image (fun x => ‖h x‖))
  rintro _ ⟨x, hx, rfl⟩
  have hz := L_vanishes hf hzero hw hx
  have he : ‖h x‖ = |(h - w) x| := by simp [hz, Real.norm_eq_abs]
  change ‖h x‖ ≤ normOn A (h - w)
  rw [he]
  exact abs_apply_le_normOn hA (bounded_of_unitBall hunit) _ (hsub hx)

/-- Positive geometric weights of total mass one. -/
lemma geometric_hasSum {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => (1 - q) * q ^ n) 1 := by
  have hh := (hasSum_geometric_of_lt_one hq.le hq1).mul_left (1 - q)
  simpa only [mul_inv_cancel₀ (sub_pos.mpr hq1).ne'] using hh

lemma geometric_tail {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (n : ℕ) :
    JamesBlockLemma.Spec.tailMass (fun j => (1 - q) * q ^ j) n = q ^ n := by
  unfold JamesBlockLemma.Spec.tailMass
  simp only [pow_add, ← mul_assoc, tsum_mul_right, tsum_mul_left,
    tsum_geometric_of_lt_one hq.le hq1, mul_inv_cancel₀ (sub_pos.mpr hq1).ne', one_mul]

/-- The scalar tail of a translated dual-unit-ball sequence is bounded by
twice the remaining weight. -/
lemma eval_tail_le {β : ℕ → ℝ} (hβ : Summable β) (hβ0 : ∀ n, 0 ≤ β n)
    {g : ℕ → E →L[ℝ] ℝ} (hg : ∀ n, ‖g n‖ ≤ 1)
    {w : E →L[ℝ] ℝ} (hw : ‖w‖ ≤ 1) {x : E} (hx : ‖x‖ ≤ 1) (n : ℕ) :
    (∑' k, β (k + n) * ((g (k + n) - w) x)) ≤
      2 * JamesBlockLemma.Spec.tailMass β n := by
  have hb (j : ℕ) : (g j - w) x ≤ 2 := by
    have hgx := (g j).unit_le_opNorm x hx
    have hwx := w.unit_le_opNorm x hx
    rw [Real.norm_eq_abs, abs_le] at hgx hwx
    change g j x - w x ≤ 2
    linarith [hg j]
  have hsum := weighted_sub_summable hβ hβ0 hg w
  have heval : Summable (fun j => β j * ((g j - w) x)) := by
    simpa only [smul_apply, smul_eq_mul] using summable_apply hsum x
  have htβ := hβ.comp_injective (add_left_injective n)
  have htu := heval.comp_injective (add_left_injective n)
  calc
    _ ≤ ∑' k, β (k + n) * 2 := htu.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left (hb _) (hβ0 _)) (htβ.mul_right 2)
    _ = _ := by rw [tsum_mul_right]; exact mul_comm _ _

/-- Strict prefix estimates and a sufficiently small geometric ratio prevent
the infinite sum from attaining its positive supremum at any point of A. -/
lemma block_sum_eval_lt {A : Set E} (hA : A.Nonempty)
    (hunit : A ⊆ Metric.closedBall (0 : E) 1)
    {θ q a : ℝ} (hq : 0 < q) (hq1 : q < 1) (hsmall : 2 * q < a * θ)
    {g : ℕ → E →L[ℝ] ℝ} (hg : ∀ n, ‖g n‖ ≤ 1)
    {w : E →L[ℝ] ℝ} (hw : w ∈ L g)
    (hpref : ∀ n : ℕ, normOn A
      (∑ j ∈ Finset.range (n + 1), ((1 - q) * q ^ j) • (g j - w)) <
      a * (1 - θ * JamesBlockLemma.Spec.tailMass (fun j => (1 - q) * q ^ j) (n + 1)))
    {x : E} (hx : x ∈ A) :
    (∑' j, ((1 - q) * q ^ j) • (g j - w)) x < a := by
  let β : ℕ → ℝ := fun j => (1 - q) * q ^ j
  have hβ := geometric_hasSum hq hq1
  have hβpos (j : ℕ) : 0 < β j := mul_pos (sub_pos.mpr hq1) (pow_pos hq j)
  have hsum := weighted_sub_summable hβ.summable (fun j => (hβpos j).le) hg w
  have hwunit := L_norm_le_one hg hw
  have hlim := (L_bounds g ⟨1, hg⟩ w hw x).1
  have hfreq : ∃ᶠ n in atTop, g n x < w x + (a * θ - 2 * q) :=
    frequently_lt_of_liminf_lt (eval_bddAbove ⟨1, hg⟩ x).isCoboundedUnder_ge
      (hlim.trans_lt (by linarith))
  obtain ⟨n, hval, hn⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
  have hp : normOn A (∑ j ∈ Finset.range n, β j • (g j - w)) <
      a * (1 - θ * q ^ n) := by
    have hh := hpref (n - 1)
    rw [Nat.sub_add_cancel hn, geometric_tail hq hq1] at hh
    exact hh
  have hpval : (∑ j ∈ Finset.range n, β j • (g j - w)) x <
      a * (1 - θ * q ^ n) :=
    lt_of_le_of_lt (le_trans (le_abs_self _)
      (abs_apply_le_normOn hA (bounded_of_unitBall hunit) _ hx)) hp
  have hxunit : ‖x‖ ≤ 1 := by simpa using hunit hx
  have htail := eval_tail_le hβ.summable (fun j => (hβpos j).le) hg hwunit hxunit (n + 1)
  rw [geometric_tail hq hq1] at htail
  have heval : Summable (fun j => β j * ((g j - w) x)) := by
    simpa only [smul_apply, smul_eq_mul] using summable_apply hsum x
  have heq := heval.sum_add_tsum_nat_add (n + 1)
  rw [Finset.sum_range_succ] at heq
  have hprefix : (∑ j ∈ Finset.range n, β j • (g j - w)) x =
      ∑ j ∈ Finset.range n, β j * ((g j - w) x) := by
    simp only [sum_apply, smul_apply, smul_eq_mul]
  have hevaleq : (∑' j, β j • (g j - w)) x = ∑' j, β j * ((g j - w) x) := by
    simpa only [smul_apply, smul_eq_mul] using tsum_apply hsum x
  rw [← hprefix, ← hevaleq] at heq
  have hv : β n * ((g n - w) x) < β n * (a * θ - 2 * q) := by
    apply mul_lt_mul_of_pos_left _ (hβpos n)
    change g n x - w x < a * θ - 2 * q
    linarith
  have hstrict : a * (1 - θ * q ^ n) + β n * (a * θ - 2 * q) +
      2 * q ^ (n + 1) < a := by
    have hpos := mul_pos (mul_pos hq (sub_pos.mpr hsmall)) (pow_pos hq n)
    dsimp [β]
    rw [pow_succ]
    nlinarith
  calc
    _ = (∑ j ∈ Finset.range n, β j • (g j - w)) x +
        β n * ((g n - w) x) + ∑' k, β (k + (n + 1)) * ((g (k + (n + 1)) - w) x) := heq.symm
    _ < a * (1 - θ * q ^ n) + β n * (a * θ - 2 * q) + 2 * q ^ (n + 1) :=
      add_lt_add_of_lt_of_le (add_lt_add hpval hv) htail
    _ < a := hstrict

/-- The contrapositive in the balanced real case of James's theorem. -/
theorem noncompact_has_nonattaining : Spec.NoncompactHasNonattaining.{u} := by
  classical
  intro E _ _ _ A hA hbal hunit hclosed hnc
  obtain ⟨A₀, hsub, hne, hseparable, hc₀, hnc₀⟩ :=
    separable_noncompact_subset A hclosed hnc
  have hunit₀ : A₀ ⊆ {x | ‖x‖ ≤ 1} := by
    intro x hx
    simpa using hunit (hsub hx)
  obtain ⟨θ, f, hθ, hθ1, hf, hzero, hsep⟩ :=
    JamesWitness.separable_witness ℝ E A₀ hne hunit₀ hseparable hc₀ hnc₀
  have hseparation := witness_separates hA hunit hne hsub hf hzero hsep
  let q : ℝ := θ ^ 2 / 4
  have hq : 0 < q := div_pos (sq_pos_of_pos hθ) (by norm_num)
  have hq1 : q < 1 := by dsimp [q]; nlinarith
  let β : ℕ → ℝ := fun n => (1 - q) * q ^ n
  have hβpos (n : ℕ) : 0 < β n := mul_pos (sub_pos.mpr hq1) (pow_pos hq n)
  have hβ : HasSum β 1 := geometric_hasSum hq hq1
  obtain ⟨g, a, hg, hθa, ha2, hblock⟩ :=
    james_block_lemma A hA hbal hunit θ hθ hθ1 f hf hseparation β hβpos hβ
  obtain ⟨w, hw⟩ := L_nonempty g ⟨1, hg⟩
  obtain ⟨hsum, hnorm, hpref⟩ := hblock w hw
  let z : E →L[ℝ] ℝ := ∑' j, β j • (g j - w)
  have hsmall : 2 * q < a * θ := by
    have hh : θ * θ ≤ a * θ := mul_le_mul_of_nonneg_right hθa hθ.le
    dsimp [q]
    nlinarith [sq_pos_of_pos hθ]
  have hzlt : ∀ x ∈ A, z x < a := by
    intro x hx
    exact block_sum_eval_lt hA hunit hq hq1 hsmall hg hw hpref hx
  have habs : ∀ x ∈ A, |z x| < a := by
    intro x hx
    apply abs_lt.mpr
    have hneg := hzlt (-x) (hbal.neg_mem_iff.mpr hx)
    rw [map_neg] at hneg
    exact ⟨by linarith, hzlt x hx⟩
  refine ⟨z, ?_, ?_⟩
  · exact (normOn_isLUB A hA (bounded_of_unitBall hunit) z).bddAbove
  · intro x hx
    change |z x| < normOn A z
    rw [show normOn A z = a from hnorm]
    exact habs x hx

/-- Attainment contradicts the strict pointwise inequality produced above. -/
theorem balanced_attainment_compact : Spec.BalancedAttainmentCompact.{u} := by
  intro E _ _ _ A hA hbal hunit hclosed hatt
  by_contra hnc
  obtain ⟨z, _, hz⟩ := noncompact_has_nonattaining E A hA hbal hunit hclosed hnc
  obtain ⟨x, hx, heq⟩ := (hatt z).2
  exact (hz x hx).ne heq

end
end ExpandedFA.P1.JamesBalancedAttainment
