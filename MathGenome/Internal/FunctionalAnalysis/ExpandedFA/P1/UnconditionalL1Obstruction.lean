import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UnconditionalL1Obstruction
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.DualBases
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15SubsetProjections
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.EquivalentBases
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals

noncomputable section
open Filter Topology TopologicalSpace
open scoped BigOperators ENNReal
universe u v
namespace ExpandedFA.P1.UnconditionalL1Obstruction
open C01SequenceSpaces DualBasisBasicity.Spec

variable {𝕜 : Type u} [RCLike 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Diagonalization against a putative dense sequence of bounded sequences. -/
theorem linfinity_not_separable : ¬ SeparableSpace (SequenceLInfinity 𝕜) := by
  intro h
  let a := denseSeq (SequenceLInfinity 𝕜)
  let x : SequenceLInfinity 𝕜 :=
    ⟨fun n => if ‖a n n‖ < 1 / 2 then 1 else 0,
      memℓp_infty ⟨1, by
        rintro _ ⟨n, rfl⟩
        dsimp only
        split_ifs <;> simp⟩⟩
  obtain ⟨n, hn⟩ := (denseRange_denseSeq (SequenceLInfinity 𝕜)).exists_dist_lt x
    (by norm_num : (0 : ℝ) < 1 / 2)
  have heval := lp.norm_apply_le_norm ENNReal.top_ne_zero (x - a n) n
  have hsmall : ‖x n - a n n‖ < 1 / 2 := by
    exact heval.trans_lt (by simpa only [dist_eq_norm] using hn)
  by_cases hh : ‖a n n‖ < 1 / 2
  · have hx : x n = 1 := ite_eq_left hh
    rw [hx] at hsmall
    have ht := norm_add_le (1 - a n n) (a n n)
    have : (1 : ℝ) ≤ ‖1 - a n n‖ + ‖a n n‖ := by simpa using ht
    linarith
  · have hx : x n = 0 := ite_eq_right hh
    rw [hx, zero_sub, norm_neg] at hsmall
    exact hh hsmall

/-- Hahn–Banach makes restriction to a linearly isomorphic subspace onto. -/
theorem dual_restriction_surjective (M : Submodule 𝕜 E)
    (U : SequenceLp 𝕜 1 ≃L[𝕜] M) :
    Function.Surjective (fun f : E →L[𝕜] 𝕜 =>
      f.comp (M.subtypeL.comp U.toContinuousLinearMap)) := by
  intro g
  obtain ⟨f, hf, _⟩ := C05NormExtension.norm_preserving_extension 𝕜 E M
    (g.comp U.symm.toContinuousLinearMap)
  refine ⟨f, ?_⟩
  ext x
  simpa using hf (U x)

/-- Every normed space with separable continuous dual excludes a closed ℓ¹ copy. -/
theorem separable_dual_excludes_l1 [SeparableSpace (E →L[𝕜] 𝕜)] :
    ¬ Spec.ContainsClosedL1 𝕜 E := by
  rintro ⟨M, _, ⟨U⟩⟩
  let T : (E →L[𝕜] 𝕜) →L[𝕜] (SequenceLp 𝕜 1 →L[𝕜] 𝕜) :=
    (ContinuousLinearMap.compL 𝕜 (SequenceLp 𝕜 1) E 𝕜).flip
      (M.subtypeL.comp U.toContinuousLinearMap)
  have hT : Function.Surjective T := dual_restriction_surjective M U
  let : SeparableSpace (SequenceLp 𝕜 1 →L[𝕜] 𝕜) :=
    hT.denseRange.separableSpace T.continuous
  let V := FunctionSpaces.SequenceDuals.l1Duality (𝕜 := 𝕜)
  have hV : SeparableSpace (SequenceLInfinity 𝕜) :=
    V.symm.surjective.denseRange.separableSpace V.symm.continuous
  exact linfinity_not_separable hV

/-- A shrinking basis gives a countable dense linear span in the norm dual. -/
theorem shrinking_separable_dual [CompleteSpace E] (b : SchauderBasis 𝕜 E)
    (hb : IsShrinking b) : SeparableSpace (E →L[𝕜] 𝕜) := by
  have hs := ((Set.countable_range b.coord).isSeparable.span (R := 𝕜)).closure
  have ht := (DualBasisBasicity.shrinking_iff_dualSpan b).mp hb
  change TopologicalSpace.IsSeparable (dualSpan b : Set (E →L[𝕜] 𝕜)) at hs
  change dualSpan b = ⊤ at ht
  rw [ht] at hs
  exact isSeparable_univ_iff.mp hs

/-- The forward implication does not need unconditionality. -/
theorem shrinking_excludes_l1 : Spec.ShrinkingExcludesL1 := by
  intro 𝕜 E _ _ _ _ b hb
  let := shrinking_separable_dual b hb
  exact separable_dual_excludes_l1

/-- Finite and empty bases have separable dual and no closed ℓ¹ copy. -/
theorem finite_shrinking_criterion : Spec.FiniteShrinkingCriterion := by
  intro 𝕜 E _ _ _ _ d b
  have hs := ((Set.countable_range b.coord).isSeparable.span (R := 𝕜)).closure
  have ht := (DualBasisBasicity.finite_dual_facts b).2.1
  change TopologicalSpace.IsSeparable
    ((Submodule.span 𝕜 (Set.range b.coord)).topologicalClosure : Set (E →L[𝕜] 𝕜)) at hs
  rw [ht] at hs
  let : SeparableSpace (E →L[𝕜] 𝕜) := isSeparable_univ_iff.mp hs
  exact ⟨fun _ => separable_dual_excludes_l1, fun _ => DualBases.finite_shrinking b⟩


/-- A bound on all sub-sums controls the absolute sum of real scalars. -/
lemma real_sum_abs_le {ι : Type*} (s : Finset ι) (z : ι → ℝ) (B : ℝ)
    (h : ∀ t ⊆ s, |∑ i ∈ t, z i| ≤ B) :
    (∑ i ∈ s, |z i|) ≤ 2 * B := by
  classical
  have hp := (le_abs_self _).trans (h (s.filter (fun i => 0 ≤ z i)) (Finset.filter_subset _ _))
  have hn := (neg_le_abs _).trans (h (s.filter (fun i => ¬ 0 ≤ z i)) (Finset.filter_subset _ _))
  have he : (∑ i ∈ s, |z i|) =
      (∑ i ∈ s.filter (fun i => 0 ≤ z i), z i) -
      (∑ i ∈ s.filter (fun i => ¬ 0 ≤ z i), z i) := by
    simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 ≤ z i
    · simp [hi, abs_of_nonneg hi]
    · simp [hi, abs_of_neg (lt_of_not_ge hi)]
  linarith

/-- Four sub-sum bounds suffice over either scalar field. -/
lemma scalar_sum_norm_le {ι : Type*} (s : Finset ι) (z : ι → 𝕜) (B : ℝ)
    (h : ∀ t ⊆ s, ‖∑ i ∈ t, z i‖ ≤ B) :
    (∑ i ∈ s, ‖z i‖) ≤ 4 * B := by
  have hr := real_sum_abs_le s (fun i => RCLike.re (z i)) B (by
    intro t ht
    simpa using (RCLike.abs_re_le_norm (∑ i ∈ t, z i)).trans (h t ht))
  have hi := real_sum_abs_le s (fun i => RCLike.im (z i)) B (by
    intro t ht
    simpa using (RCLike.abs_im_le_norm (∑ i ∈ t, z i)).trans (h t ht))
  have he : (∑ i ∈ s, ‖z i‖) ≤
      (∑ i ∈ s, |RCLike.re (z i)|) + (∑ i ∈ s, |RCLike.im (z i)|) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hn := norm_nonneg (z i)
    have hp := mul_nonneg (abs_nonneg (RCLike.re (z i))) (abs_nonneg (RCLike.im (z i)))
    nlinarith [RCLike.norm_sq_eq_def (z := z i), sq_abs (RCLike.re (z i)),
      sq_abs (RCLike.im (z i)), abs_nonneg (RCLike.re (z i)), abs_nonneg (RCLike.im (z i))]
  linarith

/-- Disjoint coordinate supports let an ambient subset projection select
arbitrary subfamilies of the blocks. No ordering of the supports is needed. -/
lemma block_subsum_bound [CompleteSpace E] (b : UnconditionalSchauderBasis ℕ 𝕜 E)
    (u : ℕ → E)
    (hu : ∀ i j, i ≠ j → ∀ n, b.coord n (u i) = 0 ∨ b.coord n (u j) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s t : Finset ℕ) (a : ℕ → 𝕜), t ⊆ s →
      ‖∑ i ∈ t, a i • u i‖ ≤ C * ‖∑ i ∈ s, a i • u i‖ := by
  classical
  obtain ⟨P, _, hcoord, _, _, ⟨C, hC0, hC⟩, _⟩ := C15SubsetProjections.native_subset_projections b
  refine ⟨C, hC0, fun s t a hts => ?_⟩
  let A : Set ℕ := {n | ∃ i ∈ t, b.coord n (u i) ≠ 0}
  have he (i : ℕ) : P A (u i) = if i ∈ t then u i else 0 := by
    apply C15SubsetProjections.SubsetProjectionProof.ext_coordinates b
    intro n
    have hc := hcoord A (u i) n
    dsimp only at hc
    rw [hc]
    by_cases hit : i ∈ t
    · rw [ite_eq_left hit]
      by_cases hn : n ∈ A
      · rw [ite_eq_left hn]
      · rw [ite_eq_right hn]
        exact (by_contra fun hz => hn ⟨i, hit, Ne.symm hz⟩)
    · rw [ite_eq_right hit, map_zero]
      by_cases hn : n ∈ A
      · rw [ite_eq_left hn]
        obtain ⟨j, hj, hjn⟩ := hn
        exact (hu i j (by intro hij; exact hit (hij ▸ hj)) n).resolve_right hjn
      · rw [ite_eq_right hn]
  have hsum : P A (∑ i ∈ s, a i • u i) = ∑ i ∈ t, a i • u i := by
    simp only [map_sum, map_smul, he, smul_ite, smul_zero]
    rw [← Finset.sum_filter]
    exact Finset.sum_congr (Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hts))
      (fun _ _ => rfl)
  rw [← hsum]
  exact ((P A).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hC A) (norm_nonneg _))


/-- The canonical ℓ¹ finite-synthesis norm is the sum of coefficient moduli. -/
lemma norm_l1_synthesis (a : ℕ →₀ 𝕜) :
    ‖Finsupp.linearCombination 𝕜 (fun n => lp.single (E := fun _ : ℕ => 𝕜) 1 n 1) a‖ =
      ∑ i ∈ a.support, ‖a i‖ := by
  have he (n : ℕ) : a n • (lp.single (E := fun _ : ℕ => 𝕜) 1 n 1) =
      lp.single 1 n (a n) := by rw [← lp.single_smul]; simp
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, he]
  simpa using lp.norm_sum_single (E := fun _ : ℕ => 𝕜) (p := 1)
    (by simp) (fun n => a n) a.support

/-- Two-sided ℓ¹ estimates identify the whole closed span with ℓ¹. -/
lemma contains_l1_of_sum_bounds [CompleteSpace E] (u : ℕ → E)
    (h : ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ a : ℕ →₀ 𝕜,
      c * (∑ i ∈ a.support, ‖a i‖) ≤ ‖Finsupp.linearCombination 𝕜 u a‖ ∧
      ‖Finsupp.linearCombination 𝕜 u a‖ ≤ C * (∑ i ∈ a.support, ‖a i‖)) :
    Spec.ContainsClosedL1 𝕜 E := by
  let e : ℕ → SequenceLp 𝕜 1 := fun n => lp.single 1 n 1
  have hb : EquivalentBases.Spec.FiniteSumBounds (𝕜 := 𝕜) e u := by
    obtain ⟨c, C, hc, hcC, h⟩ := h
    exact ⟨c, C, hc, hcC, fun a => by simpa only [e, norm_l1_synthesis] using h a⟩
  obtain ⟨U, _⟩ := (EquivalentBases.equivalentFamilies_iff e u).mpr hb
  have ht : EquivalentBases.Spec.closedSpan (𝕜 := 𝕜) e = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
      (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ∞) x)
    apply Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro i _
    have hi := Submodule.smul_mem (EquivalentBases.Spec.closedSpan (𝕜 := 𝕜) e)
      (x i) (EquivalentBases.Spec.spanVector e i).property
    simpa only [EquivalentBases.Spec.spanVector, EquivalentBases.Spec.closedSpan, e, ← lp.single_smul, smul_eq_mul, mul_one] using hi
  let V : EquivalentBases.Spec.closedSpan (𝕜 := 𝕜) e ≃L[𝕜] SequenceLp 𝕜 1 :=
    (ContinuousLinearEquiv.ofEq _ ⊤ ht).trans Submodule.topContEquiv
  exact ⟨EquivalentBases.Spec.closedSpan (𝕜 := 𝕜) u,
    Submodule.isClosed_topologicalClosure _, ⟨V.symm.trans U⟩⟩

/-- A functional uniformly detects disjoint blocks of an unconditional basis
only if their closed span is a copy of ℓ¹. -/
theorem contains_l1_of_disjoint_blocks [CompleteSpace E]
    (b : UnconditionalSchauderBasis ℕ 𝕜 E) (u : ℕ → E)
    (hu : ∀ i j, i ≠ j → ∀ n, b.coord n (u i) = 0 ∨ b.coord n (u j) = 0)
    (hunit : ∀ i, ‖u i‖ ≤ 1) (f : E →L[𝕜] 𝕜) {δ : ℝ}
    (hδ : 0 < δ) (hf : ∀ i, δ ≤ ‖f (u i)‖) :
    Spec.ContainsClosedL1 𝕜 E := by
  obtain ⟨C, hC0, hC⟩ := block_subsum_bound b u hu
  let D := 4 * ‖f‖ * C + 1
  have hD : 0 < D := by dsimp [D]; positivity
  apply contains_l1_of_sum_bounds u
  refine ⟨δ / D, max (δ / D) 1, div_pos hδ hD, le_max_left _ _, fun a => ?_⟩
  let s := a.support
  let y := Finsupp.linearCombination 𝕜 u a
  have hsub : ∀ t ⊆ s, ‖∑ i ∈ t, a i * f (u i)‖ ≤ ‖f‖ * C * ‖y‖ := by
    intro t ht
    have he : (∑ i ∈ t, a i * f (u i)) = f (∑ i ∈ t, a i • u i) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [he]
    exact (f.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (hC s t a ht)
      (norm_nonneg f)).trans_eq (by
        simp only [s, y, Finsupp.linearCombination_apply, Finsupp.sum]
        ring))
  have hl : δ * (∑ i ∈ s, ‖a i‖) ≤ 4 * (‖f‖ * C * ‖y‖) := by
    calc
      _ = ∑ i ∈ s, ‖a i‖ * δ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ ∑ i ∈ s, ‖a i * f (u i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hf i) (norm_nonneg _)
      _ ≤ _ := scalar_sum_norm_le s _ _ hsub
  constructor
  · change δ / D * (∑ i ∈ s, ‖a i‖) ≤ ‖y‖
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hD).mpr
    dsimp [D]
    nlinarith [norm_nonneg y]
  · have hh : ‖y‖ ≤ ∑ i ∈ s, ‖a i‖ := by
      change ‖∑ i ∈ s, a i • u i‖ ≤ _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hunit i)
    exact hh.trans (le_mul_of_one_le_left (Finset.sum_nonneg (by intros; positivity))
      (le_max_right _ _))


/-- Coordinate evaluation of an ordered projection. -/
lemma coord_ordered_projection (b : SchauderBasis 𝕜 E) (N j : ℕ) (x : E) :
    b.coord j (b.proj N x) = if j < N then b.coord j x else 0 := by
  change ((b.coord j).comp (b.proj N)) x = _
  rw [DualBasisBasicity.coord_projection]
  by_cases hj : j < N <;> simp only [hj, reduceIte, zero_apply]

/-- A nonshrinking basis has uniformly detected, bounded, disjoint finite
coordinate blocks. This part does not use unconditionality. -/
theorem disjoint_blocks_of_not_shrinking [CompleteSpace E] (b : SchauderBasis 𝕜 E)
    (hn : ¬ IsShrinking b) :
    ∃ (u : ℕ → E) (f : E →L[𝕜] 𝕜) (δ : ℝ), 0 < δ ∧
      (∀ i, ‖u i‖ ≤ 1) ∧ (∀ i, δ ≤ ‖f (u i)‖) ∧
      ∀ i j, i ≠ j → ∀ n, b.coord n (u i) = 0 ∨ b.coord n (u j) = 0 := by
  classical
  have hF : dualSpan b ≠ ⊤ := by
    intro h
    exact hn ((DualBasisBasicity.shrinking_iff_dualSpan b).mpr h)
  obtain ⟨f, hf⟩ : ∃ f : E →L[𝕜] 𝕜, f ∉ dualSpan b := by
    by_contra! h
    exact hF (eq_top_iff.mpr fun f _ => h f)
  have hclosed : IsClosed (dualSpan b : Set (E →L[𝕜] 𝕜)) :=
    Submodule.isClosed_topologicalClosure _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl f hf
  have hgap (N : ℕ) : ε ≤ ‖f - f.comp (b.proj N)‖ := by
    by_contra! h
    have hx : f.comp (b.proj N) ∈ Metric.ball f ε := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using h
    exact hball hx (DualBasisBasicity.dualProjection_mem b N f)
  obtain ⟨C, hC⟩ := b.exists_norm_proj_le
  have hC0 : 0 ≤ C := (norm_nonneg (b.proj 0)).trans (hC 0)
  let D : ℝ := C * (1 + C) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let δ : ℝ := D⁻¹ * (ε / 4)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hstep (N : ℕ) : ∃ (M : ℕ) (u : E), N < M ∧ ‖u‖ ≤ 1 ∧
      δ ≤ ‖f u‖ ∧ b.proj N u = 0 ∧ b.proj M u = u := by
    obtain ⟨x, hx, hfx⟩ := (f - f.comp (b.proj N)).exists_lt_apply_of_lt_opNorm
      ((half_lt_self hε).trans_le (hgap N))
    let y := x - b.proj N x
    have hy0 : b.proj N y = 0 := by simp only [y, map_sub, b.proj_comp, min_self, sub_self]
    have hy : ‖y‖ ≤ 1 + C := by
      calc
        _ ≤ ‖x‖ + ‖b.proj N x‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + C * ‖x‖ := by
          gcongr
          exact ((b.proj N).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right (hC N) (norm_nonneg x))
        _ ≤ 1 + C := by nlinarith
    have hfy : ε / 2 < ‖f y‖ := by simpa only [y, map_sub, sub_apply,
      ContinuousLinearMap.comp_apply] using hfx
    have ht : Tendsto (fun M => ‖f (b.proj M y)‖) atTop (𝓝 ‖f y‖) :=
      ((f.continuous.tendsto y).comp (b.tendsto_proj y)).norm
    have hev : ∀ᶠ M in atTop, ε / 4 < ‖f (b.proj M y)‖ :=
      ht.eventually (eventually_gt_nhds (by linarith))
    obtain ⟨M, hM, hMN⟩ := (hev.and (eventually_gt_atTop N)).exists
    let u : E := ((D⁻¹ : ℝ) : 𝕜) • b.proj M y
    have hu_norm : ‖u‖ = D⁻¹ * ‖b.proj M y‖ := by
      simp only [u, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hD)]
    have hfu_norm : ‖f u‖ = D⁻¹ * ‖f (b.proj M y)‖ := by
      simp only [u, map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hD)]
    refine ⟨M, u, hMN, ?_, ?_, ?_, ?_⟩
    · rw [hu_norm]
      have hb : ‖b.proj M y‖ ≤ C * (1 + C) :=
        ((b.proj M).le_opNorm y).trans
          ((mul_le_mul_of_nonneg_right (hC M) (norm_nonneg y)).trans
            (mul_le_mul_of_nonneg_left hy hC0))
      calc
        _ ≤ D⁻¹ * (C * (1 + C)) := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hD).le
        _ ≤ D⁻¹ * D := mul_le_mul_of_nonneg_left (by dsimp [D]; linarith) (inv_pos.mpr hD).le
        _ = 1 := inv_mul_cancel₀ hD.ne'
    · rw [hfu_norm]
      exact mul_le_mul_of_nonneg_left hM.le (inv_pos.mpr hD).le
    · simp only [u, map_smul, b.proj_comp, min_eq_left hMN.le, hy0, smul_zero]
    · simp only [u, map_smul, b.proj_comp, min_self]
  choose M u hM hu hf hu0 hu1 using hstep
  let p : ℕ → ℕ := Nat.rec 0 (fun _ N => M N)
  have hp_succ (n : ℕ) : p (n + 1) = M (p n) := rfl
  have hp : StrictMono p := strictMono_nat_of_lt_succ (fun n => by
    rw [hp_succ]
    exact hM (p n))
  have hsupp (i n : ℕ) (hi : b.coord n (u (p i)) ≠ 0) :
      p i ≤ n ∧ n < p (i + 1) := by
    constructor
    · by_contra! hn
      have hh := congrArg (fun x => b.coord n x) (hu0 (p i))
      rw [coord_ordered_projection, ite_eq_left hn, map_zero] at hh
      exact hi hh
    · rw [hp_succ]
      by_contra! hn
      have hh := congrArg (fun x => b.coord n x) (hu1 (p i))
      rw [coord_ordered_projection, ite_eq_right (Nat.not_lt.mpr hn)] at hh
      exact hi hh.symm
  refine ⟨fun i => u (p i), f, δ, hδ, fun i => hu (p i), fun i => hf (p i), ?_⟩
  intro i j hij n
  by_cases hi : b.coord n (u (p i)) = 0
  · exact Or.inl hi
  by_cases hj : b.coord n (u (p j)) = 0
  · exact Or.inr hj
  have hsi := hsupp i n hi
  have hsj := hsupp j n hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hle : i + 1 ≤ j := by omega
    have hh := hp.monotone hle
    omega
  · have hle : j + 1 ≤ i := by omega
    have hh := hp.monotone hle
    omega


/-- James's ℓ¹ obstruction: shrinking is equivalent to exclusion of every
closed subspace isomorphic to ℓ¹, for an unconditional Schauder basis. -/
theorem shrinking_criterion : Spec.ShrinkingCriterion := by
  intro 𝕜 E _ _ _ _ b hu
  constructor
  · exact shrinking_excludes_l1 b
  · intro hno
    by_contra hn
    obtain ⟨u, f, δ, hδ, hunit, hf, hdisj⟩ := disjoint_blocks_of_not_shrinking b hn
    let bu : UnconditionalSchauderBasis ℕ 𝕜 E :=
      { basis := b.basis
        coord := b.coord
        ortho := b.ortho
        expansion := by
          intro x
          have hh := (hu x).hasSum
          have heq : (∑' n, b.coord n x • b n) = x := by
            apply tendsto_nhds_unique hh.tendsto_sum_nat
            simpa only [SchauderBasis.proj_apply] using b.tendsto_proj x
          rwa [heq] at hh }
    exact hno (contains_l1_of_disjoint_blocks bu u hdisj hunit f hδ hf)

/-- Full source statement from the raw unconditional-basis property. -/
theorem raw_shrinking_criterion : Spec.RawShrinkingCriterion := by
  intro 𝕜 E _ _ _ _ e hu
  let h := (C15SubsetProjections.rawBasis_iff_uniqueOrderedExpansions e).mpr hu.1
  obtain ⟨b, hb, hc, _⟩ := C15CoordinateContinuity.raw_native_basis h
  refine ⟨b, hb, shrinking_criterion b ?_⟩
  intro x
  have hx := (C15Unconditional.isUnconditionalSchauderBasis_iff 𝕜 E e).mp hu |>.2
    x (C15Basis.Spec.rawCoordinates h x)
    ((C01Banach.hasSequentialSum_iff E _ x).mpr (C15Basis.rawCoordinates_tendsto h x))
  have hs := (C15Unconditional.hasUnconditionalSum_iff_hasSum _ _).mp hx |>.summable
  simpa only [hb, hc] using hs

/-- The genuine finite raw-basis formulation includes zero-dimensional spaces. -/
theorem raw_finite_shrinking_criterion : Spec.RawFiniteShrinkingCriterion := by
  intro 𝕜 E _ _ _ _ d e h
  obtain ⟨b, hb, _⟩ := C15CoordinateContinuity.finite_native_basis h
  exact ⟨b, hb, finite_shrinking_criterion b⟩

end ExpandedFA.P1.UnconditionalL1Obstruction
