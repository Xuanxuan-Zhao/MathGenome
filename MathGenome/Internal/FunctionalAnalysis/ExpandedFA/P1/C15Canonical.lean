import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15Canonical
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15Basis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01ExamplesComplete
import Mathlib.Tactic.NormNum

/-! Proof of the complete standard-bases proposition, paper.tex 3941–3967.
The native sequence spaces and algebraic expansion predicate are those of the
accepted upstream interfaces. No automatic continuity of arbitrary raw bases
is needed: evaluations and canonical truncations are bounded directly. -/

open Filter Topology TopologicalSpace
open scoped BigOperators ENNReal
noncomputable section
universe u v
namespace ExpandedFA.P1.C15Canonical
open C01SequenceSpaces C15Basis C01ExamplesComplete

noncomputable abbrev c0Unit := Spec.c0Unit
namespace CanonicalSequenceBasesProof
variable {𝕜 : Type u} [RCLike 𝕜]

/-- Evaluating an ordered finite synthesis retains precisely the first N coordinates. -/
lemma lp_partialSum_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ℕ → 𝕜) (N j : ℕ) :
    orderedPartialSum (fun n => lp.single (E := fun _ : ℕ => 𝕜) p n 1) a N j =
      if j < N then a j else 0 := by
  classical
  simp only [orderedPartialSum, C15Basis.Spec.orderedPartialSum,
    ← lp.single_smul, smul_eq_mul, mul_one, lp.coeFn_sum, Finset.sum_apply,
    lp.single_apply, Finset.sum_pi_single, Finset.mem_range]

lemma c0_partialSum_apply (a : ℕ → 𝕜) (N j : ℕ) :
    (orderedPartialSum (c0Unit 𝕜) a N).val j = if j < N then a j else 0 := by
  have he (n) : (c0Unit 𝕜 n).val = lp.single ∞ n (1 : 𝕜) := rfl
  change (∑ i ∈ Finset.range N, a i • c0Unit 𝕜 i).val j = _
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul_of_tower, he]
  exact lp_partialSum_apply ∞ a N j

lemma lp_expansion (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (x : SequenceLp 𝕜 p) :
    Tendsto (orderedPartialSum (fun n => lp.single p n (1 : 𝕜)) (fun n => x n))
      atTop (𝓝 x) := by
  have he (n : ℕ) : x n • lp.single p n (1 : 𝕜) = lp.single (E := fun _ : ℕ => 𝕜) p n (x n) := by
    rw [← lp.single_smul]
    simp
  change Tendsto (fun N => ∑ i ∈ Finset.range N, x i • lp.single (E := fun _ : ℕ => 𝕜) p i (1 : 𝕜)) atTop (𝓝 x)
  simp_rw [he]
  exact (lp.hasSum_single hp x).tendsto_sum_nat

lemma c0_expansion (x : SequenceC0 𝕜) :
    Tendsto (orderedPartialSum (c0Unit 𝕜) (fun n => x.val n)) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp x.property (ε / 2) (half_pos hε)
  refine ⟨M, fun N hN => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  change ‖(orderedPartialSum (c0Unit 𝕜) (fun n => x.val n) N).val - x.val‖ ≤ ε / 2
  apply lp.norm_le_of_forall_le (half_pos hε).le
  intro j
  change ‖(orderedPartialSum (c0Unit 𝕜) (fun n => x.val n) N).val j - x.val j‖ ≤ ε / 2
  rw [c0_partialSum_apply]
  split_ifs with hj
  · simp only [sub_self, norm_zero]
    exact (half_pos hε).le
  · simpa using (hM j (hN.trans (Nat.le_of_not_gt hj))).le

/-- Coordinate continuity forces uniqueness of any ordered convergent expansion. -/
lemma lp_expansion_unique (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : SequenceLp 𝕜 p)
    (a : ℕ → 𝕜)
    (ha : Tendsto (orderedPartialSum (fun n => lp.single p n (1 : 𝕜)) a) atTop (𝓝 x)) :
    a = fun n => x n := by
  funext j
  have h := (lp.lipschitzWith_one_eval p j).continuous.continuousAt.tendsto.comp ha
  apply tendsto_nhds_unique _ h
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with N hN
  exact (lp_partialSum_apply p a N j).trans (ite_eq_left hN) |>.symm

lemma c0_expansion_unique (x : SequenceC0 𝕜) (a : ℕ → 𝕜)
    (ha : Tendsto (orderedPartialSum (c0Unit 𝕜) a) atTop (𝓝 x)) :
    a = fun n => x.val n := by
  funext j
  have h := (lp.lipschitzWith_one_eval ∞ j).continuous.continuousAt.tendsto.comp
    (continuous_subtype_val.tendsto x |>.comp ha)
  apply tendsto_nhds_unique _ h
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop j] with N hN
  exact (c0_partialSum_apply a N j).trans (ite_eq_left hN) |>.symm

end CanonicalSequenceBasesProof
open CanonicalSequenceBasesProof

theorem canonical_lp_basis : Spec.LpBasis.{u} := by
  intro 𝕜 _ p _ hp
  constructor
  · intro n hn
    have hz := congrArg (fun x : SequenceLp 𝕜 p => x n) hn
    simp at hz
  · intro x
    exact ⟨(fun n => x n), lp_expansion p hp x, fun a ha => lp_expansion_unique p x a ha⟩

theorem canonical_c0_basis : Spec.C0Basis.{u} := by
  intro 𝕜 _
  constructor
  · intro n hn
    have hz := congrArg (fun x : SequenceC0 𝕜 => x.val n) hn
    simp [Spec.c0Unit] at hz
  · intro x
    exact ⟨(fun n => x.val n), c0_expansion x, fun a ha => c0_expansion_unique x a ha⟩

theorem canonical_lp_coordinates : Spec.LpCoordinates.{u} := by
  intro 𝕜 _ p _ hp h x n
  exact congrFun (lp_expansion_unique p x _ (rawCoordinates_tendsto h x)) n

theorem canonical_c0_coordinates : Spec.C0Coordinates.{u} := by
  intro 𝕜 _ h x n
  exact congrFun (c0_expansion_unique x _ (rawCoordinates_tendsto h x)) n

namespace CanonicalSequenceBasesProof

/-- A contracting family of algebraic truncations that fixes a unit vector
has exactly the source basis constant one. No completeness is needed here. -/
lemma constant_one_of_contractive {𝕜 E : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {e : ℕ → E}
    (h : IsRawSchauderBasis (𝕜 := 𝕜) e)
    (hb : ∀ N x, ‖rawPartialSum h N x‖ ≤ ‖x‖)
    (v : E) (hv : ‖v‖ = 1)
    (hfix : ∀ N, rawPartialSum h (N + 1) v = v) : Spec.ConstantOne h := by
  let T (N : ℕ) : E →L[𝕜] E := (rawPartialSumLinearMap h N).mkContinuous 1
    (fun x => by simpa only [one_mul, rawPartialSumLinearMap_apply] using hb N x)
  have hT (N x) : T N x = rawPartialSum h N x := rfl
  have hle (N) : ‖T N‖ ≤ 1 :=
    (T N).opNorm_le_bound zero_le_one (fun x => by simpa only [hT, one_mul] using hb N x)
  have hnorm (N) : ‖T (N + 1)‖ = 1 := by
    apply le_antisymm (hle _) 
    have hh := (T (N + 1)).le_opNorm v
    simpa only [hT, hfix, hv, mul_one] using hh
  have hbound : BddAbove (Set.range fun N => ‖T N‖) :=
    ⟨1, by rintro _ ⟨N, rfl⟩; exact hle N⟩
  refine ⟨T, hT, ?_, hnorm, hbound, ?_⟩
  · ext x
    exact rawPartialSum_zero h x
  · apply le_antisymm (ciSup_le hle)
    exact (hnorm 0).symm.le.trans (le_ciSup hbound 1)

end CanonicalSequenceBasesProof

theorem canonical_lp_basis_constant : Spec.LpBasisConstant.{u} := by
  intro 𝕜 _ p _ hp h
  have hp0 : 0 < p := zero_lt_one.trans_le (Fact.out : 1 ≤ p)
  have hval (N : ℕ) (x : SequenceLp 𝕜 p) (j : ℕ) :
      rawPartialSum h N x j = if j < N then x j else 0 := by
    change orderedPartialSum (fun n => lp.single (E := fun _ : ℕ => 𝕜) p n 1) (rawCoordinates h x) N j = _
    rw [lp_partialSum_apply]
    exact congrArg (fun z : 𝕜 => if j < N then z else 0)
      (canonical_lp_coordinates 𝕜 p hp h x j)
  let v : SequenceLp 𝕜 p := lp.single p 0 1
  apply constant_one_of_contractive h ?_ v ?_ ?_
  · intro N x
    apply lp.norm_mono hp0.ne'
    intro j
    rw [hval]
    split_ifs <;> simp
  · simpa [v] using lp.norm_single (E := fun _ : ℕ => 𝕜) hp0 0 (1 : 𝕜)
  · intro N
    apply lp.ext
    funext j
    rw [hval]
    by_cases hj : j < N + 1
    · simp [hj]
    · simp only [hj, ite_false]
      exact (lp.single_apply_ne (E := fun _ : ℕ => 𝕜) p 0 1 (by omega)).symm

theorem canonical_c0_basis_constant : Spec.C0BasisConstant.{u} := by
  intro 𝕜 _ h
  have hval (N : ℕ) (x : SequenceC0 𝕜) (j : ℕ) :
      (rawPartialSum h N x).val j = if j < N then x.val j else 0 := by
    change (orderedPartialSum (c0Unit 𝕜) (rawCoordinates h x) N).val j = _
    rw [c0_partialSum_apply]
    exact congrArg (fun z : 𝕜 => if j < N then z else 0)
      (canonical_c0_coordinates 𝕜 h x j)
  apply constant_one_of_contractive h ?_ (c0Unit 𝕜 0) ?_ ?_
  · intro N x
    change ‖(rawPartialSum h N x).val‖ ≤ ‖x.val‖
    apply lp.norm_mono ENNReal.top_ne_zero
    intro j
    rw [hval]
    split_ifs <;> simp
  · change ‖lp.single (E := fun _ : ℕ => 𝕜) ∞ 0 1‖ = 1
    simp
  · intro N
    apply Subtype.ext
    apply lp.ext
    funext j
    rw [hval]
    by_cases hj : j < N + 1
    · simp [hj]
    · simp only [hj, ite_false]
      exact (lp.single_apply_ne (E := fun _ : ℕ => 𝕜) ∞ 0 1 (by omega)).symm

/-- The closure is taken in the native supremum norm on bounded sequences. -/
theorem canonical_closed_span_in_linfinity :
    Spec.ClosedSpanInLInfinity.{u} := by
  intro 𝕜 _
  let S : Submodule 𝕜 (SequenceLInfinity 𝕜) :=
    Submodule.span 𝕜 (Set.range fun n : ℕ => lp.single ∞ n (1 : 𝕜))
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩
      exact (c0Unit 𝕜 n).property
    · exact sequence_c0_closed 𝕜
  · intro x hx
    let y : SequenceC0 𝕜 := ⟨x, hx⟩
    have hc : Tendsto (fun N => (orderedPartialSum (c0Unit 𝕜) (fun n => x n) N).val)
        atTop (𝓝 x) := continuous_subtype_val.tendsto y |>.comp (c0_expansion y)
    apply S.isClosed_topologicalClosure.mem_of_tendsto hc
    apply Filter.Eventually.of_forall
    intro N
    apply S.le_topologicalClosure
    change (∑ i ∈ Finset.range N, x i • c0Unit 𝕜 i).val ∈ S
    rw [Submodule.coe_sum]
    apply Submodule.sum_mem
    intro i hi
    exact S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)

namespace SchauderSeparabilityBoundaryProof

/-- Real and imaginary coordinates give separability uniformly for RCLike. -/
lemma scalar_separable (𝕜 : Type u) [RCLike 𝕜] : SeparableSpace 𝕜 := by
  let f : ℝ × ℝ → 𝕜 := fun p => (p.1 : 𝕜) + (p.2 : 𝕜) * RCLike.I
  have hf : Continuous f :=
    (RCLike.continuous_ofReal.comp continuous_fst).add
      ((RCLike.continuous_ofReal.comp continuous_snd).mul_const _)
  have hs : Function.Surjective f := fun z =>
    ⟨(RCLike.re z, RCLike.im z), RCLike.re_add_im z⟩
  exact hs.denseRange.separableSpace hf

lemma countable_span_separable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s : Set E} (hs : s.Countable)
    (hd : Dense (Submodule.span 𝕜 s : Set E)) : SeparableSpace E := by
  let := scalar_separable 𝕜
  exact hd.isSeparable_iff.mp hs.isSeparable.span

end SchauderSeparabilityBoundaryProof
open SchauderSeparabilityBoundaryProof

theorem schauder_basis_separable :
    Spec.CountableBasisSeparable.{u,v} := by
  intro 𝕜 _ E _ _ e h
  apply countable_span_separable (𝕜 := 𝕜) (Set.countable_range e)
  intro x
  apply mem_closure_of_tendsto (rawCoordinates_tendsto h x)
  apply Filter.Eventually.of_forall
  intro N
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem finite_basis_separable :
    Spec.FiniteBasisSeparable.{u,v} := by
  intro 𝕜 _ E _ _ d e h
  apply countable_span_separable (𝕜 := 𝕜) (Set.countable_range e)
  intro x
  apply subset_closure
  rw [← finiteCoordinates_expansion h x]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

namespace SchauderSeparabilityBoundaryProof

lemma subsets_nat_not_countable : ¬ Countable (Set ℕ) := by
  intro h
  obtain ⟨f, hf⟩ := @exists_injective_nat (Set ℕ) h
  exact Function.cantor_injective f hf

end SchauderSeparabilityBoundaryProof

theorem linfinity_binary_separated_family :
    Spec.BinarySeparatedFamily.{u} := by
  classical
  intro 𝕜 _
  let F : Set ℕ → SequenceLInfinity 𝕜 := fun A =>
    ⟨(fun n => if n ∈ A then 1 else 0), memℓp_infty ⟨1, by
      rintro _ ⟨n, rfl⟩
      change ‖if n ∈ A then (1 : 𝕜) else 0‖ ≤ 1
      split_ifs <;> norm_num⟩⟩
  have hinj : Function.Injective F := by
    intro A B h
    ext n
    have hh := congrArg (fun x : SequenceLInfinity 𝕜 => x n) h
    change (if n ∈ A then (1 : 𝕜) else 0) = (if n ∈ B then 1 else 0) at hh
    by_cases ha : n ∈ A <;> by_cases hb : n ∈ B <;> simp_all
  have hdist (A B : Set ℕ) (hAB : A ≠ B) : dist (F A) (F B) = 1 := by
    rw [dist_eq_norm]
    apply le_antisymm
    · apply lp.norm_le_of_forall_le zero_le_one
      intro n
      change ‖(if n ∈ A then (1 : 𝕜) else 0) - (if n ∈ B then 1 else 0)‖ ≤ 1
      split_ifs <;> norm_num
    · obtain ⟨n, hn⟩ : ∃ n, ¬ (n ∈ A ↔ n ∈ B) := by
        exact not_forall.mp (fun h => hAB (Set.ext h))
      have hh := lp.norm_apply_le_norm ENNReal.top_ne_zero (F A - F B) n
      change ‖(if n ∈ A then (1 : 𝕜) else 0) - (if n ∈ B then 1 else 0)‖ ≤ _ at hh
      by_cases ha : n ∈ A <;> by_cases hb : n ∈ B <;> simp_all
  refine ⟨F, fun A n => rfl, hinj, hdist, ?_⟩
  intro hc
  have : (Set.univ : Set (Set ℕ)).Countable := by
    simpa only [Set.preimage_range] using hc.preimage hinj
  exact subsets_nat_not_countable (Set.countable_univ_iff.mp this)

theorem linfinity_nonseparable :
    Spec.LInfinityNonseparable.{u} := by
  intro 𝕜 _ hs
  let := hs
  obtain ⟨F, hcoord, hinj, hdist, hunc⟩ := linfinity_binary_separated_family 𝕜
  have hd : Pairwise (fun A B => Disjoint (Metric.ball (F A) (1/3))
      (Metric.ball (F B) (1/3))) := by
    intro A B hAB
    apply Metric.ball_disjoint_ball
    rw [hdist A B hAB]
    norm_num
  have hc : Countable (Set ℕ) := hd.countable_of_isOpen_disjoint
    (fun _ => Metric.isOpen_ball) (fun _ => Metric.nonempty_ball.mpr (by norm_num))
  exact subsets_nat_not_countable hc

theorem linfinity_no_schauder_basis :
    Spec.LInfinityNoBasis.{u} := by
  intro 𝕜 _
  exact ⟨fun e h => linfinity_nonseparable 𝕜 (schauder_basis_separable 𝕜 _ e h),
    fun d e h => linfinity_nonseparable 𝕜 (finite_basis_separable 𝕜 _ d e h)⟩

theorem standard_bases_and_separability_boundary :
    Spec.StandardBases.{u} := by
  exact ⟨canonical_lp_basis, canonical_c0_basis, canonical_lp_basis_constant,
    canonical_c0_basis_constant, canonical_closed_span_in_linfinity,
    linfinity_no_schauder_basis⟩

end ExpandedFA.P1.C15Canonical
