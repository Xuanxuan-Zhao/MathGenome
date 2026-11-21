import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WeakSequentialRelativeCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.SeparableWeakCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Embedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12ConvexClosure
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecificLimits.Basic

/-!
The sequential-to-compact direction of Eberlein–Šmulian.
Finite predual test sets norm each finite-dimensional bidual span. Recursively
approximating a weak-star closure point on all accumulated tests supplies a
sequence in A. Its weak subsequential limit lies in the pullback of the closed
bidual span; the uniform norming estimate then identifies that limit's image
with the original closure point. Alaoglu and the weak embedding finish the
argument without assuming that E is complete.
-/

namespace ExpandedFA.P1.WeakSequentialRelativeCompact
universe u v
set_option maxHeartbeats 800000
open Filter Set
open scoped Topology
noncomputable section

/-- An unbounded set supplies a sequence whose every subsequence is unbounded. -/
theorem sequential_norm_bounded : Spec.SequentialBoundedness.{u,v} := by
  intro 𝕜 E _ _ _ A hA
  classical
  by_contra h
  have hlarge : ∀ n : ℕ, ∃ x ∈ A, (n : ℝ) < ‖x‖ := by
    intro n
    by_contra! hn
    exact h ⟨n, Nat.cast_nonneg n, hn⟩
  choose s hs hn using hlarge
  obtain ⟨x, r, hr, hconv⟩ := hA s hs
  obtain ⟨C, _, hC⟩ := SeparableWeakCompact.weak_sequence_bounded 𝕜 E (s ∘ r) x hconv
  obtain ⟨n, hnC⟩ := exists_nat_gt C
  have hnr : (n : ℝ) ≤ (r n : ℝ) := by exact_mod_cast hr.id_le n
  have := hn (r n)
  have := hC n
  dsimp [Function.comp_def] at *
  linarith

/-- Compactness of the finite-dimensional unit sphere gives finitely many
predual evaluations with the same norming constant. -/
theorem finite_norming_tests : Spec.FiniteNormingTests.{u,v} := by
  intro 𝕜 X _ _ _ M _
  classical
  have hdist : ∀ z : M, dist z 0 = ‖z‖ := fun z =>
    (dist_eq_norm z 0).trans (congrArg (fun w : M => ‖w‖) (sub_zero z))
  let U : {f : X // ‖f‖ ≤ 1} → Set M :=
    fun f => {z | (1 : ℝ) / 2 < ‖(z : X →L[𝕜] 𝕜) f‖}
  have hU : ∀ f, IsOpen (U f) := by
    intro f
    apply isOpen_lt continuous_const
    exact (((ContinuousLinearMap.apply 𝕜 𝕜 f.val).continuous).comp
      M.subtypeL.continuous).norm
  have hcover : Metric.sphere (0 : M) 1 ⊆ ⋃ f, U f := by
    intro z hz
    have hz' : ‖(z : X →L[𝕜] 𝕜)‖ = 1 := by
      rw [Metric.mem_sphere, hdist] at hz
      exact hz
    obtain ⟨f, hf, hzf⟩ := (z : X →L[𝕜] 𝕜).exists_lt_apply_of_lt_opNorm
      (show (1 : ℝ) / 2 < ‖(z : X →L[𝕜] 𝕜)‖ by rw [hz']; norm_num)
    exact mem_iUnion.mpr ⟨⟨f, hf.le⟩, hzf⟩
  obtain ⟨F, hF⟩ := (isCompact_sphere (0 : M) 1).elim_finite_subcover U hU hcover
  refine ⟨F.image Subtype.val, ?_, ?_⟩
  · intro f hf
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hf
    exact f.property
  · intro z hz hne
    let zM : M := ⟨z, hz⟩
    let c : 𝕜 := ((‖z‖⁻¹ : ℝ) : 𝕜)
    have hp : 0 < ‖z‖ := norm_pos_iff.mpr hne
    have hc : ‖c‖ = ‖z‖⁻¹ := by
      simp [c]
    have hu : c • zM ∈ Metric.sphere (0 : M) 1 := by
      rw [Metric.mem_sphere, hdist]
      change ‖c • z‖ = 1
      rw [norm_smul c z, hc, inv_mul_cancel₀ hp.ne']
    obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp (hF hu)
    refine ⟨f.val, Finset.mem_image.mpr ⟨f, hf, rfl⟩, ?_⟩
    change (1 : ℝ) / 2 < ‖c • z f.val‖ at hzf
    rw [norm_smul, hc] at hzf
    have hm := mul_lt_mul_of_pos_left hzf hp
    have heq : ‖z‖ * (‖z‖⁻¹ * ‖z f.val‖) = ‖z f.val‖ := by
      rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    rw [heq] at hm
    linarith

/-- A point of the weak-star closure can be approximated on any finite
family of original dual vectors. -/
private theorem finite_approximation
    (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E)
    (Φ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    (hΦ : Φ ∈ @closure _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
      (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E '' A))
    (F : Finset (E →L[𝕜] 𝕜)) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ A, ∀ f ∈ F, ‖f x - Φ f‖ < ε := by
  have hb := C12WeakStar.weakStarTopology_nhds_basis 𝕜 (E →L[𝕜] 𝕜) Φ
  have hnhds := hb.mem_of_mem (i := (F, ε)) hε
  obtain ⟨_, htest, ⟨x, hx, rfl⟩⟩ :=
    (@mem_closure_iff_nhds _
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜)) _ _).mp hΦ _ hnhds
  exact ⟨x, hx, htest⟩

/-- The finite data retained after one stage of the construction. -/
private structure NormingStage (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Φ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) where
  points : Finset E
  tests : Finset (E →L[𝕜] 𝕜)
  test_norm : ∀ f ∈ tests, ‖f‖ ≤ 1
  norms : ∀ z ∈ Submodule.span 𝕜
    (insert Φ (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E '' (points : Set E))),
    z ≠ 0 → ∃ f ∈ tests, ‖z‖ < 2 * ‖z f‖

private theorem stage_exists
    (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (Φ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) (S : Finset E) :
    ∃ p : NormingStage 𝕜 E Φ, p.points = S := by
  let M : Submodule 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) := Submodule.span 𝕜
    (insert Φ (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E '' (S : Set E)))
  letI : AddCommGroup M := @Submodule.addCommGroup 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) _ _ _ M
  letI : Module 𝕜 M := @Submodule.module 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) _ _ _ M
  letI : FiniteDimensional 𝕜 M := FiniteDimensional.span_of_finite 𝕜
    ((S.finite_toSet.image _).insert Φ)
  obtain ⟨F, hF, hnorm⟩ := finite_norming_tests 𝕜 (E →L[𝕜] 𝕜) M
  exact ⟨⟨S, F, hF, hnorm⟩, rfl⟩

/-- A recursive construction in finite sets. Tests accumulate, so any test
chosen at a given stage controls all later selected points. -/
private theorem norming_construction
    (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E)
    (Φ : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
    (hΦ : Φ ∈ @closure _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
      (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E '' A)) :
    ∃ (s : ℕ → E) (p : ℕ → NormingStage 𝕜 E Φ),
      (∀ n, s n ∈ A) ∧ Monotone (fun n => (p n).points) ∧
      Monotone (fun n => (p n).tests) ∧
      (∀ n, s n ∈ (p (n+1)).points) ∧
      (∀ n f, f ∈ (p n).tests → ‖f (s n) - Φ f‖ < 1 / (n+1 : ℝ)) := by
  classical
  have hext : ∀ (p : NormingStage 𝕜 E Φ) (n : ℕ),
      ∃ q : NormingStage 𝕜 E Φ × E,
        p.points ⊆ q.1.points ∧ p.tests ⊆ q.1.tests ∧
        q.2 ∈ q.1.points ∧ q.2 ∈ A ∧
        (∀ f ∈ p.tests, ‖f q.2 - Φ f‖ < 1 / (n+1 : ℝ)) := by
    intro p n
    obtain ⟨x, hx, happrox⟩ := finite_approximation 𝕜 E A Φ hΦ p.tests
      (1 / (n+1 : ℝ)) (by positivity)
    obtain ⟨q, hq⟩ := stage_exists 𝕜 E Φ (insert x p.points)
    let q' : NormingStage 𝕜 E Φ :=
      { points := q.points
        tests := p.tests ∪ q.tests
        test_norm := by
          intro f hf
          rcases Finset.mem_union.mp hf with hf | hf
          · exact p.test_norm f hf
          · exact q.test_norm f hf
        norms := by
          intro z hz hne
          obtain ⟨f, hf, hzf⟩ := q.norms z hz hne
          exact ⟨f, Finset.mem_union_right _ hf, hzf⟩ }
    refine ⟨(q', x), ?_, ?_, ?_, hx, happrox⟩
    · dsimp [q']; rw [hq]; exact Finset.subset_insert _ _
    · exact Finset.subset_union_left
    · dsimp [q']; rw [hq]; exact Finset.mem_insert_self _ _
  choose next hnext using hext
  obtain ⟨p₀, _⟩ := stage_exists 𝕜 E Φ ∅
  let p : ℕ → NormingStage 𝕜 E Φ :=
    fun n => Nat.rec p₀ (fun n p => (next p n).1) n
  have hp : ∀ n, p (n+1) = (next (p n) n).1 := fun _ => rfl
  refine ⟨fun n => (next (p n) n).2, p, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; exact (hnext (p n) n).2.2.2.1
  · apply monotone_nat_of_le_succ
    intro n; rw [hp]; exact (hnext (p n) n).1
  · apply monotone_nat_of_le_succ
    intro n; rw [hp]; exact (hnext (p n) n).2.1
  · intro n; rw [hp]; exact (hnext (p n) n).2.2.1
  · intro n f hf; exact (hnext (p n) n).2.2.2.2 f hf

/-- A uniform norming constant persists sufficiently far to separate the
norm closure of an increasing union, even when the tests vary with n. -/
private theorem norming_closure_separates
    (𝕜 : Type u) (X : Type v) [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (M : ℕ → Submodule 𝕜 (X →L[𝕜] 𝕜)) (hM : Monotone M)
    (F : ℕ → Finset X) (hF : ∀ n f, f ∈ F n → ‖f‖ ≤ 1)
    (hnorm : ∀ n y, y ∈ M n → y ≠ 0 → ∃ f ∈ F n, ‖y‖ < 2 * ‖y f‖)
    (z : X →L[𝕜] 𝕜) (hz : z ∈ (⨆ n, M n).topologicalClosure)
    (hzero : ∀ n f, f ∈ F n → z f = 0) : z = 0 := by
  by_contra hne
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hne
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hz (‖z‖ / 4) (by positivity)
  obtain ⟨n, hyn⟩ := (Submodule.mem_iSup_of_directed M hM.directed_le).mp hy
  have hbound : ‖y‖ ≤ 2 * ‖y-z‖ := by
    by_cases hy0 : y = 0
    · rw [hy0, norm_zero]; positivity
    obtain ⟨f, hf, hyf⟩ := hnorm n y hyn hy0
    have heval : ‖y f‖ ≤ ‖y-z‖ := by
      calc
        ‖y f‖ = ‖(y-z) f‖ := by rw [sub_apply, hzero n f hf, sub_zero]
        _ ≤ ‖y-z‖ * ‖f‖ := (y-z).le_opNorm f
        _ ≤ ‖y-z‖ := mul_le_of_le_one_right (norm_nonneg _) (hF n f hf)
    linarith
  have hd : dist z y = ‖z-y‖ := dist_eq_norm z y
  rw [hd] at hdist
  have htri := norm_le_norm_sub_add z y
  rw [norm_sub_rev y z] at hbound
  linarith

/-- The finite-test construction forces every weak-star closure point to be
an evaluation at a vector of E. Completeness of E is never used. -/
theorem bidual_closure_in_range : Spec.BidualClosureInRange.{u,v} := by
  intro 𝕜 E _ _ _ A hA Φ hΦ
  classical
  let J := C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E
  obtain ⟨s, p, hsA, hpoints, htests, hsp, happrox⟩ :=
    norming_construction 𝕜 E A Φ hΦ
  let M : ℕ → Submodule 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    fun n => Submodule.span 𝕜 (insert Φ (J '' ((p n).points : Set E)))
  have hM : Monotone M := by
    intro n m hnm
    apply Submodule.span_mono
    exact insert_subset_insert (image_mono (hpoints hnm))
  letI : ContinuousAdd ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    @IsTopologicalAddGroup.toContinuousAdd ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      inferInstance inferInstance inferInstance
  let N : Submodule 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    @Submodule.topologicalClosure 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) _ _ _ _ _ _ (⨆ n, M n)
  have hΦN : Φ ∈ N := by
    apply (⨆ n, M n).le_topologicalClosure
    apply Submodule.mem_iSup_of_mem 0
    exact Submodule.subset_span (mem_insert _ _)
  have hsN : ∀ n, J (s n) ∈ N := by
    intro n
    apply (⨆ n, M n).le_topologicalClosure
    apply Submodule.mem_iSup_of_mem (n+1)
    exact Submodule.subset_span (mem_insert_of_mem _ (mem_image_of_mem J (hsp n)))
  let P : Submodule 𝕜 E := N.comap J.toLinearMap
  have hP : IsClosed (P : Set E) :=
    (⨆ n, M n).isClosed_topologicalClosure.preimage J.continuous
  have hPweak := C12ConvexClosure.isWeaklyClosed_of_isClosed_submodule 𝕜 E P hP
  obtain ⟨x, r, hr, hconv⟩ := hA s hsA
  have hxN : J x ∈ N := by
    let : TopologicalSpace E := Spec.weakTopology 𝕜 E
    exact hPweak.mem_of_tendsto hconv (Eventually.of_forall (fun n => hsN (r n)))
  have hequal : ∀ m f, f ∈ (p m).tests → f x = Φ f := by
    intro m f hf
    have ht : Tendsto (fun n => f (s n)) atTop (𝓝 (Φ f)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
        _ tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [eventually_ge_atTop m] with n hn
      exact (happrox n f (htests hn hf)).le
    have hx := C12BoundedSequences.weak_evaluation_tendsto 𝕜 E (s ∘ r) x hconv f
    exact tendsto_nhds_unique hx (ht.comp hr.tendsto_atTop)
  have hdiff : Φ - J x ∈ N :=
    @Submodule.sub_mem 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      inferInstance inferInstance inferInstance N Φ (J x) hΦN hxN
  have hz : Φ - J x = 0 := norming_closure_separates 𝕜 (E →L[𝕜] 𝕜) M hM
    (fun n => (p n).tests) (fun n => (p n).test_norm)
    (fun n => (p n).norms) (Φ - J x) hdiff (by
      intro n f hf
      change Φ f - f x = 0
      exact sub_eq_zero.mpr (hequal n f hf).symm)
  exact ⟨x, (sub_eq_zero.mp hz).symm⟩

/-- Once the bidual closure is in the canonical range, Alaoglu and the
weak embedding transport compactness back to E. -/
theorem compact_closure_of_bidual_range
    (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (A : Set E)
    (hbounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ A, ‖x‖ ≤ C)
    (hRange : @closure ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)
      (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜))
      (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E '' A) ⊆
        Set.range (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E)) :
    @IsCompact E (Spec.weakTopology 𝕜 E)
      (@closure E (Spec.weakTopology 𝕜 E) A) := by
  let J := C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E
  let B : ℝ → Set ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) := fun C => {z | ‖z‖ ≤ C}
  obtain ⟨C, hC, hAC⟩ := hbounded
  have hball := C13Alaoglu.weakStar_closedBall_isCompact 𝕜 (E →L[𝕜] 𝕜)
    (0 : (E →L[𝕜] 𝕜) →L[𝕜] 𝕜) C hC
  simp only [sub_zero] at hball
  have hsub : J '' A ⊆ B C := by
    rintro _ ⟨x, hx, rfl⟩
    change ‖C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 E x‖ ≤ C
    rw [C05BidualIsometry.canonicalEvaluation_norm 𝕜 E x]
    exact hAC x hx
  have hEmbedding := C13Embedding.canonicalEvaluation_weak_embedding 𝕜 E
  let : TopologicalSpace ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (E →L[𝕜] 𝕜)
  have he : Topology.IsEmbedding
      (StrongDual.toWeakDual : ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) ≃ₗ[𝕜]
        WeakDual 𝕜 (E →L[𝕜] 𝕜)) :=
    ⟨⟨C12WeakStar.weakStarTopology_native 𝕜 (E →L[𝕜] 𝕜)⟩,
      StrongDual.toWeakDual.injective⟩
  letI : T2Space ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) := he.t2Space
  have hcompact : IsCompact (closure (J '' A)) :=
    hball.of_isClosed_subset isClosed_closure (closure_minimal hsub hball.isClosed)
  let : TopologicalSpace E := Spec.weakTopology 𝕜 E
  have hJ := hEmbedding
  rw [hJ.closure_eq_preimage_closure_image A]
  exact hJ.isInducing.isCompact_preimage' hcompact hRange

/-- The sequential-to-compact implication for arbitrary normed spaces. -/
theorem weak_closure_isCompact : Spec.SequentialRelativeCompactness.{u,v} := by
  intro 𝕜 E _ _ _ A hA
  exact compact_closure_of_bidual_range 𝕜 E A (sequential_norm_bounded 𝕜 E A hA)
    (bidual_closure_in_range 𝕜 E A hA)

end
end ExpandedFA.P1.WeakSequentialRelativeCompact
