import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C13Nonmetrizable
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13ConverseMetric
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! The concrete nonmetrizable compact ball and the two notions of separability,
from paper.tex 2650–2662. All spaces retain their original native norms. -/

noncomputable section
open scoped Classical
open TopologicalSpace Topology
open scoped ENNReal
universe u v
namespace ExpandedFA.P1.C13Nonmetrizable
open ExpandedFA.P1.C01SequenceSpaces
open ExpandedFA.FunctionSpaces.SequenceDuals

/-- The uncountable ℓ² example combines the orthonormal obstruction with
Alaoglu and the converse metrizability theorem for the same dual ball. -/
theorem uncountable_l2_dual_ball_example :
    Spec.UncountableL2Example.{u,v} := by
  intro I 𝕜 _ hI
  have hs : ¬ SeparableSpace (Spec.L2 𝕜 I) := by
    intro hsep
    let := hsep
    let e : HilbertBasis I 𝕜 (Spec.L2 𝕜 I) := ⟨LinearIsometryEquiv.refl 𝕜 _⟩
    have hd : Pairwise (fun i j =>
        Disjoint (Metric.ball (e i) (1 / 3 : ℝ))
          (Metric.ball (e j) (1 / 3 : ℝ))) := by
      intro i j hij
      apply Metric.ball_disjoint_ball
      have hsq : ‖e i - e j‖ ^ 2 = 2 := by
        rw [norm_sub_sq (𝕜 := 𝕜), e.orthonormal.norm_eq_one,
          e.orthonormal.norm_eq_one, e.orthonormal.inner_eq_zero hij]
        norm_num
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (e i - e j)]
    exact hI (hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
      (fun i => ⟨e i, by simp⟩))
  exact ⟨hs, C13Alaoglu.banach_alaoglu 𝕜 _, fun hm =>
    hs (C13ConverseMetric.separable_of_dual_ball_weakStar_metrizable 𝕜 _ hm)⟩

/-- The countable coordinate vectors have dense scalar-linear span in ℓ¹. -/
theorem l1_separable : Spec.L1Separable.{u} := by
  intro 𝕜 _
  let e : ℕ → SequenceLp 𝕜 1 := fun n => lp.single 1 n (1 : 𝕜)
  let M := Submodule.span 𝕜 (Set.range e)
  have hM : Dense (M : Set (SequenceLp 𝕜 1)) := by
    intro x
    apply mem_closure_of_tendsto (lp.hasSum_single (by simp : (1 : ℝ≥0∞) ≠ ⊤) x)
    apply Filter.Eventually.of_forall
    intro s
    apply M.sum_mem
    intro n _
    have h := M.smul_mem (x n) (Submodule.subset_span (Set.mem_range_self n))
    simpa only [e, ← lp.single_smul, smul_eq_mul, mul_one] using h
  exact hM.isSeparable_iff.mp (Set.countable_range e).isSeparable.span

/-- The characteristic sequence of an arbitrary subset of ℕ, as a bounded
scalar sequence. This witness uses no enumeration of the subsets. -/
def binarySequence (𝕜 : Type u) [RCLike 𝕜] (A : Set ℕ) : SequenceLInfinity 𝕜 :=
  ⟨fun n => if n ∈ A then 1 else 0, memℓp_infty ⟨1, by
    classical
    rintro _ ⟨n, rfl⟩
    change ‖(if n ∈ A then (1 : 𝕜) else 0)‖ ≤ 1
    split_ifs <;> simp⟩⟩

@[simp] theorem binarySequence_apply (𝕜 : Type u) [RCLike 𝕜] (A : Set ℕ) (n : ℕ) :
    binarySequence 𝕜 A n = if n ∈ A then 1 else 0 := rfl

lemma binarySequence_norm_le (𝕜 : Type u) [RCLike 𝕜] (A : Set ℕ) :
    ‖binarySequence 𝕜 A‖ ≤ 1 := by
  classical
  apply lp.norm_le_of_forall_le zero_le_one
  intro n
  simp only [binarySequence_apply]
  split_ifs <;> simp

lemma binarySequence_dist (𝕜 : Type u) [RCLike 𝕜] (A B : Set ℕ) (hAB : A ≠ B) :
    dist (binarySequence 𝕜 A) (binarySequence 𝕜 B) = 1 := by
  classical
  rw [dist_eq_norm]
  apply le_antisymm
  · apply lp.norm_le_of_forall_le zero_le_one
    intro n
    change ‖(if n ∈ A then (1 : 𝕜) else 0) - (if n ∈ B then 1 else 0)‖ ≤ 1
    split_ifs <;> simp
  · obtain ⟨n, hn⟩ := not_forall.mp (Set.ext_iff.not.mp hAB)
    have h := lp.norm_apply_le_norm (E := fun _ : ℕ => 𝕜) (p := ∞) (by simp)
      (binarySequence 𝕜 A - binarySequence 𝕜 B) n
    change ‖(if n ∈ A then (1 : 𝕜) else 0) - (if n ∈ B then 1 else 0)‖ ≤ _ at h
    by_cases ha : n ∈ A <;> by_cases hb : n ∈ B <;> simp_all

lemma binarySequence_injective (𝕜 : Type u) [RCLike 𝕜] :
    Function.Injective (binarySequence 𝕜) := by
  intro A B h
  by_contra hn
  have hd := binarySequence_dist 𝕜 A B hn
  rw [h, dist_self] at hd
  exact zero_ne_one hd

private lemma subsets_nat_uncountable : ¬ Countable (Set ℕ) := by
  intro h
  obtain ⟨f, hf⟩ := @exists_injective_nat (Set ℕ) h
  exact Function.cantor_injective f hf

theorem binary_sequences_witness : Spec.BinarySequenceWitness.{u} := by
  intro 𝕜 _
  refine ⟨binarySequence 𝕜, binarySequence_apply 𝕜, binarySequence_norm_le 𝕜,
    binarySequence_dist 𝕜, ?_⟩
  intro hc
  have : Countable (Set.range (binarySequence 𝕜)) := hc
  exact subsets_nat_uncountable (Function.Injective.countable
    (f := Set.rangeFactorization (binarySequence 𝕜))
    (fun A B h => binarySequence_injective 𝕜 (congrArg Subtype.val h)))

/-- Radius-one-third balls about distinct binary sequences are disjoint;
a separable metric space can contain only countably many such open balls. -/
theorem lInfinity_nonseparable : Spec.LInfinityNonseparable.{u} := by
  intro 𝕜 _
  have hs : ¬ SeparableSpace (SequenceLInfinity 𝕜) := by
    intro hsep
    have := hsep
    have hd : Pairwise (fun A B : Set ℕ =>
        Disjoint (Metric.ball (binarySequence 𝕜 A) (1 / 3 : ℝ))
          (Metric.ball (binarySequence 𝕜 B) (1 / 3 : ℝ))) := by
      intro A B hAB
      apply Metric.ball_disjoint_ball
      rw [binarySequence_dist 𝕜 A B hAB]
      norm_num
    exact subsets_nat_uncountable (hd.countable_of_isOpen_disjoint
      (fun _ => Metric.isOpen_ball) (fun A => ⟨binarySequence 𝕜 A, by simp⟩))
  refine ⟨hs, ?_⟩
  intro hdual
  have := hdual
  exact hs (l1Duality.symm.surjective.denseRange.separableSpace
    l1Duality.symm.continuous)

/-- The original ℓ∞ unit ball is metrizable for its series-pairing weak-star
topology. The duality isometry preserves exactly this ball. -/
theorem lInfinity_ball_weakStar_metrizable :
    Spec.LInfinityBallMetrizable.{u} := by
  intro 𝕜 _
  have := l1_separable 𝕜
  have hm := (C13ConverseMetric.dual_ball_weakStar_metrizable_iff_separable 𝕜 (SequenceLp 𝕜 1)).mpr
    (l1_separable 𝕜)
  let U := l1Duality (𝕜 := 𝕜)
  have ht : Spec.lInfinityWeakStarTopology 𝕜 =
      TopologicalSpace.induced U
        (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (SequenceLp 𝕜 1)) := by
    rw [C12WeakStar.weakStarTopology_evaluations, induced_iInf]
    simp only [induced_compose, Function.comp_def]
    rfl
  let B := Metric.closedBall (0 : SequenceLInfinity 𝕜) 1
  let B' := Metric.closedBall (0 : SequenceLp 𝕜 1 →L[𝕜] 𝕜) 1
  let f : B → B' := fun a => ⟨U a.val, by
    simpa only [B, B', Metric.mem_closedBall, dist_zero_right, U.norm_map]
      using a.property⟩
  let t := C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (SequenceLp 𝕜 1)
  let : TopologicalSpace (SequenceLp 𝕜 1 →L[𝕜] 𝕜) := t
  let : TopologicalSpace (SequenceLInfinity 𝕜) :=
    Spec.lInfinityWeakStarTopology 𝕜
  have : MetrizableSpace B' := hm
  have hf : IsEmbedding f := by
    refine ⟨⟨?_⟩, ?_⟩
    · change TopologicalSpace.induced Subtype.val
        (Spec.lInfinityWeakStarTopology 𝕜) =
        TopologicalSpace.induced f (TopologicalSpace.induced Subtype.val t)
      rw [ht, induced_compose, induced_compose]
      rfl
    · intro a b hab
      apply Subtype.ext
      exact U.injective (congrArg Subtype.val hab)
  exact hf.metrizableSpace

end ExpandedFA.P1.C13Nonmetrizable
