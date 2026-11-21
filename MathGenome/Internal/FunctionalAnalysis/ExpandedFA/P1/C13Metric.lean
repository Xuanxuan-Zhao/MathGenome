import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C13Metric
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStar
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The series metric of fa2:p1:c13:metric (paper.tex 2564–2573).

The summable geometric majorant proves convergence and weak-star continuity
of the distance. Density in the closed unit ball proves separation. On a
norm-bounded set, a containing weak-star compact dual ball makes the continuous
injection into the series metric a topological embedding. Restriction gives
the required topology equality without any completeness hypothesis on E.
-/

namespace ExpandedFA.P1.C13Metric

universe u v
open scoped Topology
open Topology
noncomputable section

def weakStarSeriesDistance : Spec.DistanceType :=
  Spec.DistanceValue

private lemma weight_summable : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) :=
  summable_geometric_two.comp_injective (fun _ _ h => Nat.add_right_cancel h)

private lemma term_nonneg {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → Metric.closedBall (0 : E) 1) (f g : E →L[𝕜] 𝕜) (n : ℕ) :
    0 ≤ (1 / 2 : ℝ) ^ (n + 1) * min 1 ‖(f - g) (x n)‖ := by positivity

private lemma term_le_weight {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → Metric.closedBall (0 : E) 1) (f g : E →L[𝕜] 𝕜) (n : ℕ) :
    (1 / 2 : ℝ) ^ (n + 1) * min 1 ‖(f - g) (x n)‖ ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  calc
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) * 1 :=
      mul_le_mul_of_nonneg_left (min_le_left 1 ‖(f - g) (x n)‖) (by positivity)
    _ = _ := mul_one _

theorem weakStarSeries_summable : Spec.SeriesConvergence := by
  intro 𝕜 E _ _ _ x f g
  exact Summable.of_nonneg_of_le (term_nonneg x f g) (term_le_weight x f g) weight_summable

private lemma series_self {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → Metric.closedBall (0 : E) 1) (f : E →L[𝕜] 𝕜) :
    weakStarSeriesDistance 𝕜 E x f f = 0 := by
  simp [weakStarSeriesDistance, Spec.DistanceValue]

private lemma series_comm {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → Metric.closedBall (0 : E) 1) (f g : E →L[𝕜] 𝕜) :
    weakStarSeriesDistance 𝕜 E x f g = weakStarSeriesDistance 𝕜 E x g f := by
  unfold weakStarSeriesDistance Spec.DistanceValue
  apply tsum_congr
  intro n
  simp only [sub_apply, norm_sub_rev]

private lemma series_triangle {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → Metric.closedBall (0 : E) 1) (f g h : E →L[𝕜] 𝕜) :
    weakStarSeriesDistance 𝕜 E x f h ≤
      weakStarSeriesDistance 𝕜 E x f g + weakStarSeriesDistance 𝕜 E x g h := by
  unfold weakStarSeriesDistance Spec.DistanceValue
  rw [← (weakStarSeries_summable 𝕜 E x f g).tsum_add
    (weakStarSeries_summable 𝕜 E x g h)]
  apply Summable.tsum_le_tsum _ (weakStarSeries_summable 𝕜 E x f h)
    ((weakStarSeries_summable 𝕜 E x f g).add (weakStarSeries_summable 𝕜 E x g h))
  intro n
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp only [sub_apply]
  have ht : ‖f (x n) - h (x n)‖ ≤ ‖f (x n) - g (x n)‖ + ‖g (x n) - h (x n)‖ := by
    simpa only [dist_eq_norm] using dist_triangle (f (x n)) (g (x n)) (h (x n))
  by_cases hfg : ‖f (x n) - g (x n)‖ ≤ 1
  · by_cases hgh : ‖g (x n) - h (x n)‖ ≤ 1
    · rw [min_eq_right hfg, min_eq_right hgh]
      exact (min_le_right _ _).trans ht
    · rw [min_eq_right hfg, min_eq_left (le_of_not_ge hgh)]
      exact (min_le_left _ _).trans (le_add_of_nonneg_left (norm_nonneg _))
  · rw [min_eq_left (le_of_not_ge hfg)]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (by positivity))

theorem weakStarSeries_eq_zero : Spec.PositiveDefiniteness := by
  intro 𝕜 E _ _ _ x hx f g
  constructor
  · intro hz
    have htests : ∀ n, f (x n) = g (x n) := by
      intro n
      have hle := (weakStarSeries_summable 𝕜 E x f g).le_tsum n
        (fun k _ => term_nonneg x f g k)
      change _ ≤ Spec.DistanceValue 𝕜 E x f g at hle
      rw [hz] at hle
      have hw : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
      have hmin : min 1 ‖(f - g) (x n)‖ = 0 := by
        nlinarith [term_nonneg x f g n, norm_nonneg ((f - g) (x n)),
          show 0 ≤ min 1 ‖(f - g) (x n)‖ by positivity]
      have hn : ‖(f - g) (x n)‖ = 0 := by
        rcases (min_eq_iff.mp hmin) with h | h
        · norm_num at h
        · exact h.1
      simpa only [norm_eq_zero, sub_apply, sub_eq_zero] using hn
    have hball : ∀ y : Metric.closedBall (0 : E) 1, f y = g y := by
      have heq := hx.equalizer (f.continuous.comp continuous_subtype_val)
        (g.continuous.comp continuous_subtype_val) (funext htests)
      exact congr_fun heq
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply ContinuousLinearMap.opNorm_le_of_ball (ε := 1) zero_lt_one le_rfl
    intro y hy
    have hy' : y ∈ Metric.closedBall (0 : E) 1 := Metric.ball_subset_closedBall hy
    simp [sub_apply, hball ⟨y, hy'⟩]
  · rintro rfl
    exact series_self x f

/-- The displayed series gives a metric on the whole dual. Its topology is
only asserted to agree with weak-star on norm-bounded subsets. -/
@[instance_reducible]
private def seriesMetric {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → Metric.closedBall (0 : E) 1) (hx : DenseRange x) :
    MetricSpace (E →L[𝕜] 𝕜) where
  dist := weakStarSeriesDistance 𝕜 E x
  dist_self := series_self x
  dist_comm := series_comm x
  dist_triangle := series_triangle x
  eq_of_dist_eq_zero := (weakStarSeries_eq_zero 𝕜 E x hx _ _).mp

/-- Uniform summability makes the series distance weak-star continuous. -/
private lemma continuous_toSeries {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → Metric.closedBall (0 : E) 1) (hx : DenseRange x) :
    @Continuous (WeakDual 𝕜 E) (E →L[𝕜] 𝕜) inferInstance
      (seriesMetric (𝕜 := 𝕜) x hx).toUniformSpace.toTopologicalSpace
      (WeakDual.toStrongDual : WeakDual 𝕜 E → (E →L[𝕜] 𝕜)) := by
  let m := seriesMetric (𝕜 := 𝕜) x hx
  let : MetricSpace (E →L[𝕜] 𝕜) := m
  let : PseudoMetricSpace (E →L[𝕜] 𝕜) := m.toPseudoMetricSpace
  let : TopologicalSpace (E →L[𝕜] 𝕜) := m.toUniformSpace.toTopologicalSpace
  rw [continuous_iff_continuous_dist]
  change Continuous (fun p : WeakDual 𝕜 E × WeakDual 𝕜 E =>
    ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * min 1 ‖p.1 (x n) - p.2 (x n)‖)
  refine continuous_tsum (fun n => ?_) weight_summable (fun n p => ?_)
  ·
    exact continuous_const.mul (continuous_const.min
      (((WeakDual.eval_continuous (𝕜 := 𝕜) (x n : E)).comp continuous_fst).sub
        ((WeakDual.eval_continuous (𝕜 := 𝕜) (x n : E)).comp continuous_snd)).norm)
  · rw [Real.norm_of_nonneg (by positivity)]
    exact term_le_weight x p.1.toStrongDual p.2.toStrongDual n

set_option backward.isDefEq.respectTransparency false in
/-- The exact series formula metrizes every norm-bounded subset for its
relative σ(E′, E) topology, including the empty and zero-space cases. -/
theorem bounded_weakStar_metric : Spec.Metrization := by
  intro 𝕜 E _ _ _ _ x hx A hA
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le.mp hA)
  let K : Set (WeakDual 𝕜 E) := {f | ‖f.toStrongDual‖ ≤ R}
  have hK : IsCompact K := by
    simpa only [K, Metric.closedBall, dist_zero_right, Set.preimage_ofPred_eq] using
      (WeakDual.isCompact_closedBall (𝕜 := 𝕜) (E := E) 0 R)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let m := seriesMetric (𝕜 := 𝕜) x hx
  let : MetricSpace (E →L[𝕜] 𝕜) := m
  let : PseudoMetricSpace (E →L[𝕜] 𝕜) := m.toPseudoMetricSpace
  let : TopologicalSpace (E →L[𝕜] 𝕜) := m.toUniformSpace.toTopologicalSpace
  have hemb : IsEmbedding (fun f : K => f.val.toStrongDual) :=
    ((continuous_toSeries x hx).comp continuous_subtype_val).isClosedEmbedding
      (fun _ _ h => Subtype.ext h) |>.isEmbedding
  let j : A → K := fun f => ⟨StrongDual.toWeakDual f.val, hR f.val f.property⟩
  refine ⟨MetricSpace.induced (Subtype.val : A → (E →L[𝕜] 𝕜)) Subtype.val_injective m,
    fun _ _ => rfl, ?_⟩
  have heq := congrArg (TopologicalSpace.induced j) hemb.isInducing.eq_induced
  change TopologicalSpace.induced j
      (TopologicalSpace.induced (Subtype.val : K → WeakDual 𝕜 E)
        (instTopologicalSpaceWeakDual 𝕜 E)) =
    TopologicalSpace.induced j
      (TopologicalSpace.induced (fun f : K => f.val.toStrongDual)
        m.toUniformSpace.toTopologicalSpace) at heq
  simp only [induced_compose, Function.comp_def] at heq
  dsimp only [j] at heq
  change TopologicalSpace.induced (Subtype.val : A → (E →L[𝕜] 𝕜))
      m.toUniformSpace.toTopologicalSpace = _
  rw [C12WeakStar.weakStarTopology_native 𝕜 E]
  simpa only [induced_compose, Function.comp_def,
    StrongDual.toStrongDual_toWeakDual] using heq.symm

theorem dense_tests_exist : Spec.DenseTestsExistence := by
  intro 𝕜 E _ _ _ _
  let : Nonempty (Metric.closedBall (0 : E) 1) :=
    ⟨⟨0, by simp⟩⟩
  exact TopologicalSpace.exists_dense_seq _

theorem zero_space_distance : Spec.ZeroSpaceDistance := by
  intro 𝕜 E _ _ _ _
  have hs : Subsingleton (E →L[𝕜] 𝕜) := inferInstance
  refine ⟨hs, ?_⟩
  intro x f g
  rw [Subsingleton.elim g f]
  exact series_self x f

end
end ExpandedFA.P1.C13Metric
