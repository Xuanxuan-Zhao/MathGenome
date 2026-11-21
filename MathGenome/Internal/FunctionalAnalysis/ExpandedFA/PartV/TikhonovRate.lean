import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.TikhonovRate
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.TikhonovConvergence
import Mathlib.Analysis.Normed.Module.WeakDual

noncomputable section
open Filter Asymptotics
open scoped Topology InnerProductSpace
namespace ExpandedFA.PartV.TikhonovRate
universe u v w

section Helpers
variable {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G]
local notation "R" => TikhonovMinimizer.Spec.regularizer
local notation "N" => TikhonovMinimizer.Spec.normalOperator
local notation "b" => TikhonovConvergence.bias

/-- Exact bias as a scalar multiple of the inverse normal operator. -/
theorem bias_inverse (A : H →L[𝕜] G) (α : ℝ) (hα : 0 < α) (x : H) :
    b A α x = (α : 𝕜) • (N A α).inverse x := by
  have hi := (TikhonovMinimizer.normal_invertible 𝕜 H G A α hα).inverse_apply_self
    (b A α x)
  rw [TikhonovConvergence.normal_bias A α hα, map_smul] at hi
  exact hi.symm

/-- The exact reconstruction is a contraction, including on kernel components. -/
theorem norm_reconstruction_le (A : H →L[𝕜] G) (α : ℝ) (hα : 0 < α) (x : H) :
    ‖R A α (A x)‖ ≤ ‖x‖ := by
  have hn := TikhonovMinimizer.normal_equation 𝕜 H G A α hα (A x)
  have he := congrArg (fun z => RCLike.re ⟪x - R A α (A x), z⟫_𝕜) hn
  rw [TikhonovMinimizer.re_inner_normal, ContinuousLinearMap.adjoint_inner_right] at he
  simp only [map_sub, inner_sub_left, inner_self_eq_norm_sq] at he
  have hc := re_inner_le_norm (𝕜 := 𝕜) x (R A α (A x))
  have hp : α * ‖R A α (A x)‖ ^ 2 ≤ α * RCLike.re ⟪x, R A α (A x)⟫_𝕜 := by
    nlinarith [sq_nonneg ‖A x - A (R A α (A x))‖,
      norm_sub_sq (𝕜 := 𝕜) (A x) (A (R A α (A x))),
      inner_re_symm (𝕜 := 𝕜) (A x) (A (R A α (A x)))]
  have hsq := (mul_le_mul_iff_right₀ hα).mp hp
  nlinarith [norm_nonneg x, norm_nonneg (R A α (A x))]

/-- Source vectors have bias α times the reconstruction of their representative. -/
theorem bias_normal (A : H →L[𝕜] G) (α : ℝ) (hα : 0 < α) (w : H) :
    b A α (A.adjoint (A w)) = (α : 𝕜) • R A α (A w) :=
  TikhonovConvergence.bias_adjoint A α hα (A w)

/-- A norm limit of bounded images under a self-adjoint operator belongs to its
actual range. Banach–Alaoglu supplies a weak cluster point, represented in H
by Riesz; testing against B y identifies its image. -/
theorem mem_range_of_bounded_images {ι : Type*} {l : Filter ι} [NeBot l]
    (B : H →L[𝕜] H)
    (hsymm : ∀ z y : H, ⟪B z, y⟫_𝕜 = ⟪z, B y⟫_𝕜)
    (z : ι → H) (C : ℝ) (hb : ∀ᶠ i in l, ‖z i‖ ≤ C)
    (x : H) (hx : Tendsto (fun i => B (z i)) l (𝓝 x)) :
    x ∈ B.range := by
  let u : ι → WeakDual 𝕜 H := fun i =>
    StrongDual.toWeakDual (InnerProductSpace.toDual 𝕜 H (z i))
  have hball : ∀ᶠ i in l,
      u i ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 H) C := by
    filter_upwards [hb] with i hi
    simpa [u, Metric.mem_closedBall, dist_zero_right] using hi
  obtain ⟨φ, hφ, hc⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual 𝕜 H) C).exists_mapClusterPt_of_frequently
    hball.frequently
  let w : H := (InnerProductSpace.toDual 𝕜 H).symm (WeakDual.toStrongDual φ)
  refine ⟨w, ?_⟩
  apply ext_inner_right 𝕜
  intro y
  have hcluster : MapClusterPt (φ (B y)) l (fun i => ⟪B (z i), y⟫_𝕜) := by
    convert hc.continuousAt_comp (WeakDual.eval_continuous (B y)).continuousAt using 1
    funext i
    exact hsymm (z i) y
  have ht : Tendsto (fun i => ⟪B (z i), y⟫_𝕜) l (𝓝 ⟪x, y⟫_𝕜) :=
    hx.inner tendsto_const_nhds
  have hne : NeBot (𝓝 (φ (B y)) ⊓ 𝓝 ⟪x, y⟫_𝕜) :=
    hcluster.clusterPt.mono ht
  have he : φ (B y) = ⟪x, y⟫_𝕜 := by
    by_contra hn
    exact hne.ne (disjoint_nhds_nhds.mpr hn).eq_bot
  calc
    ⟪B w, y⟫_𝕜 = ⟪w, B y⟫_𝕜 := hsymm w y
    _ = φ (B y) := InnerProductSpace.toDual_symm_apply
    _ = ⟪x, y⟫_𝕜 := he

/-- Uniformly bounded inverse normal images force membership in the normal range. -/
theorem range_of_bounded_inverse (A : H →L[𝕜] G) (x : H) (C : ℝ)
    (hb : ∀ᶠ α in 𝓝[>] (0 : ℝ), ‖(N A α).inverse x‖ ≤ C) :
    x ∈ (A.adjoint.comp A).range := by
  let z : ℝ → H := fun α => (N A α).inverse x
  have hzero : Tendsto (fun α : ℝ => (α : 𝕜) • z α)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun α : ℝ => α) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      nhdsWithin_le_nhds
    apply squeeze_zero_norm'
      (show ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), ‖(α : 𝕜) • z α‖ ≤ α * C from ?_)
      (by simpa using ht.mul_const C)
    filter_upwards [hb, self_mem_nhdsWithin] with α hα hp
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left hα hp.le
  have heq : (fun α : ℝ => (A.adjoint.comp A) (z α)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun α : ℝ => x - (α : 𝕜) • z α) := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hn := (TikhonovMinimizer.normal_invertible 𝕜 H G A α hα).self_apply_inverse x
    change (α : 𝕜) • z α + (A.adjoint.comp A) (z α) = x at hn
    exact eq_sub_of_add_eq' hn
  have hlim : Tendsto (fun α : ℝ => (A.adjoint.comp A) (z α))
      (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℝ => x)
      (𝓝[>] (0 : ℝ)) (𝓝 x)).sub hzero
    simpa using ht.congr' heq.symm
  apply mem_range_of_bounded_images (A.adjoint.comp A) (fun z y => ?_) z C hb x hlim
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]

/-- An O(α) bias bounds the inverse images after cancelling the positive scalar α. -/
theorem range_of_rate (A : H →L[𝕜] G) (x : H)
    (hr : (fun α : ℝ => R A α (A x) - x) =O[𝓝[>] (0 : ℝ)]
      (fun α : ℝ => α)) : x ∈ (A.adjoint.comp A).range := by
  obtain ⟨C, hb⟩ := hr.bound
  apply range_of_bounded_inverse A x C
  filter_upwards [hb, self_mem_nhdsWithin] with α hα hp
  have he : ‖R A α (A x) - x‖ = α * ‖(N A α).inverse x‖ := by
    rw [← norm_neg, neg_sub]
    change ‖b A α x‖ = _
    rw [bias_inverse A α hp, norm_smul, RCLike.norm_ofReal, abs_of_pos hp]
  rw [he, Real.norm_eq_abs, abs_of_pos hp, mul_comm C] at hα
  exact (mul_le_mul_iff_right₀ hp).mp hα

end Helpers

theorem source_bound : Spec.SourceBound.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A x hx w hw α hα
  rw [hw, ← norm_neg, neg_sub]
  change ‖TikhonovConvergence.bias A α (A.adjoint (A w))‖ ≤ _
  rw [bias_normal A α hα, norm_smul, RCLike.norm_ofReal, abs_of_pos hα]
  exact mul_le_mul_of_nonneg_left (norm_reconstruction_le A α hα w) hα.le

theorem range_criterion : Spec.RangeCriterion.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A x hx
  constructor
  · rintro ⟨w, hw⟩
    apply IsBigO.of_bound ‖w‖
    filter_upwards [self_mem_nhdsWithin] with α hα
    rw [Real.norm_eq_abs, abs_of_pos hα, mul_comm ‖w‖]
    exact source_bound 𝕜 H G A x hx w hw.symm α hα
  · exact range_of_rate A x

end ExpandedFA.PartV.TikhonovRate
