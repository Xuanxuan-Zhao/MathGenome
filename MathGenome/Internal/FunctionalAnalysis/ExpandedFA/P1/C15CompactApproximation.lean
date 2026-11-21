import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15CompactApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15PartialSums
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.Definitions
import Mathlib.Topology.MetricSpace.Pseudo.Basic

open Filter Topology
noncomputable section
universe u v w
namespace ExpandedFA.P1.C15CompactApproximation
open ExpandedFA.P1.C15Basis ExpandedFA.P1.C15CoordinateContinuity
open ExpandedFA.P1.C15PartialSums

/-- A uniformly bounded family of linear operators converging pointwise to the
identity converges uniformly on each compact set in the original norm. -/
theorem uniform_on_compact_of_bounded_pointwise
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : ℕ → E →L[𝕜] E) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ N x, ‖T N x‖ ≤ C * ‖x‖)
    (hp : ∀ x, Tendsto (fun N => T N x) atTop (𝓝 x))
    (K : Set E) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x ∈ K, ‖T N x - x‖ < ε := by
  have hC1 : 0 < C + 1 := by positivity
  have hδ : 0 < ε / (2 * (C + 1)) := by positivity
  obtain ⟨s, _, hs, hcover⟩ := hK.finite_cover_balls hδ
  have hevent : ∀ᶠ N in atTop, ∀ z ∈ s, ‖T N z - z‖ < ε / 2 := by
    apply hs.eventually_all.mpr
    intro z _
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp (hp z)) (ε / 2) (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨N₀, fun N hN x hx => ?_⟩
  obtain ⟨z, hzs, hxz⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hdist : ‖x - z‖ < ε / (2 * (C + 1)) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hxz
  have hsmall : (C + 1) * ‖x - z‖ < ε / 2 := by
    have := (lt_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp hdist
    nlinarith
  have hdecomp : T N x - x = (T N (x - z) - (x - z)) + (T N z - z) := by
    rw [map_sub]
    abel
  rw [hdecomp]
  calc
    ‖(T N (x - z) - (x - z)) + (T N z - z)‖ ≤
        ‖T N (x - z) - (x - z)‖ + ‖T N z - z‖ := norm_add_le _ _
    _ ≤ (C + 1) * ‖x - z‖ + ‖T N z - z‖ := by
      nlinarith [norm_sub_le (T N (x - z)) (x - z), hb N (x - z)]
    _ < ε := by linarith [hN₀ N hN z hzs]

/-- Uniform convergence of the source's infinite ordered basis truncations. -/
theorem raw_basis_uniform_compact_convergence :
    Spec.RawUniformCompactConvergence := by
  intro 𝕜 E _ _ _ _ e h K hK ε hε
  obtain ⟨T, H, _, _⟩ := raw_partial_sum_bounds h
  have hp (x : E) : Tendsto (fun N => T N x) atTop (𝓝 x) := by
    simpa only [H.agrees] using H.converges x
  obtain ⟨N₀, hN₀⟩ := uniform_on_compact_of_bounded_pointwise T
    (ExpandedFA.P1.C15PartialSums.Spec.basisConstant T) H.nonneg
    (fun N x => by simpa only [H.agrees] using H.norm_bound N x) hp K hK ε hε
  exact ⟨N₀, fun N hN x hx => by simpa only [H.agrees] using hN₀ N hN x hx⟩

/-- Finite truncations stabilize at the identity, including the empty basis. -/
theorem finite_basis_uniform_compact_convergence :
    Spec.FiniteUniformCompactConvergence := by
  intro 𝕜 E _ _ _ _ d e h K _ ε hε
  refine ⟨d, fun N hN x _ => ?_⟩
  change ‖finitePartialSum h N x - x‖ < ε
  rw [finitePartialSum_of_le h N hN x, sub_self, norm_zero]
  exact hε

/-- Uniform approximation on the compact unit-ball image controls the operator
norm after composition. This step requires no completeness of either space. -/
theorem norm_comp_sub_tendsto_of_uniform_image
    {𝕜 : Type u} {X : Type v} {E : Type w} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (P : ℕ → E →L[𝕜] E) (T : X →L[𝕜] E)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ y ∈ closure (T '' Metric.closedBall (0 : X) 1), ‖P N y - y‖ < ε) :
    Tendsto (fun N => ‖(P N).comp T - T‖) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := hu (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hb : ‖(P N).comp T - T‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    have hmem : T x ∈ closure (T '' Metric.closedBall (0 : X) 1) :=
      subset_closure ⟨x, by simp [Metric.mem_closedBall, dist_zero_right, hx], rfl⟩
    exact (hN₀ N hN (T x) hmem).le
  simpa only [dist_zero_right, norm_norm] using hb.trans_lt (half_lt_self hε)

/-- A compact map into a Banach space with an actual ordered Schauder basis
is approximated in operator norm by its bounded finite-rank truncations. -/
theorem raw_basis_compact_operator_approximation :
    Spec.RawCompactOperatorApproximation := by
  intro 𝕜 X E _ _ _ _ _ _ e h T hT
  classical
  have hcompact : ExpandedFA.Compactness.IsCompactLinearMap T := hT
  let U := ContinuousLinearMap.mkOfIsCompactOperator
    ((ExpandedFA.Compactness.compact_iff_isCompactOperator T).mp hcompact)
  obtain ⟨b, _, _, hbp⟩ := raw_native_basis h
  refine ⟨U, rfl, fun N => (b.proj N).comp U, ?_, ?_, ?_⟩
  · intro N x
    exact hbp N (T x)
  · intro N
    have hfin : FiniteDimensional 𝕜 (b.proj N).toLinearMap.range := by
      rw [b.range_proj_eq_span]
      exact FiniteDimensional.span_of_finite 𝕜 ((Finset.range N).finite_toSet.image b)
    exact Submodule.finiteDimensional_of_le
      (LinearMap.range_comp_le_range U.toLinearMap (b.proj N).toLinearMap)
  · apply norm_comp_sub_tendsto_of_uniform_image
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := raw_basis_uniform_compact_convergence h
      (closure (T '' Metric.closedBall (0 : X) 1)) hcompact ε hε
    exact ⟨N₀, fun N hN y hy => by simpa only [hbp] using hN₀ N hN y hy⟩

/-- The finite-list case retains every dimension, including the empty basis of
the zero space. Its truncations in fact stabilize at the original operator. -/
theorem finite_basis_compact_operator_approximation :
    Spec.FiniteCompactOperatorApproximation := by
  intro 𝕜 X E _ _ _ _ _ _ d e h T hT
  classical
  have hcompact : ExpandedFA.Compactness.IsCompactLinearMap T := hT
  let U := ContinuousLinearMap.mkOfIsCompactOperator
    ((ExpandedFA.Compactness.compact_iff_isCompactOperator T).mp hcompact)
  obtain ⟨b, _, _, hbp⟩ := finite_native_basis h
  let P (N : ℕ) := b.proj (Finset.univ.filter (fun i : Fin d => i.val < N))
  have hp (N : ℕ) (x : E) : P N x = finitePartialSum h N x := hbp N x
  let := finiteBasis_finiteDimensional h
  refine ⟨U, rfl, fun N => (P N).comp U, ?_, ?_, ?_⟩
  · intro N x
    exact hp N (T x)
  · intro N
    infer_instance
  · apply norm_comp_sub_tendsto_of_uniform_image
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := finite_basis_uniform_compact_convergence h
      (closure (T '' Metric.closedBall (0 : X) 1)) hcompact ε hε
    exact ⟨N₀, fun N hN y hy => by simpa only [hp] using hN₀ N hN y hy⟩

end ExpandedFA.P1.C15CompactApproximation
