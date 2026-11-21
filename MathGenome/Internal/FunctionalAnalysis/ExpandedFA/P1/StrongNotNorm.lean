import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.StrongNotNorm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01SequenceSpaces

noncomputable section
open Filter
open scoped Topology ENNReal

universe u
namespace ExpandedFA.P1.StrongNotNorm
open ExpandedFA.P1.C01SequenceSpaces
open Spec

abbrev coordinateProjection : ProjectionType.{u} := ProjectionValue

@[simp] theorem coordinateProjection_apply (𝕜 : Type u) [RCLike 𝕜]
    (n : ℕ+) (x : L2 𝕜) :
    coordinateProjection 𝕜 n x = lp.single 2 (Equiv.pnatEquivNat n)
      (x (Equiv.pnatEquivNat n)) := rfl

@[simp] theorem coordinateVector_norm (𝕜 : Type u) [RCLike 𝕜] (n : ℕ+) :
    ‖coordinateVector 𝕜 n‖ = 1 := by
  simp [coordinateVector, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

theorem coordinate_projection_formula : Formula.{u} := by
  intro 𝕜 _ n x
  constructor
  · change coordinateProjection 𝕜 n x = _
    rw [coordinateProjection_apply]
    change lp.single (E := fun _ : ℕ => 𝕜) 2 _ _ =
      _ • lp.single (E := fun _ : ℕ => 𝕜) 2 _ (1 : 𝕜)
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  · intro j
    classical
    change coordinateProjection 𝕜 n x (Equiv.pnatEquivNat j) = _
    rw [coordinateProjection_apply]
    by_cases h : j = n
    · subst j; simp
    · simp [h]

@[simp] theorem coordinateProjection_vector (𝕜 : Type u) [RCLike 𝕜] (n : ℕ+) :
    coordinateProjection 𝕜 n (coordinateVector 𝕜 n) = coordinateVector 𝕜 n := by
  simp [coordinateVector]

@[simp] theorem coordinateProjection_norm_apply (𝕜 : Type u) [RCLike 𝕜]
    (n : ℕ+) (x : L2 𝕜) :
    ‖coordinateProjection 𝕜 n x‖ = ‖x (Equiv.pnatEquivNat n)‖ := by
  rw [coordinateProjection_apply, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

/-- The upper bound is coordinate contractivity; the lower bound tests e_n. -/
theorem coordinate_projection_norms : Norms.{u} := by
  intro 𝕜 _ n
  have hn : ‖coordinateProjection 𝕜 n‖ = 1 := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      rw [coordinateProjection_norm_apply, one_mul]
      exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x _
    · have h := (coordinateProjection 𝕜 n).le_opNorm (coordinateVector 𝕜 n)
      simpa [coordinateVector] using h
  exact ⟨coordinateVector_norm 𝕜 n, hn, by simpa using hn⟩

theorem coordinate_projection_rank_one : RankOne.{u} := by
  intro 𝕜 _ n
  have hr : LinearMap.range (coordinateProjection 𝕜 n).toLinearMap =
      Submodule.span 𝕜 {coordinateVector 𝕜 n} := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      change coordinateProjection 𝕜 n x ∈ _
      change ProjectionValue 𝕜 n x ∈ _
      rw [(coordinate_projection_formula 𝕜 n x).1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · apply Submodule.span_le.mpr
      intro y hy
      have hy' : y = coordinateVector 𝕜 n := by simpa using hy
      subst y
      exact ⟨coordinateVector 𝕜 n, coordinateProjection_vector 𝕜 n⟩
  refine ⟨hr, ?_⟩
  rw [hr]
  apply finrank_span_singleton
  intro h
  have := coordinateVector_norm 𝕜 n
  simp [h] at this

/-- The upstream ℓᵖ coordinate limit applies at p=2, and its checked
positive-integer reindexing keeps the manuscript's indexing convention. -/
theorem coordinate_projection_pointwise_norm : PointwiseNorm.{u} := by
  intro 𝕜 _ x
  refine ⟨fun n => coordinateProjection_norm_apply 𝕜 n x, ?_⟩
  have hx : Tendsto (fun n : ℕ+ => x (Equiv.pnatEquivNat n)) atTop (𝓝 0) := by
    apply ((sequence_reindexing.2.2.2.1 𝕜
      (fun n : ℕ+ => x (Equiv.pnatEquivNat n)))).mp
    simpa using lp_coordinates_tendsto_zero 𝕜 2 (by norm_num) x
  simpa only [coordinateProjection_norm_apply, norm_zero] using hx.norm

theorem coordinate_projection_strong_convergence : StrongConvergence.{u} := by
  intro 𝕜 _ x
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (coordinate_projection_pointwise_norm 𝕜 x).2

theorem coordinate_projection_not_norm_convergence : NotNormConvergence.{u} := by
  intro 𝕜 _
  have hzero : ¬ Tendsto (fun n : ℕ+ => ProjectionValue 𝕜 n) atTop (𝓝 0) := by
    intro h
    have hnorm := h.norm
    have hconst : Tendsto (fun _ : ℕ+ => (1 : ℝ)) atTop (𝓝 0) := by
      simpa only [(coordinate_projection_norms 𝕜 _).2.1, norm_zero] using hnorm
    have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
    exact one_ne_zero this
  refine ⟨hzero, ?_⟩
  rintro ⟨T, hT⟩
  have hTzero : T = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    change T x = 0
    have hx : Tendsto (fun n : ℕ+ => ProjectionValue 𝕜 n x) atTop (𝓝 (T x)) :=
      ((continuous_eval_const x).tendsto T).comp hT
    exact tendsto_nhds_unique hx (coordinate_projection_strong_convergence 𝕜 x)
  subst T
  exact hzero hT

end ExpandedFA.P1.StrongNotNorm
