import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.TikhonovConvergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.TikhonovMinimizer

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace ExpandedFA.PartV.TikhonovConvergence
universe u v w

section Helpers
variable {𝕜 : Type u} {H : Type v} {G : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G]

local notation "R" => TikhonovMinimizer.Spec.regularizer
local notation "N" => TikhonovMinimizer.Spec.normalOperator

/-- The exact-data bias, with sign chosen as target minus reconstruction. -/
def bias (A : H →L[𝕜] G) (α : ℝ) : H →L[𝕜] H :=
  ContinuousLinearMap.id 𝕜 H - (R A α).comp A

/-- Its normal equation has right-hand side αx. -/
theorem normal_bias (A : H →L[𝕜] G) (α : ℝ) (hα : 0 < α) (x : H) :
    N A α (bias A α x) = (α : 𝕜) • x := by
  change N A α (x - R A α (A x)) = _
  rw [map_sub, TikhonovMinimizer.normal_equation 𝕜 H G A α hα]
  simp only [TikhonovMinimizer.Spec.normalOperator, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
  abel

/-- The bias is a contraction, uniformly for positive parameters. -/
theorem norm_bias_le (A : H →L[𝕜] G) (α : ℝ) (hα : 0 < α) (x : H) :
    ‖bias A α x‖ ≤ ‖x‖ := by
  have he := TikhonovMinimizer.normal_coercive A α (bias A α x)
  rw [normal_bias A α hα, inner_smul_right, RCLike.re_ofReal_mul] at he
  have hc := re_inner_le_norm (𝕜 := 𝕜) (bias A α x) x
  have hb : ‖bias A α x‖ ^ 2 ≤ ‖bias A α x‖ * ‖x‖ :=
    (mul_le_mul_iff_right₀ hα).mp (he.trans (mul_le_mul_of_nonneg_left hc hα.le))
  nlinarith [norm_nonneg (bias A α x), norm_nonneg x]

/-- On the adjoint range, the bias is α times the regularizer. -/
theorem bias_adjoint (A : H →L[𝕜] G) (α : ℝ) (hα : 0 < α) (y : G) :
    bias A α (A.adjoint y) = (α : 𝕜) • R A α y := by
  have hi := (TikhonovMinimizer.normal_invertible 𝕜 H G A α hα).inverse_apply_self
    (bias A α (A.adjoint y))
  rw [normal_bias A α hα, map_smul] at hi
  exact hi.symm

/-- This dense-range estimate tends to zero with the parameter. -/
theorem norm_bias_adjoint_le (A : H →L[𝕜] G) (α : ℝ) (hα : 0 < α) (y : G) :
    ‖bias A α (A.adjoint y)‖ ≤ Real.sqrt α / 2 * ‖y‖ := by
  rw [bias_adjoint A α hα, norm_smul, RCLike.norm_ofReal, abs_of_pos hα]
  have hb := (R A α).le_opNorm y
  have hr := TikhonovMinimizer.regularizer_norm 𝕜 H G A α hα
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  calc
    α * ‖R A α y‖ ≤ α * (1 / (2 * Real.sqrt α) * ‖y‖) :=
      mul_le_mul_of_nonneg_left
        (hb.trans (mul_le_mul_of_nonneg_right hr (norm_nonneg y))) hα.le
    _ = Real.sqrt α / 2 * ‖y‖ := by
      have hsq := Real.sq_sqrt hα.le
      field_simp
      rw [hsq]

/-- Dense-range convergence, valid along any filter with positive parameters
eventually and parameters tending to zero. -/
theorem bias_adjoint_tendsto {ι : Type*} {l : Filter ι} (A : H →L[𝕜] G)
    (α : ι → ℝ) (hpos : ∀ᶠ i in l, 0 < α i)
    (hlim : Tendsto α l (𝓝 0)) (y : G) :
    Tendsto (fun i => bias A (α i) (A.adjoint y)) l (𝓝 0) := by
  apply squeeze_zero_norm'
    (hpos.mono fun i hi => norm_bias_adjoint_le A (α i) hi y)
  have hs := (Real.continuous_sqrt.tendsto 0).comp hlim
  simpa using (hs.div_const 2).mul_const ‖y‖

/-- Extend the dense-range limit by the uniform contraction bound. -/
theorem bias_tendsto {ι : Type*} {l : Filter ι} (A : H →L[𝕜] G)
    (α : ι → ℝ) (hpos : ∀ᶠ i in l, 0 < α i)
    (hlim : Tendsto α l (𝓝 0)) (x : H) (hx : x ∈ A.ker.orthogonal) :
    Tendsto (fun i => bias A (α i) x) l (𝓝 0) := by
  rw [A.orthogonal_ker] at hx
  have hclosure : x ∈ closure (A.adjoint.range : Set H) := hx
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hclosure (ε / 2) (by positivity)
  obtain ⟨y, rfl⟩ := hz
  rw [dist_eq_norm] at hdist
  change ‖x - A.adjoint y‖ < ε / 2 at hdist
  have ht := bias_adjoint_tendsto A α hpos hlim y
  have he := Metric.tendsto_nhds.mp ht (ε / 2) (by positivity)
  filter_upwards [hpos, he] with i hi hsmall
  rw [dist_zero_right] at hsmall ⊢
  calc
    ‖bias A (α i) x‖ =
        ‖bias A (α i) (x - A.adjoint y) + bias A (α i) (A.adjoint y)‖ := by
      rw [map_sub, sub_add_cancel]
    _ ≤ ‖bias A (α i) (x - A.adjoint y)‖ + ‖bias A (α i) (A.adjoint y)‖ :=
      norm_add_le _ _
    _ ≤ ‖x - A.adjoint y‖ + ‖bias A (α i) (A.adjoint y)‖ :=
      add_le_add (norm_bias_le A (α i) hi _) le_rfl
    _ < ε := by linarith

/-- The reconstruction form of the preceding general-filter limit. -/
theorem exact_tendsto {ι : Type*} {l : Filter ι} (A : H →L[𝕜] G)
    (α : ι → ℝ) (hpos : ∀ᶠ i in l, 0 < α i)
    (hlim : Tendsto α l (𝓝 0)) (x : H) (hx : x ∈ A.ker.orthogonal) :
    Tendsto (fun i => R A (α i) (A x)) l (𝓝 x) := by
  have hb := (tendsto_const_nhds : Tendsto (fun _ : ι => x) l (𝓝 x)).sub
    (bias_tendsto A α hpos hlim x hx)
  simpa only [bias, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, sub_sub_cancel, sub_zero] using hb

end Helpers

theorem exact_convergence : Spec.ExactConvergence.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A x hx
  exact exact_tendsto A id self_mem_nhdsWithin nhdsWithin_le_nhds x hx

theorem error_decomposition : Spec.ErrorDecomposition.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A α f g x
  rw [map_sub]
  abel

theorem noise_bound : Spec.NoiseBound.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A α hα δ f g hnoise
  have hs : 0 < 2 * Real.sqrt α := mul_pos (by norm_num) (Real.sqrt_pos.mpr hα)
  calc
    ‖TikhonovMinimizer.Spec.regularizer A α (g - f)‖ ≤
        ‖TikhonovMinimizer.Spec.regularizer A α‖ * ‖g - f‖ :=
      (TikhonovMinimizer.Spec.regularizer A α).le_opNorm _
    _ ≤ (1 / (2 * Real.sqrt α)) * δ :=
      mul_le_mul (TikhonovMinimizer.regularizer_norm 𝕜 H G A α hα) hnoise
        (norm_nonneg _) (one_div_nonneg.mpr hs.le)
    _ = δ / (2 * Real.sqrt α) := by ring

theorem total_error_bound : Spec.TotalErrorBound.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A α hα δ f g x hnoise
  rw [error_decomposition 𝕜 H G A α f g x]
  exact (norm_add_le _ _).trans
    (add_le_add le_rfl (noise_bound 𝕜 H G A α hα δ f g hnoise))

theorem noisy_convergence : Spec.NoisyConvergence.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ A x hx α g hpos hlim hratio hnoise
  have hp : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < α δ :=
    (show ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ from self_mem_nhdsWithin).mono
      fun δ hδ => hpos δ hδ
  have he := exact_tendsto A α hp hlim x hx
  have hn : Tendsto
      (fun δ => TikhonovMinimizer.Spec.regularizer A (α δ) (g δ - A x))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact noise_bound 𝕜 H G A (α δ) (hpos δ hδ) δ (A x) (g δ) (hnoise δ hδ)
    · simpa only [zero_div, div_div, mul_comm (Real.sqrt _) 2] using hratio.div_const 2
  have ht := he.add hn
  simpa only [map_sub, add_sub_cancel, add_zero] using ht

end ExpandedFA.PartV.TikhonovConvergence
