import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FractionalSmoothCounterexample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.WeakVolterraResolvent
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The example `fa2:p5:fractional-regularity-example`.

The shifted Mittag--Leffler power series all have infinite radius of convergence.
Writing x = t^α gives u(t)-1 = x G₁(x) and the second remainder x² G₂(x).
Repeated differentiation gives t^(α-j) Hⱼ(t^α), where Hⱼ is smooth at zero.
This proves every weighted derivative bound without assuming differentiability
of an infinite sum. A hypothetical endpoint derivative would force G₁(0)=0,
contradicting its nonzero first coefficient.
-/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ExpandedFA.PartV.FractionalSmoothCounterexample

variable {𝕜 : Type} [RCLike 𝕜]

def coefficient (α : ℝ) (ζ : 𝕜) (n : ℕ) : 𝕜 :=
  (Real.Gamma ((n : ℝ) * α + 1))⁻¹ • ζ ^ n

lemma coefficient_norm {α : ℝ} (hα : 0 < α) (ζ : 𝕜) (n : ℕ) :
    ‖coefficient α ζ n‖ = ‖ζ‖ ^ n / Real.Gamma ((n : ℝ) * α + 1) := by
  rw [coefficient, norm_smul, norm_inv, norm_pow,
    Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity)).le]
  ring

lemma coefficient_summable {α : ℝ} (hα : 0 < α) (ζ : 𝕜) {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun n => ‖coefficient α ζ n‖ * r ^ n) := by
  simpa only [coefficient_norm hα, mul_pow, div_mul_eq_mul_div, mul_comm (‖ζ‖ ^ _) (r ^ _)] using
    WeakVolterraBounds.summable_pow_div_gamma hα (mul_nonneg (norm_nonneg ζ) hr)

lemma shifted_summable {α : ℝ} (hα : 0 < α) (ζ : 𝕜) (k : ℕ)
    {r : ℝ} (hr : 0 ≤ r) : Summable (fun n => ‖coefficient α ζ (n+k)‖ * r ^ n) := by
  by_cases hz : r = 0
  · apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [hz, zero_pow hn]
  have h := ((coefficient_summable hα ζ hr).comp_injective
    (show Function.Injective (fun n : ℕ => n+k) from fun _ _ h => Nat.add_right_cancel h)).mul_right (r^k)⁻¹
  convert h using 1
  ext n
  simp only [Function.comp_apply, pow_add]
  field_simp

def profile (α : ℝ) (ζ : 𝕜) (k : ℕ) (x : ℝ) : 𝕜 :=
  FormalMultilinearSeries.ofScalarsSum (fun n => coefficient α ζ (n+k)) (algebraMap ℝ 𝕜 x)

lemma profile_smooth {α : ℝ} (hα : 0 < α) (ζ : 𝕜) (k : ℕ) :
    ContDiff ℝ ∞ (profile α ζ k) := by
  let p : FormalMultilinearSeries 𝕜 𝕜 𝕜 := FormalMultilinearSeries.ofScalars 𝕜 (fun n => coefficient α ζ (n+k))
  have hr : p.radius = ⊤ := by
    apply p.radius_eq_top_of_summable_norm
    intro r
    simpa only [p, FormalMultilinearSeries.ofScalars_norm,
      DenselyNormedField.toNontriviallyNormedField, NNReal.toReal] using
      (shifted_summable hα ζ k r.property)
  have ha : AnalyticOnNhd 𝕜 p.sum univ := by
    intro x _
    apply (p.hasFPowerSeriesOnBall (by rw [hr]; exact ENNReal.zero_lt_top)).analyticAt_of_mem
    simp [hr]
  have hc : ContDiff 𝕜 ∞ p.sum := ha.contDiff
  exact (hc.restrict_scalars ℝ).comp (show ContDiff ℝ ∞ (algebraMap ℝ 𝕜) by
    simpa using (RCLike.ofRealCLM (K := 𝕜)).contDiff)

lemma profile_hasSum {α : ℝ} (hα : 0 < α) (ζ : 𝕜) (k : ℕ) (x : ℝ) :
    HasSum (fun n => x ^ n • coefficient α ζ (n+k)) (profile α ζ k x) := by
  have hs : Summable (fun n => x ^ n • coefficient α ζ (n+k)) := by
    apply Summable.of_norm
    simpa only [norm_smul, norm_pow, mul_comm] using shifted_summable hα ζ k (norm_nonneg x)
  convert hs.hasSum using 1
  rw [profile, FormalMultilinearSeries.ofScalars_sum_eq]
  apply tsum_congr
  intro n
  simp [Algebra.smul_def, ← map_pow, mul_comm]

lemma profile_shift {α : ℝ} (hα : 0 < α) (ζ : 𝕜) (k : ℕ) (x : ℝ) :
    profile α ζ k x = coefficient α ζ k + x • profile α ζ (k+1) x := by
  have htail := (profile_hasSum hα ζ (k+1) x).const_smul x
  have he : (fun n => x • (x^n • coefficient α ζ (n+(k+1)))) =
      (fun n => x^(n+1) • coefficient α ζ (n+1+k)) := by
    ext n
    simp [smul_smul, pow_succ, mul_comm, Nat.add_comm, Nat.add_left_comm]
  rw [he] at htail
  simpa only [pow_zero, one_smul, zero_add] using
    (profile_hasSum hα ζ k x).unique htail.zero_add

lemma solution_profile {α : ℝ} (hα : 0 < α) (ζ : 𝕜) {t : ℝ} (ht : 0 ≤ t) :
    Spec.solution α ζ t = profile α ζ 0 (t ^ α) := by
  rw [Spec.solution, ← (profile_hasSum hα ζ 0 (t ^ α)).tsum_eq]
  apply tsum_congr
  intro n
  rw [WeakVolterraResolvent.Spec.mittagTerm, coefficient, smul_smul]
  simp only [Nat.add_zero]
  congr 1
  rw [div_eq_mul_inv, ← Real.rpow_mul_natCast ht, mul_comm α (n : ℝ)]

@[simp] lemma coefficient_zero (α : ℝ) (ζ : 𝕜) : coefficient α ζ 0 = 1 := by
  simp [coefficient]

lemma solution_residual {α : ℝ} (hα : 0 < α) (ζ : 𝕜) {t : ℝ} (ht : 0 ≤ t) :
    Spec.solution α ζ t - 1 = t ^ α • profile α ζ 1 (t ^ α) := by
  rw [solution_profile hα ζ ht, profile_shift hα ζ 0, coefficient_zero]
  simp

/-- A real power tending to zero from positive time. -/
lemma rpow_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => t ^ a) (𝓝[>] 0) (𝓝 0) := by
  simpa [Real.zero_rpow ha.ne'] using
    (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto.mono_left
      nhdsWithin_le_nhds

lemma profile_zero (α : ℝ) (ζ : 𝕜) (k : ℕ) :
    profile α ζ k 0 = coefficient α ζ k := by
  simp [profile]

theorem solution_identification : Spec.SolutionIdentification := by
  intro 𝕜 _ α T hα hT ζ
  obtain ⟨u, hs, _, he, hu, hz⟩ := WeakVolterraResolvent.mittag_leffler α T hα hT ζ
  exact ⟨u, fun t => (hs t).tsum_eq.symm, he, hu, hz _ rfl⟩

lemma solution_zero {α : ℝ} (hα : 0 < α) (ζ : 𝕜) : Spec.solution α ζ 0 = 1 := by
  rw [solution_profile hα ζ le_rfl, Real.zero_rpow hα.ne', profile_zero, coefficient_zero]

theorem zero_interval : Spec.ZeroInterval := by
  intro 𝕜 _ α hα ζ
  refine ⟨solution_zero hα ζ, fun _ => 1, contDiff_const, ?_⟩
  intro t ht
  have : t = 0 := le_antisymm ht.2 ht.1
  simp [this, solution_zero hα ζ]

theorem positive_smoothness : Spec.PositiveSmoothness := by
  intro 𝕜 _ α hα ζ
  have hp : ContDiffOn ℝ ∞ (fun t : ℝ => t ^ α) (Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (fun t ht => ne_of_gt ht)
  have h := ((profile_smooth hα ζ 0).comp_contDiffOn hp).sub (contDiffOn_const (c := (1 : 𝕜)))
  apply h.congr
  intro t ht
  rw [solution_profile hα ζ ht.le]
  rfl

/-- The smooth factor after repeatedly differentiating a weighted composition. -/
def differentiatedProfile (α : ℝ) (G : ℝ → 𝕜) : ℕ → ℝ → 𝕜
  | 0 => G
  | j+1 => fun x => (α - (j : ℝ)) • differentiatedProfile α G j x +
      (α*x) • deriv (differentiatedProfile α G j) x

lemma differentiatedProfile_smooth (α : ℝ) {G : ℝ → 𝕜} (hG : ContDiff ℝ ∞ G) :
    ∀ j, ContDiff ℝ ∞ (differentiatedProfile α G j)
  | 0 => hG
  | j+1 => by
    have hj := differentiatedProfile_smooth α hG j
    exact (hj.const_smul _).add
      ((contDiff_const.mul contDiff_id).smul (contDiff_infty_iff_deriv.mp hj).2)

lemma weighted_derivative (α a : ℝ) {G : ℝ → 𝕜} (hG : Differentiable ℝ G)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => s ^ a • G (s ^ α))
      (t ^ (a-1) • (a • G (t ^ α) + (α * t ^ α) • deriv G (t ^ α))) t := by
  have h₁ := Real.hasDerivAt_rpow_const (p := a) (Or.inl ht.ne')
  have h₂ := (hG (t ^ α)).hasDerivAt.scomp t
    (Real.hasDerivAt_rpow_const (p := α) (Or.inl ht.ne'))
  convert h₁.smul h₂ using 1
  · rfl
  simp only [smul_add, smul_smul]
  have he : t ^ a * (α * t ^ (α-1)) = t ^ (a-1) * (α * t ^ α) := by
    calc
      _ = α * (t ^ a * t ^ (α-1)) := by ring
      _ = α * t ^ (a + (α-1)) := by rw [Real.rpow_add ht]
      _ = α * t ^ ((a-1) + α) := by congr 2; ring
      _ = _ := by rw [Real.rpow_add ht]; ring
  rw [he, mul_comm (t ^ (a-1)) a, add_comm]
  rfl

lemma iterated_derivative_factor {α : ℝ} (hα : 0 < α) (ζ : 𝕜) (j : ℕ)
    {t : ℝ} (ht : 0 < t) :
    iteratedDeriv j (fun s => Spec.solution α ζ s - 1) t =
      t ^ (α - (j : ℝ)) • differentiatedProfile α (profile α ζ 1) j (t ^ α) := by
  induction j generalizing t with
  | zero => simpa [differentiatedProfile] using solution_residual hα ζ ht.le
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv j (fun s => Spec.solution α ζ s - 1) =ᶠ[𝓝 t]
        (fun s => s ^ (α - (j : ℝ)) •
          differentiatedProfile α (profile α ζ 1) j (s ^ α)) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact ih hs
    rw [he.deriv_eq]
    have hd := weighted_derivative α (α - (j : ℝ))
      ((differentiatedProfile_smooth α (profile_smooth hα ζ 1) j).differentiable (by simp)) ht
    rw [hd.deriv]
    simp only [differentiatedProfile, Nat.cast_add, Nat.cast_one]
    congr 2
    ring

lemma continuous_factor_bound {α : ℝ} (hα : 0 < α) {G : ℝ → 𝕜}
    (hG : ContinuousAt G 0) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
      ∀ t : ℝ, 0 < t → t < δ → ‖G (t ^ α)‖ ≤ C := by
  have hc := (hG.norm.tendsto.comp (rpow_tendsto_zero hα)).eventually
    (gt_mem_nhds (lt_add_one ‖G 0‖))
  obtain ⟨δ, hδ, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hc
  refine ⟨‖G 0‖ + 1, δ, by positivity, hδ, ?_⟩
  intro t ht htδ
  exact (hb ⟨ht, htδ⟩).le

theorem derivative_bounds : Spec.DerivativeBounds := by
  intro 𝕜 _ α hα ζ j
  obtain ⟨C, δ, hC, hδ, hb⟩ := continuous_factor_bound hα
    (differentiatedProfile_smooth α (profile_smooth hα ζ 1) j).continuous.continuousAt
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro t ht htδ
  rw [iterated_derivative_factor hα ζ j ht, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
  exact (mul_le_mul_of_nonneg_left (hb t ht htδ) (Real.rpow_nonneg ht.le _)).trans_eq
    (mul_comm _ _)

lemma second_remainder {α : ℝ} (hα : 0 < α) (ζ : 𝕜) {t : ℝ} (ht : 0 < t) :
    Spec.solution α ζ t - 1 - (t ^ α / Real.Gamma (1 + α)) • ζ =
      t ^ (2 * α) • profile α ζ 2 (t ^ α) := by
  rw [solution_residual hα ζ ht.le, profile_shift hα ζ 1]
  have hc : coefficient α ζ 1 = (Real.Gamma (1 + α))⁻¹ • ζ := by
    simp [coefficient, add_comm]
  rw [hc, smul_add, smul_smul, div_eq_mul_inv, add_sub_cancel_left, smul_smul]
  congr 1
  rw [show 2 * α = α + α by ring, Real.rpow_add ht]

theorem expansion : Spec.Expansion := by
  intro 𝕜 _ α hα ζ
  obtain ⟨C, δ, _, hδ, hb⟩ := continuous_factor_bound hα
    (profile_smooth hα ζ 2).continuous.continuousAt
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hδ] with t ht
  rw [second_remainder hα ζ ht.1, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  exact (mul_le_mul_of_nonneg_left (hb t ht.1 ht.2)
    (Real.rpow_nonneg ht.1.le _)).trans_eq (mul_comm _ _)

lemma leading_coefficient_nonzero {α : ℝ} (hα : 0 < α) {ζ : 𝕜} (hζ : ζ ≠ 0) :
    coefficient α ζ 1 ≠ 0 := by
  rw [coefficient, pow_one]
  exact smul_ne_zero (inv_ne_zero (Real.Gamma_pos_of_pos (by positivity)).ne') hζ

theorem no_differentiable_extension : Spec.NoDifferentiableExtension := by
  intro 𝕜 _ α T hα hα₁ hT ζ hζ
  rintro ⟨v, hv, he⟩
  have hv0 : v 0 = 1 := (he 0 ⟨le_rfl, hT.le⟩).trans (solution_zero hα ζ)
  have hd := hv.hasDerivAt.tendsto_slope_zero_right
  simp only [zero_add] at hd
  have hlim : Tendsto
      (fun t : ℝ => t ^ (1 - α) • (t⁻¹ • (v t - v 0)))
      (𝓝[>] 0) (𝓝 (0 : 𝕜)) := by
    simpa only [zero_smul] using (rpow_tendsto_zero (sub_pos.mpr hα₁)).smul hd
  have heq : (fun t : ℝ => t ^ (1 - α) • (t⁻¹ • (v t - v 0))) =ᶠ[𝓝[>] 0]
      (fun t => profile α ζ 1 (t ^ α)) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    rw [he t ⟨ht.1.le, ht.2.le⟩, hv0, solution_residual hα ζ ht.1.le,
      smul_smul, smul_smul, Real.rpow_sub ht.1, Real.rpow_one]
    have hp : t ^ α ≠ 0 := (Real.rpow_pos_of_pos ht.1 α).ne'
    have hc : (t / t ^ α) * t⁻¹ * t ^ α = 1 := by field_simp [hp, ht.1.ne']
    rw [hc, one_smul]
  have hzero := hlim.congr' heq
  have hcoeff : Tendsto (fun t : ℝ => profile α ζ 1 (t ^ α))
      (𝓝[>] 0) (𝓝 (coefficient α ζ 1)) := by
    simpa only [Function.comp_def, profile_zero] using
      (profile_smooth hα ζ 1).continuous.continuousAt.tendsto.comp (rpow_tendsto_zero hα)
  exact leading_coefficient_nonzero hα hζ (tendsto_nhds_unique hcoeff hzero)

theorem no_c1_extension : Spec.NoC1Extension := by
  intro 𝕜 _ α T hα hα₁ hT ζ hζ
  rintro ⟨v, hv, he⟩
  exact no_differentiable_extension α T hα hα₁ hT ζ hζ
    ⟨v, hv.differentiableAt (by simp), he⟩

end ExpandedFA.PartV.FractionalSmoothCounterexample
