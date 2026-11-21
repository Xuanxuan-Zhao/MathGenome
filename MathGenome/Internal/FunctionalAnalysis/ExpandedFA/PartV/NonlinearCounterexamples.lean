import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.NonlinearCounterexamples
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.PartV.NonlinearCounterexamples

lemma waiting_of_le {c t : ℝ} (ht : t ≤ c) : waiting c t = 0 := by
  simp [waiting, max_eq_right (sub_nonpos.mpr ht)]

lemma waiting_of_ge {c t : ℝ} (ht : c ≤ t) : waiting c t = (t-c)^2 := by
  simp [waiting, max_eq_left (sub_nonneg.mpr ht)]

lemma continuous_waiting (c : ℝ) : Continuous (waiting c) := by
  unfold waiting
  fun_prop

lemma waiting_integrand (c s : ℝ) :
    2 * Real.sqrt |waiting c s| = 2 * max (s-c) 0 := by
  rw [waiting, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (le_max_right _ _)]

lemma waiting_integral {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    (∫ s in 0..t, 2 * Real.sqrt |waiting c s|) = waiting c t := by
  simp_rw [waiting_integrand]
  have hcont : Continuous (fun s : ℝ => 2 * max (s-c) 0) := by fun_prop
  by_cases htc : t ≤ c
  · rw [waiting_of_le htc]
    trans ∫ _s in (0 : ℝ)..t, (0 : ℝ)
    swap
    · simp
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    simp [max_eq_right (show s-c ≤ 0 by linarith [hs.2])]
  · have hct : c ≤ t := le_of_not_ge htc
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 c) (hcont.intervalIntegrable c t)]
    have hz : (∫ s in 0..c, 2 * max (s-c) 0) = 0 := by
      trans ∫ _s in (0 : ℝ)..c, (0 : ℝ)
      swap
      · simp
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hc] at hs
      simp [max_eq_right (show s-c ≤ 0 by linarith [hs.2])]
    rw [hz, zero_add, waiting_of_ge hct]
    calc
      (∫ s in c..t, 2 * max (s-c) 0) = ∫ s in c..t, 2 * (s-c) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hct] at hs
        simp only [max_eq_left (sub_nonneg.mpr hs.1)]
      _ = (t-c)^2 := by
        rw [intervalIntegral.integral_const_mul]
        have hi : (∫ s in c..t, s-c) = (∫ s in c..t, s) - ∫ _s in c..t, c :=
          intervalIntegral.integral_sub (continuous_id.intervalIntegrable c t)
            (continuous_const.intervalIntegrable c t)
        rw [hi, integral_id, intervalIntegral.integral_const]
        ring

theorem waiting_family : Spec.WaitingFamily := by
  intro T hT c hc
  refine ⟨⟨(continuous_waiting c).continuousOn, fun t ht =>
    (waiting_integral hc ht.1).symm⟩, fun t ht => waiting_of_le ht,
    fun t ht => waiting_of_ge ht, ?_⟩
  intro t ht
  refine ⟨sq_nonneg _, ?_⟩
  unfold waiting
  apply pow_le_pow_left₀ (le_max_right _ _) _
  exact max_le (by linarith) ht.1

theorem waiting_nonuniqueness : Spec.Nonuniqueness := by
  intro T hT
  refine ⟨waiting 0, waiting T, (waiting_family T hT.le 0 le_rfl).1,
    (waiting_family T hT.le T hT.le).1, ?_, ?_⟩
  · simp [waiting_of_le (le_refl (0 : ℝ)), waiting_of_le hT.le]
  · rw [waiting_of_ge hT.le, waiting_of_le (le_refl T), sub_zero]
    exact ne_of_gt (sq_pos_of_pos hT)

/-- Constant extension is used only to apply FTC; all asserted equations
remain equations for the original function on the original interval. -/
lemma continuous_extension {F : Type*} [TopologicalSpace F] {T : ℝ}
    (hT : 0 ≤ T) {f : ℝ → F} (hf : ContinuousOn f (Icc 0 T)) :
    ∃ g : ℝ → F, Continuous g ∧ EqOn g f (Icc 0 T) := by
  refine ⟨IccExtend hT (fun t : Icc 0 T => f t), ?_, ?_⟩
  · exact (continuousOn_iff_continuous_domRestrict.mp hf).Icc_extend'
  · intro t ht
    exact IccExtend_of_mem hT _ ht

lemma primitive_derivative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : ℝ → F} (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun t => ∫ s in 0..t, f s) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

lemma integral_eq_on_initial {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {T t : ℝ} {f g : ℝ → F} (hfg : EqOn f g (Icc 0 T)) (ht : t ∈ Icc 0 T) :
    (∫ s in 0..t, f s) = ∫ s in 0..t, g s := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  exact hfg ⟨hs.1, hs.2.trans ht.2⟩

lemma integral_equation_deriv_right {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {T : ℝ} (hT : 0 ≤ T)
    {u f : ℝ → F} {ξ : F} (hf : ContinuousOn f (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T, u t = ξ + ∫ s in 0..t, f s)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt u (f t) (Ici t) t := by
  obtain ⟨g, hg, hgf⟩ := continuous_extension hT hf
  have hp := ((primitive_derivative hg t).const_add ξ).hasDerivWithinAt (s := Ici t)
  rw [hgf ⟨ht.1, ht.2.le⟩] at hp
  have he' (x : ℝ) (hx : x ∈ Icc 0 T) :
      u x = ξ + ∫ s in 0..x, g s := by
    rw [he x hx, integral_eq_on_initial hgf hx]
  apply hp.congr_of_eventuallyEq _ (he' t ⟨ht.1, ht.2.le⟩)
  filter_upwards [Icc_mem_nhdsGE ht.2] with x hx
  exact he' x ⟨ht.1.trans hx.1, hx.2⟩

section Scalar
variable {𝕜 : Type*} [RCLike 𝕜]

theorem scalar_waiting_family : Spec.ScalarWaitingFamily := by
  intro 𝕜 _ T hT
  have hs (c : ℝ) (hc : 0 ≤ c) :
      IsScalarWaitingSolution 𝕜 T (fun t => (waiting c t : 𝕜)) := by
    refine ⟨(RCLike.continuous_ofReal.comp (continuous_waiting c)).continuousOn, ?_⟩
    intro t ht
    simpa only [RCLike.norm_ofReal, RCLike.intervalIntegral_ofReal] using
      congrArg (fun x : ℝ => (x : 𝕜)) (waiting_integral hc ht.1).symm
  refine ⟨hs, ?_⟩
  intro hTpos
  refine ⟨(fun t => (waiting 0 t : 𝕜)), (fun t => (waiting T t : 𝕜)),
    hs 0 le_rfl, hs T hT, ?_, ?_⟩
  · simp [waiting_of_le (le_refl (0 : ℝ)), waiting_of_le hT]
  · intro he
    have hh := RCLike.ofReal_injective he
    rw [waiting_of_ge hT, waiting_of_le (le_refl T), sub_zero] at hh
    exact (sq_pos_of_pos hTpos).ne' hh

lemma cast_derivative (t : ℝ) : HasDerivAt (fun s : ℝ => (s : 𝕜)) 1 t := by
  simpa using (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasDerivAt (x := t)

lemma blowup_derivative {t : ℝ} (ht : t < 1) :
    HasDerivAt (blowup 𝕜) ((blowup 𝕜 t)^2) t := by
  have hn : (1 - (t : 𝕜)) ≠ 0 := by
    rw [← RCLike.ofReal_one, ← RCLike.ofReal_sub, RCLike.ofReal_ne_zero]
    linarith
  convert! ((cast_derivative (𝕜 := 𝕜) t).const_sub 1).inv hn using 1
  simp [blowup, inv_pow]

theorem blowup_existence : Spec.BlowupExistence := by
  intro 𝕜 _ T hT hT1
  have hc : ContinuousOn (blowup 𝕜) (Icc 0 T) := by
    intro t ht
    exact (blowup_derivative (lt_of_le_of_lt ht.2 hT1)).continuousAt.continuousWithinAt
  refine ⟨hc, ?_⟩
  intro t ht
  have hd : ∀ s ∈ Ioo 0 t,
      HasDerivAt (blowup 𝕜) ((blowup 𝕜 s)^2) s := by
    intro s hs
    exact blowup_derivative ((hs.2.trans_le ht.2).trans hT1)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hc.mono (Icc_subset_Icc_right ht.2)) hd
    (((hc.mono (Icc_subset_Icc_right ht.2)).pow 2).intervalIntegrable_of_Icc ht.1)
  simpa [blowup] using (eq_add_of_sub_eq' hi.symm)

/-- A necessary identity valid even if the alleged interval reaches one. -/
lemma square_solution_identity {T : ℝ} (hT : 0 ≤ T) {u : ℝ → 𝕜}
    (hu : IsSquareSolution 𝕜 T u) :
    ∀ t ∈ Icc 0 T, (1 - (t : 𝕜)) * u t = 1 := by
  have hu0 : u 0 = 1 := by simpa using hu.2 0 ⟨le_rfl, hT⟩
  let q : ℝ → 𝕜 := fun t => (1 - (t : 𝕜)) * u t - 1
  have hqc : ContinuousOn q (Icc 0 T) :=
    ((continuousOn_const.sub RCLike.continuous_ofReal.continuousOn).mul hu.1).sub continuousOn_const
  have hqd : ∀ t ∈ Ico 0 T, HasDerivWithinAt q (u t * q t) (Ici t) t := by
    intro t ht
    have hd := integral_equation_deriv_right hT (hu.1.pow 2) hu.2 ht
    convert (((cast_derivative (𝕜 := 𝕜) t).const_sub 1).hasDerivWithinAt.mul hd).sub_const 1 using 1
    dsimp [q]
    ring
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hu.1).isBounded.exists_norm_le
  have hzero : ∀ t ∈ Icc 0 T, q t = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hqc hqd (by simp [q, hu0])
      (fun t ht => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _ ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩) (norm_nonneg _))
  intro t ht
  exact sub_eq_zero.mp (hzero t ht)

theorem blowup_uniqueness : Spec.BlowupUniqueness := by
  intro 𝕜 _ T hT hT1 u hu t ht
  have hi := square_solution_identity hT hu t ht
  have hn : 1 - (t : 𝕜) ≠ 0 := by
    rw [← RCLike.ofReal_one, ← RCLike.ofReal_sub, RCLike.ofReal_ne_zero]
    linarith [ht.2]
  change u t = (1 - (t : 𝕜))⁻¹
  calc
    u t = (1 - (t : 𝕜))⁻¹ * ((1 - (t : 𝕜)) * u t) := by
      rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
    _ = (1 - (t : 𝕜))⁻¹ := by rw [hi, mul_one]

theorem blowup_on_maximal_interval : Spec.BlowupOnMaximalInterval := by
  intro 𝕜 _
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (blowup_derivative ht.2).continuousAt.continuousWithinAt
  · intro t ht
    exact (blowup_existence 𝕜 t ht.1 ht.2).2 t ⟨ht.1, le_rfl⟩
  · intro u hc he t ht
    have hs : Icc 0 t ⊆ Ico 0 1 := fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
    exact blowup_uniqueness 𝕜 t ht.1 ht.2 u
      ⟨hc.mono hs, fun s hs' => he s (hs hs')⟩ ⟨ht.1, le_rfl⟩

theorem no_solution_through_one : Spec.NoSolutionThroughOne := by
  intro 𝕜 _ T hT ⟨u, hu⟩
  have hi := square_solution_identity (by linarith : 0 ≤ T) hu 1 ⟨zero_le_one, hT⟩
  simp at hi

theorem no_bounded_continuation : Spec.NoBoundedContinuation := by
  intro 𝕜 _ ⟨u, M, heq, hb⟩
  have hM : 0 ≤ M := (norm_nonneg (u 0)).trans (hb 0 ⟨le_rfl, zero_lt_one⟩)
  let t : ℝ := 1 - (M+2)⁻¹
  have hp : 0 < M+2 := by linarith
  have ht : t ∈ Ico 0 1 := by
    constructor
    · dsimp [t]
      have := (inv_le_one₀ hp).mpr (by linarith : 1 ≤ M+2)
      linarith
    · dsimp [t]
      exact sub_lt_self _ (inv_pos.mpr hp)
  have hr : 1-t = (M+2)⁻¹ := by dsimp [t]; ring
  have hn : ‖blowup 𝕜 t‖ = M+2 := by
    dsimp [blowup]
    rw [← RCLike.ofReal_one, ← RCLike.ofReal_sub, hr,
      ← RCLike.ofReal_inv, inv_inv, RCLike.norm_ofReal, abs_of_pos hp]
  have hm := hb t ht
  rw [heq ht, hn] at hm
  linarith

theorem homogeneous_constants : Spec.HomogeneousConstants := by
  intro 𝕜 _ T hT z
  refine ⟨continuousOn_const, ?_⟩
  intro t ht
  simp [intervalIntegral.integral_const, RCLike.real_smul_eq_coe_mul]

theorem third_singleton : Spec.ThirdSingleton := by
  intro 𝕜 _ u
  have hc : ContinuousOn u (Icc (0 : ℝ) 0) := by
    rw [Icc_self]
    exact (subsingleton_singleton).continuousOn u
  constructor <;> refine ⟨hc, ?_⟩ <;> intro t ht <;>
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
  all_goals subst t; simp

/-- The average of a continuous function over [0,t] tends to its value at
zero. Here FTC supplies the limit, with the original equation substituted
only for 0 < t ≤ T. -/
theorem inhomogeneous_nonexistence : Spec.InhomogeneousNonexistence := by
  intro 𝕜 _ T hT ⟨u, hu⟩
  obtain ⟨v, hv, hvu⟩ := continuous_extension hT.le hu.1
  have hv0 : v 0 = u 0 := hvu ⟨le_rfl, hT.le⟩
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • (∫ s in 0..t, v s))
      (𝓝[>] 0) (𝓝 (u 0)) := by
    simpa [hv0] using (primitive_derivative hv 0).tendsto_slope_zero_right
  have heq : v =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => 1 + t⁻¹ • (∫ s in 0..t, v s)) := by
    filter_upwards [Ioc_mem_nhdsGT hT] with t ht
    have htu : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have he := hu.2 t htu
    simp only [ite_true] at he
    rw [← integral_eq_on_initial hvu htu] at he
    have hn : (t : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr ht.1.ne'
    rw [hvu htu]
    rw [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv]
    calc
      u t = (t : 𝕜)⁻¹ * ((t : 𝕜) * u t) := by
        rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
      _ = 1 + (t : 𝕜)⁻¹ * ∫ s in 0..t, v s := by
        rw [he, mul_add, inv_mul_cancel₀ hn]
  have hl : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 (u 0)) := by
    simpa [hv0] using (hv.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hr : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 (1 + u 0)) :=
    (tendsto_const_nhds.add hlim).congr' heq.symm
  have hh : u 0 = 1 + u 0 := tendsto_nhds_unique hl hr
  have : (0 : 𝕜) = 1 := by linear_combination hh
  exact zero_ne_one this

end Scalar

end ExpandedFA.PartV.NonlinearCounterexamples
