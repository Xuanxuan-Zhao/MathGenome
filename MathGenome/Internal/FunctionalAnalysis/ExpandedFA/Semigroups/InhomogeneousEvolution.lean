import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.InhomogeneousEvolution
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.ClassicalEvolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Classical and mild inhomogeneous evolution for `fa2:p3:evolution`.
The estimates use the exact supremum of operator norms. Classical existence
uses differentiation of a fixed integral and the defining generator limit,
with one-sided endpoint derivatives and the actual sum graph norm. -/

noncomputable section
open Filter Topology Set MeasureTheory
open scoped NNReal Interval
namespace ExpandedFA.Semigroups.InhomogeneousEvolution
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X
open InhomogeneousEvolutionSpec

/-- Strong continuity and local bounds give joint continuity of the action. -/
theorem continuous_action (S : C0Semigroup 𝕜 X) :
    Continuous (fun p : ℝ≥0 × X => S.operators p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact GeneratorDeterminesSemigroup.tendsto_apply S
    continuous_fst.continuousAt continuous_snd.continuousAt

theorem intervalBound_bddAbove (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) :
    BddAbove ((fun s : ℝ≥0 => ‖S.operators s‖) '' Icc 0 τ) := by
  obtain ⟨C, _, hC⟩ := S.bounded_on_interval τ
  exact ⟨C, by rintro _ ⟨s, hs, rfl⟩; exact hC s hs.2⟩

theorem norm_le_intervalBound (S : C0Semigroup 𝕜 X) (τ : ℝ≥0)
    (s : ℝ≥0) (hs : s ≤ τ) : ‖S.operators s‖ ≤ intervalBound S τ :=
  le_csSup (intervalBound_bddAbove S τ) ⟨s, ⟨s.coe_nonneg, hs⟩, rfl⟩

theorem intervalBound_nonneg (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) :
    0 ≤ intervalBound S τ :=
  (norm_nonneg _).trans (norm_le_intervalBound S τ 0 (zero_le))

theorem kernel_measurable (S : C0Semigroup 𝕜 X) (t : ℝ) {f : ℝ → X}
    {μ : Measure ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun s => S.operators (t - s).toNNReal (f s)) μ :=
  (continuous_action S).comp_aestronglyMeasurable
    ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.prodMk hf)

theorem kernel_norm_le (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) {t s : ℝ}
    (ht : t ≤ τ) (hs : 0 ≤ s) (y : X) :
    ‖S.operators (t - s).toNNReal y‖ ≤ intervalBound S τ * ‖y‖ := by
  apply ((S.operators _).le_opNorm y).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
  apply norm_le_intervalBound
  simpa only [Real.toNNReal_coe] using
    Real.toNNReal_le_toNNReal (show t - s ≤ (τ : ℝ) by linarith)

omit [CompleteSpace X] in
theorem forcing_intervalIntegrable {τ : ℝ≥0} {f : ℝ → X}
    (hf : IntegrableOn f (Icc 0 (τ : ℝ))) : IntervalIntegrable f volume 0 τ := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le τ.coe_nonneg).mpr hf

theorem kernel_integrable (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) {f : ℝ → X}
    (hf : IntegrableOn f (Icc 0 (τ : ℝ))) {t : ℝ} (ht : t ≤ τ) :
    IntegrableOn (fun s => S.operators (t - s).toNNReal (f s)) (Icc 0 (τ : ℝ)) := by
  apply (hf.norm.const_mul (intervalBound S τ)).mono'
    (kernel_measurable S t hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact kernel_norm_le S τ ht hs.1 (f s)

theorem kernel_intervalIntegrable (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) {f : ℝ → X}
    (hf : IntegrableOn f (Icc 0 (τ : ℝ))) {t : ℝ} (ht : t ∈ Icc 0 (τ : ℝ)) :
    IntervalIntegrable (fun s => S.operators (t - s).toNNReal (f s)) volume 0 t := by
  apply (forcing_intervalIntegrable (kernel_integrable S τ hf ht.2)).mono_set
  simpa only [uIcc_of_le ht.1, uIcc_of_le τ.coe_nonneg] using
    Icc_subset_Icc le_rfl ht.2

@[simp] theorem solution_zero (S : C0Semigroup 𝕜 X) (x : X) (f : ℝ → X) :
    solution S x f 0 = x := by simp [solution]

theorem convolution_norm_le (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) {f : ℝ → X}
    (hf : IntegrableOn f (Icc 0 (τ : ℝ))) {t : ℝ} (ht : t ∈ Icc 0 (τ : ℝ)) :
    ‖∫ s in (0 : ℝ)..t, S.operators (t - s).toNNReal (f s)‖ ≤
      intervalBound S τ * ∫ s in (0 : ℝ)..(τ : ℝ), ‖f s‖ := by
  have hfi := forcing_intervalIntegrable hf
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, intervalBound S τ * ‖f s‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht.1
      · exact Eventually.of_forall (fun s hs => kernel_norm_le S τ ht.2 hs.1.le _)
      · exact (hfi.norm.const_mul _).mono_set (by
          simpa only [uIcc_of_le ht.1, uIcc_of_le τ.coe_nonneg] using
            Icc_subset_Icc le_rfl ht.2)
    _ = intervalBound S τ * ∫ s in (0 : ℝ)..t, ‖f s‖ :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Eventually.of_forall (fun _ => norm_nonneg _)) hfi.norm)
      (intervalBound_nonneg S τ)

theorem solution_norm_le (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) (x : X) {f : ℝ → X}
    (hf : IntegrableOn f (Icc 0 (τ : ℝ))) {t : ℝ} (ht : t ∈ Icc 0 (τ : ℝ)) :
    ‖solution S x f t‖ ≤
      intervalBound S τ * (‖x‖ + ∫ s in (0 : ℝ)..(τ : ℝ), ‖f s‖) := by
  calc
    _ ≤ ‖S.operators t.toNNReal x‖ +
        ‖∫ s in (0 : ℝ)..t, S.operators (t - s).toNNReal (f s)‖ := norm_add_le _ _
    _ ≤ intervalBound S τ * ‖x‖ + intervalBound S τ * ∫ s in (0 : ℝ)..(τ : ℝ), ‖f s‖ :=
      add_le_add (by simpa only [sub_zero] using kernel_norm_le S τ ht.2 le_rfl x)
        (convolution_norm_le S τ hf ht)
    _ = _ := (mul_add _ _ _).symm

/-- Dominated convergence on a fixed interval handles arbitrary L¹ forcing,
including nonseparable Banach spaces. The moving endpoint is an indicator. -/
theorem convolution_continuousOn (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) {f : ℝ → X}
    (hf : IntegrableOn f (Icc 0 (τ : ℝ))) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t,
      S.operators (t - s).toNNReal (f s)) (Icc 0 (τ : ℝ)) := by
  let F : ℝ → ℝ → X := fun t => (Iic t).indicator
    (fun s => S.operators (t - s).toNNReal (f s))
  have hfi := forcing_intervalIntegrable hf
  have hmeas (t : ℝ) : AEStronglyMeasurable (F t) (volume.restrict (Ι 0 (τ : ℝ))) := by
    exact (kernel_measurable S t hfi.def'.aestronglyMeasurable).indicator measurableSet_Iic
  have heq (t : ℝ) (ht : t ∈ Icc 0 (τ : ℝ)) :
      (∫ s in (0 : ℝ)..(τ : ℝ), F t s) =
        ∫ s in (0 : ℝ)..t, S.operators (t - s).toNNReal (f s) :=
    intervalIntegral.integral_indicator ht
  intro t ht
  have hc : ContinuousWithinAt (fun t => ∫ s in (0 : ℝ)..(τ : ℝ), F t s)
      (Icc 0 (τ : ℝ)) t := by
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun s => intervalBound S τ * ‖f s‖)
    · exact Eventually.of_forall hmeas
    · filter_upwards [self_mem_nhdsWithin] with r hr
      apply Eventually.of_forall
      intro s hs
      dsimp [F]
      by_cases hsr : s ≤ r
      · rw [indicator_of_mem (show s ∈ Iic r from hsr)]
        exact kernel_norm_le S τ hr.2 (by
          rw [uIoc_of_le τ.coe_nonneg] at hs; exact hs.1.le) _
      · rw [indicator_of_notMem (show s ∉ Iic r from hsr), norm_zero]
        exact mul_nonneg (intervalBound_nonneg S τ) (norm_nonneg _)
    · exact hfi.norm.const_mul _
    · have hne : ∀ᵐ s : ℝ, s ≠ t := by
        filter_upwards [compl_mem_ae_iff.mpr (measure_singleton t)] with s hs
        exact hs
      filter_upwards [hne] with s hst
      intro _
      rcases lt_or_gt_of_ne hst with hst | hts
      · have he : (fun r => F r s) =ᶠ[𝓝[Icc 0 (τ : ℝ)] t]
            (fun r => S.operators (r - s).toNNReal (f s)) := by
          filter_upwards [(eventually_gt_nhds hst).filter_mono nhdsWithin_le_nhds] with r hr
          exact indicator_of_mem (show s ∈ Iic r from hr.le) _
        apply ContinuousWithinAt.congr_of_eventuallyEq
          ((S.continuous_real_orbit (f s)).comp
            (continuous_id.sub (continuous_const : Continuous (fun _ : ℝ => s)))).continuousAt.continuousWithinAt he
        exact indicator_of_mem (show s ∈ Iic t from hst.le) _
      · have he : (fun r => F r s) =ᶠ[𝓝[Icc 0 (τ : ℝ)] t] (fun _ => 0) := by
          filter_upwards [(eventually_lt_nhds hts).filter_mono nhdsWithin_le_nhds] with r hr
          exact indicator_of_notMem (show s ∉ Iic r from not_le.mpr hr) _
        apply continuousWithinAt_const.congr_of_eventuallyEq he
        exact indicator_of_notMem (show s ∉ Iic t from not_le.mpr hts) _
  exact hc.congr (fun r hr => (heq r hr).symm) (heq t ht).symm

theorem solution_continuousOn (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) (x : X) {f : ℝ → X}
    (hf : IntegrableOn f (Icc 0 (τ : ℝ))) :
    ContinuousOn (solution S x f) (Icc 0 (τ : ℝ)) :=
  (S.continuous_real_orbit x).continuousOn.add (convolution_continuousOn S τ hf)

theorem solution_sub (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) (x y : X) {f g : ℝ → X}
    (hf : IntegrableOn f (Icc 0 (τ : ℝ))) (hg : IntegrableOn g (Icc 0 (τ : ℝ)))
    {t : ℝ} (ht : t ∈ Icc 0 (τ : ℝ)) :
    solution S x f t - solution S y g t = solution S (x - y) (fun s => f s - g s) t := by
  simp only [solution, map_sub]
  rw [intervalIntegral.integral_sub (kernel_intervalIntegrable S τ hf ht)
    (kernel_intervalIntegrable S τ hg ht)]
  abel

theorem solution_supNorm_le (S : C0Semigroup 𝕜 X) (τ : ℝ≥0) (x : X) {f : ℝ → X}
    (hf : IntegrableOn f (Icc 0 (τ : ℝ))) :
    supNorm τ (solution S x f) ≤
      intervalBound S τ * (‖x‖ + ∫ s in (0 : ℝ)..(τ : ℝ), ‖f s‖) := by
  apply csSup_le
  · exact ⟨_, ⟨0, ⟨le_rfl, τ.coe_nonneg⟩, rfl⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact solution_norm_le S τ x hf ht

theorem mild_well_posedness : MildWellPosedness (𝕜 := 𝕜) (X := X) := by
  intro S τ x f hf
  refine ⟨fun t ht => kernel_intervalIntegrable S τ hf ht,
    solution_continuousOn S τ x hf, solution_zero S x f,
    solution_supNorm_le S τ x hf, ?_⟩
  intro y g hg
  apply csSup_le
  · exact ⟨_, ⟨0, ⟨le_rfl, τ.coe_nonneg⟩, rfl⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    dsimp only
    rw [solution_sub S τ x y hf hg ht]
    exact solution_norm_le S τ (x - y) (hf.sub hg) ht

/-- A local homogeneous equation makes the backward comparison orbit have
zero right derivative. Only the value at the current time needs to lie in D(A). -/
theorem comparison_hasDeriv_right (S : C0Semigroup 𝕜 X) (u : ℝ → X)
    {t s : ℝ} (hst : s < t) (hy : u s ∈ (A S).domain)
    (hd : HasDerivWithinAt u (A S ⟨u s, hy⟩) (Ici s) s) :
    HasDerivWithinAt (fun r => S.operators (t - r).toNNReal (u r)) 0 (Ici s) s := by
  let y : (A S).domain := ⟨u s, hy⟩
  let G : ℝ → X := fun r => S.operators (t - r).toNNReal (u s)
  have hG : HasDerivAt G (-S.operators (t - s).toNNReal (A S y)) s := by
    have horbit := (S.hasDerivWithinAt_orbit y (t - s) (sub_pos.mpr hst).le).hasDerivAt
      (Ici_mem_nhds (sub_pos.mpr hst))
    exact horbit.comp_const_sub t s
  have hu := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp (hd.mono Ioi_subset_Ici_self)
  have haction := GeneratorDeterminesSemigroup.tendsto_apply S
    ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds : Tendsto (fun r : ℝ => (t - r).toNNReal) (𝓝[>] s) (𝓝 (t - s).toNNReal)) hu
  have hGlim := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp
    (hG.hasDerivWithinAt (s := Ioi s))
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  have hz := haction.add hGlim
  simp only [y, Function.comp_def, Pi.sub_apply, id_eq, add_neg_cancel] at hz
  apply hz.congr'
  apply Eventually.of_forall
  intro r
  simp only [slope_def_module, G]
  rw [(S.operators _).map_smul_of_tower, map_sub, ← smul_add]
  congr 1
  abel

/-- Uniqueness on the actual finite closed interval, including a singleton. -/
theorem classical_uniqueness : ClassicalUniqueness (𝕜 := 𝕜) (X := X) := by
  intro S τ x f u v hsolu hsolv
  obtain ⟨hu0, hu, huc, hud, _⟩ := hsolu
  obtain ⟨hv0, hv, hvc, hvd, _⟩ := hsolv
  let w : ℝ → X := fun r => u r - v r
  have hw0 : w 0 = 0 := by simp [w, hu0, hv0]
  have hw (r : Icc (0 : ℝ) (τ : ℝ)) : w r ∈ (A S).domain :=
    (A S).domain.sub_mem (hu r) (hv r)
  have hwd (r : Icc (0 : ℝ) (τ : ℝ)) :
      HasDerivWithinAt w (A S ⟨w r, hw r⟩) (Icc 0 (τ : ℝ)) r := by
    have he : A S ⟨w r, hw r⟩ = A S ⟨u r, hu r⟩ - A S ⟨v r, hv r⟩ :=
      (A S).map_sub ⟨u r, hu r⟩ ⟨v r, hv r⟩
    simpa only [he, w, Pi.sub_def, add_sub_add_right_eq_sub] using (hud r).sub (hvd r)
  intro t ht
  have hc : ContinuousOn (fun r : ℝ => S.operators (t - r).toNNReal (w r)) (Icc 0 t) := by
    intro r hr
    exact GeneratorDeterminesSemigroup.tendsto_apply S
      ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
      (((huc.continuousOn.sub hvc.continuousOn) r ⟨hr.1, hr.2.trans ht.2⟩).mono
        (Icc_subset_Icc le_rfl ht.2))
  have hd : ∀ r ∈ Ico (0 : ℝ) t, HasDerivWithinAt
      (fun q : ℝ => S.operators (t - q).toNNReal (w q)) 0 (Ici r) r := by
    intro r hr
    apply comparison_hasDeriv_right S w hr.2 (hw ⟨r, hr.1, hr.2.le.trans ht.2⟩)
    apply (hwd ⟨r, hr.1, hr.2.le.trans ht.2⟩).mono_of_mem_nhdsWithin
    exact mem_of_superset (Icc_mem_nhdsGE (hr.2.trans_le ht.2))
      (Icc_subset_Icc hr.1 le_rfl)
  have he := constant_of_has_deriv_right_zero hc hd t ⟨ht.1, le_rfl⟩
  have hz : w t = 0 := by
    simpa only [sub_self, Real.toNNReal_zero, C0Semigroup.zero_apply,
      hw0, map_zero] using he
  exact sub_eq_zero.mp hz

/-- The zero-horizon classical existence case imposes no extra compatibility
condition on f, since all time derivatives are within the singleton. -/
theorem classical_existence_zero (S : C0Semigroup 𝕜 X) (x : (A S).domain) (f : ℝ → X) :
    IsClassicalSolution S 0 x f (solution S x f) := by
  have he : EqOn (solution S x f) (fun _ => (x : X)) (Icc (0 : ℝ) 0) := by
    intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    exact solution_zero S x f
  let hu : ∀ t : Icc (0 : ℝ) 0, solution S x f t ∈ (A S).domain :=
    fun t => (he t.2).symm ▸ x.2
  refine ⟨solution_zero S x f, hu, ?_, ?_, ?_⟩
  · exact contDiffOn_const.congr he
  · intro t
    exact HasFDerivWithinAt.of_finite (by
      simpa only [NNReal.coe_zero, Icc_self] using (finite_singleton (0 : ℝ)))
  · apply continuous_of_const
    intro t s
    have hts : t = s := Subtype.ext (le_antisymm
      (t.2.2.trans s.2.1) (s.2.2.trans t.2.1))
    subst s
    rfl

/-- Constant extension of finite-interval data. -/
def extendForcing (τ : ℝ≥0) (f : ℝ → X) (r : ℝ) : X :=
  f (projIcc 0 (τ : ℝ) τ.coe_nonneg r)

theorem extendForcing_eq (τ : ℝ≥0) (f : ℝ → X) {r : ℝ}
    (hr : r ∈ Icc 0 (τ : ℝ)) : extendForcing τ f r = f r := by
  simp [extendForcing, projIcc_of_mem _ hr]

theorem extendForcing_left (τ : ℝ≥0) (f : ℝ → X) {r : ℝ}
    (hr : r ≤ 0) : extendForcing τ f r = f 0 := by
  simp [extendForcing, projIcc_of_le_left _ hr]

theorem extendForcing_continuous (τ : ℝ≥0) {f : ℝ → X}
    (hf : ContinuousOn f (Icc 0 (τ : ℝ))) : Continuous (extendForcing τ f) :=
  hf.domRestrict.comp (LipschitzWith.projIcc τ.coe_nonneg).continuous

theorem extendForcing_lipschitz (τ : ℝ≥0) {f : ℝ → X} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc 0 (τ : ℝ))) : LipschitzWith K (extendForcing τ f) := by
  unfold extendForcing
  simpa only [mul_one, Function.comp_def, Set.domRestrict_apply] using
    hf.to_restrict.comp (LipschitzWith.projIcc τ.coe_nonneg)

/-- Reversing time in the convolution requires no differentiability. -/
theorem convolution_flip (S : C0Semigroup 𝕜 X) (f : ℝ → X) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, S.operators (t-s).toNNReal (f s)) =
      ∫ s in (0 : ℝ)..t, S.operators s.toNNReal (f (t-s)) := by
  simpa only [sub_zero, sub_self, sub_sub_cancel] using
    (intervalIntegral.integral_comp_sub_left
      (fun s => S.operators s.toNNReal (f (t-s))) t (a := 0) (b := t))

/-- Differentiation of a fixed integral of the constant extension. The two
joins of the extension never enter the pointwise derivative on a set of
positive measure, including when the parameter is an endpoint. -/
theorem extended_integral_hasDerivAt (S : C0Semigroup 𝕜 X) (τ B : ℝ≥0)
    {f : ℝ → X} (hf : ContDiffOn ℝ 1 f (Icc 0 (τ : ℝ)))
    (hτ : 0 < (τ : ℝ)) {t : ℝ} (ht : t ∈ Icc 0 (τ : ℝ)) :
    HasDerivAt (fun r => ∫ s in (0 : ℝ)..(B : ℝ),
      S.operators s.toNNReal (extendForcing τ f (r-s) - f 0))
      (∫ s in (0 : ℝ)..(B : ℝ), (Iic t).indicator
        (fun s => S.operators s.toNNReal
          (extendForcing τ (derivWithin f (Icc 0 (τ : ℝ))) (t-s))) s) t := by
  let g := derivWithin f (Icc 0 (τ : ℝ))
  have hg : ContinuousOn g (Icc 0 (τ : ℝ)) :=
    (hf.derivWithin (m := 0) (uniqueDiffOn_Icc hτ) (by simp)).continuousOn
  have hF := extendForcing_continuous τ hf.continuousOn
  have hG := extendForcing_continuous τ hg
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hL := extendForcing_lipschitz τ hK
  let C : ℝ := intervalBound S B * K
  have hC : 0 ≤ C := mul_nonneg (intervalBound_nonneg S B) K.coe_nonneg
  have hcont (r : ℝ) : Continuous (fun s : ℝ =>
      S.operators s.toNNReal (extendForcing τ f (r-s) - f 0)) :=
    (continuous_action S).comp (continuous_real_toNNReal.prodMk
      ((hF.comp (continuous_const.sub continuous_id)).sub continuous_const))
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (s := univ) (bound := fun _ => C) univ_mem
    (Eventually.of_forall (fun r => (hcont r).aestronglyMeasurable))
    ((hcont t).intervalIntegrable _ _) ?_ ?_ intervalIntegrable_const ?_).2
  · exact (((continuous_action S).comp (continuous_real_toNNReal.prodMk
      (hG.comp (continuous_const.sub continuous_id)))).aestronglyMeasurable).indicator
        measurableSet_Iic
  · apply Eventually.of_forall
    intro s hs
    rw [uIoc_of_le B.coe_nonneg] at hs
    apply LipschitzWith.lipschitzOnWith
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro r q
    calc
      _ = ‖S.operators s.toNNReal
          (extendForcing τ f (r-s) - extendForcing τ f (q-s))‖ := by
        rw [dist_eq_norm, ← map_sub]; congr 1; abel
      _ ≤ intervalBound S B *
          ‖extendForcing τ f (r-s) - extendForcing τ f (q-s)‖ := by
        simpa only [sub_zero] using kernel_norm_le S B (t := s) (s := 0) hs.2 le_rfl _
      _ ≤ intervalBound S B * (K * dist (r-s) (q-s)) :=
        mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hL.dist_le_mul (r-s) (q-s))
          (intervalBound_nonneg S B)
      _ = (Real.nnabs C : ℝ) * dist r q := by
        simp only [Real.coe_nnabs, abs_of_nonneg hC, C, dist_sub_right]; ring
  · have hne : ∀ᵐ s : ℝ, s ≠ t := by
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton t)] with s hs
      exact hs
    filter_upwards [hne] with s hst hs
    rw [uIoc_of_le B.coe_nonneg] at hs
    by_cases hlt : s < t
    · have hin : t-s ∈ Ioo 0 (τ : ℝ) := ⟨by linarith, by linarith [hs.1, ht.2]⟩
      have he : (fun r => extendForcing τ f (r-s)) =ᶠ[𝓝 t] (fun r => f (r-s)) := by
        filter_upwards [(continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
          (Ioo_mem_nhds hin.1 hin.2)] with r hr
        exact extendForcing_eq τ f ⟨hr.1.le, hr.2.le⟩
      have hd := (((hf.differentiableOn one_ne_zero (t-s) ⟨hin.1.le, hin.2.le⟩).hasDerivWithinAt).hasDerivAt (Icc_mem_nhds hin.1 hin.2)).comp_sub_const t s
      rw [show derivWithin f (Icc 0 (τ : ℝ)) (t-s) = g (t-s) from rfl] at hd
      have hd' := (hd.congr_of_eventuallyEq he).sub_const (f 0)
      have hout := ((S.operators s.toNNReal).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd'
      change HasDerivAt _ ((Iic t).indicator
        (fun s => S.operators s.toNNReal (extendForcing τ g (t-s))) s) t
      rw [indicator_of_mem (show s ∈ Iic t from hlt.le),
        extendForcing_eq τ g ⟨hin.1.le, hin.2.le⟩]
      exact hout
    · have hgt : t < s := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hst)
      have he : (fun r => S.operators s.toNNReal (extendForcing τ f (r-s) - f 0))
          =ᶠ[𝓝 t] (fun _ => (0 : X)) := by
        filter_upwards [eventually_lt_nhds hgt] with r hr
        simp [extendForcing_left τ f (show r-s ≤ 0 by linarith)]
      simpa only [indicator_of_notMem (show s ∉ Iic t from not_le.mpr hgt)] using
        (hasDerivAt_const t (0 : X)).congr_of_eventuallyEq he

/-- A fixed-interval representation, valid on its entire nonnegative horizon. -/
def extendedConvolution (S : C0Semigroup 𝕜 X) (τ B : ℝ≥0) (f : ℝ → X) (t : ℝ) : X :=
  (∫ s in (0 : ℝ)..t, S.operators s.toNNReal (f 0)) +
    ∫ s in (0 : ℝ)..(B : ℝ),
      S.operators s.toNNReal (extendForcing τ f (t-s) - f 0)

theorem extendedConvolution_eq (S : C0Semigroup 𝕜 X) (τ B : ℝ≥0)
    {f : ℝ → X} (hf : ContinuousOn f (Icc 0 (τ : ℝ)))
    {t : ℝ} (ht : t ∈ Icc 0 (B : ℝ)) :
    extendedConvolution S τ B f t =
      ∫ s in (0 : ℝ)..t, S.operators (t-s).toNNReal (extendForcing τ f s) := by
  let F := extendForcing τ f
  have hc : Continuous F := extendForcing_continuous τ hf
  have hk : Continuous (fun s : ℝ => S.operators s.toNNReal (F (t-s) - f 0)) :=
    (continuous_action S).comp (continuous_real_toNNReal.prodMk
      ((hc.comp (continuous_const.sub continuous_id)).sub continuous_const))
  have he : (∫ s in (0 : ℝ)..(B : ℝ), S.operators s.toNNReal (F (t-s) - f 0)) =
      ∫ s in (0 : ℝ)..t, S.operators s.toNNReal (F (t-s) - f 0) := by
    rw [← intervalIntegral.integral_indicator ht]
    apply intervalIntegral.integral_congr
    intro s hs
    by_cases hst : s ≤ t
    · simp only [indicator, mem_ofPred_eq, hst, ↓reduceIte]
    · simp only [indicator, mem_ofPred_eq, hst, ↓reduceIte]
      simp only [F, extendForcing_left τ f (show t-s ≤ 0 by linarith), sub_self, map_zero]
  rw [extendedConvolution, he, convolution_flip]
  rw [← intervalIntegral.integral_add ((S.continuous_real_orbit (f 0)).intervalIntegrable 0 t)
    (hk.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro s _
  change S.operators s.toNNReal (f 0) + S.operators s.toNNReal (F (t-s)-f 0) =
    S.operators s.toNNReal (F (t-s))
  rw [map_sub]
  abel

theorem extendedConvolution_hasDerivAt (S : C0Semigroup 𝕜 X) (τ B : ℝ≥0)
    {f : ℝ → X} (hf : ContDiffOn ℝ 1 f (Icc 0 (τ : ℝ)))
    (hτ : 0 < (τ : ℝ)) (hB : τ ≤ B) {t : ℝ} (ht : t ∈ Icc 0 (τ : ℝ)) :
    HasDerivAt (extendedConvolution S τ B f)
      (S.operators t.toNNReal (f 0) +
        ∫ s in (0 : ℝ)..t, S.operators (t-s).toNNReal
          (derivWithin f (Icc 0 (τ : ℝ)) s)) t := by
  have hd := (S.hasDerivAt_integral (f 0) t).add
    (extended_integral_hasDerivAt S τ B hf hτ ht)
  have he : (∫ s in (0 : ℝ)..(B : ℝ), (Iic t).indicator
      (fun s => S.operators s.toNNReal
        (extendForcing τ (derivWithin f (Icc 0 (τ : ℝ))) (t-s))) s) =
      ∫ s in (0 : ℝ)..t, S.operators (t-s).toNNReal
        (derivWithin f (Icc 0 (τ : ℝ)) s) := by
    calc
      _ = ∫ s in (0 : ℝ)..t, S.operators s.toNNReal
          (extendForcing τ (derivWithin f (Icc 0 (τ : ℝ))) (t-s)) :=
        intervalIntegral.integral_indicator (a₁ := 0) (a₂ := t) (a₃ := (B : ℝ))
          ⟨ht.1, ht.2.trans (by exact_mod_cast hB)⟩
      _ = _ := by
        rw [convolution_flip]
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ht.1] at hs
        dsimp only
        rw [extendForcing_eq τ (derivWithin f (Icc 0 (τ : ℝ)))
          ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩]
  rw [he] at hd
  exact hd

/-- Splitting the mild convolution exposes the semigroup evolution of its
previous value and the contribution from the new time interval. -/
theorem convolution_add_time (S : C0Semigroup 𝕜 X) {f : ℝ → X}
    (hf : Continuous f) {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h) :
    (∫ s in (0 : ℝ)..(t+h), S.operators (t+h-s).toNNReal (f s)) =
      S.operators h.toNNReal (∫ s in (0 : ℝ)..t, S.operators (t-s).toNNReal (f s)) +
        ∫ s in t..(t+h), S.operators (t+h-s).toNNReal (f s) := by
  have hc (r : ℝ) : Continuous (fun s : ℝ => S.operators (r-s).toNNReal (f s)) :=
    (continuous_action S).comp
      ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).prodMk hf)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hc (t+h)).intervalIntegrable 0 t) ((hc (t+h)).intervalIntegrable t (t+h))]
  congr 1
  rw [← (S.operators h.toNNReal).intervalIntegral_comp_comm ((hc t).intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  dsimp only
  rw [← S.add_apply]
  congr 2
  apply NNReal.coe_injective
  rw [NNReal.coe_add, Real.coe_toNNReal _ hh,
    Real.coe_toNNReal _ (show 0 ≤ t-s by linarith [hs.2]),
    Real.coe_toNNReal _ (show 0 ≤ t+h-s by linarith [hs.2])]
  ring

/-- Normalizing the new-time contribution gives the forcing at the base time.
A linear change of variables makes the domain of integration fixed. -/
theorem convolution_boundary_limit (S : C0Semigroup 𝕜 X) {f : ℝ → X}
    (hf : Continuous f) (t : ℝ) :
    Tendsto (fun h : ℝ => h⁻¹ •
      ∫ s in t..(t+h), S.operators (t+h-s).toNNReal (f s)) (𝓝[>] 0) (𝓝 (f t)) := by
  let H : ℝ → ℝ → X := fun h r => S.operators (h-h*r).toNNReal (f (h*r+t))
  have hc : Continuous H.uncurry := by
    exact (continuous_action S).comp
      ((continuous_real_toNNReal.comp
        (continuous_fst.sub (continuous_fst.mul continuous_snd))).prodMk
        (hf.comp ((continuous_fst.mul continuous_snd).add continuous_const)))
  have hi : Continuous (fun h => ∫ r in (0 : ℝ)..1, H h r) := by
    have he : (fun h => ∫ r in (0 : ℝ)..1, H h r) =
        (fun h => ∫ r in Icc (0 : ℝ) 1, H h r) := by
      funext h
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
    rw [he]
    exact continuous_parametric_integral_of_continuous hc isCompact_Icc
  have hz : (∫ r in (0 : ℝ)..1, H 0 r) = f t := by simp [H]
  rw [← hz]
  apply hi.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have he := intervalIntegral.integral_comp_mul_add
    (fun s => S.operators (t+h-s).toNNReal (f s)) (ne_of_gt hh) t (a := 0) (b := 1)
  simpa only [H, mul_zero, zero_add, mul_one, add_comm h t,
    show ∀ r : ℝ, t+h-(h*r+t) = h-h*r by intro r; ring] using he

/-- Differentiability of a mild convolution gives membership in the exact
generator graph. The comparison curve need only agree for nearby future times. -/
theorem convolution_generator_limit (S : C0Semigroup 𝕜 X) {f V : ℝ → X}
    (hf : Continuous f) {t : ℝ} (ht : 0 ≤ t) {d : X} (hd : HasDerivAt V d t)
    (he : (fun h : ℝ => V (t+h)) =ᶠ[𝓝[>] 0]
      (fun h => ∫ s in (0 : ℝ)..(t+h), S.operators (t+h-s).toNNReal (f s)))
    (het : V t = ∫ s in (0 : ℝ)..t, S.operators (t-s).toNNReal (f s)) :
    HasGeneratorLimit S (V t) (d - f t) := by
  have hd' := (show HasDerivAt V d (t+0) by simpa using hd).comp_const_add t 0
  have hl := hd'.tendsto_slope_zero_right.sub (convolution_boundary_limit S hf t)
  change Tendsto (fun h => differenceQuotient S h (V t)) (𝓝[>] 0) (𝓝 (d-f t))
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin, he] with h hh heh
  simp only [add_zero, zero_add] at *
  rw [S.differenceQuotient_real, heh, convolution_add_time S hf ht hh.le, ← het]
  simp only [smul_sub, smul_add]
  abel

/-- C¹ forcing gives the exact classical convolution, with continuity in the
sum graph norm. The proof uses the defining generator limit directly. -/
theorem convolution_classical (S : C0Semigroup 𝕜 X) (τ : ℝ≥0)
    {f : ℝ → X} (hf : ContDiffOn ℝ 1 f (Icc 0 (τ : ℝ)))
    (hτ : 0 < (τ : ℝ)) :
    IsClassicalSolution S τ 0 f
      (fun t => ∫ s in (0 : ℝ)..t, S.operators (t-s).toNNReal (f s)) := by
  let I := Icc (0 : ℝ) (τ : ℝ)
  let B : ℝ≥0 := τ + 1
  let v : ℝ → X := fun t => ∫ s in (0 : ℝ)..t, S.operators (t-s).toNNReal (f s)
  let V := extendedConvolution S τ B f
  let g := derivWithin f I
  let d := solution S (f 0) g
  have hg : ContinuousOn g I :=
    (hf.derivWithin (m := 0) (uniqueDiffOn_Icc hτ) (by simp)).continuousOn
  have hdc : ContinuousOn d I := solution_continuousOn S τ (f 0) hg.integrableOn_Icc
  have he (t : ℝ) (ht : t ∈ I) : V t = v t := by
    dsimp only [V, v]
    rw [extendedConvolution_eq S τ B hf.continuousOn
      ⟨ht.1, ht.2.trans (by dsimp [B]; simp)⟩]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    dsimp only
    rw [extendForcing_eq τ f ⟨hs.1, hs.2.trans ht.2⟩]
  have hdV (t : ℝ) (ht : t ∈ I) : HasDerivAt V (d t) t :=
    extendedConvolution_hasDerivAt S τ B hf hτ (by dsimp [B]; simp) ht
  have hd (t : ℝ) (ht : t ∈ I) : HasDerivWithinAt v (d t) I t :=
    (hdV t ht).hasDerivWithinAt.congr (fun r hr => (he r hr).symm) (he t ht).symm
  have hl (t : ℝ) (ht : t ∈ I) : HasGeneratorLimit S (v t) (d t - f t) := by
    have hE : (fun h : ℝ => V (t+h)) =ᶠ[𝓝[>] 0]
        (fun h => ∫ s in (0 : ℝ)..(t+h), S.operators (t+h-s).toNNReal
          (extendForcing τ f s)) := by
      have hδ : 0 < (B : ℝ) - t := by
        change 0 < (τ : ℝ) + 1 - t
        linarith [ht.2]
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with h hh hsmall
      exact extendedConvolution_eq S τ B hf.continuousOn ⟨add_nonneg ht.1 hh.le, by linarith⟩
    have hlim := convolution_generator_limit S
      (extendForcing_continuous τ hf.continuousOn) ht.1 (hdV t ht) hE
      (extendedConvolution_eq S τ B hf.continuousOn
        ⟨ht.1, ht.2.trans (by dsimp [B]; simp)⟩)
    rwa [he t ht, extendForcing_eq τ f ht] at hlim
  let hv : ∀ t : I, v t ∈ (A S).domain := fun t => ⟨d t-f t, hl t t.2⟩
  have hAv (t : I) : A S ⟨v t, hv t⟩ = d t-f t :=
    generator_limit_unique S _ _ _ (generator_has_limit S ⟨v t, hv t⟩) (hl t t.2)
  have hvc : ContDiffOn ℝ 1 v I := by
    apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hτ)).mpr
    refine ⟨fun t ht => (hd t ht).differentiableWithinAt, ?_⟩
    exact hdc.congr (fun t ht => (hd t ht).derivWithin ((uniqueDiffOn_Icc hτ) t ht))
  refine ⟨by simp, hv, hvc, ?_, ?_⟩
  · intro t
    rw [hAv]
    simpa only [sub_add_cancel] using hd t t.2
  · apply continuous_iff_continuousAt.mpr
    intro t
    apply (ClassicalEvolution.tendsto_graph_iff (A S)).mpr
    constructor
    · exact (hvc.continuousOn.domRestrict).continuousAt
    · have hc : Continuous (fun r : I => d r - f r) :=
        (hdc.sub hf.continuousOn).domRestrict
      change Tendsto (fun r : I => A S ⟨v r, hv r⟩) (𝓝 t) (𝓝 (A S ⟨v t, hv t⟩))
      simp only [hAv]
      exact hc.continuousAt

/-- Classical existence for the original variation-of-constants formula,
including a zero horizon and both one-sided endpoint derivatives. -/
theorem classical_existence : ClassicalExistence (𝕜 := 𝕜) (X := X) := by
  intro S τ x f hf
  by_cases hτ : τ = 0
  · subst τ
    exact classical_existence_zero S x f
  have hpos : 0 < (τ : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hτ)
  obtain ⟨_, hv, hvc, hvd, hvg⟩ := convolution_classical S τ hf hpos
  obtain ⟨_, ho, hoc, hod⟩ := ClassicalEvolution.classical_existence S x
  let hu : ∀ t : Icc (0 : ℝ) (τ : ℝ), solution S x f t ∈ (A S).domain :=
    fun t => (A S).domain.add_mem (ho ⟨t, t.2.1⟩) (hv t)
  have hA (t : Icc (0 : ℝ) (τ : ℝ)) :
      A S ⟨solution S x f t, hu t⟩ =
        S.operators (t : ℝ).toNNReal (A S x) +
          A S ⟨(∫ s in (0 : ℝ)..(t : ℝ), S.operators ((t : ℝ)-s).toNNReal (f s)), hv t⟩ := by
    rw [show (⟨solution S x f t, hu t⟩ : (A S).domain) =
        ⟨S.operators (t : ℝ).toNNReal x, ho ⟨t, t.2.1⟩⟩ +
        ⟨_, hv t⟩ from rfl, (A S).map_add]
    rw [SemigroupGrowthAndGenerator.generator_commutes S _ x _]
  refine ⟨solution_zero S x f, hu,
    (hoc.mono (show Icc (0 : ℝ) (τ : ℝ) ⊆ Ici 0 from Icc_subset_Ici_self)).add hvc, ?_, ?_⟩
  · intro t
    rw [hA]
    have hd := (S.hasDerivWithinAt_orbit x t t.2.1).mono Icc_subset_Ici_self |>.add (hvd t)
    convert hd using 1 <;> first | rfl | (simp only [add_assoc, generator, A, C0SemigroupSpec.generatorValue])
  · apply continuous_iff_continuousAt.mpr
    intro t
    apply (ClassicalEvolution.tendsto_graph_iff (A S)).mpr
    constructor
    · exact ((solution_continuousOn S τ x hf.continuousOn.integrableOn_Icc).domRestrict).continuousAt
    · have hvA : Continuous (fun r : Icc (0 : ℝ) (τ : ℝ) => A S
          (Unbounded.GraphDomain.toDomain (A S) (⟨_, hv r⟩ : Unbounded.GraphDomain (A S)))) := by
        apply continuous_iff_continuousAt.mpr
        intro r
        exact ((ClassicalEvolution.tendsto_graph_iff (A S)).mp hvg.continuousAt).2
      have hc := ((S.continuous_real_orbit (A S x)).comp continuous_subtype_val).add hvA
      simp only [Unbounded.GraphDomain.toDomain, hA]
      exact hc.continuousAt

end ExpandedFA.Semigroups.InhomogeneousEvolution
