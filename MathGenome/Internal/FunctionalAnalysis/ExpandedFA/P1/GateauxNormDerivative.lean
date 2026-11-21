import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.GateauxNormDerivative
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C13Alaoglu
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ExpandedFA.P1.GateauxNormDerivative

open Filter Set
open scoped Topology
universe u v

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma re_apply_le_norm (f : E →L[𝕜] 𝕜) (hf : ‖f‖ ≤ 1) (y : E) :
    RCLike.re (f y) ≤ ‖y‖ := by
  calc
    RCLike.re (f y) ≤ ‖f y‖ := RCLike.re_le_norm _
    _ ≤ ‖f‖ * ‖y‖ := f.le_opNorm y
    _ ≤ ‖y‖ := by nlinarith [norm_nonneg y]

lemma support_lower (x h : E) (f : E →L[𝕜] 𝕜) (hf : ‖f‖ ≤ 1)
    (hfx : f x = (‖x‖ : 𝕜)) (t : ℝ) :
    ‖x‖ + t * RCLike.re (f h) ≤ ‖x + (t : 𝕜) • h‖ := by
  simpa [map_add, map_smul, hfx, RCLike.mul_re] using
    re_apply_le_norm f hf (x + (t : 𝕜) • h)

lemma support_upper (x h : E) {t : ℝ} (g : E →L[𝕜] 𝕜) (hg : ‖g‖ ≤ 1)
    (hgx : g (x + (t : 𝕜) • h) = (‖x + (t : 𝕜) • h‖ : 𝕜)) :
    ‖x + (t : 𝕜) • h‖ ≤ ‖x‖ + t * RCLike.re (g h) := by
  have he := congrArg RCLike.re hgx
  simp only [map_add, map_smul, smul_eq_mul, map_add, RCLike.mul_re,
    RCLike.ofReal_re, RCLike.ofReal_im, zero_mul, sub_zero] at he
  linarith [re_apply_le_norm g hg x]

/-- A derivative, when it exists, agrees with every norming functional. -/
lemma derivative_eq_re_support (x h : E) (f : E →L[𝕜] 𝕜)
    (hf : ‖f‖ ≤ 1) (hfx : f x = (‖x‖ : 𝕜)) {d : ℝ}
    (hd : HasDerivAt (fun t : ℝ => ‖x + (t : 𝕜) • h‖) d 0) :
    d = RCLike.re (f h) := by
  have hmin : IsLocalMin (fun t : ℝ =>
      ‖x + (t : 𝕜) • h‖ - (‖x‖ + t * RCLike.re (f h))) 0 := by
    apply IsMinOn.isLocalMin (s := univ) _ (by simp)
    intro t _
    simpa using sub_nonneg.mpr (support_lower x h f hf hfx t)
  have he := hmin.hasDerivAt_eq_zero
    (hd.sub ((hasDerivAt_id (0 : ℝ)).mul_const (RCLike.re (f h)) |>.const_add ‖x‖))
  simpa using sub_eq_zero.mp he

/-- Real parts determine scalar-linear functionals over either scalar field. -/
lemma dual_ext_re (f g : E →L[𝕜] 𝕜)
    (he : ∀ h, RCLike.re (f h) = RCLike.re (g h)) : f = g := by
  ext h
  apply RCLike.ext (he h)
  have hi := he ((RCLike.I : 𝕜) • h)
  simpa only [map_smul, smul_eq_mul, RCLike.I_mul_re, neg_inj] using hi

lemma normalized_support_iff (x : E) (hx : x ≠ 0) (f : E →L[𝕜] 𝕜) :
    f ((‖x‖⁻¹ : 𝕜) • x) = 1 ↔ f x = (‖x‖ : 𝕜) := by
  have hn : (‖x‖ : 𝕜) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx)
  simp only [map_smul, smul_eq_mul]
  constructor
  · intro h
    calc f x = (‖x‖ : 𝕜) * ((‖x‖ : 𝕜)⁻¹ * f x) := by field_simp
         _ = _ := by rw [h, mul_one]
  · intro h
    rw [h, inv_mul_cancel₀ hn]

lemma smoothNonzero_iff_unique_support (x : E) (hx : x ≠ 0) :
    Spec.SmoothNonzero 𝕜 x ↔
      ∃ f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f x = (‖x‖ : 𝕜) ∧
        ∀ g : E →L[𝕜] 𝕜, ‖g‖ = 1 → g x = (‖x‖ : 𝕜) → g = f := by
  change (∃ f, {g : E →L[𝕜] 𝕜 | ‖g‖ = 1 ∧
    g ((‖x‖⁻¹ : 𝕜) • x) = 1} = {f}) ↔ _
  simp only [normalized_support_iff x hx]
  constructor
  · rintro ⟨f, hf⟩
    have hff : ‖f‖ = 1 ∧ f x = (‖x‖ : 𝕜) := by
      change f ∈ {g : E →L[𝕜] 𝕜 | ‖g‖ = 1 ∧ g x = (‖x‖ : 𝕜)}
      rw [hf]; exact mem_singleton f
    exact ⟨f, hff.1, hff.2, fun g hg hgx => by
      have : g ∈ {f} := hf ▸ (show g ∈ {g : E →L[𝕜] 𝕜 |
        ‖g‖ = 1 ∧ g x = (‖x‖ : 𝕜)} from ⟨hg, hgx⟩)
      exact mem_singleton_iff.mp this⟩
  · rintro ⟨f, hf, hfx, hu⟩
    refine ⟨f, Set.ext fun g => ?_⟩
    simp only [mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun hg => hu g hg.1 hg.2, fun he => he ▸ ⟨hf, hfx⟩⟩

lemma gateaux_implies_smooth (x : E) (hx : x ≠ 0)
    (hd : Spec.RealGateauxDifferentiable 𝕜 x) : Spec.SmoothNonzero 𝕜 x := by
  obtain ⟨f, hf, hfx⟩ := C05Norming.norming_functional_nonzero 𝕜 E x hx
  apply (smoothNonzero_iff_unique_support x hx).2
  refine ⟨f, hf, hfx, ?_⟩
  intro g hg hgx
  obtain ⟨L, hL⟩ := hd
  apply dual_ext_re
  intro h
  exact (derivative_eq_re_support x h g hg.le hgx (hL h)).symm.trans
    (derivative_eq_re_support x h f hf.le hfx (hL h))

/-- Norming functionals at nearby points nearly norm the original point.
The estimate is uniform over the whole dual unit ball. -/
lemma nearby_support_estimate (x h : E) (t : ℝ) (g : E →L[𝕜] 𝕜)
    (hg : ‖g‖ ≤ 1)
    (hgx : g (x + (t : 𝕜) • h) = (‖x + (t : 𝕜) • h‖ : 𝕜)) :
    ‖g x - (‖x‖ : 𝕜)‖ ≤ 2 * |t| * ‖h‖ := by
  have hgh : ‖g h‖ ≤ ‖h‖ := by
    calc ‖g h‖ ≤ ‖g‖ * ‖h‖ := g.le_opNorm h
         _ ≤ ‖h‖ := by nlinarith [norm_nonneg h]
  have hnorm : |‖x + (t : 𝕜) • h‖ - ‖x‖| ≤ |t| * ‖h‖ := by
    simpa [norm_smul] using abs_norm_sub_norm_le (x + (t : 𝕜) • h) x
  have he : g x - (‖x + (t : 𝕜) • h‖ : 𝕜) = -(t : 𝕜) * g h := by
    rw [← hgx, map_add, map_smul, smul_eq_mul]
    ring
  calc
    ‖g x - (‖x‖ : 𝕜)‖ ≤
      ‖g x - (‖x + (t : 𝕜) • h‖ : 𝕜)‖ +
        ‖(‖x + (t : 𝕜) • h‖ : 𝕜) - (‖x‖ : 𝕜)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * |t| * ‖h‖ := by
      rw [he, norm_mul, norm_neg, RCLike.norm_ofReal, ← RCLike.ofReal_sub,
        RCLike.norm_ofReal]
      nlinarith [mul_le_mul_of_nonneg_left hgh (abs_nonneg t)]

/-- Compactness and unique support imply weak-star convergence of all
choices of norming functionals along a line. -/
lemma norming_tendsto (x h : E) (hx : x ≠ 0) (f : E →L[𝕜] 𝕜)
    (hu : ∀ g : E →L[𝕜] 𝕜, ‖g‖ = 1 → g x = (‖x‖ : 𝕜) → g = f)
    (g : ℝ → E →L[𝕜] 𝕜) (hg : ∀ t, ‖g t‖ ≤ 1)
    (hgn : ∀ t, g t (x + (t : 𝕜) • h) = (‖x + (t : 𝕜) • h‖ : 𝕜)) :
    Tendsto (fun t => StrongDual.toWeakDual (g t)) (𝓝 0)
      (𝓝 (StrongDual.toWeakDual f)) := by
  have hzero : Tendsto (fun t => g t x - (‖x‖ : 𝕜)) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero_norm (fun t => nearby_support_estimate x h t (g t) (hg t) (hgn t))
    simpa using (tendsto_const_nhds.mul (continuous_abs.tendsto (0 : ℝ))).mul_const ‖h‖
  have hval : Tendsto (fun t => g t x) (𝓝 0) (𝓝 (‖x‖ : 𝕜)) := by
    simpa using hzero.add_const (‖x‖ : 𝕜)
  have hc := WeakDual.isCompact_closedBall (0 : E →L[𝕜] 𝕜) 1
  apply hc.tendsto_nhds_of_unique_mapClusterPt
  · exact Eventually.of_forall fun t => by simpa using hg t
  · intro y hy hcy
    have hyn : ‖WeakDual.toStrongDual y‖ ≤ 1 := by simpa using hy
    have hcyval := hcy.continuousAt_comp (WeakDual.eval_continuous x).continuousAt
    have hyx : y x = (‖x‖ : 𝕜) :=
      eq_of_nhds_neBot (hcyval.clusterPt.mono hval)
    have hynorm : ‖WeakDual.toStrongDual y‖ = 1 := by
      have hp := (WeakDual.toStrongDual y).le_opNorm x
      have hpx : ‖x‖ ≤ ‖WeakDual.toStrongDual y‖ * ‖x‖ := by
        simpa [hyx] using hp
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      nlinarith
    have hey := hu (WeakDual.toStrongDual y) hynorm hyx
    exact WeakDual.toStrongDual.injective hey

/-- At a point with unique support, the two support inequalities squeeze
all real difference quotients to the real part of that support. -/
lemma unique_support_hasDeriv (x : E) (hx : x ≠ 0) (f : E →L[𝕜] 𝕜)
    (hf : ‖f‖ = 1) (hfx : f x = (‖x‖ : 𝕜))
    (hu : ∀ g : E →L[𝕜] 𝕜, ‖g‖ = 1 → g x = (‖x‖ : 𝕜) → g = f)
    (h : E) :
    HasDerivAt (fun t : ℝ => ‖x + (t : 𝕜) • h‖) (RCLike.re (f h)) 0 := by
  classical
  choose g hg hgn using fun t : ℝ =>
    C05Norming.norming_functional 𝕜 E (x + (t : 𝕜) • h)
  have hconv := norming_tendsto x h hx f hu g hg hgn
  have hev : Tendsto (fun t => RCLike.re (g t h)) (𝓝[≠] 0)
      (𝓝 (RCLike.re (f h))) :=
    (RCLike.continuous_re.tendsto _ |>.comp
      ((WeakDual.eval_continuous h).tendsto _ |>.comp hconv)).mono_left nhdsWithin_le_nhds
  have hlo : Tendsto (fun t => min (RCLike.re (f h)) (RCLike.re (g t h)))
      (𝓝[≠] 0) (𝓝 (RCLike.re (f h))) := by
    simpa using (tendsto_const_nhds (x := RCLike.re (f h))).min hev
  have hhi : Tendsto (fun t => max (RCLike.re (f h)) (RCLike.re (g t h)))
      (𝓝[≠] 0) (𝓝 (RCLike.re (f h))) := by
    simpa using (tendsto_const_nhds (x := RCLike.re (f h))).max hev
  have hb : ∀ᶠ t : ℝ in 𝓝[≠] 0,
      min (RCLike.re (f h)) (RCLike.re (g t h)) ≤
        (‖x + (t : 𝕜) • h‖ - ‖x‖) / t ∧
      (‖x + (t : 𝕜) • h‖ - ‖x‖) / t ≤
        max (RCLike.re (f h)) (RCLike.re (g t h)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    have hl := support_lower x h f hf.le hfx t
    have hh := support_upper x h (g t) (hg t) (hgn t)
    rcases ht0.lt_or_gt with ht | ht
    · constructor
      · apply (min_le_right _ _).trans
        apply (le_div_iff_of_neg ht).2
        nlinarith
      · apply le_trans _ (le_max_left _ _)
        apply (div_le_iff_of_neg ht).2
        nlinarith
    · constructor
      · apply (min_le_left _ _).trans
        apply (le_div_iff₀ ht).2
        nlinarith
      · apply le_trans _ (le_max_right _ _)
        apply (div_le_iff₀ ht).2
        nlinarith
  rw [hasDerivAt_iff_tendsto_slope]
  have hq := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    (hb.mono fun _ hh => hh.1) (hb.mono fun _ hh => hh.2)
  convert hq using 1
  ext t
  simp [slope_def_field]

lemma smooth_implies_gateaux (x : E) (hx : x ≠ 0)
    (hs : Spec.SmoothNonzero 𝕜 x) : Spec.RealGateauxDifferentiable 𝕜 x := by
  obtain ⟨f, hf, hfx, hu⟩ := (smoothNonzero_iff_unique_support x hx).1 hs
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  refine ⟨RCLike.reCLM.comp (f.restrictScalars ℝ), ?_⟩
  intro h
  exact unique_support_hasDeriv x hx f hf hfx hu h

/-- Smoothness is equivalent to real Gâteaux differentiability, at every
nonzero point, over ℝ or ℂ and without completeness. -/
theorem smooth_iff_gateaux : Spec.Characterization.{u,v} := by
  intro 𝕜 E _ _ _ x hx
  exact ⟨smooth_implies_gateaux x hx, gateaux_implies_smooth x hx⟩

/-- The derivative at a unit smooth point is the real part of the unique
scalar-linear unit norming functional. -/
theorem unit_derivative_formula : Spec.UnitDerivativeFormula.{u,v} := by
  intro 𝕜 E _ _ _ x hx hs
  have hx0 : x ≠ 0 := by intro he; simp [he] at hx
  have hs' : Spec.SmoothNonzero 𝕜 x := by
    simpa [Spec.SmoothNonzero, hx] using hs
  obtain ⟨f, hf, hfx, hu⟩ := (smoothNonzero_iff_unique_support x hx0).1 hs'
  refine ⟨f, hf, by simpa [hx] using hfx, ?_, ?_⟩
  · intro g hg hgx
    apply hu g hg
    simpa [hx] using hgx
  · exact unique_support_hasDeriv x hx0 f hf hfx hu

end ExpandedFA.P1.GateauxNormDerivative
