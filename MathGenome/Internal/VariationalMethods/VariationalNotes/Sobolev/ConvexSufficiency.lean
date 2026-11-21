import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.ConvexSufficiency
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.SobolevEulerLagrange
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.StrictConvexUniqueness
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Convex

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace VariationalNotes.Sobolev
open EulerLagrange

/-- The differentiable support inequality, with the manuscript's two pairings. -/
theorem convex_fiber_support {d m : ℕ}
    {F : Vector m → Gradient m d → ℝ}
    {Fs : Vector m → Gradient m d → Vector m}
    {FZ : Vector m → Gradient m d → Gradient m d}
    (hc : ConvexOn ℝ univ (fun y : Vector m × Gradient m d => F y.1 y.2))
    (hd : ∀ y : Vector m × Gradient m d,
      HasFDerivAt (fun y => F y.1 y.2) (fiberDerivative (Fs y.1 y.2) (FZ y.1 y.2)) y)
    (s w : Vector m) (Z W : Gradient m d) :
    F s Z + (⟪Fs s Z, w⟫_ℝ + frobenius (FZ s Z) W) ≤ F (s+w) (Z+W) := by
  have hl : ConvexOn ℝ univ (fun t : ℝ => F (s + t • w) (Z + t • W)) := by
    have H := hc.comp_affineMap (AffineMap.lineMap (s,Z) ((s,Z) + (w,W)))
    simpa [Function.comp_def, AffineMap.lineMap_apply_module', add_comm] using H
  have hd' := hasDerivAt_fieldVariation (F := fun (_ : Domain d) => F)
    (Fs := fun _ => Fs) (FZ := fun _ => FZ) (x := 0) hd
    (fun _ => s) (fun _ => w) (fun _ => Z) (fun _ => W) 0
  have H := hl.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hd'
  simp only [slope_def_field, sub_zero, div_one, zero_smul, add_zero,
    one_smul, fieldVariation] at H
  linarith

/-- Growth domination supplies integrability at a stationary point without
assuming it is already a local minimizer. Measurability follows by differentiating
a.e. measurable energy slices, so merely Lebesgue measurable base sections suffice. -/
theorem integrable_sobolevWeakDensity_of_domination {d m : ℕ}
    {Ω : Opens (Domain d)} {p : Exponent}
    {F : Domain d → Vector m → Gradient m d → ℝ}
    {Fs : Domain d → Vector m → Gradient m d → Vector m}
    {FZ : Domain d → Vector m → Gradient m d → Gradient m d}
    (hF : SobolevIntegrandRegularity Ω F Fs FZ)
    (hdom : SobolevLineDomination (Ω := Ω) (p := p) Fs FZ)
    (u w : W1p Ω m p) :
    Integrable (sobolevWeakDensity Fs FZ u w) (domainMeasure Ω) := by
  obtain ⟨b, hb, hbd⟩ := hdom u w
  have hm := aestronglyMeasurable_directional_derivative
    (measurable_sobolev_line hF.1 (hF.2.mono fun x hx =>
      continuous_iff_continuousAt.mpr fun y => (hx.1 y).continuousAt) u w)
    (hF.2.mono (fun x hx => hasDerivAt_fieldVariation hx.1
      (value Ω m p u) (value Ω m p w) (gradient Ω m p u) (gradient Ω m p w) 0))
  have he : fieldVariation Fs FZ (value Ω m p u) (value Ω m p w)
      (gradient Ω m p u) (gradient Ω m p w) 0 = sobolevWeakDensity Fs FZ u w := by
    funext x
    simp [fieldVariation, sobolevWeakDensity]
  rw [he] at hm
  apply hb.mono' hm
  filter_upwards [hbd] with x hx
  simpa [fieldVariation, sobolevWeakDensity, Real.norm_eq_abs] using hx 0 (by norm_num)

/-- Integration of support uses the actual admissible difference v-u. -/
theorem convex_sufficiency_of_line_domination {d m : ℕ}
    {Ω : Opens (Domain d)} {p : Exponent}
    {F : Domain d → Vector m → Gradient m d → ℝ}
    {Fs : Domain d → Vector m → Gradient m d → Vector m}
    {FZ : Domain d → Vector m → Gradient m d → Gradient m d}
    (hF : SobolevIntegrandRegularity Ω F Fs FZ)
    (hdom : SobolevLineDomination (Ω := Ω) (p := p) Fs FZ)
    (hc : ∀ᵐ x ∂domainMeasure Ω,
      ConvexOn ℝ univ (fun y : Vector m × Gradient m d => F x y.1 y.2))
    (u₀ : W1p Ω m p) (href : FiniteReference F u₀)
    (u : W1p Ω m p) (hu : u ∈ affineClass Ω m p u₀)
    (hstat : ∀ w : W1pZero Ω m p,
      (∫ x, sobolevWeakDensity Fs FZ u w x ∂domainMeasure Ω) = 0) :
    ∀ v ∈ affineClass Ω m p u₀, energy Ω m p F u ≤ energy Ω m p F v := by
  have hfinite := (allTests_of_line_domination hF hdom u₀ href).1
  have hi (v : W1p Ω m p) (hv : v ∈ affineClass Ω m p u₀) :
      Integrable (fun x => F x (value Ω m p v x) (gradient Ω m p v x)) (domainMeasure Ω) := by
    apply EulerLagrange.integrable_of_extendedIntegral_finite
      (aemeasurable_field_substitution hF.1
        (hF.2.mono fun x hx =>
          continuous_iff_continuousAt.mpr fun y => (hx.1 y).continuousAt)
        ((Lp.aestronglyMeasurable (value Ω m p v)).aemeasurable.prodMk
          (Lp.aestronglyMeasurable (gradient Ω m p v)).aemeasurable))
    exact hfinite v hv
  intro v hv
  have hw : v-u ∈ zeroSubmodule Ω m p := by
    have H := (zeroSubmodule Ω m p).sub_mem hv hu
    convert H using 1; abel
  let w : W1pZero Ω m p := ⟨v-u, hw⟩
  have hden := integrable_sobolevWeakDensity_of_domination hF hdom u w
  have hsup : ∀ᵐ x ∂domainMeasure Ω,
      F x (value Ω m p u x) (gradient Ω m p u x) +
        sobolevWeakDensity Fs FZ u w x ≤ F x (value Ω m p v x) (gradient Ω m p v x) := by
    have he : u + (w : W1p Ω m p) = v := by dsimp [w]; abel
    have hr := sobolev_line_representatives u (w : W1p Ω m p) 1
    rw [one_smul, he] at hr
    filter_upwards [hc, hF.2, hr.1, hr.2] with x hx hd hs hZ
    simp only [one_smul] at hs hZ
    rw [hs, hZ]
    exact convex_fiber_support hx hd.1 _ _ _ _
  have H := integral_mono_ae ((hi u hu).add hden) (hi v hv) hsup
  simp only [Pi.add_apply] at H
  rw [integral_add (hi u hu) hden, hstat w, add_zero] at H
  change extendedIntegral (domainMeasure Ω) _ ≤ extendedIntegral (domainMeasure Ω) _
  rw [extendedIntegral_eq_integral (hi u hu), extendedIntegral_eq_integral (hi v hv)]
  exact EReal.coe_le_coe_iff.mpr H

theorem convex_sufficiency_power : ConvexSufficiencyExpected.PowerGrowth := by
  intro d m hd hm Ω hΩ p hp F Fs FZ hF hg hc u₀ href u hu hstat
  obtain ⟨b, C, hC, hb, hbd⟩ := hg
  exact convex_sufficiency_of_line_domination hF
    (powerGrowth_line_domination hp hC hb hbd) hc u₀ href u hu hstat

theorem convex_sufficiency_one : ConvexSufficiencyExpected.BoundedGrowth := by
  intro d m hd hm Ω hΩ p hp F Fs FZ hF hg hc u₀ href u hu hstat
  obtain ⟨b, hb, hbd⟩ := hg
  exact convex_sufficiency_of_line_domination hF
    (boundedGrowth_line_domination hp hb hbd) hc u₀ href u hu hstat

/-- A power greater than one of the norm is strictly convex in a strictly
convex normed space. Equal norms use strict convexity of the ball; unequal
norms use strict convexity of the scalar power. -/
theorem strictConvexOn_norm_rpow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {p : ℝ} (hp : 1 < p) :
    StrictConvexOn ℝ univ (fun x : E => ‖x‖ ^ p) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  simp only [smul_eq_mul]
  by_cases he : ‖x‖ = ‖y‖
  · have hlt := norm_combo_lt_of_ne (le_refl ‖x‖) (le_of_eq he.symm) hxy ha hb hab
    have H := Real.rpow_lt_rpow (norm_nonneg (a • x + b • y)) hlt (by linarith : 0 < p)
    calc
      ‖a • x + b • y‖ ^ p < ‖x‖ ^ p := H
      _ = a * ‖x‖ ^ p + b * ‖y‖ ^ p := by rw [← he, ← add_mul, hab, one_mul]
  · have hnorm : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb] using
        norm_add_le (a • x) (b • y)
    have H := (strictConvexOn_rpow hp).2 (norm_nonneg x) (norm_nonneg y) he ha hb hab
    exact (Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith)).trans_lt H

/-- The gradient power density is integrable at every Sobolev competitor. -/
theorem integrable_gradient_power {d m : ℕ} (Ω : Opens (Domain d)) (p : Exponent)
    (w : W1p Ω m p) :
    Integrable (fun x => ‖gradient Ω m p w x‖ ^ p.real) (domainMeasure Ω) := by
  have H := (Lp.memLp (gradient Ω m p w)).integrable_norm_rpow
    (ne_of_gt (ENNReal.ofReal_pos.mpr p.pos)) ENNReal.ofReal_ne_top
  simpa only [Exponent.toReal] using H

/-- Source power-energy conclusion, including finiteness at every competitor.
The imported gradient-only uniqueness theorem concludes using Poincaré on
v-u in the zero-boundary subspace. -/
theorem power_energy_unique : ConvexSufficiencyExpected.PowerUniqueness := by
  intro d m hd hm Ω hΩ p hp u₀ u hu humin v hv hvmin
  have hn (w : W1p Ω m p) : NegativePartIntegrable (domainMeasure Ω)
      (fun x => ‖gradient Ω m p w x‖ ^ p.real) := by
    apply negativePartIntegrable_of_lower_bound
      (integrable_gradient_power Ω p w).aemeasurable (a := fun _ => 0) (integrable_zero _ _ _)
    exact Eventually.of_forall (fun x => by
      simpa only [neg_zero] using Real.rpow_nonneg (norm_nonneg (gradient Ω m p w x)) p.real)
  apply gradient_strict_convex_uniqueness_of_measurable hd hm Ω hΩ p u₀
    (fun _ _ Z => ‖Z‖ ^ p.real)
    (fun w _ => (integrable_gradient_power Ω p w).aemeasurable)
    (Eventually.of_forall (fun _ _ _ _ => rfl))
    (Eventually.of_forall (fun _ => strictConvexOn_norm_rpow hp))
    (fun w _ => hn w) u hu (∫ x, ‖gradient Ω m p u x‖ ^ p.real ∂domainMeasure Ω)
    (extendedIntegral_eq_integral (integrable_gradient_power Ω p u)) humin v hv hvmin

end VariationalNotes.Sobolev
