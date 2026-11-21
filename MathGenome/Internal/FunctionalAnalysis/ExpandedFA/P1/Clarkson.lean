import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.Clarkson
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Interpolation.RieszThorin
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14UniformConvexity
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace ExpandedFA.P1.Clarkson
open C14UniformConvexity

/-- Power form of the finite-p norm on the usual a.e. quotient. -/
lemma lp_norm_rpow_eq_integral {𝕜 : Type v} [RCLike 𝕜]
    {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal) (f : Lp 𝕜 p μ) :
    ‖f‖ ^ p.toReal = ∫ x, ‖f x‖ ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := (ENNReal.toReal_pos_iff.mp hp).1.ne'
  have hpt : p ≠ ∞ := (ENNReal.toReal_pos_iff.mp hp).2.ne
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm hp0 hpt,
    ENNReal.toReal_ofReal (by positivity), Real.rpow_inv_rpow (by positivity) hp.ne']

/-- The scalar upper-range estimate from the parallelogram identity and
convexity of the power p/2. -/
lemma scalar_upper {𝕜 : Type v} [RCLike 𝕜] {p : ℝ} (hp : 2 ≤ p)
    (a b : 𝕜) :
    ‖a+b‖^p + ‖a-b‖^p ≤ (2:ℝ)^(p-1) * (‖a‖^p+‖b‖^p) := by
  have hr : 1 ≤ p / 2 := by linarith
  have hpow (t : ℝ) (ht : 0 ≤ t) : (t^2)^(p/2) = t^p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
    congr 1
    ring
  have hmean : (‖a‖^2+‖b‖^2)^(p/2) ≤
      (2:ℝ)^(p/2-1) * (‖a‖^p+‖b‖^p) := by
    have h := NNReal.rpow_add_le_mul_rpow_add_rpow (‖a‖₊^2) (‖b‖₊^2) hr
    have hh : (‖a‖^2+‖b‖^2)^(p/2) ≤
        (2:ℝ)^(p/2-1) * ((‖a‖^2)^(p/2)+(‖b‖^2)^(p/2)) := by
      exact_mod_cast h
    simpa only [hpow _ (norm_nonneg _)] using hh
  calc
    ‖a+b‖^p + ‖a-b‖^p = (‖a+b‖^2)^(p/2) + (‖a-b‖^2)^(p/2) := by
      rw [hpow _ (norm_nonneg _), hpow _ (norm_nonneg _)]
    _ ≤ (‖a+b‖^2+‖a-b‖^2)^(p/2) :=
      Real.add_rpow_le_rpow_add (sq_nonneg _) (sq_nonneg _) hr
    _ = (2:ℝ)^(p/2) * (‖a‖^2+‖b‖^2)^(p/2) := by
      rw [parallelogram_law_with_norm 𝕜, Real.mul_rpow (by norm_num) (by positivity)]
    _ ≤ (2:ℝ)^(p/2) * ((2:ℝ)^(p/2-1) * (‖a‖^p+‖b‖^p)) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = (2:ℝ)^(p-1) * (‖a‖^p+‖b‖^p) := by
      rw [← mul_assoc, ← Real.rpow_add (by norm_num)]
      congr 2
      ring

/-- Integrating the scalar inequality works for any positive measure. -/
theorem upper_range :
  ∀ (𝕜 : Type v) [RCLike 𝕜] {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (f g : Lp 𝕜 (ENNReal.ofReal p) μ),
    ‖f + g‖ ^ p + ‖f - g‖ ^ p ≤
      (2 : ℝ) ^ (p - 1) * (‖f‖ ^ p + ‖g‖ ^ p) := by
  intro 𝕜 _ X _ μ p hp _ f g
  have hp0 : 0 < p := by linarith
  have he : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hn (h : Lp 𝕜 (ENNReal.ofReal p) μ) : ‖h‖^p = ∫ x, ‖h x‖^p ∂μ := by
    simpa only [he] using lp_norm_rpow_eq_integral (by simpa only [he] using hp0) h
  have hi (h : Lp 𝕜 (ENNReal.ofReal p) μ) : Integrable (fun x => ‖h x‖^p) μ := by
    simpa only [he] using (Lp.memLp h).integrable_norm_rpow
      (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top
  have hpoint : ∀ᵐ x ∂μ, ‖(f+g) x‖^p + ‖(f-g) x‖^p ≤
      (2:ℝ)^(p-1) * (‖f x‖^p + ‖g x‖^p) := by
    filter_upwards [Lp.coeFn_add f g, Lp.coeFn_sub f g] with x ha hs
    simpa only [ha, hs, Pi.add_apply, Pi.sub_apply] using scalar_upper hp (f x) (g x)
  have h := integral_mono_ae ((hi (f+g)).add (hi (f-g)))
    (((hi f).add (hi g)).const_mul ((2:ℝ)^(p-1))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (hi (f+g)) (hi (f-g)), integral_const_mul,
    integral_add (hi f) (hi g), ← hn (f+g), ← hn (f-g), ← hn f, ← hn g] at h
  exact h

lemma scalar_power_midpoint_le {𝕜 : Type u} [RCLike 𝕜] {p : ℝ} (hp : 1 < p)
    (a b : 𝕜) : (‖a + b‖ / 2) ^ p ≤ (‖a‖ ^ p + ‖b‖ ^ p) / 2 := by
  have hm := (strictConvexOn_rpow hp).convexOn.2
    (norm_nonneg a) (norm_nonneg b) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)+(1/2)=1)
  simp only [smul_eq_mul] at hm
  calc
    (‖a + b‖ / 2) ^ p ≤ ((‖a‖ + ‖b‖) / 2) ^ p :=
      Real.rpow_le_rpow (by positivity) (by linarith [norm_add_le a b]) (by linarith)
    _ ≤ (‖a‖ ^ p + ‖b‖ ^ p) / 2 := by convert hm using 1 <;> ring_nf

lemma scalar_power_midpoint_lt {𝕜 : Type u} [RCLike 𝕜] {p : ℝ} (hp : 1 < p)
    (a b : 𝕜) (hne : a ≠ b) : (‖a + b‖ / 2) ^ p < (‖a‖ ^ p + ‖b‖ ^ p) / 2 := by
  by_cases hn : ‖a‖ = ‖b‖
  · have ht := norm_combo_lt_of_ne (le_refl ‖a‖) (le_of_eq hn.symm) hne
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (1/2:ℝ)+(1/2)=1)
    have hh : ‖a + b‖ / 2 < ‖a‖ := by
      have hs : (1/2:ℝ) • a + (1/2:ℝ) • b = (1/2:ℝ) • (a+b) := (smul_add _ _ _).symm
      rw [hs, norm_smul] at ht
      norm_num at ht
      linarith
    have := Real.rpow_lt_rpow (by positivity : 0 ≤ ‖a+b‖/2) hh (by linarith : 0<p)
    simpa [hn] using this
  · have hm := (strictConvexOn_rpow hp).2 (norm_nonneg a) (norm_nonneg b) hn
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (1/2:ℝ)+(1/2)=1)
    simp only [smul_eq_mul] at hm
    calc
      (‖a+b‖/2)^p ≤ ((‖a‖+‖b‖)/2)^p :=
        Real.rpow_le_rpow (by positivity) (by linarith [norm_add_le a b]) (by linarith)
      _ < (‖a‖^p+‖b‖^p)/2 := by convert hm using 1 <;> ring_nf

/-- A positive scalar convexity gap on each separated normalized level set.
The complex plane also contains the isometric real case. -/
lemma complex_normalized_power_gap {p t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ a b : ℂ,
      (‖a‖ ^ p + ‖b‖ ^ p) / 2 = 1 → t ≤ ‖a - b‖ ^ p →
      γ ≤ 1 - (‖a + b‖ / 2) ^ p := by
  let S : Set (ℂ × ℂ) := {z | (‖z.1‖ ^ p + ‖z.2‖ ^ p) / 2 = 1 ∧ t ≤ ‖z.1-z.2‖^p}
  have hp0 : 0 < p := by linarith
  have hc : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_le (f := fun _ : ℂ × ℂ => t)
        (g := fun z : ℂ × ℂ => ‖z.1-z.2‖^p) continuous_const (by fun_prop)
  have hbound : S ⊆ Metric.closedBall (0 : ℂ) ((2:ℝ)^p⁻¹) ×ˢ
      Metric.closedBall (0 : ℂ) ((2:ℝ)^p⁻¹) := by
    intro z hz
    have h₁ : ‖z.1‖^p ≤ 2 := by
      have : 0 ≤ ‖z.2‖^p := by positivity
      linarith [hz.1]
    have h₂ : ‖z.2‖^p ≤ 2 := by
      have : 0 ≤ ‖z.1‖^p := by positivity
      linarith [hz.1]
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) (by norm_num) hp0).mpr h₁
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) (by norm_num) hp0).mpr h₂
  have hcompact : IsCompact S :=
    ((isCompact_closedBall (0:ℂ) _).prod (isCompact_closedBall (0:ℂ) _)).of_isClosed_subset hc hbound
  obtain ⟨γ, hγ, hgap⟩ := hcompact.exists_forall_le'
    (f := fun z => 1 - (‖z.1 + z.2‖ / 2)^p) (by fun_prop) (a := 0) (by
      intro z hz
      have hne : z.1 ≠ z.2 := by
        intro heq
        have h := hz.2
        simp [heq, Real.zero_rpow hp0.ne'] at h
        linarith
      have := scalar_power_midpoint_lt hp z.1 z.2 hne
      rw [hz.1] at this
      linarith)
  exact ⟨γ, hγ, fun a b hab hd => hgap (a,b) ⟨hab,hd⟩⟩

lemma scalar_power_sub_le {𝕜 : Type u} [RCLike 𝕜] {p : ℝ} (hp : 1 < p)
    (a b : 𝕜) : ‖a-b‖^p ≤ (2:ℝ)^p * ((‖a‖^p+‖b‖^p)/2) := by
  have h := scalar_power_midpoint_le hp a (-b)
  rw [← sub_eq_add_neg, norm_neg, Real.div_rpow (norm_nonneg _) (by norm_num)] at h
  exact (div_le_iff₀ (by positivity : 0 < (2:ℝ)^p)).mp h |>.trans_eq (mul_comm _ _)

/-- The same positive gap works over every RCLike field by its isometric
real-linear embedding in ℂ. -/
lemma scalar_normalized_power_gap {p t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (𝕜 : Type u) [RCLike 𝕜] (a b : 𝕜),
      (‖a‖ ^ p + ‖b‖ ^ p) / 2 = 1 → t ≤ ‖a - b‖ ^ p →
      γ ≤ 1 - (‖a + b‖ / 2) ^ p := by
  obtain ⟨γ,hγ,h⟩ := complex_normalized_power_gap hp ht
  refine ⟨γ,hγ,fun 𝕜 _ a b hab hd => ?_⟩
  have hn (z : 𝕜) : ‖RCLike.map 𝕜 ℂ z‖ = ‖z‖ := RCLike.norm_to_complex z
  have hh := h (RCLike.map 𝕜 ℂ a) (RCLike.map 𝕜 ℂ b)
  simp only [← map_add, ← map_sub, hn] at hh
  exact hh hab hd

/-- A homogeneous pointwise inequality suitable for integration on an
arbitrary measure space; the constant is independent of the field. -/
lemma scalar_power_defect_bound {p t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (𝕜 : Type u) [RCLike 𝕜] (a b : 𝕜),
      ‖a-b‖^p ≤ t * ((‖a‖^p+‖b‖^p)/2) +
        C * (((‖a‖^p+‖b‖^p)/2) - (‖a+b‖/2)^p) := by
  obtain ⟨γ,hγ,hgap⟩ := scalar_normalized_power_gap hp ht
  let C := (2:ℝ)^p / γ
  have hC : 0 < C := by dsimp [C]; positivity
  have hnormalized (𝕜 : Type u) [RCLike 𝕜] (a b : 𝕜)
      (hs : (‖a‖^p+‖b‖^p)/2=1) :
      ‖a-b‖^p ≤ t + C * (1 - (‖a+b‖/2)^p) := by
    have hm := scalar_power_midpoint_le hp a b
    rw [hs] at hm
    by_cases hd : t ≤ ‖a-b‖^p
    · have hg := hgap 𝕜 a b hs hd
      have hu := scalar_power_sub_le hp a b
      rw [hs, mul_one] at hu
      have hcγ : C * γ = (2:ℝ)^p := by dsimp [C]; field_simp
      have hmul := mul_le_mul_of_nonneg_left hg hC.le
      rw [hcγ] at hmul
      linarith
    · have hnonneg := mul_nonneg hC.le (sub_nonneg.mpr hm)
      linarith
  refine ⟨C,hC,fun 𝕜 _ a b => ?_⟩
  have hp0 : 0 < p := by linarith
  let s := (‖a‖^p+‖b‖^p)/2
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  by_cases hs : s = 0
  · have ha : a = 0 := by
      have hz : ‖a‖^p = 0 := by
        have : 0 ≤ ‖b‖^p := by positivity
        dsimp [s] at hs; nlinarith [Real.rpow_nonneg (norm_nonneg a) p]
      exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg a) hp0.ne').mp hz)
    have hb : b = 0 := by
      have hz : ‖b‖^p = 0 := by
        have : 0 ≤ ‖a‖^p := by positivity
        dsimp [s] at hs; nlinarith [Real.rpow_nonneg (norm_nonneg b) p]
      exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg b) hp0.ne').mp hz)
    simp [ha,hb,Real.zero_rpow hp0.ne']
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    let r := s ^ p⁻¹
    have hr : 0 < r := by dsimp [r]; positivity
    have hrpow : r ^ p = s := Real.rpow_inv_rpow hs0 hp0.ne'
    have hscale (z : 𝕜) : ‖(r⁻¹:ℝ) • z‖ ^ p = ‖z‖^p / s := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
        Real.mul_rpow (inv_nonneg.mpr hr.le) (norm_nonneg _), Real.inv_rpow hr.le, hrpow]
      ring
    have hsn : (‖(r⁻¹:ℝ) • a‖^p + ‖(r⁻¹:ℝ) • b‖^p)/2 = 1 := by
      rw [hscale, hscale]
      calc
        _ = s / s := by dsimp [s]; ring
        _ = 1 := div_self hs
    have hd : ‖(r⁻¹:ℝ) • a - (r⁻¹:ℝ) • b‖^p = ‖a-b‖^p / s := by
      rw [← smul_sub, hscale]
    have hm : (‖(r⁻¹:ℝ) • a + (r⁻¹:ℝ) • b‖/2)^p = (‖a+b‖/2)^p / s := by
      rw [← smul_add, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      rw [show r⁻¹ * ‖a+b‖ / 2 = r⁻¹ * (‖a+b‖/2) by ring,
        Real.mul_rpow (inv_nonneg.mpr hr.le) (by positivity), Real.inv_rpow hr.le, hrpow]
      ring
    have h := hnormalized 𝕜 ((r⁻¹:ℝ) • a) ((r⁻¹:ℝ) • b) hsn
    rw [hd,hm] at h
    have hh := mul_le_mul_of_nonneg_right h hspos.le
    convert hh using 1 <;> field_simp
    ring


lemma lp_power_defect_integrated {p t C : ℝ} (hp : 1 < p)
    (hC : ∀ (𝕜 : Type v) [RCLike 𝕜] (a b : 𝕜),
      ‖a-b‖^p ≤ t * ((‖a‖^p+‖b‖^p)/2) +
        C * (((‖a‖^p+‖b‖^p)/2) - (‖a+b‖/2)^p))
    {𝕜 : Type v} [RCLike 𝕜] {X : Type u} [MeasurableSpace X] (μ : Measure X)
    [Fact (1 ≤ ENNReal.ofReal p)] (f g : Lp 𝕜 (ENNReal.ofReal p) μ) :
    ‖f-g‖^p ≤ t * ((‖f‖^p+‖g‖^p)/2) +
      C * (((‖f‖^p+‖g‖^p)/2) - ‖(2:𝕜)⁻¹ • (f+g)‖^p) := by
  have hp0 : 0 < p := by linarith
  have he : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hq : 0 < (ENNReal.ofReal p).toReal := by rwa [he]
  have hn (h : Lp 𝕜 (ENNReal.ofReal p) μ) : ‖h‖^p = ∫ x, ‖h x‖^p ∂μ := by
    simpa only [he] using lp_norm_rpow_eq_integral hq h
  have hi (h : Lp 𝕜 (ENNReal.ofReal p) μ) : Integrable (fun x => ‖h x‖^p) μ := by
    simpa only [he] using (Lp.memLp h).integrable_norm_rpow
      (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top
  let m := (2:𝕜)⁻¹ • (f+g)
  let s : X → ℝ := fun x => (‖f x‖^p+‖g x‖^p)/2
  have his : Integrable s μ := ((hi f).add (hi g)).div_const 2
  have hm : ∀ᵐ x ∂μ, ‖m x‖ = ‖f x + g x‖ / 2 := by
    filter_upwards [Lp.coeFn_smul (2:𝕜)⁻¹ (f+g), Lp.coeFn_add f g] with x hx hy
    dsimp [m]
    rw [hx, Pi.smul_apply, hy, Pi.add_apply, norm_smul, norm_inv]
    norm_num
    ring
  have hpoint : ∀ᵐ x ∂μ, ‖(f-g) x‖^p ≤ t * s x + C * (s x - ‖m x‖^p) := by
    filter_upwards [Lp.coeFn_sub f g, hm] with x hx hm
    rw [hx, Pi.sub_apply, hm]
    exact hC 𝕜 (f x) (g x)
  have hinter := integral_mono_ae (hi (f-g))
    ((his.const_mul t).add ((his.sub (hi m)).const_mul C)) hpoint
  simp only [Pi.add_apply, Pi.sub_apply] at hinter
  rw [integral_add (f := fun x => t * s x)
      (g := fun x => C * (s x - ‖m x‖^p)) (his.const_mul t) ((his.sub (hi m)).const_mul C),
    integral_const_mul, integral_const_mul, integral_sub his (hi m)] at hinter
  have hsint : ∫ x, s x ∂μ = (‖f‖^p+‖g‖^p)/2 := by
    dsimp [s]
    rw [integral_div, integral_add (hi f) (hi g), ← hn f, ← hn g]
  rw [hsint, ← hn (f-g), ← hn m] at hinter
  exact hinter

/-- Uniform convexity with one modulus for all scalar fields, domains and
positive measures at the given exponent and separation. -/
theorem measure_lp_uniform_modulus :
    ∀ (p : ℝ), 1 < p → ∀ ε : ℝ, 0 < ε → ε ≤ 2 →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (𝕜 : Type v) [RCLike 𝕜] (X : Type u)
      [MeasurableSpace X] (μ : Measure X)
      [Fact (1 ≤ ENNReal.ofReal p)] (f g : Lp 𝕜 (ENNReal.ofReal p) μ),
      ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → ε ≤ ‖f-g‖ →
        ‖(2:𝕜)⁻¹ • (f+g)‖ ≤ 1-δ := by
  intro p hp ε hε _hε₂
  let : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
  have hp0 : 0 < p := by linarith
  let t := ε^p / 2
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨C,hC,hpoint⟩ := scalar_power_defect_bound.{v} hp ht
  let k := min (t/C) (1/2)
  have hk : 0 < k := lt_min (div_pos ht hC) (by norm_num)
  have hkhalf : k ≤ 1/2 := min_le_right _ _
  have hkC : C*k ≤ t := by
    have h := (le_div_iff₀ hC).mp (min_le_left (t/C) (1/2))
    dsimp [k]
    nlinarith
  have hbase : 0 ≤ 1-k := by linarith
  have hroot : (1-k)^p⁻¹ < 1 :=
    Real.rpow_lt_one hbase (by linarith) (inv_pos.mpr hp0)
  refine ⟨1-(1-k)^p⁻¹, by linarith, fun 𝕜 _ X _ μ _ f g hf hg hsep => ?_⟩
  have hdist : 2*t ≤ ‖f-g‖^p := by
    have h := Real.rpow_le_rpow hε.le hsep hp0.le
    dsimp [t]
    linarith
  have hfg : (‖f‖^p+‖g‖^p)/2 ≤ 1 := by
    have h₁ := Real.rpow_le_rpow (norm_nonneg f) hf hp0.le
    have h₂ := Real.rpow_le_rpow (norm_nonneg g) hg hp0.le
    simp only [Real.one_rpow] at h₁ h₂
    linarith
  have hint := lp_power_defect_integrated hp hpoint μ f g
  have hsum := mul_le_mul_of_nonneg_left hfg (add_nonneg ht.le hC.le)
  have hpow : ‖(2:𝕜)⁻¹ • (f+g)‖^p ≤ 1-k := by
    nlinarith
  rw [sub_sub_cancel]
  exact (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hbase hp0).mpr hpow

/-- Uniform convexity, independently obtained by a scalar compactness gap.
The constant works for both fields and arbitrary measure spaces. -/
theorem uniformly_convex :
  ∀ (𝕜 : Type v) [RCLike 𝕜] {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)],
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜 (Lp 𝕜 (ENNReal.ofReal p) μ) := by
  intro 𝕜 _ X _ μ p hp _ ε hε hε₂
  obtain ⟨δ, hδ, h⟩ := measure_lp_uniform_modulus p hp ε hε hε₂
  exact ⟨δ, hδ, h 𝕜 X μ⟩

namespace TwoPoint
abbrev μ₂ : Measure (Fin 2) := Measure.count

def evalAE : ((Fin 2) →ₘ[μ₂] ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun f := f
  invFun f := AEEqFun.mk f (by fun_prop)
  left_inv f := AEEqFun.mk_coeFn f
  right_inv f := funext (Measure.ae_count_iff.mp (AEEqFun.coeFn_mk f _))
  map_add' f g := funext (Measure.ae_count_iff.mp (AEEqFun.coeFn_add f g))
  map_smul' c f := funext (Measure.ae_count_iff.mp (AEEqFun.coeFn_smul c f))

lemma pair_memLp (f : Fin 2 → ℂ) (p : ℝ≥0∞) : MemLp f p μ₂ := by
  apply MemLp.of_bound (by fun_prop) (max ‖f 0‖ ‖f 1‖)
  apply ae_of_all
  intro i
  fin_cases i <;> simp

lemma pair_norm (f : Fin 2 → ℂ) {r : ℝ} (hr : 0 < r) :
    (eLpNorm f (ENNReal.ofReal r) μ₂).toReal =
      (‖f 0‖ ^ r + ‖f 1‖ ^ r) ^ (1/r) := by
  rw [(pair_memLp f _).eLpNorm_eq_integral_rpow_norm (by positivity) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity)]
  simp [integral_count, Fin.sum_univ_two, ENNReal.toReal_ofReal hr.le]

lemma pair_norm_one (f : Fin 2 → ℂ) :
    (eLpNorm f 1 μ₂).toReal = ‖f 0‖ + ‖f 1‖ := by
  simpa using pair_norm f (by norm_num : (0:ℝ)<1)

lemma pair_norm_top (f : Fin 2 → ℂ) :
    (eLpNorm f ∞ μ₂).toReal = max ‖f 0‖ ‖f 1‖ := by
  rw [eLpNorm_exponent_top (by fun_prop), eLpNormEssSup_count]
  have hs : (⨆ i : Fin 2, ‖f i‖ₑ) = max ‖f 0‖ₑ ‖f 1‖ₑ := by
    apply le_antisymm
    · apply iSup_le
      intro i
      fin_cases i <;> simp
    · exact max_le (le_iSup (fun i => ‖f i‖ₑ) 0) (le_iSup (fun i => ‖f i‖ₑ) 1)
  rw [hs, ENNReal.toReal_max] <;> simp

def hadamard : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun f := ![f 0 + f 1, f 0 - f 1]
  map_add' f g := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c f := by ext i; fin_cases i <;> simp <;> ring

lemma bound_one (f : Fin 2 → ℂ) :
    eLpNorm (hadamard f) ∞ μ₂ ≤ eLpNorm f 1 μ₂ := by
  apply (ENNReal.toReal_le_toReal (pair_memLp _ _).eLpNorm_lt_top.ne
    (pair_memLp _ _).eLpNorm_lt_top.ne).mp
  rw [pair_norm_top, pair_norm_one]
  exact max_le (norm_add_le _ _) (norm_sub_le _ _)

lemma bound_two (f : Fin 2 → ℂ) :
    eLpNorm (hadamard f) 2 μ₂ ≤ ENNReal.ofReal (Real.sqrt 2) * eLpNorm f 2 μ₂ := by
  apply (ENNReal.toReal_le_toReal (pair_memLp _ _).eLpNorm_lt_top.ne
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (pair_memLp _ _).eLpNorm_lt_top.ne)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have he : ENNReal.ofReal (2:ℝ) = 2 := by norm_num
  rw [← he, pair_norm _ (by norm_num), pair_norm _ (by norm_num)]
  have hid := parallelogram_law_with_norm ℂ (f 0) (f 1)
  simp only [hadamard, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at *
  norm_num only [Real.rpow_two, one_div] at *
  rw [hid, Real.mul_rpow (by norm_num) (by positivity), Real.sqrt_eq_rpow]

def hadamardAE : ((Fin 2) →ₘ[μ₂] ℂ) →ₗ[ℂ] ((Fin 2) →ₘ[μ₂] ℂ) :=
  evalAE.symm.toLinearMap.comp (hadamard.comp evalAE.toLinearMap)

def hadamardSum (p₀ p₁ : ℝ≥0∞) :
    ExpandedFA.Interpolation.RieszThorinSpec.SumSpace μ₂ p₀ p₁ →ₗ[ℂ] ((Fin 2) →ₘ[μ₂] ℂ) :=
  hadamardAE.comp (Submodule.subtype _)

lemma hadamardSum_apply (p₀ p₁ : ℝ≥0∞)
    (f : ExpandedFA.Interpolation.RieszThorinSpec.SumSpace μ₂ p₀ p₁) :
    evalAE (hadamardSum p₀ p₁ f) = hadamard (evalAE f.val) := by
  exact evalAE.apply_symm_apply _

open ExpandedFA.Interpolation.RieszThorinSpec

lemma endpoint_one : EndpointBound (hadamardSum 1 2) 1 ∞ 1 := by
  intro f hf
  refine ⟨pair_memLp _ _, ?_⟩
  change eLpNorm (evalAE (hadamardSum 1 2 f)) ∞ μ₂ ≤ _
  rw [hadamardSum_apply]
  rw [ENNReal.ofReal_one, one_mul]
  exact bound_one (evalAE f.val)

lemma endpoint_two : EndpointBound (hadamardSum 1 2) 2 2 (Real.sqrt 2) := by
  intro f hf
  refine ⟨pair_memLp _ _, ?_⟩
  change eLpNorm (evalAE (hadamardSum 1 2 f)) 2 μ₂ ≤ _
  rw [hadamardSum_apply]
  exact bound_two (evalAE f.val)

lemma interpolates_pair {p : ℝ} (hp : 1 < p) (hp₂ : p < 2) :
    Interpolates 1 2 (ENNReal.ofReal p) (2*(1-1/p)) ∧
    Interpolates ∞ 2 (ENNReal.ofReal (p/(p-1))) (2*(1-1/p)) := by
  have hp0 : 0 < p := by linarith
  have ht0 : 0 < 2*(1-1/p) := by field_simp; nlinarith
  have ht1 : 2*(1-1/p) < 1 := by field_simp; nlinarith
  have hq0 : 0 < p/(p-1) := div_pos hp0 (by linarith)
  have hn₁ : ENNReal.ofReal (1 - 2*(1-1/p)) * (1:ℝ≥0∞)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have hn₂ : ENNReal.ofReal (2*(1-1/p)) * (2:ℝ≥0∞)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
  constructor
  · unfold Interpolates
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp0))
      (ENNReal.add_ne_top.mpr ⟨hn₁,hn₂⟩)).mp
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hp0.le,
      ENNReal.toReal_add hn₁ hn₂, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (show 0 ≤ 1-2*(1-1/p) by linarith),
      ENNReal.toReal_ofReal ht0.le]
    norm_num
    ring
  · unfold Interpolates
    rw [ENNReal.inv_top, mul_zero, zero_add]
    apply (ENNReal.toReal_eq_toReal_iff'
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hq0)) hn₂).mp
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hq0.le,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal ht0.le]
    norm_num
    field_simp
    <;> ring


lemma scalar_lower_complex {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) (a b : ℂ) :
    let q := p/(p-1)
    ‖a+b‖^q + ‖a-b‖^q ≤ 2 * (‖a‖^p+‖b‖^p)^(q/p) := by
  rcases hp₂.eq_or_lt with heq | hlt
  · subst p
    norm_num
    exact (parallelogram_law_with_norm ℂ a b).le
  have hp0 : 0 < p := by linarith
  let q := p/(p-1)
  have hq0 : 0 < q := div_pos hp0 (by linarith)
  let θ := 2*(1-1/p)
  have ht0 : 0 < θ := by dsimp [θ]; field_simp; nlinarith
  have ht1 : θ < 1 := by dsimp [θ]; field_simp; nlinarith
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hp.le)⟩
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    have hq1 : 1 ≤ q := by dsimp [q]; apply (le_div_iff₀ (by linarith)).mpr; linarith
    exact_mod_cast (ENNReal.ofReal_le_ofReal hq1)⟩
  let f : Fin 2 → ℂ := ![a,b]
  let F := (pair_memLp f (ENNReal.ofReal p)).toLp f
  obtain ⟨hf, hm, hb⟩ := ExpandedFA.Interpolation.riesz_thorin
    μ₂ μ₂ 1 2 ∞ 2 (ENNReal.ofReal p) (ENNReal.ofReal q) θ 1 (Real.sqrt 2)
    ht0 ht1 (by norm_num) (by positivity)
    (interpolates_pair hp hlt).1 (interpolates_pair hp hlt).2
    (hadamardSum 1 2) endpoint_one endpoint_two F
  have hF : evalAE (F : (Fin 2) →ₘ[μ₂] ℂ) = f :=
    funext (Measure.ae_count_iff.mp (MemLp.coeFn_toLp (pair_memLp f _)))
  have hFn : ‖F‖ = (eLpNorm f (ENNReal.ofReal p) μ₂).toReal :=
    Lp.norm_toLp _ _
  change (eLpNorm (evalAE (hadamardSum 1 2 ⟨(F : (Fin 2) →ₘ[μ₂] ℂ),hf⟩))
    (ENNReal.ofReal q) μ₂).toReal ≤ _ at hb
  rw [hadamardSum_apply, hF, hFn, pair_norm _ hq0, pair_norm _ hp0] at hb
  simp only [Real.one_rpow, one_mul] at hb
  let A := ‖hadamard f 0‖^q+‖hadamard f 1‖^q
  let B := ‖f 0‖^p+‖f 1‖^p
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ A^(1/q)) hb hq0.le
  have hout : (A^(1/q))^q = A := by
    rw [← Real.rpow_mul hA, one_div_mul_cancel hq0.ne', Real.rpow_one]
  have hin : (B^(1/p))^q = B^(q/p) := by
    rw [← Real.rpow_mul hB]
    congr 1
    ring
  have hconst : ((Real.sqrt 2)^θ)^q = (2:ℝ) := by
    rw [← Real.rpow_mul (by positivity : 0 ≤ Real.sqrt 2), Real.sqrt_eq_rpow,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    have he : (1/2:ℝ) * (θ * q) = 1 := by
      dsimp [θ,q]
      field_simp
    rw [he, Real.rpow_one]
  change (A^(1/q))^q ≤ ((Real.sqrt 2)^θ * B^(1/p))^q at hpow
  rw [hout, Real.mul_rpow (by positivity) (by positivity), hconst, hin] at hpow
  simpa [A,B,hadamard,f] using hpow

end TwoPoint

/-- The complex estimate transports isometrically to either scalar field. -/
lemma scalar_lower {𝕜 : Type v} [RCLike 𝕜] {p : ℝ}
    (hp : 1 < p) (hp₂ : p ≤ 2) (a b : 𝕜) :
    let q := p/(p-1)
    ‖a+b‖^q+‖a-b‖^q ≤ 2*(‖a‖^p+‖b‖^p)^(q/p) := by
  have h := TwoPoint.scalar_lower_complex hp hp₂ (RCLike.map 𝕜 ℂ a) (RCLike.map 𝕜 ℂ b)
  have hn (z : 𝕜) : ‖RCLike.map 𝕜 ℂ z‖ = ‖z‖ := RCLike.norm_to_complex z
  simpa only [← map_add, ← map_sub, hn] using h

/-- Minkowski for the integral of a two-coordinate vector, with no restriction
on the underlying measure. -/
lemma two_minkowski_integral {X : Type u} [MeasurableSpace X] (μ : Measure X)
    {r : ℝ} (hr : 1 ≤ r) {a b : X → ℝ} (ha : Integrable a μ)
    (hb : Integrable b μ) (ha0 : ∀ᵐ x ∂μ, 0 ≤ a x) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) :
    ((∫ x, a x ∂μ)^r + (∫ x, b x ∂μ)^r)^(1/r) ≤
      ∫ x, (a x^r + b x^r)^(1/r) ∂μ := by
  have hr0 : 0 < r := by linarith
  have he : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  letI : Fact (1 ≤ ENNReal.ofReal r) :=
    ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hr⟩
  let F : X → PiLp (ENNReal.ofReal r) (fun _ : Fin 2 => ℝ) :=
    fun x => WithLp.toLp _ ![a x,b x]
  have hF : ∀ i, Integrable (fun x => F x i) μ := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
  have hnorm : ∀ᵐ x ∂μ, ‖F x‖ = (a x^r+b x^r)^(1/r) := by
    filter_upwards [ha0,hb0] with x hx hy
    rw [PiLp.norm_eq_sum (by simpa only [he] using hr0)]
    simp [F, Fin.sum_univ_two, he, Real.norm_eq_abs, abs_of_nonneg hx, abs_of_nonneg hy]
  have hnormI : ‖∫ x, F x ∂μ‖ =
      ((∫ x, a x ∂μ)^r+(∫ x, b x ∂μ)^r)^(1/r) := by
    rw [PiLp.norm_eq_sum (by simpa only [he] using hr0)]
    simp only [Fin.sum_univ_two, he]
    change (‖(∫ x, F x ∂μ) 0‖^r+‖(∫ x, F x ∂μ) 1‖^r)^(1/r) = _
    rw [eval_integral_piLp hF 0, eval_integral_piLp hF 1]
    simp [F, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg_of_ae ha0),
      abs_of_nonneg (integral_nonneg_of_ae hb0)]
  calc
    _ = ‖∫ x, F x ∂μ‖ := hnormI.symm
    _ ≤ ∫ x, ‖F x‖ ∂μ := norm_integral_le_integral_norm F
    _ = _ := integral_congr_ae hnorm

/-- The lower-range Clarkson inequality follows from the scalar estimate
and Minkowski for the two coordinate integrals. -/
theorem lower_range :
  ∀ (𝕜 : Type v) [RCLike 𝕜] {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (hp : 1 < p) (hp₂ : p ≤ 2)
    [Fact (1 ≤ ENNReal.ofReal p)] (f g : Lp 𝕜 (ENNReal.ofReal p) μ),
    let q := p / (p - 1)
    ‖f + g‖ ^ q + ‖f - g‖ ^ q ≤
      2 * (‖f‖ ^ p + ‖g‖ ^ p) ^ (q / p) := by
  intro 𝕜 _ X _ μ p hp hp₂ _ f g
  have hp0 : 0 < p := by linarith
  let q := p/(p-1)
  let r := q/p
  let s := p/q
  have hq0 : 0 < q := div_pos hp0 (by linarith)
  have hr : 1 ≤ r := by
    dsimp [r,q]
    rw [div_div]
    apply (le_div_iff₀ (mul_pos (by linarith) hp0)).mpr
    nlinarith
  have hs : 0 < s := div_pos hp0 hq0
  have hrs : 1/r = s := by dsimp [r,s]; field_simp
  have hsr : s*r=1 := by dsimp [s,r]; field_simp
  have hpow (a : ℝ) (ha : 0 ≤ a) : (a^p)^r = a^q := by
    rw [← Real.rpow_mul ha]
    congr 1
    dsimp [r]
    field_simp
  have he : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hn (h : Lp 𝕜 (ENNReal.ofReal p) μ) : ‖h‖^p = ∫ x, ‖h x‖^p ∂μ := by
    simpa only [he] using lp_norm_rpow_eq_integral (by simpa only [he] using hp0) h
  have hi (h : Lp 𝕜 (ENNReal.ofReal p) μ) : Integrable (fun x => ‖h x‖^p) μ := by
    simpa only [he] using (Lp.memLp h).integrable_norm_rpow
      (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top
  let A : X → ℝ := fun x => ‖(f+g) x‖^q + ‖(f-g) x‖^q
  have hA : Integrable (fun x => A x ^ s) μ := by
    letI : Fact (1 ≤ ENNReal.ofReal r) :=
      ⟨by exact_mod_cast ENNReal.ofReal_le_ofReal hr⟩
    let F : X → PiLp (ENNReal.ofReal r) (fun _ : Fin 2 => ℝ) :=
      fun x => WithLp.toLp _ ![‖(f+g) x‖^p, ‖(f-g) x‖^p]
    have hF : Integrable F μ := by
      apply Integrable.of_eval_piLp
      intro i
      fin_cases i
      · exact hi (f+g)
      · exact hi (f-g)
    apply hF.norm.congr
    filter_upwards [] with x
    rw [PiLp.norm_eq_sum (by rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ r)]; linarith)]
    simp only [Fin.sum_univ_two, ENNReal.toReal_ofReal (show 0 ≤ r by linarith)]
    change (‖‖(f+g) x‖^p‖^r+‖‖(f-g) x‖^p‖^r)^(1/r) = A x^s
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      hpow _ (norm_nonneg _), hpow _ (norm_nonneg _), hrs]
  have hpoint : ∀ᵐ x ∂μ, A x ^ s ≤
      (2:ℝ)^s * (‖f x‖^p + ‖g x‖^p) := by
    filter_upwards [Lp.coeFn_add f g, Lp.coeFn_sub f g] with x hadd hsub
    have h := scalar_lower hp hp₂ (f x) (g x)
    change ‖f x+g x‖^q+‖f x-g x‖^q ≤ 2*(‖f x‖^p+‖g x‖^p)^r at h
    have hh := Real.rpow_le_rpow (by positivity :
      0 ≤ ‖f x+g x‖^q+‖f x-g x‖^q) h hs.le
    have hexp : r*s=1 := by linarith [hsr]
    rw [Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_mul (by positivity : 0 ≤ ‖f x‖^p+‖g x‖^p),
      hexp, Real.rpow_one] at hh
    simpa only [A, hadd, hsub, Pi.add_apply, Pi.sub_apply] using hh
  have hmixed := two_minkowski_integral μ hr (hi (f+g)) (hi (f-g))
    (ae_of_all μ (fun x => by positivity)) (ae_of_all μ (fun x => by positivity))
  rw [← hn (f+g), ← hn (f-g), hpow _ (norm_nonneg _),
    hpow _ (norm_nonneg _), hrs] at hmixed
  simp_rw [hpow _ (norm_nonneg _)] at hmixed
  have hint := integral_mono_ae hA (((hi f).add (hi g)).const_mul ((2:ℝ)^s)) hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_const_mul, integral_add (hi f) (hi g), ← hn f, ← hn g] at hint
  have hh : (‖f+g‖^q+‖f-g‖^q)^s ≤ (2:ℝ)^s * (‖f‖^p+‖g‖^p) :=
    hmixed.trans hint
  have hraise := Real.rpow_le_rpow (by positivity :
    0 ≤ (‖f+g‖^q+‖f-g‖^q)^s) hh (by linarith : 0 ≤ r)
  have hleft : ((‖f+g‖^q+‖f-g‖^q)^s)^r = ‖f+g‖^q+‖f-g‖^q := by
    rw [← Real.rpow_mul (by positivity), hsr, Real.rpow_one]
  have hc : ((2:ℝ)^s)^r = 2 := by
    rw [← Real.rpow_mul (by norm_num), hsr, Real.rpow_one]
  rw [hleft, Real.mul_rpow (by positivity) (by positivity), hc] at hraise
  exact hraise

end ExpandedFA.P1.Clarkson
