import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14UniformConvexity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.LpUniformConvexity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Uniform convexity of ordinary scalar Lᵖ for arbitrary positive measures,
paper.tex:2894–2938. The shared Bochner quotient is definitionally Mathlib's
`Lp`; its identification with the ordinary scalar measurable a.e. quotient
is proved in the accepted `BochnerLpCompleteness` module.

For p > 1 the scalar midpoint p-power has a strictly positive defect on
separated normalized pairs. Compactness in ℂ supplies a uniform gap, which
also applies to ℝ through the norm-preserving RCLike map. Homogeneity yields
  ‖a-b‖^p ≤ t s + C (s - ‖(a+b)/2‖^p),
where s = (‖a‖^p + ‖b‖^p)/2. Integration gives the same inequality for
Lᵖ norms without restricting the measure. For t = ε^p/2, a separated pair
in the unit ball therefore has a positive midpoint defect. Taking a pth root
produces the required modulus. Empty normalized level sets and zero Lᵖ spaces
are included by the compactness and closed-ball formulations.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ExpandedFA.P1.LpUniformConvexity
universe u v

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


lemma lp_norm_rpow_eq_integral {𝕜 : Type v} [RCLike 𝕜] {X : Type u} [MeasurableSpace X]
    {μ : Measure X} {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 0 < q.toReal) (f : Lp 𝕜 q μ) :
    ‖f‖ ^ q.toReal = ∫ x, ‖f x‖ ^ q.toReal ∂μ := by
  have hq0 : q ≠ 0 := (ENNReal.toReal_pos_iff.mp hq).1.ne'
  have hqt : q ≠ ∞ := (ENNReal.toReal_pos_iff.mp hq).2.ne
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm hq0 hqt,
    ENNReal.toReal_ofReal (by positivity), Real.rpow_inv_rpow (by positivity) hq.ne']

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
  ∀ (p : ℝ) (hp : 1 < p) (ε : ℝ), 0 < ε → ε ≤ 2 →
    ∃ δ : ℝ, 0 < δ ∧ ∀ (𝕜 : Type v) [RCLike 𝕜]
      (X : Type u) [MeasurableSpace X] (μ : Measure X),
      letI : Fact (1 ≤ ENNReal.ofReal p) :=
        ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
      ∀ f g : FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue 𝕜
        (ENNReal.ofReal p) μ,
        ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → ε ≤ ‖f - g‖ →
          ‖(2 : 𝕜)⁻¹ • (f + g)‖ ≤ 1 - δ := by
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
  refine ⟨1-(1-k)^p⁻¹, by linarith, fun 𝕜 _ X _ μ f g hf hg hsep => ?_⟩
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

/-- The original closed-unit-ball definition follows from the uniform modulus. -/
theorem measure_lp_uniformly_convex :
  ∀ (𝕜 : Type v) [RCLike 𝕜] (X : Type u) [MeasurableSpace X]
    (μ : Measure X) (p : ℝ) (hp : 1 < p),
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
    C14UniformConvexity.Spec.UniformlyConvexValue 𝕜
      (FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue 𝕜 (ENNReal.ofReal p) μ) := by
  intro 𝕜 _ X _ μ p hp ε hε hε₂
  obtain ⟨δ,hδ,h⟩ := measure_lp_uniform_modulus p hp ε hε hε₂
  exact ⟨δ,hδ,h 𝕜 X μ⟩


end ExpandedFA.P1.LpUniformConvexity
