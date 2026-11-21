import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachGeometry.Clarkson
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachGeometry.ClarksonLargeExponent
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
universe u
namespace ExpandedFA.BanachGeometry

/-- The two large-exponent inequalities are the accepted upstream theorem. -/
theorem clarkson_large : ClarksonSpec.LargeExponent.{u} := clarkson_large_exponent



/-- Two-coordinate Minkowski integral inequality. No measure-size condition is needed. -/
lemma two_coordinate_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {r : ℝ} (hr : 1 ≤ r) {a b : X → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ)
    (ha0 : ∀ᵐ x ∂μ, 0 ≤ a x) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x) :
    ((∫ x, a x ∂μ) ^ r + (∫ x, b x ∂μ) ^ r) ^ (1 / r) ≤
      ∫ x, (a x ^ r + b x ^ r) ^ (1 / r) ∂μ := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let R := ENNReal.ofReal r
  have : Fact (1 ≤ R) := ⟨by simpa [R] using ENNReal.ofReal_le_ofReal hr⟩
  let e := (PiLp.continuousLinearEquiv R ℝ (fun _ : Fin 2 => ℝ)).symm
  let h : X → (Fin 2 → ℝ) := fun x => ![a x, b x]
  have hh : Integrable h μ := integrable_pi_iff.mpr (by
    intro i; fin_cases i <;> assumption)
  have hn (z : Fin 2 → ℝ) :
      ‖e z‖ = (|z 0| ^ r + |z 1| ^ r) ^ (1 / r) := by
    rw [PiLp.norm_eq_sum (by simpa [R, ENNReal.toReal_ofReal hr0.le] using hr0)]
    simp [e, R, ENNReal.toReal_ofReal hr0.le, Fin.sum_univ_two, Real.norm_eq_abs]
  have heq : ‖∫ x, e (h x) ∂μ‖ =
      ((∫ x, a x ∂μ) ^ r + (∫ x, b x ∂μ) ^ r) ^ (1 / r) := by
    rw [e.integral_comp_comm, hn]
    rw [eval_integral (integrable_pi_iff.mp hh), eval_integral (integrable_pi_iff.mp hh)]
    simp [h, abs_of_nonneg (integral_nonneg_of_ae ha0),
      abs_of_nonneg (integral_nonneg_of_ae hb0)]
  rw [← heq]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [ha0, hb0] with x hax hbx
  simp [hn, h, abs_of_nonneg hax, abs_of_nonneg hbx]

namespace Clarkson

lemma lp_power_integral {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ∞) (f : Lp E p μ) :
    ∫ x, ‖f x‖ ^ p.toReal ∂μ = ‖f‖ ^ p.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp) (Fact.out : 1 ≤ p))
  have hP0 := ENNReal.toReal_pos hp0 hpt
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal hp0 hpt (Lp.aestronglyMeasurable f),
    Real.rpow_inv_rpow (integral_nonneg (fun _ => by positivity)) hP0.ne']

set_option maxHeartbeats 800000 in
/-- Integrating the scalar estimate in ℓ^(q/p) proves the small-exponent
Clarkson estimate without imposing sigma-finiteness. -/
theorem lp_small {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p.toReal) (hp2 : p.toReal ≤ 2) (hpt : p ≠ ∞) (f g : Lp 𝕜 p μ) :
    let q := p.toReal / (p.toReal - 1)
    ‖f + g‖ ^ q + ‖f - g‖ ^ q ≤
      2 * (‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal) ^ (q / p.toReal) := by
  let P := p.toReal
  let Q := P / (P - 1)
  let R := (P - 1)⁻¹
  have hP : 1 < P := hp
  have hP0 : 0 < P := by linarith
  have hd : 0 < P - 1 := by linarith
  have hR : 1 ≤ R := (one_le_inv₀ hd).mpr (by dsimp [P]; linarith)
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hQ2 : 2 ≤ Q := (le_div_iff₀ hd).mpr (by dsimp [P]; linarith)
  have hPR : P * R = Q := by rfl
  have hQd : Q - 1 = R := by dsimp [Q, R]; field_simp; ring
  have hQP : Q / (Q - 1) = P := by rw [hQd]; dsimp [Q, R]; field_simp
  have hQR : Q / P = R := by dsimp [Q, R]; field_simp
  have hRi : R * (1 / R) = 1 := mul_one_div_cancel hR0.ne'
  have hQRi : Q * (1 / R) = P := by rw [← hPR, mul_assoc, hRi, mul_one]
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp) (Fact.out : 1 ≤ p))
  have hi (h : Lp 𝕜 p μ) : Integrable (fun x => ‖h x‖ ^ P) μ :=
    (Lp.memLp h).integrable_norm_rpow hp0 hpt
  have hm := two_coordinate_integral hR (hi (f + g)) (hi (f - g))
    (Filter.Eventually.of_forall (fun _ => by positivity))
    (Filter.Eventually.of_forall (fun _ => by positivity))
  rw [lp_power_integral hpt, lp_power_integral hpt] at hm
  change ((‖f + g‖ ^ P) ^ R + (‖f - g‖ ^ P) ^ R) ^ (1 / R) ≤ _ at hm
  conv_lhs at hm => rw [← Real.rpow_mul (norm_nonneg _),
    ← Real.rpow_mul (norm_nonneg _), hPR]
  have hs : ∀ᵐ x ∂μ,
      ((‖(f + g) x‖ ^ P) ^ R + (‖(f - g) x‖ ^ P) ^ R) ^ (1 / R) ≤
        (2 : ℝ) ^ (1 / R) * (‖f x‖ ^ P + ‖g x‖ ^ P) := by
    filter_upwards [Lp.coeFn_add f g, Lp.coeFn_sub f g] with x hx hy
    rw [hx, hy, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _), hPR]
    have hs := Real.rpow_le_rpow (by positivity) (two_point hQ2 (f x) (g x))
      (le_of_lt (one_div_pos.mpr hR0))
    rw [hQP, hQd, Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_mul (by positivity), hRi, Real.rpow_one] at hs
    exact hs
  have hbound : (‖f + g‖ ^ Q + ‖f - g‖ ^ Q) ^ (1 / R) ≤
      (2 : ℝ) ^ (1 / R) * (‖f‖ ^ P + ‖g‖ ^ P) := by
    refine hm.trans ?_
    calc
      _ ≤ ∫ x, (2 : ℝ) ^ (1 / R) * (‖f x‖ ^ P + ‖g x‖ ^ P) ∂μ :=
        integral_mono_ae ?_ ((hi f |>.add (hi g)).const_mul _) hs
      _ = _ := by rw [integral_const_mul, integral_add (hi f) (hi g),
        lp_power_integral hpt, lp_power_integral hpt]
    -- Integrability of the finite-dimensional norm follows from that of its coordinates.
    let e := (PiLp.continuousLinearEquiv (ENNReal.ofReal R) ℝ
      (fun _ : Fin 2 => ℝ)).symm
    have : Fact (1 ≤ ENNReal.ofReal R) :=
      ⟨by simpa using ENNReal.ofReal_le_ofReal hR⟩
    have hh0 : Integrable (fun x => (![‖(f + g) x‖ ^ P, ‖(f - g) x‖ ^ P] : Fin 2 → ℝ)) μ :=
      integrable_pi_iff.mpr (by
        intro i
        fin_cases i
        · exact hi (f + g)
        · exact hi (f - g))
    have hh : Integrable (fun x => e ![‖(f + g) x‖ ^ P, ‖(f - g) x‖ ^ P]) μ :=
      e.integrable_comp_iff.mpr hh0
    convert hh.norm using 1
    ext x
    rw [PiLp.norm_eq_sum (by simpa [ENNReal.toReal_ofReal hR0.le] using hR0)]
    simp [e, ENNReal.toReal_ofReal hR0.le, Fin.sum_univ_two, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have ht := Real.rpow_le_rpow (by positivity) hbound hR0.le
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hR0.ne', Real.rpow_one,
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by norm_num),
    one_div_mul_cancel hR0.ne', Real.rpow_one] at ht
  change ‖f + g‖ ^ Q + ‖f - g‖ ^ Q ≤ 2 * (‖f‖ ^ P + ‖g‖ ^ P) ^ (Q / P)
  rw [hQR]
  exact ht

end Clarkson

/-- Both scalar fields and arbitrary measures are included. -/
theorem clarkson_small : ClarksonSpec.SmallExponent.{u} := by
  intro X _ μ 𝕜 _ p _ hp hp2 hpt f g
  exact Clarkson.lp_small hp hp2 hpt f g


namespace Clarkson

/-- Rescaling a power estimate to the midpoint and half-difference. -/
lemma midpoint_of_power_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (f g : E)
    (h : ‖f + g‖ ^ r + ‖f - g‖ ^ r ≤ (2 : ℝ) ^ r) :
    ‖(1 / 2 : ℝ) • (f + g)‖ ^ r + ‖(1 / 2 : ℝ) • (f - g)‖ ^ r ≤ 1 := by
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  rw [Real.mul_rpow (by norm_num) (norm_nonneg _),
    Real.mul_rpow (by norm_num) (norm_nonneg _), ← mul_add]
  calc
    _ ≤ (1 / 2 : ℝ) ^ r * (2 : ℝ) ^ r := mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 := by rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num

end Clarkson

/-- Unit-ball Clarkson inequality with the single exponent max(p,q). -/
theorem clarkson_midpoint_power : ClarksonSpec.MidpointPower.{u} := by
  intro X _ μ 𝕜 _ p _ hp hpt f g hf hg
  let P := p.toReal
  let Q := P / (P - 1)
  have hP : 1 < P := hp
  have hP0 : 0 < P := by linarith
  have hd : 0 < P - 1 := by linarith
  change ‖(1 / 2 : ℝ) • (f + g)‖ ^ max P Q +
    ‖(1 / 2 : ℝ) • (f - g)‖ ^ max P Q ≤ 1
  apply Clarkson.midpoint_of_power_bound
  rcases le_total 2 P with hlarge | hsmall
  · have hQle : Q ≤ P := (div_le_iff₀ hd).mpr (by nlinarith)
    rw [max_eq_left hQle]
    have hb := (clarkson_large_exponent μ 𝕜 p hlarge hpt f g).1.trans
      (clarkson_large_exponent μ 𝕜 p hlarge hpt f g).2
    change ‖f + g‖ ^ P + ‖f - g‖ ^ P ≤ _ at hb
    have hf' := Real.rpow_le_one (norm_nonneg f) hf hP0.le
    have hg' := Real.rpow_le_one (norm_nonneg g) hg hP0.le
    calc
      _ ≤ (2 : ℝ) ^ (P - 1) * (‖f‖ ^ P + ‖g‖ ^ P) := hb
      _ ≤ (2 : ℝ) ^ (P - 1) * 2 := by gcongr; linarith
      _ = (2 : ℝ) ^ (P - 1) * 2 ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (2 : ℝ) ^ P := by
        rw [← Real.rpow_add (by norm_num)]
        congr 1
        ring
  · have hPle : P ≤ Q := (le_div_iff₀ hd).mpr (by nlinarith)
    have hQ0 : 0 < Q := div_pos hP0 hd
    have hQR : 1 + Q / P = Q := by dsimp [Q]; field_simp; ring
    rw [max_eq_right hPle]
    have hb := Clarkson.lp_small hp hsmall hpt f g
    have hf' := Real.rpow_le_one (norm_nonneg f) hf hP0.le
    have hg' := Real.rpow_le_one (norm_nonneg g) hg hP0.le
    calc
      _ ≤ 2 * (‖f‖ ^ P + ‖g‖ ^ P) ^ (Q / P) := hb
      _ ≤ 2 * (2 : ℝ) ^ (Q / P) := by gcongr; linarith
      _ = (2 : ℝ) ^ Q := by
        nth_rw 1 [← Real.rpow_one (2 : ℝ)]
        rw [← Real.rpow_add (by norm_num), hQR]


namespace Clarkson

/-- Nonnegativity and strict positivity of the explicit power modulus. -/
lemma power_modulus_nonneg {r ε : ℝ} (hr : 0 < r) (hε0 : 0 ≤ ε) (hε2 : ε ≤ 2) :
    0 ≤ 1 - (1 - (ε / 2) ^ r) ^ (1 / r) ∧
    (0 < ε → 0 < 1 - (1 - (ε / 2) ^ r) ^ (1 / r)) := by
  have he0 : 0 ≤ ε / 2 := by positivity
  have he1 : ε / 2 ≤ 1 := by linarith
  have ht0 : 0 ≤ (ε / 2) ^ r := Real.rpow_nonneg he0 _
  have ht1 : (ε / 2) ^ r ≤ 1 := Real.rpow_le_one he0 he1 hr.le
  constructor
  · have hb := Real.rpow_le_one (by linarith : 0 ≤ 1 - (ε / 2) ^ r)
      (by linarith : 1 - (ε / 2) ^ r ≤ 1) (one_div_pos.mpr hr).le
    linarith
  · intro he
    have htpos := Real.rpow_pos_of_pos (by linarith : 0 < ε / 2) r
    have hb := Real.rpow_lt_one (by linarith : 0 ≤ 1 - (ε / 2) ^ r)
      (by linarith : 1 - (ε / 2) ^ r < 1) (one_div_pos.mpr hr)
    linarith

/-- The quantitative midpoint estimate extracted from the power sum. -/
lemma midpoint_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r ε : ℝ} (hr : 0 < r) (hε0 : 0 ≤ ε) (f g : E)
    (hε : ε ≤ ‖f - g‖)
    (h : ‖(1 / 2 : ℝ) • (f + g)‖ ^ r + ‖(1 / 2 : ℝ) • (f - g)‖ ^ r ≤ 1) :
    ‖(1 / 2 : ℝ) • (f + g)‖ ≤ (1 - (ε / 2) ^ r) ^ (1 / r) := by
  have he : ε / 2 ≤ ‖(1 / 2 : ℝ) • (f - g)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    linarith
  have ht := Real.rpow_le_rpow (by positivity) he hr.le
  have hb : ‖(1 / 2 : ℝ) • (f + g)‖ ^ r ≤ 1 - (ε / 2) ^ r := by linarith
  have hn := Real.rpow_le_rpow (by positivity) hb (one_div_pos.mpr hr).le
  rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hr.ne', Real.rpow_one] at hn
  exact hn

end Clarkson

/-- The stated modulus is valid throughout [0,2], and positive on (0,2]. -/
theorem clarkson_modulus : ClarksonSpec.ModulusEstimate.{u} := by
  intro X _ μ 𝕜 _ p _ hp hpt ε he0 he2
  let r := max p.toReal (p.toReal / (p.toReal - 1))
  have hr : 0 < r := lt_of_lt_of_le (by linarith : 0 < p.toReal) (le_max_left _ _)
  have hd := Clarkson.power_modulus_nonneg hr he0 he2
  refine ⟨hd.1, hd.2, ?_⟩
  intro f g hf hg he
  have hn := Clarkson.midpoint_norm_le hr he0 f g he
    (clarkson_midpoint_power μ 𝕜 p hp hpt f g hf hg)
  simpa [ClarksonSpec.modulus, r] using hn

/-- Uniform convexity, with no nontriviality or measure-size assumptions. -/
theorem clarkson_uniformConvex : ClarksonSpec.UniformConvexity.{u} := by
  intro X _ μ 𝕜 _ p _ hp hpt
  constructor
  intro ε he
  by_cases he2 : ε ≤ 2
  · have hm := clarkson_modulus μ 𝕜 p hp hpt ε he.le he2
    refine ⟨2 * ClarksonSpec.modulus p.toReal ε, by linarith [hm.2.1 he], ?_⟩
    intro f hf g hg hfg
    have hn := hm.2.2 f g hf.le hg.le hfg
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1/2)] at hn
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro f hf g hg hfg
    have hn := norm_sub_le f g
    rw [hf, hg] at hn
    exact (he2 (by linarith)).elim

end ExpandedFA.BanachGeometry
