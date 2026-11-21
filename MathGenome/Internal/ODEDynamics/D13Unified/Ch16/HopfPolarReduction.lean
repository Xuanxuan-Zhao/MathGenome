import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfPolarReduction
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.CubicNormalForm
import MathGenome.Internal.MultivariableAnalysis.D04.C05.MorseCoefficients
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace D13Unified.Ch16.HopfPolarReduction

open Complex Filter Set
open scoped ComplexConjugate
open Specs.D13Unified.Ch16.CubicHomologicalElimination
open Specs.D13Unified.Ch16.CubicNormalForm
open Specs.D13Unified.Ch16.HopfReturnExpansion
open Specs.D13Unified.Ch16.HopfPolarReduction

lemma direction_norm (θ : ℝ) : ‖direction θ‖ = 1 := by
  simp [direction, Complex.norm_exp]

lemma direction_conj_mul (θ : ℝ) : conj (direction θ) * direction θ = 1 := by
  simp [Complex.conj_mul', direction_norm]

lemma polarPoint_norm (r θ : ℝ) : ‖polarPoint r θ‖ = |r| := by
  simp [polarPoint, direction_norm]

lemma polarRemainder_norm (F : ℝ × ℂ → ℂ) (θ r μ : ℝ) :
    ‖polarRemainder F θ r μ‖ = ‖remainder F (μ, polarPoint r θ)‖ := by
  simp [polarRemainder, direction_norm]

lemma rotated_normalPolynomial (F : ℝ × ℂ → ℂ) (θ r μ : ℝ) :
    conj (direction θ) * normalPolynomial F μ (polarPoint r θ) =
      eigenvalue (spectralReal F μ) (spectralImag F μ) * r + coefficient F μ * r ^ 3 := by
  have hd := direction_conj_mul θ
  unfold normalPolynomial polarPoint
  simp only [map_mul, Complex.conj_ofReal]
  calc
    _ = eigenvalue (spectralReal F μ) (spectralImag F μ) * r *
          (conj (direction θ) * direction θ) +
        coefficient F μ * r ^ 3 * (conj (direction θ) * direction θ) ^ 2 := by ring
    _ = _ := by rw [hd]; ring

theorem polarVelocityIdentity : PolarVelocityIdentity := by
  intro F θ r μ hr
  have hn := rotated_normalPolynomial F θ r μ
  have hfull : conj (direction θ) * transformedField F (μ, polarPoint r θ) =
      eigenvalue (spectralReal F μ) (spectralImag F μ) * r + coefficient F μ * r ^ 3 +
        polarRemainder F θ r μ := by
    rw [D13Unified.Ch16.CubicNormalForm.transformedField_eq]
    change conj (direction θ) * (normalPolynomial F μ (polarPoint r θ) + _) = _
    rw [mul_add, hn]; rfl
  rw [hfull]
  apply Complex.ext <;>
    simp [eigenvalue, radialVelocity, angularVelocity, ← Complex.ofReal_pow,
      Complex.mul_re, Complex.mul_im] <;> field_simp

lemma polarRemainder_bound (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hR : UniformRemainderBounds F ε ρ C) (θ r μ : ℝ)
    (hr : |r| < ρ) (hμ : |μ| < ε) :
    ‖polarRemainder F θ r μ‖ ≤ C * |r| ^ 4 := by
  obtain ⟨_, _, _, _, _, hv, _⟩ := hR (μ, polarPoint r θ)
    ⟨hμ, by simpa [polarPoint_norm] using hr⟩
  simpa [polarRemainder_norm, polarPoint_norm] using hv

lemma angular_remainder_bound (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hR : UniformRemainderBounds F ε ρ C) (θ r μ : ℝ)
    (hr : |r| < ρ) (hμ : |μ| < ε) :
    |(polarRemainder F θ r μ).im / r| ≤ C * |r| ^ 3 := by
  by_cases hz : r = 0
  · simp [hz]
  have hp : 0 < |r| := abs_pos.mpr hz
  rw [abs_div, div_le_iff₀ hp]
  calc
    |(polarRemainder F θ r μ).im| ≤ ‖polarRemainder F θ r μ‖ := abs_im_le_norm _
    _ ≤ C * |r| ^ 4 := polarRemainder_bound F hR θ r μ hr hμ
    _ = C * |r| ^ 3 * |r| := by ring

lemma angular_coefficients_regular (F : ℝ × ℂ → ℂ) (μ : ℝ)
    (ha : ContDiffAt ℝ 4 (spectralReal F) μ)
    (hb : ContDiffAt ℝ 4 (spectralImag F) μ)
    (hc : ContDiffAt ℝ 2 (coefficient F) μ) (hb0 : spectralImag F μ ≠ 0) :
    ContDiffAt ℝ 2 (angularLinear F) μ ∧ ContDiffAt ℝ 2 (angularCubic F) μ := by
  have ha2 : ContDiffAt ℝ 2 (spectralReal F) μ := ha.of_le (by norm_num)
  have hb2 : ContDiffAt ℝ 2 (spectralImag F) μ := hb.of_le (by norm_num)
  refine ⟨ha2.div hb2 hb0, ?_⟩
  have hcr := Complex.reCLM.contDiff.contDiffAt.comp μ hc
  have hci := Complex.imCLM.contDiff.contDiffAt.comp μ hc
  exact (hcr.div hb2 hb0).sub ((ha2.mul hci).div (hb2.pow 2) (pow_ne_zero _ hb0))

/-- The radius is common to every angle, including signed radius zero. -/
lemma uniformAngularPositivity (F : ℝ × ℂ → ℂ) (ω : ℝ) {ε ρ C : ℝ}
    (hω : 0 < ω) (hε : 0 < ε) (hρ : 0 < ρ) (hC : 0 < C)
    (hb : ContinuousAt (spectralImag F) 0) (hb0 : spectralImag F 0 = ω)
    (hc : ContinuousAt (coefficient F) 0) (hR : UniformRemainderBounds F ε ρ C) :
    ∃ ε' > 0, ∃ ρ' > 0, ε' ≤ ε ∧ ρ' ≤ ρ ∧
      ∀ θ r μ : ℝ, |r| < ρ' → |μ| < ε' →
        ω / 2 < angularVelocity F θ r μ := by
  let M := |(coefficient F 0).im| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hbn : ∀ᶠ μ in nhds (0 : ℝ), 3 * ω / 4 < spectralImag F μ :=
    hb.eventually (lt_mem_nhds (by rw [hb0]; linarith))
  have hcn : ∀ᶠ μ in nhds (0 : ℝ), |(coefficient F μ).im| < M :=
    (Complex.continuous_im.continuousAt.comp hc).abs.eventually (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp (hbn.and hcn)
  let ε' := min ε δ
  let ρ' := min ρ (min 1 (ω / (8 * (M + C + 1))))
  have hden : 0 < 8 * (M + C + 1) := by positivity
  have hρ' : 0 < ρ' := lt_min hρ (lt_min zero_lt_one (div_pos hω hden))
  refine ⟨ε', lt_min hε hδ, ρ', hρ', min_le_left _ _, min_le_left _ _, ?_⟩
  intro θ r μ hr hμ
  have hrρ : |r| < ρ := hr.trans_le (min_le_left _ _)
  have hr1 : |r| < 1 := hr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrs : |r| < ω / (8 * (M + C + 1)) :=
    hr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hμε : |μ| < ε := hμ.trans_le (min_le_left _ _)
  have hμδ : dist μ 0 < δ := by
    simpa [Real.dist_eq] using hμ.trans_le (min_le_right ε δ)
  obtain ⟨hbl, hcl⟩ := hd hμδ
  have hr2 : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
  have hs2 : |r| ^ 2 ≤ |r| := by nlinarith [abs_nonneg r]
  have hs3 : |r| ^ 3 ≤ |r| := by
    calc
      |r| ^ 3 = |r| ^ 2 * |r| := by ring
      _ ≤ |r| * |r| := mul_le_mul_of_nonneg_right hs2 (abs_nonneg r)
      _ ≤ |r| := by nlinarith
  have hm : |(coefficient F μ).im * r ^ 2| ≤ M * |r| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg r), hr2]
    exact (mul_le_mul_of_nonneg_right hcl.le (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hs2 hM.le)
  have he : |(polarRemainder F θ r μ).im / r| ≤ C * |r| :=
    (angular_remainder_bound F hR θ r μ hrρ hμε).trans
      (mul_le_mul_of_nonneg_left hs3 hC.le)
  have hsmall : 8 * (M + C + 1) * |r| < ω := by
    have hh := (lt_div_iff₀ hden).mp hrs
    nlinarith
  have hmlo := (abs_le.mp hm).1
  have helo := (abs_le.mp he).1
  unfold angularVelocity
  nlinarith [abs_nonneg r]

theorem polarNeighborhood : PolarNeighborhood := by
  intro F ω hF hω heig heq
  obtain ⟨_, hb0, ε, hε, ρ, hρ, C, hC, hcoord, hR, hdata⟩ :=
    CubicNormalForm.normalForm F ω hF hω heig heq
  have hz : |(0 : ℝ)| < ε := by simpa using hε
  obtain ⟨_, _, hb, hc, _⟩ := hdata 0 hz
  obtain ⟨ε', hε', ρ', hρ', heε, hrρ, hpos⟩ :=
    uniformAngularPositivity F ω hω hε hρ hC hb.continuousAt hb0 hc.continuousAt hR
  refine ⟨ε', hε', ρ', hρ', C, hC,
    CubicNormalForm.coordinateValidity_mono hcoord heε hrρ,
    CubicNormalForm.uniformRemainderBounds_mono hR heε hrρ, ?_, hpos⟩
  intro μ hμ
  obtain ⟨hb, ha, hbr, hc, _⟩ := hdata μ (hμ.trans_le heε)
  exact angular_coefficients_regular F μ ha hbr hc hb.ne'

/-- Exact residual identity before making any asymptotic estimate. -/
lemma angular_quotient_identity (a b c d e f r : ℝ) (hb : b ≠ 0) (hr : r ≠ 0)
    (hD : b + c * r ^ 2 + e / r ≠ 0) :
    (a * r + d * r ^ 3 + f) / (b + c * r ^ 2 + e / r) -
        (a / b) * r - (d / b - a * c / b ^ 2) * r ^ 3 =
      (f - (a / b) * e - (d / b - a * c / b ^ 2) * c * r ^ 5 -
        (d / b - a * c / b ^ 2) * e * r ^ 2) / (b + c * r ^ 2 + e / r) := by
  apply (eq_div_iff hD).2
  rw [sub_mul, sub_mul, div_mul_cancel₀ _ hD]
  field_simp [hb, hr]
  ring

lemma polarPoint_zero_angle (r : ℝ) : polarPoint r 0 = (r : ℂ) := by
  simp [polarPoint, direction]

lemma polarPoint_full_turn (r : ℝ) : polarPoint r (2 * Real.pi) = (r : ℂ) := by
  simp [polarPoint, direction, Complex.exp_mul_I]

lemma polarPoint_not_positiveRay (r θ : ℝ) (hr : 0 < r)
    (hθ : θ ∈ Ioo 0 (2 * Real.pi)) : ¬ positiveRay (polarPoint r θ) := by
  intro hp
  have hi : Real.sin θ = 0 := by
    have := hp.1
    simpa [polarPoint, direction, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos, hr.ne'] using this
  have hc : 0 < Real.cos θ := by
    have := hp.2
    simpa [polarPoint, direction, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos, hr] using this
  have hs := Real.sin_sq_add_cos_sq θ
  have hc1 : Real.cos θ = 1 := by nlinarith
  have heq := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos, hθ.1]) hθ.2).mp hc1
  linarith [hθ.1]

lemma inverseWithin {f g : ℝ → ℝ} {s t : Set ℝ} {a d : ℝ}
    (ha : a ∈ t) (hg : ContinuousWithinAt g t a) (hgs : MapsTo g t s)
    (hf : HasDerivWithinAt f d s (g a)) (hd : d ≠ 0)
    (hi : ∀ y ∈ t, f (g y) = y) : HasDerivWithinAt g d⁻¹ t a := by
  have ht := hg.tendsto_nhdsWithin hgs
  have hf' := HasFDerivWithinAt.of_comp_of_leftInverse
    (f'symm := ContinuousLinearMap.toSpanSingleton ℝ d⁻¹)
    ht hf.hasFDerivWithinAt (hasDerivWithinAt_id a t).hasFDerivWithinAt
    (by filter_upwards [self_mem_nhdsWithin] with y hy using hi y hy) (by
      intro v
      simp [ContinuousLinearMap.toSpanSingleton_apply, hd]) ha
  convert hf'.hasDerivWithinAt using 1; simp


lemma clockData {L : ℝ} (hL : 0 < L) (v : ℝ → ℝ)
    (hv : ContinuousOn v (Icc 0 L)) (hp : ∀ θ ∈ Icc 0 L, 0 < v θ) :
    let clock := fun θ => ∫ s in (0 : ℝ)..θ, v s
    clock 0 = 0 ∧ ContinuousOn clock (Icc 0 L) ∧
    (∀ θ ∈ Icc 0 L, HasDerivWithinAt clock (v θ) (Icc 0 L) θ) ∧
    StrictMonoOn clock (Icc 0 L) ∧ 0 < clock L ∧
    BijOn clock (Icc 0 L) (Icc 0 (clock L)) := by
  dsimp only
  let w := IccExtend hL.le (fun θ : Icc 0 L => v θ)
  have hw : Continuous w := hv.domRestrict.Icc_extend'
  have heq (θ : ℝ) (hθ : θ ∈ Icc 0 L) :
      (∫ s in (0 : ℝ)..θ, w s) = ∫ s in (0 : ℝ)..θ, v s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc 0 L := by
      rw [uIcc_of_le hθ.1] at hs
      exact ⟨hs.1, hs.2.trans hθ.2⟩
    exact IccExtend_of_mem _ _ hs'
  have hd : ∀ θ ∈ Icc 0 L,
      HasDerivWithinAt (fun θ => ∫ s in (0 : ℝ)..θ, v s) (v θ) (Icc 0 L) θ := by
    intro θ hθ
    have hh : HasDerivWithinAt (fun θ => ∫ s in (0 : ℝ)..θ, w s) (w θ) (Icc 0 L) θ := (intervalIntegral.integral_hasDerivAt_right
      (hw.intervalIntegrable 0 θ) (hw.stronglyMeasurableAtFilter _ _) hw.continuousAt).hasDerivWithinAt
    rw [show w θ = v θ from IccExtend_of_mem _ _ hθ] at hh
    exact hh.congr (fun s hs => (heq s hs).symm) (heq θ hθ).symm
  have hc : ContinuousOn (fun θ => ∫ s in (0 : ℝ)..θ, v s) (Icc 0 L) :=
    fun θ hθ => (hd θ hθ).continuousWithinAt
  have hm : StrictMonoOn (fun θ => ∫ s in (0 : ℝ)..θ, v s) (Icc 0 L) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hc
      (fun θ hθ => (hd θ (interior_subset hθ)).mono interior_subset)
      (fun θ hθ => hp θ (interior_subset hθ))
  have hz : (∫ s in (0 : ℝ)..0, v s) = 0 := by simp
  have him : (fun θ => ∫ s in (0 : ℝ)..θ, v s) '' Icc 0 L =
      Icc 0 (∫ s in (0 : ℝ)..L, v s) := by
    simpa using hc.image_Icc_of_monotoneOn hL.le hm.monotoneOn
  refine ⟨hz, hc, hd, hm, ?_, ?_⟩
  · simpa using hm (left_mem_Icc.mpr hL.le) (right_mem_Icc.mpr hL.le) hL
  · exact ⟨fun θ hθ => him ▸ mem_image_of_mem _ hθ, hm.injOn,
      fun y hy => by simpa [him] using hy⟩

lemma compactClockInverse {L T : ℝ} (_hL : 0 < L) (hT : 0 < T) (clock : ℝ → ℝ)
    (hc : ContinuousOn clock (Icc 0 L)) (hb : BijOn clock (Icc 0 L) (Icc 0 T)) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc 0 T) ∧ MapsTo g (Icc 0 T) (Icc 0 L) ∧
      (∀ θ ∈ Icc 0 L, g (clock θ) = θ) ∧ (∀ t ∈ Icc 0 T, clock (g t) = t) := by
  let e := hb.equiv clock
  have hec : Continuous e := hc.domRestrict.subtype_mk _
  let h := hec.homeoOfEquivCompactToT2
  let g : ℝ → ℝ := IccExtend hT.le (fun t : Icc 0 T => (h.symm t : ℝ))
  have hg : Continuous g := (continuous_subtype_val.comp h.continuous_invFun).Icc_extend'
  have hgval (t : ℝ) (ht : t ∈ Icc 0 T) : g t = (h.symm ⟨t, ht⟩ : ℝ) :=
    IccExtend_of_mem _ _ ht
  refine ⟨g, hg.continuousOn, ?_, ?_, ?_⟩
  · intro t ht
    rw [hgval t ht]
    exact (h.symm ⟨t, ht⟩).property
  · intro θ hθ
    rw [hgval _ (hb.mapsTo hθ)]
    exact congrArg Subtype.val (h.symm_apply_apply ⟨θ, hθ⟩)
  · intro t ht
    rw [hgval t ht]
    exact congrArg Subtype.val (h.apply_symm_apply ⟨t, ht⟩)

lemma direction_hasDerivAt (θ : ℝ) :
    HasDerivAt direction (direction θ * I) θ := by
  convert (Real.hasDerivAt_cos θ).ofReal_comp.add
    ((Real.hasDerivAt_sin θ).ofReal_comp.mul_const I) using 1
  · ext t
    simp [direction, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  · simp [direction, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring_nf
    simp [sub_eq_add_neg]

lemma direction_continuous : Continuous direction :=
  continuous_iff_continuousAt.mpr fun θ => (direction_hasDerivAt θ).continuousAt

lemma angularVelocity_continuousOn_curve (F : ℝ × ℂ → ℂ) {ε ρ C μ : ℝ}
    (hR : UniformRemainderBounds F ε ρ C) (hμ : |μ| < ε)
    {s : Set ℝ} {u : ℝ → ℝ} (hu : ContinuousOn u s)
    (hur : ∀ θ ∈ s, 0 < u θ ∧ u θ < ρ) :
    ContinuousOn (fun θ => angularVelocity F θ (u θ) μ) s := by
  have hq : ContinuousOn (fun θ => polarPoint (u θ) θ) s :=
    (Complex.continuous_ofReal.comp_continuousOn hu).mul direction_continuous.continuousOn
  have he : ContinuousOn (fun θ => polarRemainder F θ (u θ) μ) s := by
    intro θ hθ
    have hbox : (μ, polarPoint (u θ) θ) ∈ stateParameterBox ε ρ := by
      exact ⟨hμ, by simpa [polarPoint_norm, abs_of_pos (hur θ hθ).1] using (hur θ hθ).2⟩
    have hc := (hR _ hbox).1.continuousAt
    exact (Complex.continuous_conj.continuousAt.comp
      direction_continuous.continuousAt).continuousWithinAt.mul
        (ContinuousAt.comp_continuousWithinAt (f := fun s : ℝ => (μ, polarPoint (u s) s)) hc ((show ContinuousWithinAt (fun _ : ℝ => μ) s θ from continuousWithinAt_const).prodMk (hq θ hθ)))
  exact (continuousOn_const.add (continuousOn_const.mul (hu.pow 2))).add
    ((Complex.continuous_im.comp_continuousOn he).div hu (fun θ hθ => (hur θ hθ).1.ne'))

lemma polarCurve_hasDerivWithinAt (F : ℝ × ℂ → ℂ) (μ θ : ℝ) {s : Set ℝ}
    {u : ℝ → ℝ} (hu : HasDerivWithinAt u (angularField F θ (u θ) μ) s θ) :
    HasDerivWithinAt (fun θ => polarPoint (u θ) θ)
      ((angularField F θ (u θ) μ : ℂ) * direction θ +
        (u θ : ℂ) * (direction θ * I)) s θ :=
  hu.ofReal_comp.mul (direction_hasDerivAt θ).hasDerivWithinAt

lemma polarCurve_velocity (F : ℝ × ℂ → ℂ) (μ θ r : ℝ) (hr : r ≠ 0)
    (hD : angularVelocity F θ r μ ≠ 0) :
    ((angularField F θ r μ : ℂ) * direction θ + (r : ℂ) * (direction θ * I)) =
      (1 / angularVelocity F θ r μ : ℝ) • transformedField F (μ, polarPoint r θ) := by
  have h := polarVelocityIdentity F θ r μ hr
  have hfield : transformedField F (μ, polarPoint r θ) =
      direction θ * ((radialVelocity F θ r μ : ℂ) + I * (r * angularVelocity F θ r μ : ℝ)) := by
    calc
      _ = direction θ * (conj (direction θ) * transformedField F (μ, polarPoint r θ)) := by
        rw [← mul_assoc, mul_comm (direction θ), direction_conj_mul, one_mul]
      _ = _ := by rw [h]
  rw [hfield, Complex.real_smul]
  simp only [angularField, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul]
  have hDc : (angularVelocity F θ r μ : ℂ) ≠ 0 := by exact_mod_cast hD
  field_simp

lemma reconstructOnChart (F : ℝ × ℂ → ℂ) {ω ε ρ C : ℝ}
    (hω : 0 < ω) (hR : UniformRemainderBounds F ε ρ C)
    (hpos : ∀ θ r μ : ℝ, |r| < ρ → |μ| < ε → ω / 2 < angularVelocity F θ r μ) :
    ReconstructionOnChart F ε ρ := by
  intro μ r u hμ hr hu0 hu hud hur
  let L := 2 * Real.pi
  have hL : 0 < L := by dsimp [L]; positivity
  let D : ℝ → ℝ := fun θ => angularVelocity F θ (u θ) μ
  have hD : ∀ θ ∈ Icc 0 L, 0 < D θ := by
    intro θ hθ
    have hh := hpos θ (u θ) μ (by rw [abs_of_pos (hur θ hθ).1]; exact (hur θ hθ).2) hμ
    dsimp [D]
    linarith
  have hDc : ContinuousOn D (Icc 0 L) := angularVelocity_continuousOn_curve F hR hμ hu hur
  have hvc : ContinuousOn (fun θ => 1 / D θ) (Icc 0 L) :=
    continuousOn_const.div hDc (fun θ hθ => (hD θ hθ).ne')
  let clock := physicalClock F μ u
  obtain ⟨hc0, hcc, hcd, hcm, hT, hcb⟩ :=
    clockData hL (fun θ => 1 / D θ) hvc (fun θ hθ => one_div_pos.mpr (hD θ hθ))
  change clock 0 = 0 at hc0
  change ContinuousOn clock (Icc 0 L) at hcc
  change ∀ θ ∈ Icc 0 L, HasDerivWithinAt clock (1 / D θ) (Icc 0 L) θ at hcd
  change StrictMonoOn clock (Icc 0 L) at hcm
  change 0 < clock L at hT
  change BijOn clock (Icc 0 L) (Icc 0 (clock L)) at hcb
  obtain ⟨g, hgc, hgs, hgi, hcg⟩ := compactClockInverse hL hT clock hcc hcb
  have hgd : ∀ t ∈ Icc 0 (clock L), HasDerivWithinAt g (D (g t)) (Icc 0 (clock L)) t := by
    intro t ht
    have hh := inverseWithin ht (hgc t ht) hgs (hcd (g t) (hgs ht))
      (one_div_ne_zero (hD (g t) (hgs ht)).ne') hcg
    simpa using hh
  let q : ℝ → ℂ := fun θ => polarPoint (u θ) θ
  have hqc : ContinuousOn q (Icc 0 L) :=
    (Complex.continuous_ofReal.comp_continuousOn hu).mul direction_continuous.continuousOn
  have hqd : ∀ θ ∈ Icc 0 L,
      HasDerivWithinAt q ((1 / D θ) • transformedField F (μ, q θ)) (Icc 0 L) θ := by
    intro θ hθ
    have hh := polarCurve_hasDerivWithinAt F μ θ (hud θ hθ)
    rw [polarCurve_velocity F μ θ (u θ) (hur θ hθ).1.ne' (hD θ hθ).ne'] at hh
    exact hh
  let z : ℝ → ℂ := q ∘ g
  have hzc : ContinuousOn z (Icc 0 (clock L)) := hqc.comp hgc hgs
  have hzd : ∀ t ∈ Icc 0 (clock L),
      HasDerivWithinAt z (transformedField F (μ, z t)) (Icc 0 (clock L)) t := by
    intro t ht
    have hh := (hqd (g t) (hgs ht)).scomp t (hgd t ht) hgs
    convert hh using 1
    simp [z, Function.comp_def, (hD (g t) (hgs ht)).ne']
  have hzclock : ∀ θ ∈ Icc 0 L, z (clock θ) = polarPoint (u θ) θ := by
    intro θ hθ
    simp [z, Function.comp_def, hgi θ hθ, q]
  have h0 : (0 : ℝ) ∈ Icc 0 L := left_mem_Icc.mpr hL.le
  have hlast : L ∈ Icc 0 L := right_mem_Icc.mpr hL.le
  have hz0 : z 0 = (r : ℂ) := by
    simpa [hc0, hu0, polarPoint_zero_angle] using hzclock 0 h0
  have hzL : z (clock L) = (u L : ℂ) := by
    simpa only [L, polarPoint_full_turn] using hzclock L hlast
  have havoid : ∀ t ∈ Ioo 0 (clock L), ¬ positiveRay (z t) := by
    intro t ht
    have hgt := hgs ⟨ht.1.le, ht.2.le⟩
    have hgz : 0 < g t := by
      by_contra hn
      have hg0 : g t = 0 := le_antisymm (le_of_not_gt hn) hgt.1
      have hh := hcg t ⟨ht.1.le, ht.2.le⟩
      rw [hg0, hc0] at hh
      linarith [ht.1]
    have hgL : g t < L := by
      by_contra hn
      have hgL : g t = L := le_antisymm hgt.2 (le_of_not_gt hn)
      have hh := hcg t ⟨ht.1.le, ht.2.le⟩
      rw [hgL] at hh
      linarith [ht.2]
    exact polarPoint_not_positiveRay (u (g t)) (g t) (hur _ hgt).1 ⟨hgz, hgL⟩
  refine ⟨clock L, hT, z, hc0, rfl, hcc, hcm, hcb, hcd, hzc, ?_, hzclock, hz0, hzL, ?_⟩
  · intro t ht
    refine ⟨hzd t ht, ?_⟩
    change ‖polarPoint (u (g t)) (g t)‖ < ρ
    rw [polarPoint_norm, abs_of_pos (hur _ (hgs ht)).1]
    exact (hur _ (hgs ht)).2
  · exact ⟨clock L, hT, z, hzc, hzd, hz0, hzL, (hur L hlast).1, havoid⟩

noncomputable def compactIntegralCLM (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] : C(Icc (0 : ℝ) 1, Y) →L[ℝ] Y :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t in (0 : ℝ)..1, IccExtend zero_le_one f t
      map_add' := by
        intro f g
        change (∫ t in (0 : ℝ)..1, (IccExtend zero_le_one f t + IccExtend zero_le_one g t)) = _
        exact intervalIntegral.integral_add
          (f.continuous.Icc_extend'.intervalIntegrable 0 1)
          (g.continuous.Icc_extend'.intervalIntegrable 0 1)
      map_smul' := by
        intro c f
        change (∫ t in (0 : ℝ)..1, c • IccExtend zero_le_one f t) = _
        exact intervalIntegral.integral_smul c _ }
    1 (by
      intro f
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (f := IccExtend zero_le_one f)
        (fun t _ => f.norm_coe_le_norm _))

lemma compactIntegralCLM_mkD {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] (v : ℝ → Y) (hv : ContinuousOn v (Icc (0 : ℝ) 1)) :
    compactIntegralCLM Y (ContinuousMap.mkD (fun t : Icc (0 : ℝ) 1 => v t) 0) =
      ∫ t in (0 : ℝ)..1, v t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
  rw [IccExtend_of_mem zero_le_one _ ht']
  exact ContinuousMap.mkD_apply_of_continuous hv.domRestrict

lemma contDiffOn_compactIntegral {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (r : ℕ) (W : Set (X × ℝ)) (hW : IsOpen W) (f : X × ℝ → Y)
    (hf : ContDiffOn ℝ r f W) (U : Set X) (hU : IsOpen U)
    (hUW : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (x,t) ∈ W) :
    ContDiffOn ℝ r (fun x => ∫ t in (0 : ℝ)..1, f (x,t)) U := by
  have h := (compactIntegralCLM Y).contDiff.comp_contDiffOn
    (D04.MorseParameter.contDiffOn_curry r W hW f hf U hU hUW)
  apply h.congr
  intro x hx
  exact (compactIntegralCLM_mkD _
    (hf.continuousOn.comp (by fun_prop) (fun t ht => hUW x hx t ht))).symm

lemma direction_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n direction := by
  have hh : ContDiff ℝ n (fun θ : ℝ => (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) :=
    (Complex.ofRealCLM.contDiff.comp Real.contDiff_cos).add
      ((Complex.ofRealCLM.contDiff.comp Real.contDiff_sin).mul contDiff_const)
  convert hh using 1
  ext θ
  simp [direction, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

lemma polarBox_isOpen (ε ρ : ℝ) : IsOpen (polarBox ε ρ) := by
  unfold polarBox
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter
    ((isOpen_lt (continuous_fst.comp continuous_snd).abs continuous_const).inter
    (isOpen_lt (continuous_snd.comp continuous_snd).abs continuous_const)))

lemma polarSegment_box {ε ρ : ℝ} {x : ℝ × (ℝ × ℝ)}
    (hx : x ∈ polarBox ε ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (x.2.2, polarPoint (t * x.2.1) x.1) ∈ stateParameterBox ε ρ := by
  refine ⟨hx.2.2.2, ?_⟩
  rw [polarPoint_norm, abs_mul, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans_lt hx.2.2.1

lemma polarSegment_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun p : (ℝ × (ℝ × ℝ)) × ℝ =>
      (p.1.2.2, polarPoint (p.2 * p.1.2.1) p.1.1)) := by
  unfold polarPoint
  have hd := (direction_contDiff n).comp (contDiff_fst.comp contDiff_fst :
    ContDiff ℝ n (fun p : (ℝ × (ℝ × ℝ)) × ℝ => p.1.1))
  exact (contDiff_snd.comp (contDiff_snd.comp contDiff_fst)).prodMk
    ((Complex.ofRealCLM.contDiff.comp (contDiff_snd.mul
      (contDiff_fst.comp (contDiff_snd.comp contDiff_fst)))).mul hd)

lemma dividedRemainder_contDiffOn (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hR : UniformRemainderBounds F ε ρ C) :
    ContDiffOn ℝ 2 (dividedRemainder F) (polarBox ε ρ) := by
  let P := fun p : (ℝ × (ℝ × ℝ)) × ℝ =>
      (p.1.2.2, polarPoint (p.2 * p.1.2.1) p.1.1)
  let W := P ⁻¹' stateParameterBox ε ρ
  have hbox : IsOpen (stateParameterBox ε ρ) := by
    exact (isOpen_lt continuous_fst.abs continuous_const).inter
      (isOpen_lt continuous_snd.norm continuous_const)
  have hW : IsOpen W := hbox.preimage (polarSegment_contDiff 2).continuous
  have hI : ContDiffOn ℝ 2
      (fun p : (ℝ × (ℝ × ℝ)) × ℝ => spatialDerivative (remainder F) (P p) (direction p.1.1)) W := by
    intro p hp
    exact (((hR _ hp).2.1.comp p (polarSegment_contDiff 2).contDiffAt).clm_apply
      ((direction_contDiff 2).comp (contDiff_fst.comp contDiff_fst)).contDiffAt).contDiffWithinAt
  have hint := contDiffOn_compactIntegral 2 W hW _ hI (polarBox ε ρ)
    (polarBox_isOpen ε ρ) (fun x hx t ht => polarSegment_box hx ht)
  exact (Complex.conjCLE.contDiff.comp ((direction_contDiff 2).comp contDiff_fst)).contDiffOn.mul hint

lemma remainder_zero (F : ℝ × ℂ → ℂ) {ε ρ C μ : ℝ}
    (hρ : 0 < ρ) (hR : UniformRemainderBounds F ε ρ C) (hμ : |μ| < ε) :
    remainder F (μ, 0) = 0 := by
  have hh := (hR (μ, 0) ⟨hμ, by simpa using hρ⟩).2.2.2.2.2.1
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using hh) (norm_nonneg _)

lemma dividedRemainder_bound (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hC : 0 ≤ C) (hR : UniformRemainderBounds F ε ρ C)
    {x : ℝ × (ℝ × ℝ)} (hx : x ∈ polarBox ε ρ) :
    ‖dividedRemainder F x‖ ≤ C * |x.2.1| ^ 3 := by
  unfold dividedRemainder
  rw [norm_mul, Complex.norm_conj, direction_norm, one_mul]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := C * |x.2.1| ^ 3) ?_).trans_eq (by simp)
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := (by simpa [uIoc_of_le zero_le_one] using Ioc_subset_Icc_self ht)
  have hh := (hR _ (polarSegment_box hx ht')).2.2.2.2.2.2.1
  calc
    ‖spatialDerivative (remainder F) _ (direction x.1)‖ ≤ ‖spatialDerivative (remainder F) _‖ := by
      simpa [direction_norm] using (spatialDerivative (remainder F) _).le_opNorm (direction x.1)
    _ ≤ C * ‖polarPoint (t * x.2.1) x.1‖ ^ 3 := hh
    _ ≤ C * |x.2.1| ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [polarPoint_norm, abs_mul, abs_of_nonneg ht'.1]
      exact mul_le_of_le_one_left (abs_nonneg _) ht'.2

lemma dividedRemainder_zero (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hC : 0 ≤ C) (hR : UniformRemainderBounds F ε ρ C)
    {θ μ : ℝ} (hθμ : (θ, (0 : ℝ), μ) ∈ polarBox ε ρ) :
    dividedRemainder F (θ, 0, μ) = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using dividedRemainder_bound F hC hR hθμ) (norm_nonneg _)

set_option maxHeartbeats 1000000 in
lemma dividedRemainder_mul (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hρ : 0 < ρ) (hR : UniformRemainderBounds F ε ρ C)
    {x : ℝ × (ℝ × ℝ)} (hx : x ∈ polarBox ε ρ) :
    (x.2.1 : ℂ) * dividedRemainder F x = polarRemainder F x.1 x.2.1 x.2.2 := by
  let J : ℝ → ℂ := fun t =>
    spatialDerivative (remainder F) (x.2.2, polarPoint (t * x.2.1) x.1) (direction x.1)
  have hcJ : ContinuousOn J (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ((hR _ (polarSegment_box hx ht)).2.1.continuousAt.comp_continuousWithinAt
      (f := fun s : ℝ => (x.2.2, polarPoint (s * x.2.1) x.1))
      ((continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => x.2.2) (Icc 0 1) t).prodMk
        (by unfold polarPoint; fun_prop))).clm_apply continuousWithinAt_const
  have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun s => remainder F (x.2.2, polarPoint (s * x.2.1) x.1)) (x.2.1 • J t) t := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
    have hdR : DifferentiableAt ℝ (fun w => remainder F (x.2.2, w))
        (polarPoint (t * x.2.1) x.1) :=
      (hR _ (polarSegment_box hx ht')).1.differentiableAt (by norm_num) |>.comp _
        ((differentiableAt_const x.2.2).prodMk differentiableAt_id)
    have hdp : HasDerivAt (fun s => polarPoint (s * x.2.1) x.1)
        (polarPoint x.2.1 x.1) t := by
      simpa [polarPoint, Complex.ofReal_mul, mul_assoc] using
        (hasDerivAt_id t).ofReal_comp.mul_const (polarPoint x.2.1 x.1)
    have hh : HasDerivAt (fun s => remainder F (x.2.2, polarPoint (s * x.2.1) x.1))
        (spatialDerivative (remainder F) (x.2.2, polarPoint (t * x.2.1) x.1)
          (polarPoint x.2.1 x.1)) t := by
      simpa only [Function.comp_def, spatialDerivative] using! hdR.hasFDerivAt.comp_hasDerivAt t hdp
    have he : spatialDerivative (remainder F) (x.2.2, polarPoint (t * x.2.1) x.1)
        (polarPoint x.2.1 x.1) = x.2.1 • J t := by
      simp only [J, polarPoint, ← Complex.real_smul, map_smul]
    rw [he] at hh
    exact hh
  have hi : IntervalIntegrable (fun t => x.2.1 • J t) MeasureTheory.volume 0 1 :=
    (by simpa only [uIcc_of_le zero_le_one, Pi.smul_apply] using! hcJ.const_smul x.2.1 : ContinuousOn (fun t => x.2.1 • J t) (uIcc 0 1)).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simp only [zero_mul, one_mul, polarPoint, Complex.ofReal_zero, zero_mul,
    remainder_zero F hρ hR hx.2.2.2, sub_zero] at he
  rw [intervalIntegral.integral_smul, Complex.real_smul] at he
  unfold dividedRemainder polarRemainder
  change _ = conj (direction x.1) * remainder F (x.2.2, (x.2.1 : ℂ) * direction x.1)
  calc
    _ = conj (direction x.1) * ((x.2.1 : ℂ) * ∫ t in (0 : ℝ)..1, J t) := by ring
    _ = _ := by rw [he]


lemma dividedRemainder_im (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hR : UniformRemainderBounds F ε ρ C)
    {x : ℝ × (ℝ × ℝ)} (hx : x ∈ polarBox ε ρ) :
    (dividedRemainder F x).im = (polarRemainder F x.1 x.2.1 x.2.2).im / x.2.1 := by
  by_cases hr : x.2.1 = 0
  · have hx0 : x = (x.1, 0, x.2.2) := by ext <;> simp [hr]
    rw [hx0, dividedRemainder_zero F hC hR (hx0 ▸ hx)]
    simp
  · apply (eq_div_iff hr).mpr
    have hh := congrArg Complex.im (dividedRemainder_mul F hρ hR hx)
    simpa [mul_comm] using hh

lemma signedFactor_zero (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hC : 0 ≤ C) (hR : UniformRemainderBounds F ε ρ C)
    {θ μ : ℝ} (hx : (θ, (0 : ℝ), μ) ∈ polarBox ε ρ) :
    signedFactor F (θ, 0, μ) = angularLinear F μ := by
  simp [signedFactor, dividedRemainder_zero F hC hR hx, angularLinear]

lemma signedFactor_angularField (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hR : UniformRemainderBounds F ε ρ C)
    {x : ℝ × (ℝ × ℝ)} (hx : x ∈ polarBox ε ρ) :
    angularField F x.1 x.2.1 x.2.2 = x.2.1 * signedFactor F x := by
  have hi := dividedRemainder_im F hρ hC hR hx
  have hr := congrArg Complex.re (dividedRemainder_mul F hρ hR hx)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hr
  unfold angularField radialVelocity angularVelocity signedFactor
  rw [hi, mul_div_assoc']
  congr 1
  rw [mul_add, mul_add, hr]
  ring

lemma signedFactor_contDiffOn (F : ℝ × ℂ → ℂ) {ω ε ρ C : ℝ}
    (hω : 0 < ω) (hρ : 0 < ρ) (hC : 0 ≤ C) (hR : UniformRemainderBounds F ε ρ C)
    (ha : ∀ μ : ℝ, |μ| < ε → ContDiffAt ℝ 2 (spectralReal F) μ)
    (hb : ∀ μ : ℝ, |μ| < ε → ContDiffAt ℝ 2 (spectralImag F) μ)
    (hc : ∀ μ : ℝ, |μ| < ε → ContDiffAt ℝ 2 (coefficient F) μ)
    (hpos : ∀ θ r μ : ℝ, |r| < ρ → |μ| < ε → ω / 2 < angularVelocity F θ r μ) :
    ContDiffOn ℝ 2 (signedFactor F) (polarBox ε ρ) := by
  intro x hx
  have hproj : ContDiffAt ℝ 2 (fun x : ℝ × (ℝ × ℝ) => x.2.2) x :=
    (contDiff_snd.comp contDiff_snd).contDiffAt
  have hrad : ContDiffAt ℝ 2 (fun x : ℝ × (ℝ × ℝ) => x.2.1) x :=
    (contDiff_fst.comp contDiff_snd).contDiffAt
  have ha' := (ha _ hx.2.2.2).comp x hproj
  have hb' := (hb _ hx.2.2.2).comp x hproj
  have hc' := (hc _ hx.2.2.2).comp x hproj
  have hcr := Complex.reCLM.contDiff.contDiffAt.comp x hc'
  have hci := Complex.imCLM.contDiff.contDiffAt.comp x hc'
  have hS := (dividedRemainder_contDiffOn F hR).contDiffAt ((polarBox_isOpen _ _).mem_nhds hx)
  have hSr := Complex.reCLM.contDiff.contDiffAt.comp x hS
  have hSi := Complex.imCLM.contDiff.contDiffAt.comp x hS
  have hnum := (ha'.add (hcr.mul (hrad.pow 2))).add hSr
  have hden := (hb'.add (hci.mul (hrad.pow 2))).add hSi
  apply (hnum.div hden ?_).contDiffWithinAt
  change spectralImag F x.2.2 + (coefficient F x.2.2).im * x.2.1 ^ 2 + (dividedRemainder F x).im ≠ 0
  rw [dividedRemainder_im F hρ hC hR hx]
  change angularVelocity F x.1 x.2.1 x.2.2 ≠ 0
  have hh := hpos x.1 x.2.1 x.2.2 hx.2.2.1 hx.2.2.2
  linarith

lemma scalarResidual_differentiable (F : ℝ × ℂ → ℂ) (G : ℝ × (ℝ × ℝ) → ℝ)
    {x : ℝ × (ℝ × ℝ)} (hG : ContDiffAt ℝ 2 G x)
    (hA : ContDiffAt ℝ 2 (angularLinear F) x.2.2)
    (hB : ContDiffAt ℝ 2 (angularCubic F) x.2.2) :
    DifferentiableAt ℝ (fun r => scalarResidual F G x.1 r x.2.2) x.2.1 ∧
    DifferentiableAt ℝ (fun μ => scalarResidual F G x.1 x.2.1 μ) x.2.2 := by
  have hGr : ContDiffAt ℝ 2 (fun r => G (x.1, r, x.2.2)) x.2.1 :=
    hG.comp x.2.1 (by fun_prop)
  have hGμ : ContDiffAt ℝ 2 (fun μ => G (x.1, x.2.1, μ)) x.2.2 :=
    hG.comp x.2.2 (by fun_prop)
  have hr : ContDiffAt ℝ 2 (fun r => scalarResidual F G x.1 r x.2.2) x.2.1 :=
    ((contDiffAt_id.mul hGr).sub (contDiffAt_const.mul contDiffAt_id)).sub
      (contDiffAt_const.mul (contDiffAt_id.pow 3))
  have hμ : ContDiffAt ℝ 2 (fun μ => scalarResidual F G x.1 x.2.1 μ) x.2.2 :=
    ((contDiffAt_const.mul hGμ).sub (hA.mul contDiffAt_const)).sub
      (hB.mul contDiffAt_const)
  exact ⟨hr.differentiableAt (by norm_num), hμ.differentiableAt (by norm_num)⟩

theorem smoothPolarReduction : SmoothPolarReduction := by
  intro F ω hF hω heig heq
  obtain ⟨_, hb0, ε, hε, ρ, hρ, C, hC, hcoord, hR, hdata⟩ :=
    CubicNormalForm.normalForm F ω hF hω heig heq
  have hz : |(0 : ℝ)| < ε := by simpa using hε
  obtain ⟨_, _, hb, hc, _⟩ := hdata 0 hz
  obtain ⟨ε', hε', ρ', hρ', heε, hrρ, hpos⟩ :=
    uniformAngularPositivity F ω hω hε hρ hC hb.continuousAt hb0 hc.continuousAt hR
  have hR' := CubicNormalForm.uniformRemainderBounds_mono hR heε hrρ
  have hGa : ∀ μ : ℝ, |μ| < ε' → ContDiffAt ℝ 2 (spectralReal F) μ :=
    fun μ hμ => (hdata μ (hμ.trans_le heε)).2.1.of_le (by norm_num)
  have hGb : ∀ μ : ℝ, |μ| < ε' → ContDiffAt ℝ 2 (spectralImag F) μ :=
    fun μ hμ => (hdata μ (hμ.trans_le heε)).2.2.1.of_le (by norm_num)
  have hGc : ∀ μ : ℝ, |μ| < ε' → ContDiffAt ℝ 2 (coefficient F) μ :=
    fun μ hμ => (hdata μ (hμ.trans_le heε)).2.2.2.1
  have hG := signedFactor_contDiffOn F hω hρ' hC.le hR' hGa hGb hGc hpos
  have hAB : ∀ μ : ℝ, |μ| < ε' →
      ContDiffAt ℝ 2 (angularLinear F) μ ∧ ContDiffAt ℝ 2 (angularCubic F) μ := by
    intro μ hμ
    obtain ⟨hb, ha, hbr, hc, _⟩ := hdata μ (hμ.trans_le heε)
    exact angular_coefficients_regular F μ ha hbr hc hb.ne'
  refine ⟨ε', hε', ρ', hρ', C, hC,
    CubicNormalForm.coordinateValidity_mono hcoord heε hrρ, hR', hG, hAB, hpos, ?_,
    reconstructOnChart F hω hR' hpos⟩
  intro x hx
  have hx0 : (x.1, (0 : ℝ), x.2.2) ∈ polarBox ε' ρ' :=
    ⟨hx.1, hx.2.1, by simpa using hρ', hx.2.2.2⟩
  refine ⟨signedFactor_zero F hC.le hR' hx0,
    signedFactor_angularField F hρ' hC.le hR' hx, ?_⟩
  exact scalarResidual_differentiable F _
    (hG.contDiffAt ((polarBox_isOpen _ _).mem_nhds hx))
    (hAB _ hx.2.2.2).1 (hAB _ hx.2.2.2).2


/-! Uniform scalar estimates from the actual normal-form remainder. -/

lemma quotient_order_bounds (K s H Hr Hμ D Dr Dμ : ℝ)
    (hK : 1 ≤ K) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hH : |H| ≤ K * s ^ 4) (hHr : |Hr| ≤ K * s ^ 3)
    (hHμ : |Hμ| ≤ K * s ^ 4) (hD : |D⁻¹| ≤ K)
    (hDr : |Dr| ≤ K) (hDμ : |Dμ| ≤ K) :
    |H / D| ≤ 2 * K ^ 4 * s ^ 4 ∧
    |Hr / D - H * Dr / D ^ 2| ≤ 2 * K ^ 4 * s ^ 3 ∧
    |Hμ / D - H * Dμ / D ^ 2| ≤ 2 * K ^ 4 * s ^ 4 := by
  have hK0 : 0 ≤ K := by linarith
  have hK2 : K ^ 2 ≤ K ^ 4 := by nlinarith [sq_nonneg (K ^ 2 - 1)]
  have hs43 : s ^ 4 ≤ s ^ 3 := by nlinarith [pow_nonneg hs 3, mul_le_mul_of_nonneg_left hs1 (pow_nonneg hs 3)]
  have hq (x : ℝ) (n : ℕ) (hx : |x| ≤ K * s ^ n) : |x / D| ≤ K ^ 2 * s ^ n := by
    rw [div_eq_mul_inv, abs_mul]
    calc
      _ ≤ (K * s ^ n) * K := mul_le_mul hx hD (abs_nonneg _) (mul_nonneg hK0 (pow_nonneg hs _))
      _ = _ := by ring
  have hp (x : ℝ) (hx : |x| ≤ K) : |H * x / D ^ 2| ≤ K ^ 4 * s ^ 4 := by
    rw [div_eq_mul_inv, ← inv_pow, abs_mul, abs_mul, abs_pow]
    calc
      _ ≤ (K * s ^ 4) * K * K ^ 2 := by gcongr
      _ = _ := by ring
  refine ⟨(hq H 4 hH).trans ?_, ?_, ?_⟩
  · gcongr; nlinarith
  · calc
      _ ≤ |Hr / D| + |H * Dr / D ^ 2| := abs_sub _ _
      _ ≤ K ^ 2 * s ^ 3 + K ^ 4 * s ^ 4 := add_le_add (hq Hr 3 hHr) (hp Dr hDr)
      _ ≤ K ^ 4 * s ^ 3 + K ^ 4 * s ^ 3 := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ |Hμ / D| + |H * Dμ / D ^ 2| := abs_sub _ _
      _ ≤ K ^ 2 * s ^ 4 + K ^ 4 * s ^ 4 := add_le_add (hq Hμ 4 hHμ) (hp Dμ hDμ)
      _ ≤ K ^ 4 * s ^ 4 + K ^ 4 * s ^ 4 := by gcongr
      _ = _ := by ring
lemma residual_numerator_bound (M r A B c e f : ℝ)
    (hM : 1 ≤ M) (hr : |r| ≤ 1) (hA : |A| ≤ M) (hB : |B| ≤ M)
    (hc : |c| ≤ M) (he : |e| ≤ M * |r| ^ 4) (hf : |f| ≤ M * |r| ^ 4) :
    |f - A * e - B * c * r ^ 5 - B * e * r ^ 2| ≤ 4 * M ^ 2 * |r| ^ 4 := by
  have hM0 : 0 ≤ M := by linarith
  have hp54 : |r| ^ 5 ≤ |r| ^ 4 := pow_le_pow_of_le_one (abs_nonneg r) hr (by omega)
  have hp21 : |r| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg r) hr
  calc
    _ ≤ |f| + |A * e| + |B * c * r ^ 5| + |B * e * r ^ 2| := by
      grw [abs_sub, abs_sub, abs_sub]
    _ = |f| + |A| * |e| + |B| * |c| * |r| ^ 5 + |B| * |e| * |r| ^ 2 := by
      simp only [abs_mul, abs_pow]
    _ ≤ M * |r| ^ 4 + M * (M * |r| ^ 4) +
        M * M * |r| ^ 4 + M * (M * |r| ^ 4) * 1 := by gcongr
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hM (pow_nonneg (abs_nonneg r) 4)]

lemma residual_radial_numerator_bound (M r A B c e fr er : ℝ)
    (hM : 1 ≤ M) (hr : |r| ≤ 1) (hA : |A| ≤ M) (hB : |B| ≤ M)
    (hc : |c| ≤ M) (he : |e| ≤ M * |r| ^ 4)
    (hf : |fr| ≤ M * |r| ^ 3) (her : |er| ≤ M * |r| ^ 3) :
    |fr - A * er - 5 * B * c * r ^ 4 - B * er * r ^ 2 - 2 * B * e * r| ≤
      10 * M ^ 2 * |r| ^ 3 := by
  have hM0 : 0 ≤ M := by linarith
  have hp43 : |r| ^ 4 ≤ |r| ^ 3 := pow_le_pow_of_le_one (abs_nonneg r) hr (by omega)
  have hp21 : |r| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg r) hr
  have he3 : |e| ≤ M * |r| ^ 3 := he.trans (mul_le_mul_of_nonneg_left hp43 hM0)
  calc
    _ ≤ |fr| + |A * er| + |5 * B * c * r ^ 4| + |B * er * r ^ 2| + |2 * B * e * r| := by
      grw [abs_sub, abs_sub, abs_sub, abs_sub]
    _ = |fr| + |A| * |er| + 5 * |B| * |c| * |r| ^ 4 +
        |B| * |er| * |r| ^ 2 + 2 * |B| * |e| * |r| := by
      simp only [abs_mul, abs_pow]; norm_num
    _ ≤ M * |r| ^ 3 + M * (M * |r| ^ 3) + 5 * M * M * |r| ^ 3 +
        M * (M * |r| ^ 3) * 1 + 2 * M * (M * |r| ^ 3) * 1 := by gcongr
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hM (pow_nonneg (abs_nonneg r) 3)]

lemma residual_parameter_numerator_bound (M r A B c Ad Bd cd e fm em : ℝ)
    (hM : 1 ≤ M) (hr : |r| ≤ 1) (hA : |A| ≤ M) (hB : |B| ≤ M)
    (hc : |c| ≤ M) (hAd : |Ad| ≤ M) (hBd : |Bd| ≤ M) (hcd : |cd| ≤ M)
    (he : |e| ≤ M * |r| ^ 4)
    (hf : |fm| ≤ M * |r| ^ 4) (hem : |em| ≤ M * |r| ^ 4) :
    |fm - Ad * e - A * em - Bd * c * r ^ 5 - B * cd * r ^ 5 -
        Bd * e * r ^ 2 - B * em * r ^ 2| ≤ 7 * M ^ 2 * |r| ^ 4 := by
  have hM0 : 0 ≤ M := by linarith
  have hp54 : |r| ^ 5 ≤ |r| ^ 4 := pow_le_pow_of_le_one (abs_nonneg r) hr (by omega)
  have hp21 : |r| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg r) hr
  calc
    _ ≤ |fm| + |Ad * e| + |A * em| + |Bd * c * r ^ 5| + |B * cd * r ^ 5| +
        |Bd * e * r ^ 2| + |B * em * r ^ 2| := by
      grw [abs_sub, abs_sub, abs_sub, abs_sub, abs_sub, abs_sub]
    _ = |fm| + |Ad| * |e| + |A| * |em| + |Bd| * |c| * |r| ^ 5 +
        |B| * |cd| * |r| ^ 5 + |Bd| * |e| * |r| ^ 2 + |B| * |em| * |r| ^ 2 := by
      simp only [abs_mul, abs_pow]
    _ ≤ M * |r| ^ 4 + M * (M * |r| ^ 4) + M * (M * |r| ^ 4) +
        M * M * |r| ^ 4 + M * M * |r| ^ 4 +
        M * (M * |r| ^ 4) * 1 + M * (M * |r| ^ 4) * 1 := by gcongr
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hM (pow_nonneg (abs_nonneg r) 4)]

lemma polar_denominator_derivative_bounds (M r c e er bm cm em : ℝ)
    (hM : 0 ≤ M) (hr : |r| ≤ 1) (hr0 : r ≠ 0)
    (hc : |c| ≤ M) (he : |e| ≤ M * |r| ^ 4)
    (her : |er| ≤ M * |r| ^ 3) (hbm : |bm| ≤ M) (hcm : |cm| ≤ M)
    (hem : |em| ≤ M * |r| ^ 4) :
    |2 * c * r + er / r - e / r ^ 2| ≤ 4 * M ∧
    |bm + cm * r ^ 2 + em / r| ≤ 3 * M := by
  have hrp : 0 < |r| := abs_pos.mpr hr0
  have hp2 : |r| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg r) hr
  have hp3 : |r| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg r) hr
  have her' : |er / r| ≤ M := by
    rw [abs_div, div_le_iff₀ hrp]
    calc
      |er| ≤ M * |r| ^ 3 := her
      _ ≤ M * |r| := mul_le_mul_of_nonneg_left
        (pow_le_of_le_one (abs_nonneg r) hr (by omega)) hM
  have he' : |e / r ^ 2| ≤ M := by
    rw [abs_div, abs_pow, div_le_iff₀ (pow_pos hrp 2)]
    exact he.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (abs_nonneg r) hr (by omega : 2 ≤ 4)) hM)
  have hem' : |em / r| ≤ M := by
    rw [abs_div, div_le_iff₀ hrp]
    exact hem.trans (mul_le_mul_of_nonneg_left
      (pow_le_of_le_one (abs_nonneg r) hr (by omega)) hM)
  constructor
  · calc
      _ ≤ |2 * c * r| + |er / r| + |e / r ^ 2| := by
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 2 * M * 1 + M + M := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; gcongr
      _ = _ := by ring
  · calc
      _ ≤ |bm| + |cm * r ^ 2| + |em / r| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ M + M * 1 + M := by
        simp only [abs_mul, abs_pow]; gcongr
      _ = _ := by ring


/-- Finitely many locally C² scalar functions admit common local value and
first-derivative bounds, with a constant that also dominates two given numbers. -/
lemma finiteFamilyC1Bounds {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (hf : ∀ i, ContDiffAt ℝ 2 (f i) 0)
    {ε : ℝ} (hε : 0 < ε) (C D : ℝ) :
    ∃ ε' > 0, ε' ≤ ε ∧ ∃ M : ℝ, 1 ≤ M ∧ C ≤ M ∧ D ≤ M ∧
      ∀ μ, |μ| < ε' → ∀ i, |f i μ| ≤ M ∧ |deriv (f i) μ| ≤ M := by
  classical
  let S := ∑ i, (|f i 0| + |deriv (f i) 0|)
  let M := 1 + |C| + |D| + S
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hM : 1 ≤ M := by dsimp [M]; linarith [abs_nonneg C, abs_nonneg D]
  have hCM : C ≤ M := by
    dsimp [M]
    linarith [le_abs_self C, abs_nonneg D]
  have hDM : D ≤ M := by
    dsimp [M]
    linarith [abs_nonneg C, le_abs_self D]
  have hsum (i : ι) : |f i 0| + |deriv (f i) 0| ≤ S := by
    exact Finset.single_le_sum (f := fun j : ι => |f j 0| + |deriv (f j) 0|)
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      (Finset.mem_univ i)
  have hevent : ∀ᶠ μ in nhds (0 : ℝ), ∀ i, |f i μ| < M ∧ |deriv (f i) μ| < M := by
    apply Filter.eventually_all.mpr
    intro i
    have hfM : |f i 0| < M := by
      dsimp [M]
      linarith [hsum i, abs_nonneg (deriv (f i) 0), abs_nonneg C, abs_nonneg D]
    have hdM : |deriv (f i) 0| < M := by
      dsimp [M]
      linarith [hsum i, abs_nonneg (f i 0), abs_nonneg C, abs_nonneg D]
    have hdc : ContinuousAt (deriv (f i)) 0 :=
      ((hf i).derivWithin (m := 1) (by norm_num)).continuousAt
    exact ((hf i).continuousAt.abs.eventually (gt_mem_nhds hfM)).and
      (hdc.abs.eventually (gt_mem_nhds hdM))
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨min ε δ, lt_min hε hδ, min_le_left _ _, M, hM, hCM, hDM, ?_⟩
  intro μ hμ i
  have hμδ : |μ| < δ := hμ.trans_le (min_le_right _ _)
  have h := hh (by simpa [Real.dist_eq] using hμδ) i
  exact ⟨h.1.le, h.2.le⟩

/-- Increasing the uniform remainder constant preserves every regularity
assertion and all four estimates on the same chart. -/
lemma uniformRemainderBounds_enlarge {F : ℝ × ℂ → ℂ} {ε ρ C D : ℝ}
    (h : UniformRemainderBounds F ε ρ C) (hCD : C ≤ D) :
    UniformRemainderBounds F ε ρ D := by
  intro x hx
  obtain ⟨hR, hS, hT, hdR, hdS, hv, hs, hp, hps⟩ := h x hx
  refine ⟨hR, hS, hT, hdR, hdS, ?_, ?_, ?_, ?_⟩
  · exact hv.trans (mul_le_mul_of_nonneg_right hCD (by positivity))
  · exact hs.trans (mul_le_mul_of_nonneg_right hCD (by positivity))
  · exact hp.trans (mul_le_mul_of_nonneg_right hCD (by positivity))
  · exact hps.trans (mul_le_mul_of_nonneg_right hCD (by positivity))

/-- One chart and one constant for the four scalar polar coefficients and
their parameter derivatives. -/
lemma polarCoefficientBounds (F : ℝ × ℂ → ℂ) {ε : ℝ} (hε : 0 < ε) (C ω : ℝ)
    (hb : ContDiffAt ℝ 2 (spectralImag F) 0)
    (hc : ContDiffAt ℝ 2 (coefficient F) 0)
    (hA : ContDiffAt ℝ 2 (angularLinear F) 0)
    (hB : ContDiffAt ℝ 2 (angularCubic F) 0) :
    ∃ ε' > 0, ε' ≤ ε ∧ ∃ M : ℝ, 1 ≤ M ∧ C ≤ M ∧ 2 / ω ≤ M ∧
      ∀ μ, |μ| < ε' →
        (|spectralImag F μ| ≤ M ∧ |deriv (spectralImag F) μ| ≤ M) ∧
        (|(coefficient F μ).im| ≤ M ∧ |deriv (fun μ => (coefficient F μ).im) μ| ≤ M) ∧
        (|angularLinear F μ| ≤ M ∧ |deriv (angularLinear F) μ| ≤ M) ∧
        (|angularCubic F μ| ≤ M ∧ |deriv (angularCubic F) μ| ≤ M) := by
  let f : Fin 4 → ℝ → ℝ :=
    ![spectralImag F, (fun μ => (coefficient F μ).im), angularLinear F, angularCubic F]
  have hfi : ∀ i, ContDiffAt ℝ 2 (f i) 0 := by
    intro i
    fin_cases i
    · exact hb
    · exact Complex.imCLM.contDiff.contDiffAt.comp 0 hc
    · exact hA
    · exact hB
  obtain ⟨ε', hε', hεε, M, hM, hCM, hωM, hfM⟩ :=
    finiteFamilyC1Bounds f hfi hε C (2 / ω)
  refine ⟨ε', hε', hεε, M, hM, hCM, hωM, ?_⟩
  intro μ hμ
  exact ⟨hfM μ hμ 0, hfM μ hμ 1, hfM μ hμ 2, hfM μ hμ 3⟩


lemma polarRemainder_hasDerivAt_radius (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hR : UniformRemainderBounds F ε ρ C) (θ r μ : ℝ)
    (hr : |r| < ρ) (hμ : |μ| < ε) :
    HasDerivAt (fun s => polarRemainder F θ s μ)
      (conj (direction θ) * spatialDerivative (remainder F) (μ, polarPoint r θ) (direction θ)) r := by
  have hbox : (μ, polarPoint r θ) ∈ stateParameterBox ε ρ :=
    ⟨hμ, by simpa [polarPoint_norm] using hr⟩
  have hdR : DifferentiableAt ℝ (fun w => remainder F (μ, w)) (polarPoint r θ) :=
    (hR _ hbox).1.differentiableAt (by norm_num) |>.comp _
      ((differentiableAt_const μ).prodMk differentiableAt_id)
  have hdp : HasDerivAt (fun s => polarPoint s θ) (direction θ) r := by
    simpa [polarPoint] using (hasDerivAt_id r).ofReal_comp.mul_const (direction θ)
  have hh := hdR.hasFDerivAt.comp_hasDerivAt r hdp
  simpa only [Function.comp_def, spatialDerivative, polarRemainder] using!
    hh.const_mul (conj (direction θ))

lemma polarRemainder_deriv_radius_bound (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hR : UniformRemainderBounds F ε ρ C) (θ r μ : ℝ)
    (hr : |r| < ρ) (hμ : |μ| < ε) :
    ‖deriv (fun s => polarRemainder F θ s μ) r‖ ≤ C * |r| ^ 3 := by
  rw [(polarRemainder_hasDerivAt_radius F hR θ r μ hr hμ).deriv]
  simp only [norm_mul, Complex.norm_conj, direction_norm, one_mul]
  calc
    ‖spatialDerivative (remainder F) _ (direction θ)‖ ≤ ‖spatialDerivative (remainder F) _‖ := by
      simpa [direction_norm] using (spatialDerivative (remainder F) _).le_opNorm (direction θ)
    _ ≤ C * |r| ^ 3 := by
      simpa [polarPoint_norm] using
        (hR (μ, polarPoint r θ) ⟨hμ, by simpa [polarPoint_norm] using hr⟩).2.2.2.2.2.2.1

lemma polarRemainder_hasDerivAt_parameter (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hR : UniformRemainderBounds F ε ρ C) (θ r μ : ℝ)
    (hr : |r| < ρ) (hμ : |μ| < ε) :
    HasDerivAt (fun s => polarRemainder F θ r s)
      (conj (direction θ) * deriv (fun s => remainder F (s, polarPoint r θ)) μ) μ := by
  have hd := (hR (μ, polarPoint r θ) ⟨hμ, by simpa [polarPoint_norm] using hr⟩).2.2.2.1
  exact hd.hasDerivAt.const_mul _

lemma polarRemainder_deriv_parameter_bound (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hR : UniformRemainderBounds F ε ρ C) (θ r μ : ℝ)
    (hr : |r| < ρ) (hμ : |μ| < ε) :
    ‖deriv (fun s => polarRemainder F θ r s) μ‖ ≤ C * |r| ^ 4 := by
  rw [(polarRemainder_hasDerivAt_parameter F hR θ r μ hr hμ).deriv]
  simp only [norm_mul, Complex.norm_conj, direction_norm, one_mul]
  simpa [polarPoint_norm] using
    (hR (μ, polarPoint r θ) ⟨hμ, by simpa [polarPoint_norm] using hr⟩).2.2.2.2.2.2.2.1

lemma hasDerivAt_re {f : ℝ → ℂ} {v : ℂ} {x : ℝ} (hf : HasDerivAt f v x) :
    HasDerivAt (fun y => (f y).re) v.re x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hf

lemma hasDerivAt_im {f : ℝ → ℂ} {v : ℂ} {x : ℝ} (hf : HasDerivAt f v x) :
    HasDerivAt (fun y => (f y).im) v.im x := by
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf

lemma polarRemainder_radius_scalar_data (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hR : UniformRemainderBounds F ε ρ C) (θ r μ : ℝ)
    (hr : |r| < ρ) (hμ : |μ| < ε) :
    ∃ df de : ℝ,
      HasDerivAt (fun s => (polarRemainder F θ s μ).re) df r ∧
      HasDerivAt (fun s => (polarRemainder F θ s μ).im) de r ∧
      |df| ≤ C * |r| ^ 3 ∧ |de| ≤ C * |r| ^ 3 := by
  let v := deriv (fun s => polarRemainder F θ s μ) r
  have hv : HasDerivAt (fun s => polarRemainder F θ s μ) v r :=
    (polarRemainder_hasDerivAt_radius F hR θ r μ hr hμ).differentiableAt.hasDerivAt
  have hbound : ‖v‖ ≤ C * |r| ^ 3 := polarRemainder_deriv_radius_bound F hR θ r μ hr hμ
  exact ⟨v.re, v.im, hasDerivAt_re hv, hasDerivAt_im hv,
    (abs_re_le_norm v).trans hbound, (abs_im_le_norm v).trans hbound⟩

lemma polarRemainder_parameter_scalar_data (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hR : UniformRemainderBounds F ε ρ C) (θ r μ : ℝ)
    (hr : |r| < ρ) (hμ : |μ| < ε) :
    ∃ df de : ℝ,
      HasDerivAt (fun s => (polarRemainder F θ r s).re) df μ ∧
      HasDerivAt (fun s => (polarRemainder F θ r s).im) de μ ∧
      |df| ≤ C * |r| ^ 4 ∧ |de| ≤ C * |r| ^ 4 := by
  let v := deriv (fun s => polarRemainder F θ r s) μ
  have hv : HasDerivAt (fun s => polarRemainder F θ r s) v μ :=
    (polarRemainder_hasDerivAt_parameter F hR θ r μ hr hμ).differentiableAt.hasDerivAt
  have hbound : ‖v‖ ≤ C * |r| ^ 4 := polarRemainder_deriv_parameter_bound F hR θ r μ hr hμ
  exact ⟨v.re, v.im, hasDerivAt_re hv, hasDerivAt_im hv,
    (abs_re_le_norm v).trans hbound, (abs_im_le_norm v).trans hbound⟩

lemma scalarResidual_zero (F : ℝ × ℂ → ℂ) (G : ℝ × (ℝ × ℝ) → ℝ) (θ μ : ℝ) :
    scalarResidual F G θ 0 μ = 0 := by simp [scalarResidual]

lemma scalarResidual_parameter_deriv_zero (F : ℝ × ℂ → ℂ)
    (G : ℝ × (ℝ × ℝ) → ℝ) (θ μ : ℝ) :
    deriv (fun s => scalarResidual F G θ 0 s) μ = 0 := by
  simp only [scalarResidual, zero_mul, zero_pow (by decide : 3 ≠ 0), mul_zero, sub_self]
  exact deriv_const μ 0

lemma scalarResidual_radius_hasDerivAt_zero (F : ℝ × ℂ → ℂ)
    (G : ℝ × (ℝ × ℝ) → ℝ) (θ μ : ℝ)
    (hG : DifferentiableAt ℝ (fun r => G (θ, r, μ)) 0)
    (hzero : G (θ, 0, μ) = angularLinear F μ) :
    HasDerivAt (fun r => scalarResidual F G θ r μ) 0 0 := by
  have hh := (((hasDerivAt_id (0 : ℝ)).mul hG.hasDerivAt).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul (angularLinear F μ))).sub
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul (angularCubic F μ))
  simpa [scalarResidual, hzero, Pi.mul_apply, Pi.sub_apply] using! hh

noncomputable def residualNumerator (F : ℝ × ℂ → ℂ) (θ r μ : ℝ) : ℝ :=
  (polarRemainder F θ r μ).re - angularLinear F μ * (polarRemainder F θ r μ).im -
    angularCubic F μ * (coefficient F μ).im * r ^ 5 -
    angularCubic F μ * (polarRemainder F θ r μ).im * r ^ 2

lemma scalarResidual_eq_quotient (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hR : UniformRemainderBounds F ε ρ C)
    {x : ℝ × (ℝ × ℝ)} (hx : x ∈ polarBox ε ρ)
    (hb : spectralImag F x.2.2 ≠ 0) (hr : x.2.1 ≠ 0)
    (hD : angularVelocity F x.1 x.2.1 x.2.2 ≠ 0) :
    scalarResidual F (signedFactor F) x.1 x.2.1 x.2.2 =
      residualNumerator F x.1 x.2.1 x.2.2 / angularVelocity F x.1 x.2.1 x.2.2 := by
  unfold scalarResidual
  rw [← signedFactor_angularField F hρ hC hR hx]
  exact angular_quotient_identity _ _ _ _ _ _ _ hb hr hD

lemma hasDerivAt_quotient_sub {N D : ℝ → ℝ} {n d x : ℝ}
    (hN : HasDerivAt N n x) (hD : HasDerivAt D d x) (hD0 : D x ≠ 0) :
    HasDerivAt (fun s => N s / D s) (n / D x - N x * d / D x ^ 2) x := by
  convert hN.div hD hD0 using 1
  field_simp

lemma residualNumerator_hasDerivAt_radius (F : ℝ × ℂ → ℂ) (θ r μ df de : ℝ)
    (hf : HasDerivAt (fun s => (polarRemainder F θ s μ).re) df r)
    (he : HasDerivAt (fun s => (polarRemainder F θ s μ).im) de r) :
    HasDerivAt (fun s => residualNumerator F θ s μ)
      (df - angularLinear F μ * de - 5 * angularCubic F μ * (coefficient F μ).im * r ^ 4 -
        angularCubic F μ * (de * r ^ 2 + 2 * (polarRemainder F θ r μ).im * r)) r := by
  have hh := ((hf.sub (he.const_mul (angularLinear F μ))).sub
    (((hasDerivAt_id r).pow 5).const_mul (angularCubic F μ * (coefficient F μ).im))).sub
      ((he.mul ((hasDerivAt_id r).pow 2)).const_mul (angularCubic F μ))
  convert! hh using 1
  · funext s; simp [residualNumerator]; ring
  · simp; ring

lemma angularVelocity_hasDerivAt_radius (F : ℝ × ℂ → ℂ) (θ r μ de : ℝ)
    (hr : r ≠ 0) (he : HasDerivAt (fun s => (polarRemainder F θ s μ).im) de r) :
    HasDerivAt (fun s => angularVelocity F θ s μ)
      (2 * (coefficient F μ).im * r + de / r - (polarRemainder F θ r μ).im / r ^ 2) r := by
  have hh := ((((hasDerivAt_id r).pow 2).const_mul (coefficient F μ).im).const_add
    (spectralImag F μ)).add (he.div (hasDerivAt_id r) hr)
  convert! hh using 1
  simp
  field_simp [hr]
  ring

lemma residualNumerator_hasDerivAt_parameter (F : ℝ × ℂ → ℂ) (θ r μ df de dA dB dci : ℝ)
    (hf : HasDerivAt (fun s => (polarRemainder F θ r s).re) df μ)
    (he : HasDerivAt (fun s => (polarRemainder F θ r s).im) de μ)
    (hA : HasDerivAt (angularLinear F) dA μ) (hB : HasDerivAt (angularCubic F) dB μ)
    (hci : HasDerivAt (fun s => (coefficient F s).im) dci μ) :
    HasDerivAt (fun s => residualNumerator F θ r s)
      (df - dA * (polarRemainder F θ r μ).im - angularLinear F μ * de -
        dB * (coefficient F μ).im * r ^ 5 - angularCubic F μ * dci * r ^ 5 -
        dB * (polarRemainder F θ r μ).im * r ^ 2 - angularCubic F μ * de * r ^ 2) μ := by
  have hh := ((hf.sub (hA.mul he)).sub ((hB.mul hci).mul_const (r ^ 5))).sub
    ((hB.mul he).mul_const (r ^ 2))
  convert! hh using 1
  ring

lemma angularVelocity_hasDerivAt_parameter (F : ℝ × ℂ → ℂ) (θ r μ de db dci : ℝ)
    (he : HasDerivAt (fun s => (polarRemainder F θ r s).im) de μ)
    (hb : HasDerivAt (spectralImag F) db μ)
    (hci : HasDerivAt (fun s => (coefficient F s).im) dci μ) :
    HasDerivAt (fun s => angularVelocity F θ r s) (db + dci * r ^ 2 + de / r) μ := by
  exact (hb.add (hci.mul_const (r ^ 2))).add (he.div_const r)

lemma scalarResidual_radius_hasDerivAt (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hR : UniformRemainderBounds F ε ρ C)
    {θ r μ df de : ℝ} (hx : (θ, r, μ) ∈ polarBox ε ρ)
    (hb : spectralImag F μ ≠ 0) (hr : r ≠ 0)
    (hD : angularVelocity F θ r μ ≠ 0)
    (hf : HasDerivAt (fun s => (polarRemainder F θ s μ).re) df r)
    (he : HasDerivAt (fun s => (polarRemainder F θ s μ).im) de r) :
    HasDerivAt (fun s => scalarResidual F (signedFactor F) θ s μ)
      ((df - angularLinear F μ * de - 5 * angularCubic F μ * (coefficient F μ).im * r ^ 4 -
        angularCubic F μ * (de * r ^ 2 + 2 * (polarRemainder F θ r μ).im * r)) /
          angularVelocity F θ r μ -
        residualNumerator F θ r μ *
          (2 * (coefficient F μ).im * r + de / r - (polarRemainder F θ r μ).im / r ^ 2) /
          angularVelocity F θ r μ ^ 2) r := by
  have hND := hasDerivAt_quotient_sub
    (residualNumerator_hasDerivAt_radius F θ r μ df de hf he)
    (angularVelocity_hasDerivAt_radius F θ r μ de hr he) hD
  apply hND.congr_of_eventuallyEq
  have hboxE : ∀ᶠ s in nhds r, (θ, s, μ) ∈ polarBox ε ρ :=
    (show ContinuousAt (fun s : ℝ => (θ, s, μ)) r by fun_prop).eventually
      ((polarBox_isOpen _ _).mem_nhds hx)
  have hDE := (angularVelocity_hasDerivAt_radius F θ r μ de hr he).continuousAt.eventually_ne hD
  filter_upwards [hboxE, eventually_ne_nhds hr, hDE] with s hs hsz hsD
  exact scalarResidual_eq_quotient F hρ hC hR hs hb hsz hsD

lemma scalarResidual_parameter_hasDerivAt (F : ℝ × ℂ → ℂ) {ε ρ C : ℝ}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hR : UniformRemainderBounds F ε ρ C)
    {θ r μ df de dA dB db dci : ℝ} (hx : (θ, r, μ) ∈ polarBox ε ρ)
    (hb0 : spectralImag F μ ≠ 0) (hr : r ≠ 0)
    (hD : angularVelocity F θ r μ ≠ 0)
    (hf : HasDerivAt (fun s => (polarRemainder F θ r s).re) df μ)
    (he : HasDerivAt (fun s => (polarRemainder F θ r s).im) de μ)
    (hA : HasDerivAt (angularLinear F) dA μ) (hB : HasDerivAt (angularCubic F) dB μ)
    (hb : HasDerivAt (spectralImag F) db μ)
    (hci : HasDerivAt (fun s => (coefficient F s).im) dci μ) :
    HasDerivAt (fun s => scalarResidual F (signedFactor F) θ r s)
      ((df - dA * (polarRemainder F θ r μ).im - angularLinear F μ * de -
        dB * (coefficient F μ).im * r ^ 5 - angularCubic F μ * dci * r ^ 5 -
        dB * (polarRemainder F θ r μ).im * r ^ 2 - angularCubic F μ * de * r ^ 2) /
          angularVelocity F θ r μ -
        residualNumerator F θ r μ * (db + dci * r ^ 2 + de / r) /
          angularVelocity F θ r μ ^ 2) μ := by
  have hND := hasDerivAt_quotient_sub
    (residualNumerator_hasDerivAt_parameter F θ r μ df de dA dB dci hf he hA hB hci)
    (angularVelocity_hasDerivAt_parameter F θ r μ de db dci he hb hci) hD
  apply hND.congr_of_eventuallyEq
  have hboxE : ∀ᶠ s in nhds μ, (θ, r, s) ∈ polarBox ε ρ :=
    (show ContinuousAt (fun s : ℝ => (θ, r, s)) μ by fun_prop).eventually
      ((polarBox_isOpen _ _).mem_nhds hx)
  have hDE := (angularVelocity_hasDerivAt_parameter F θ r μ de db dci he hb hci).continuousAt.eventually_ne hD
  have hbE := hb.continuousAt.eventually_ne hb0
  filter_upwards [hboxE, hbE, hDE] with s hs hsb hsD
  exact scalarResidual_eq_quotient F hρ hC hR hs hsb hr hsD

set_option maxHeartbeats 1200000 in
lemma scalarResidual_pointwise_bounds (F : ℝ × ℂ → ℂ) {ω ε ρ C M : ℝ}
    (hω : 0 < ω) (hρ : 0 < ρ) (hC : 0 ≤ C) (hR : UniformRemainderBounds F ε ρ C)
    (hM : 1 ≤ M) (hCM : C ≤ M) (hωM : 2 / ω ≤ M)
    {θ r μ : ℝ} (hx : (θ, r, μ) ∈ polarBox ε ρ) (hr1 : |r| ≤ 1)
    (hb0 : spectralImag F μ ≠ 0) (hDpos : ω / 2 < angularVelocity F θ r μ)
    (hGr : DifferentiableAt ℝ (fun s => signedFactor F (θ, s, μ)) r)
    (hA : DifferentiableAt ℝ (angularLinear F) μ)
    (hB : DifferentiableAt ℝ (angularCubic F) μ)
    (hb : DifferentiableAt ℝ (spectralImag F) μ)
    (hci : DifferentiableAt ℝ (fun s => (coefficient F s).im) μ)
    (hAM : |angularLinear F μ| ≤ M) (hBM : |angularCubic F μ| ≤ M)
    (hciM : |(coefficient F μ).im| ≤ M)
    (hAdM : |deriv (angularLinear F) μ| ≤ M) (hBdM : |deriv (angularCubic F) μ| ≤ M)
    (hbdM : |deriv (spectralImag F) μ| ≤ M)
    (hcidM : |deriv (fun s => (coefficient F s).im) μ| ≤ M) :
    |scalarResidual F (signedFactor F) θ r μ| ≤ 2 * (10 * M ^ 2) ^ 4 * |r| ^ 4 ∧
    |deriv (fun s => scalarResidual F (signedFactor F) θ s μ) r| ≤
      2 * (10 * M ^ 2) ^ 4 * |r| ^ 3 ∧
    |deriv (fun s => scalarResidual F (signedFactor F) θ r s) μ| ≤
      2 * (10 * M ^ 2) ^ 4 * |r| ^ 4 := by
  by_cases hr0 : r = 0
  · subst r
    have hd := scalarResidual_radius_hasDerivAt_zero F (signedFactor F) θ μ hGr
      (signedFactor_zero F hC hR hx)
    simp [scalarResidual_zero, hd.deriv, scalarResidual_parameter_deriv_zero]
  have hM0 : 0 ≤ M := by linarith
  have hMM : M ≤ M ^ 2 := by nlinarith
  let K := 10 * M ^ 2
  have hK : 1 ≤ K := by dsimp [K]; nlinarith
  have hMK : M ≤ K := by dsimp [K]; nlinarith [sq_nonneg M]
  have h4MK : 4 * M ≤ K := by dsimp [K]; nlinarith [sq_nonneg M]
  have h3MK : 3 * M ≤ K := by dsimp [K]; nlinarith [sq_nonneg M]
  have hr : |r| < ρ := hx.2.2.1
  have hμ : |μ| < ε := hx.2.2.2
  let e := (polarRemainder F θ r μ).im
  let f := (polarRemainder F θ r μ).re
  have heM : |e| ≤ M * |r| ^ 4 :=
    ((abs_im_le_norm _).trans (polarRemainder_bound F hR θ r μ hr hμ)).trans
      (mul_le_mul_of_nonneg_right hCM (pow_nonneg (abs_nonneg r) 4))
  have hfM : |f| ≤ M * |r| ^ 4 :=
    ((abs_re_le_norm _).trans (polarRemainder_bound F hR θ r μ hr hμ)).trans
      (mul_le_mul_of_nonneg_right hCM (pow_nonneg (abs_nonneg r) 4))
  obtain ⟨fr, er, hfr, her, hfrC, herC⟩ := polarRemainder_radius_scalar_data F hR θ r μ hr hμ
  obtain ⟨fm, em, hfm, hem, hfmC, hemC⟩ := polarRemainder_parameter_scalar_data F hR θ r μ hr hμ
  have hfrM := hfrC.trans (mul_le_mul_of_nonneg_right hCM (pow_nonneg (abs_nonneg r) 3))
  have herM := herC.trans (mul_le_mul_of_nonneg_right hCM (pow_nonneg (abs_nonneg r) 3))
  have hfmM := hfmC.trans (mul_le_mul_of_nonneg_right hCM (pow_nonneg (abs_nonneg r) 4))
  have hemM := hemC.trans (mul_le_mul_of_nonneg_right hCM (pow_nonneg (abs_nonneg r) 4))
  let N := residualNumerator F θ r μ
  let Nr := fr - angularLinear F μ * er - 5 * angularCubic F μ * (coefficient F μ).im * r ^ 4 -
    angularCubic F μ * (er * r ^ 2 + 2 * e * r)
  let Nm := fm - deriv (angularLinear F) μ * e - angularLinear F μ * em -
    deriv (angularCubic F) μ * (coefficient F μ).im * r ^ 5 -
    angularCubic F μ * deriv (fun s => (coefficient F s).im) μ * r ^ 5 -
    deriv (angularCubic F) μ * e * r ^ 2 - angularCubic F μ * em * r ^ 2
  let D := angularVelocity F θ r μ
  let Dr := 2 * (coefficient F μ).im * r + er / r - e / r ^ 2
  let Dm := deriv (spectralImag F) μ + deriv (fun s => (coefficient F s).im) μ * r ^ 2 + em / r
  have hN : |N| ≤ K * |r| ^ 4 := by
    have hh := residual_numerator_bound M r _ _ _ e f hM hr1 hAM hBM hciM heM hfM
    change |N| ≤ 4 * M ^ 2 * |r| ^ 4 at hh
    exact hh.trans (by dsimp [K]; gcongr; norm_num)
  have hNr : |Nr| ≤ K * |r| ^ 3 := by
    have hh := residual_radial_numerator_bound M r _ _ _ e fr er hM hr1 hAM hBM hciM heM hfrM herM
    convert hh using 1 <;> dsimp [Nr, K] <;> congr 1 <;> ring
  have hNm : |Nm| ≤ K * |r| ^ 4 := by
    have hh := residual_parameter_numerator_bound M r _ _ _ _ _ _ e fm em hM hr1 hAM hBM hciM
      hAdM hBdM hcidM heM hfmM hemM
    change |Nm| ≤ 7 * M ^ 2 * |r| ^ 4 at hh
    exact hh.trans (by dsimp [K]; gcongr; norm_num)
  have hD0 : 0 < D := (half_pos hω).trans hDpos
  have hDinv : |D⁻¹| ≤ K := by
    rw [abs_of_pos (inv_pos.mpr hD0)]
    calc
      D⁻¹ ≤ (ω / 2)⁻¹ := (inv_le_inv₀ hD0 (half_pos hω)).mpr hDpos.le
      _ = 2 / ω := by field_simp
      _ ≤ M := hωM
      _ ≤ K := hMK
  have hDen := polar_denominator_derivative_bounds M r _ e er _ _ em hM0 hr1 hr0 hciM heM herM
    hbdM hcidM hemM
  have hDr : |Dr| ≤ K := hDen.1.trans h4MK
  have hDm : |Dm| ≤ K := hDen.2.trans h3MK
  have hh := quotient_order_bounds K |r| N Nr Nm D Dr Dm hK (abs_nonneg r) hr1 hN hNr hNm
    hDinv hDr hDm
  have hval := scalarResidual_eq_quotient F hρ hC hR hx hb0 hr0 hD0.ne'
  have hrad := scalarResidual_radius_hasDerivAt F hρ hC hR hx hb0 hr0 hD0.ne' hfr her
  have hpar := scalarResidual_parameter_hasDerivAt F hρ hC hR hx hb0 hr0 hD0.ne' hfm hem
    hA.hasDerivAt hB.hasDerivAt hb.hasDerivAt hci.hasDerivAt
  rw [hval, hrad.deriv, hpar.deriv]
  exact hh


set_option maxHeartbeats 1000000 in
theorem polarReduction : PolarReduction := by
  intro F ω hF hω heig heq
  obtain ⟨ε, hε, ρ, hρ, C, hC, hcoord, hR, hG, hAB, hpos, hfactor, _⟩ :=
    smoothPolarReduction F ω hF hω heig heq
  obtain ⟨_, _, εn, hεn, _, _, _, _, _, _, hdata⟩ :=
    CubicNormalForm.normalForm F ω hF hω heig heq
  have hz : |(0 : ℝ)| < ε := by simpa using hε
  have hzn : |(0 : ℝ)| < εn := by simpa using hεn
  obtain ⟨_, _, hb, hc, _⟩ := hdata 0 hzn
  obtain ⟨ε', hε', heε, M, hM, hCM, hωM, hcoef⟩ :=
    polarCoefficientBounds F (lt_min hε hεn) C ω (hb.of_le (by norm_num)) hc
      (hAB 0 hz).1 (hAB 0 hz).2
  have heS : ε' ≤ ε := heε.trans (min_le_left _ _)
  have heN : ε' ≤ εn := heε.trans (min_le_right _ _)
  let ρ' := min ρ 1
  have hρ' : 0 < ρ' := lt_min hρ zero_lt_one
  have hrρ : ρ' ≤ ρ := min_le_left _ _
  have hr1 : ρ' ≤ 1 := min_le_right _ _
  let C' := C + 2 * (10 * M ^ 2) ^ 4 + 1
  have hC' : 0 < C' := by dsimp [C']; positivity
  have hCC' : C ≤ C' := by dsimp [C']; nlinarith [pow_nonneg (sq_nonneg M) 4]
  have hEC' : 2 * (10 * M ^ 2) ^ 4 ≤ C' := by dsimp [C']; linarith
  have hcoord' := CubicNormalForm.coordinateValidity_mono hcoord heS hrρ
  have hR' := CubicNormalForm.uniformRemainderBounds_mono hR heS hrρ
  have hsub : polarBox ε' ρ' ⊆ polarBox ε ρ := by
    intro x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.1.trans_le hrρ, hx.2.2.2.trans_le heS⟩
  have hG' := hG.mono hsub
  have hAB' : ∀ μ : ℝ, |μ| < ε' →
      ContDiffAt ℝ 2 (angularLinear F) μ ∧ ContDiffAt ℝ 2 (angularCubic F) μ :=
    fun μ hμ => hAB μ (hμ.trans_le heS)
  have hpos' : ∀ θ r μ : ℝ, |r| < ρ' → |μ| < ε' →
      ω / 2 < angularVelocity F θ r μ :=
    fun θ r μ hr hμ => hpos θ r μ (hr.trans_le hrρ) (hμ.trans_le heS)
  refine ⟨ε', hε', ρ', hρ', C', hC', signedFactor F, ?_,
    reconstructOnChart F hω hR' hpos'⟩
  refine ⟨hcoord', uniformRemainderBounds_enlarge hR' hCC', hG', hAB', hpos', ?_⟩
  intro x hx
  obtain ⟨hzero, heqG, hdr, hdμ⟩ := hfactor x (hsub hx)
  have hμ : |x.2.2| < ε' := hx.2.2.2
  have hregular := hdata x.2.2 (hμ.trans_le heN)
  have hGb : DifferentiableAt ℝ (spectralImag F) x.2.2 :=
    hregular.2.2.1.differentiableAt (by norm_num)
  have hGci : DifferentiableAt ℝ (fun μ => (coefficient F μ).im) x.2.2 :=
    (Complex.imCLM.contDiff.contDiffAt.comp x.2.2 hregular.2.2.2.1).differentiableAt (by norm_num)
  have hGx : ContDiffAt ℝ 2 (signedFactor F) x := hG'.contDiffAt ((polarBox_isOpen _ _).mem_nhds hx)
  have hinner : ContDiffAt ℝ 2 (fun r : ℝ => (x.1, r, x.2.2)) x.2.1 := by fun_prop
  have hGrCD : ContDiffAt ℝ 2 (fun r : ℝ => signedFactor F (x.1, r, x.2.2)) x.2.1 := by
    exact ContDiffAt.comp (𝕜 := ℝ) (g := signedFactor F)
      (f := fun r : ℝ => (x.1, r, x.2.2)) x.2.1 hGx hinner
  have hGr : DifferentiableAt ℝ (fun r => signedFactor F (x.1, r, x.2.2)) x.2.1 :=
    hGrCD.differentiableAt (by norm_num)
  obtain ⟨hbM, hciM, hAM, hBM⟩ := hcoef x.2.2 hμ
  have hres := scalarResidual_pointwise_bounds F hω hρ' hC.le hR' hM hCM hωM
    (θ := x.1) (r := x.2.1) (μ := x.2.2) hx (hx.2.2.1.le.trans hr1)
    hregular.1.ne' (hpos' _ _ _ hx.2.2.1 hμ) hGr
    ((hAB' _ hμ).1.differentiableAt (by norm_num)) ((hAB' _ hμ).2.differentiableAt (by norm_num)) hGb hGci
    hAM.1 hBM.1 hciM.1 hAM.2 hBM.2 hbM.2 hciM.2
  refine ⟨hzero, heqG, hpos' _ _ _ hx.2.2.1 hμ, hdr, hdμ, ?_, ?_, ?_⟩
  · exact hres.1.trans (mul_le_mul_of_nonneg_right hEC' (by positivity))
  · exact hres.2.1.trans (mul_le_mul_of_nonneg_right hEC' (by positivity))
  · exact hres.2.2.trans (mul_le_mul_of_nonneg_right hEC' (by positivity))


end D13Unified.Ch16.HopfPolarReduction
