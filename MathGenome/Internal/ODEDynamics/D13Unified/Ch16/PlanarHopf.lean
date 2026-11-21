import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.PlanarHopf
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.HopfReturnExpansion
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.HopfPeriodicBranch
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.HopfPeriodicOrbitBridge
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Orbits
import MathGenome.Internal.ODEDynamics.D13Unified.Ch12.LinearizedStability
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.OrbitalInstability
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace D13Unified.Ch16.PlanarHopf
open Set Filter
open Specs.D13Unified.Ch16
open CubicHomologicalElimination CubicNormalForm HopfReturnExpansion HopfPeriodicBranch
open Specs.D13Unified.Ch16.PlanarHopf

/-- Smoothness of the actual coefficient, with no division by the vanishing
real eigenvalue part. The upstream exponential-integral lemma handles A=0. -/
lemma cubicReturnCoefficient_continuousAt_zero
    (F : ℝ × ℂ → ℂ) (ω : ℝ) (h : SourceHypotheses F ω) :
    ContinuousAt (cubicReturnCoefficient F) 0 := by
  obtain ⟨ε, hε, ρ, _, C, _, _, _, hreg⟩ :=
    CubicNormalForm.normalForm F ω h.1 h.2.1 h.2.2.1 h.2.2.2.1 |>.2.2
  obtain ⟨hb, ha, hbi, hc, _⟩ := hreg 0 (by simpa using hε)
  have hA : ContDiffAt ℝ 2 (angularLinear F) 0 :=
    (ha.of_le (by norm_num)).div (hbi.of_le (by norm_num)) (ne_of_gt hb)
  have hB : ContDiffAt ℝ 2 (angularCubic F) 0 := by
    unfold angularCubic
    exact ((Complex.reCLM.contDiff.comp_contDiffAt 0 hc).div
      (hbi.of_le (by norm_num)) (ne_of_gt hb)).sub
      (((ha.of_le (by norm_num)).mul (Complex.imCLM.contDiff.comp_contDiffAt 0 hc)).div
        ((hbi.of_le (by norm_num)).pow 2) (pow_ne_zero _ (ne_of_gt hb)))
  have hi : ContinuousAt (fun μ : ℝ => ∫ s in (0 : ℝ)..2 * Real.pi,
      Real.exp (2 * angularLinear F μ * s)) 0 :=
    (HopfAngularScalarEstimates.exponentialIntegral_c2 (2 * Real.pi)).continuous.continuousAt.comp
      (continuousAt_const.mul hA.continuousAt)
  exact (hB.continuousAt.mul
    (((continuousAt_const : ContinuousAt (fun _ : ℝ => 2 * Real.pi) 0).mul
      hA.continuousAt).rexp)).mul hi

/-- At a fixed radius the linear term can be eliminated exactly. This
identity is the step connecting the controlled return error to the transverse
multiplier; all derivatives here are derivatives of the actual map. -/
lemma multiplier_identity (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hd : ReturnData F ω ε ρ δ C P Q) (μ r : ℝ)
    (hμ : |μ| < ε) (hr : 0 < r) (hrδ : r < δ) (hfix : P (r, μ) = r) :
    deriv (fun s => P (s, μ)) r - 1 - 2 * cubicReturnCoefficient F μ * r ^ 2 =
      deriv (fun s => returnError F P (s, μ)) r - returnError F P (r, μ) / r := by
  have hopen : IsOpen (returnBox δ ε) := by
    apply IsOpen.and
    · exact isOpen_lt (continuous_fst.abs) continuous_const
    · exact isOpen_lt (continuous_snd.abs) continuous_const
  have hq : (r, μ) ∈ returnBox δ ε := ⟨by rwa [abs_of_pos hr], hμ⟩
  have hp : DifferentiableAt ℝ (fun s => P (s, μ)) r :=
    ((hd.smooth_map.contDiffAt (hopen.mem_nhds hq)).differentiableAt (by norm_num)).comp r
      ((differentiableAt_id).prodMk (differentiableAt_const μ))
  have herr : deriv (fun s => returnError F P (s, μ)) r =
      deriv (fun s => P (s, μ)) r - linearReturnFactor F μ -
        cubicReturnCoefficient F μ * (3 * r ^ 2) := by
    unfold returnError
    simpa only [Pi.sub_def, Pi.pow_def, id_eq, mul_one, Nat.cast_ofNat, Nat.reduceSub] using ((hp.hasDerivAt.sub ((hasDerivAt_id r).const_mul (linearReturnFactor F μ))).sub
      (((hasDerivAt_id r).pow 3).const_mul (cubicReturnCoefficient F μ))).deriv
  have hval : returnError F P (r, μ) =
      r - linearReturnFactor F μ * r - cubicReturnCoefficient F μ * r ^ 3 := by
    simp only [returnError, hfix]
  rw [herr, hval]
  field_simp [ne_of_gt hr]
  <;> ring

/-- The multiplier error is cubic, uniformly at fixed points of any map
satisfying the genuine upstream return estimates. -/
lemma multiplier_error_bound (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hd : ReturnData F ω ε ρ δ C P Q) (μ r : ℝ)
    (hμ : |μ| < ε) (hr : 0 < r) (hrδ : r < δ) (hfix : P (r, μ) = r) :
    |deriv (fun s => P (s, μ)) r - 1 - 2 * cubicReturnCoefficient F μ * r ^ 2|
      ≤ 2 * C * r ^ 3 := by
  rw [multiplier_identity F ω ε ρ δ C P Q hε hδ hd μ r hμ hr hrδ hfix]
  have hq : (r, μ) ∈ returnBox δ ε := ⟨by rwa [abs_of_pos hr], hμ⟩
  obtain ⟨_, hv, hdr, _⟩ := hd.estimates _ hq
  rw [abs_of_pos hr] at hv hdr
  have hv' : |returnError F P (r, μ) / r| ≤ C * r ^ 3 := by
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
    calc
      _ ≤ C * r ^ 4 := hv
      _ = C * r ^ 3 * r := by ring
  exact (abs_sub _ _).trans ((add_le_add hdr hv').trans_eq (by ring))

/-- A quantitative scalar consequence of the relative multiplier estimate.
The small-radius condition also supplies the strict positivity needed for
attraction, rather than merely proving that the multiplier is below one. -/
lemma multiplier_signs {m K k C r : ℝ} (hk : k ≠ 0) (hC : 0 < C)
    (hr : 0 < r) (hr1 : r < 1)
    (hrC : r < |k| / (8 * (C + 1)))
    (hrk : r < 1 / (3 * |k| + 1))
    (hK : |K - k| < |k| / 4)
    (herr : |m - 1 - 2 * K * r ^ 2| ≤ 2 * C * r ^ 3) :
    0 < m ∧ (k < 0 → m < 1) ∧ (0 < k → 1 < m) := by
  have hkpos : 0 < |k| := abs_pos.mpr hk
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hCr : 2 * C * r < |k| / 2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 8 * (C + 1))).mp hrC
    nlinarith
  have hCr3 : 2 * C * r ^ 3 < |k| / 2 * r ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_right hCr hr2]
  have hkr2 : 3 * |k| * r ^ 2 < 1 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 3 * |k| + 1)).mp hrk
    have hsq : r ^ 2 < r := by nlinarith
    have hm := mul_lt_mul_of_pos_left hsq (by positivity : 0 < 3 * |k|)
    nlinarith
  have hcenter : |m - 1 - 2 * k * r ^ 2| < |k| * r ^ 2 := by
    calc
      _ = |(m - 1 - 2 * K * r ^ 2) + 2 * (K - k) * r ^ 2| := by congr 1; ring
      _ ≤ |m - 1 - 2 * K * r ^ 2| + |2 * (K - k) * r ^ 2| := abs_add_le _ _
      _ ≤ 2 * C * r ^ 3 + |2 * (K - k) * r ^ 2| := add_le_add herr le_rfl
      _ = 2 * C * r ^ 3 + 2 * |K - k| * r ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_pos hr2]
        norm_num
      _ < |k| / 2 * r ^ 2 + |k| / 2 * r ^ 2 := by
        apply add_lt_add hCr3
        nlinarith [mul_lt_mul_of_pos_right hK hr2]
      _ = |k| * r ^ 2 := by ring
  have hb := abs_lt.mp hcenter
  refine ⟨?_, ?_, ?_⟩
  · have hka : -|k| ≤ k := neg_abs_le k
    have hh := mul_le_mul_of_nonneg_right hka hr2.le
    nlinarith
  · intro hneg
    rw [abs_of_neg hneg] at hb
    nlinarith [mul_neg_of_neg_of_pos hneg hr2]
  · intro hpos
    rw [abs_of_pos hpos] at hb
    nlinarith [mul_pos hpos hr2]

/-- The strict transverse-multiplier test follows from the original family
hypotheses and the actual return data. It assumes no periodic-orbit stability. -/
theorem sourceMultiplierClassification : MultiplierClassification := by
  intro F ω ε ρ δ C P Q h hε hδ hC hd
  let k := cubicReturnCoefficient F 0
  have ht : 0 < turnAngle := by unfold turnAngle; positivity
  have hkval : k = turnAngle * firstLyapunovCoefficient F / ω :=
    HopfReturnExpansion.source_coefficient_at_zero F ω h.1 h.2.1 h.2.2.1 h.2.2.2.1
  have hk : k ≠ 0 := by
    rw [hkval]
    exact div_ne_zero (mul_ne_zero ht.ne' h.2.2.2.2.2) h.2.1.ne'
  have hkpos : 0 < |k| := abs_pos.mpr hk
  obtain ⟨η₀, hη₀, hnear⟩ := Metric.continuousAt_iff.mp
    (cubicReturnCoefficient_continuousAt_zero F ω h) (|k| / 4) (by positivity)
  let η := min ε η₀
  let d := min δ (min 1 (min (|k| / (8 * (C + 1))) (1 / (3 * |k| + 1))))
  have hη : 0 < η := lt_min hε hη₀
  have hdpos : 0 < d := by
    dsimp [d]
    exact lt_min hδ (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  refine ⟨η, hη, d, hdpos, min_le_left _ _, min_le_left _ _, ?_⟩
  intro μ r hμ hr hfix
  have hμε : |μ| < ε := hμ.trans_le (min_le_left _ _)
  have hμη : |μ| < η₀ := hμ.trans_le (min_le_right _ _)
  have hrδ : r < δ := hr.2.trans_le (min_le_left _ _)
  have hrest := hr.2.trans_le (min_le_right δ _)
  have hr1 : r < 1 := hrest.trans_le (min_le_left _ _)
  have hrest' := hrest.trans_le (min_le_right (1 : ℝ) _)
  have hrC : r < |k| / (8 * (C + 1)) := hrest'.trans_le (min_le_left _ _)
  have hrk : r < 1 / (3 * |k| + 1) := hrest'.trans_le (min_le_right _ _)
  have hK : |cubicReturnCoefficient F μ - k| < |k| / 4 := by
    simpa only [Real.dist_eq, sub_zero] using hnear (by simpa only [Real.dist_eq, sub_zero] using hμη)
  obtain ⟨hm, hneg, hpos⟩ := multiplier_signs hk hC hr.1 hr1 hrC hrk hK
    (multiplier_error_bound F ω ε ρ δ C P Q hε hδ hd μ r hμε hr.1 hrδ hfix)
  refine ⟨hm, ?_, ?_⟩
  · intro hell
    apply hneg
    rw [hkval]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ht hell) h.2.1
  · intro hell
    apply hpos
    rw [hkval]
    exact div_pos (mul_pos ht hell) h.2.1

/-- Existence, uniqueness, amplitude asymptotics and strict return multipliers
for the original family, using the proved periodic-branch construction. -/
theorem planarHopfGeometry : Specs.D13Unified.Ch16.PlanarHopf.Geometry :=
  ⟨HopfPeriodicBranch.periodicBranch, sourceMultiplierClassification⟩

/-- Leastness is a conclusion about the physical solution, not a convention
selecting an arbitrary period from the existential orbit definition. -/
lemma exists_leastPeriodOrbit {f : ℂ → ℂ} {Γ : Set ℂ}
    (hΓ : IsPeriodicOrbit f Γ) : ∃ T : ℝ, LeastPeriodOrbit f Γ T := by
  obtain ⟨z, S, hS, hper, hsol, hnc, htrace⟩ := hΓ
  have hc : Continuous z := continuous_iff_continuousAt.mpr (fun t => (hsol t).continuousAt)
  have hn : ¬ ∀ t, z t = z 0 := by
    intro hh
    obtain ⟨s, t, hst⟩ := hnc
    exact hst ((hh s).trans (hh t).symm)
  obtain ⟨T, hT, hperT, hmin, _⟩ := Ch11.Orbits.exists_least_period z hc hn hS.ne' hper
  exact ⟨T, hT, z, hperT, hsol, hnc, htrace, hmin⟩

lemma reciprocal_velocity_error {v ω b : ℝ} (hω : 0 < ω) (hv : ω / 2 < v)
    (hb : 0 ≤ b) (hvb : |v - ω| ≤ b) :
    |1 / v - 1 / ω| ≤ 2 * b / ω ^ 2 := by
  have hvpos : 0 < v := lt_trans (half_pos hω) hv
  have hden : 0 < v * ω := mul_pos hvpos hω
  have hsmall : 0 < ω ^ 2 / 2 := by positivity
  have hdenle : ω ^ 2 / 2 ≤ v * ω := by
    nlinarith [mul_pos (by linarith : 0 < v - ω / 2) hω]
  calc
    |1 / v - 1 / ω| = |v - ω| / (v * ω) := by
      rw [show 1 / v - 1 / ω = -(v - ω) / (v * ω) by field_simp; ring]
      rw [abs_div, abs_neg, abs_of_pos hden]
    _ ≤ b / (v * ω) := div_le_div_of_nonneg_right hvb hden.le
    _ ≤ b / (ω ^ 2 / 2) := div_le_div_of_nonneg_left hb hsmall hdenle
    _ = 2 * b / ω ^ 2 := by ring

/-- Quantitative physical-clock estimate over a genuine angular turn.
This retains the endpoint derivatives; it makes no unjustified exchange
of a return-map multiplier with the derivative of a physical-time map. -/
lemma turn_clock_error (ω b : ℝ) (hω : 0 < ω) (hb : 0 ≤ b)
    (v clock : ℝ → ℝ) (hzero : clock 0 = 0)
    (hclock : ∀ θ ∈ Icc 0 turnAngle,
      HasDerivWithinAt clock (1 / v θ) (Icc 0 turnAngle) θ)
    (hv : ∀ θ ∈ Icc 0 turnAngle, ω / 2 < v θ)
    (hvb : ∀ θ ∈ Icc 0 turnAngle, |v θ - ω| ≤ b) :
    |clock turnAngle - turnAngle / ω| ≤ (2 * b / ω ^ 2) * turnAngle := by
  have ht : 0 ≤ turnAngle := by unfold turnAngle; positivity
  have hder : ∀ θ ∈ Icc 0 turnAngle,
      HasDerivWithinAt (fun θ => clock θ - θ / ω) (1 / v θ - 1 / ω)
        (Icc 0 turnAngle) θ := by
    intro θ hθ
    exact (hclock θ hθ).sub (((hasDerivAt_id θ).div_const ω).hasDerivWithinAt)
  have hbound : ∀ θ ∈ Icc 0 turnAngle, ‖1 / v θ - 1 / ω‖ ≤ 2 * b / ω ^ 2 := by
    intro θ hθ
    exact reciprocal_velocity_error hω (hv θ hθ) hb (hvb θ hθ)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    (convex_Icc (0 : ℝ) turnAngle) (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht)
  simpa only [hzero, zero_div, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht] using hh

/-- A first angular turn lasts at most 4π/ω in physical time.
This estimate uses only angular positivity and holds before passing to a
closed periodic solution. -/
lemma turn_clock_bound (ω : ℝ) (hω : 0 < ω) (v clock : ℝ → ℝ)
    (hzero : clock 0 = 0)
    (hclock : ∀ θ ∈ Icc 0 turnAngle,
      HasDerivWithinAt clock (1 / v θ) (Icc 0 turnAngle) θ)
    (hv : ∀ θ ∈ Icc 0 turnAngle, ω / 2 < v θ) :
    |clock turnAngle| ≤ 2 * turnAngle / ω := by
  have ht : 0 ≤ turnAngle := by unfold turnAngle; positivity
  have hbound : ∀ θ ∈ Icc 0 turnAngle, ‖1 / v θ‖ ≤ 2 / ω := by
    intro θ hθ
    have hvpos : 0 < v θ := lt_trans (half_pos hω) (hv θ hθ)
    rw [Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hvpos)]
    apply (div_le_div_iff₀ hvpos hω).mpr
    linarith [hv θ hθ]
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hclock hbound
    (convex_Icc (0 : ℝ) turnAngle) (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht)
  simpa only [hzero, sub_zero, Real.norm_eq_abs, abs_of_nonneg ht, div_mul_eq_mul_div] using hh

/-- A uniform angular error estimate using the very same remainder as the
normal form. It applies at every angle, not just on the positive ray. -/
lemma angular_velocity_error_bound (F : ℝ × ℂ → ℂ) (ε ρ C ω μ r θ : ℝ)
    (hR : UniformRemainderBounds F ε ρ C) (hμ : |μ| < ε) (hr : |r| < ρ) :
    |angularVelocity F θ r μ - ω| ≤ |spectralImag F μ - ω| +
      |(coefficient F μ).im| * |r| ^ 2 + C * |r| ^ 3 := by
  calc
    _ = |(spectralImag F μ - ω) + (coefficient F μ).im * r ^ 2 +
        (polarRemainder F θ r μ).im / r| := by unfold angularVelocity; congr 1; ring
    _ ≤ |(spectralImag F μ - ω) + (coefficient F μ).im * r ^ 2| +
        |(polarRemainder F θ r μ).im / r| := abs_add_le _ _
    _ ≤ (|spectralImag F μ - ω| + |(coefficient F μ).im * r ^ 2|) +
        C * |r| ^ 3 := add_le_add (abs_add_le _ _)
          (HopfReturnExpansion.angular_remainder_bound F ε ρ C μ r θ hR hμ hr)
    _ = _ := by rw [abs_mul, abs_pow]

/-- Angular velocity converges to ω uniformly in the angle, using the
source normal form and its uniform remainder rather than pointwise polar
notation. Signed radius zero is included. -/
lemma uniform_angular_velocity_limit (F : ℝ × ℂ → ℂ) (ω : ℝ)
    (h : SourceHypotheses F ω) (κ : ℝ) (hκ : 0 < κ) :
    ∃ η > 0, ∃ d > 0, ∀ μ r θ : ℝ, |μ| < η → |r| < d →
      |angularVelocity F θ r μ - ω| < κ := by
  obtain ⟨ha0, hb0, ε, hε, ρ, hρ, C, hC, hcoord, hR, hreg⟩ :=
    CubicNormalForm.normalForm F ω h.1 h.2.1 h.2.2.1 h.2.2.2.1
  obtain ⟨_, _, hb, hc, _⟩ := hreg 0 (by simpa using hε)
  let M := ‖coefficient F 0‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMC : 0 < M + C := add_pos hM hC
  have hbn : ∀ᶠ μ in nhds (0 : ℝ), |spectralImag F μ - ω| < κ / 2 := by
    have hc' : ContinuousAt (fun μ => |spectralImag F μ - ω|) 0 :=
      (hb.continuousAt.sub continuousAt_const).abs
    apply hc'.eventually (gt_mem_nhds _)
    simpa only [hb0, sub_self, abs_zero] using half_pos hκ
  have hcn : ∀ᶠ μ in nhds (0 : ℝ), ‖coefficient F μ‖ < M :=
    hc.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨η₀, hη₀, hnear⟩ := Metric.eventually_nhds_iff.mp (hbn.and hcn)
  let η := min ε η₀
  let d := min ρ (min 1 (κ / (2 * (M + C))))
  refine ⟨η, lt_min hε hη₀, d, lt_min hρ (lt_min zero_lt_one (by positivity)), ?_⟩
  intro μ r θ hμ hr
  have hμε : |μ| < ε := hμ.trans_le (min_le_left _ _)
  have hμη : dist μ 0 < η₀ := by
    simpa only [Real.dist_eq, sub_zero] using hμ.trans_le (min_le_right ε η₀)
  obtain ⟨hbμ, hcμ⟩ := hnear hμη
  have hrρ : |r| < ρ := hr.trans_le (min_le_left _ _)
  have hr1 : |r| ≤ 1 := (hr.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hrκ : |r| < κ / (2 * (M + C)) :=
    hr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hprod : (M + C) * |r| < κ / 2 := by
    have hh := (lt_div_iff₀ (show 0 < 2 * (M + C) by positivity)).mp hrκ
    nlinarith
  have hp2 : |r| ^ 2 ≤ |r| := by nlinarith [abs_nonneg r]
  have hp3 : |r| ^ 3 ≤ |r| := by
    calc
      |r| ^ 3 = |r| ^ 2 * |r| := by ring
      _ ≤ |r| * |r| := mul_le_mul_of_nonneg_right hp2 (abs_nonneg r)
      _ ≤ |r| := by nlinarith [abs_nonneg r]
  have hi : |(coefficient F μ).im| ≤ M := (Complex.abs_im_le_norm _).trans hcμ.le
  have h1 := mul_le_mul_of_nonneg_right hi (sq_nonneg |r|)
  have h2 := mul_le_mul_of_nonneg_left hp2 hM.le
  have h3 := mul_le_mul_of_nonneg_left hp3 hC.le
  have he := angular_velocity_error_bound F ε ρ C ω μ r θ hR hμε hrρ
  nlinarith

/-- The real basis in the shared equilibrium criteria is exactly (1,i).
This bridge checks the actual derivative matrix used by both interfaces. -/
lemma complexifiedLinearization_eq_toMatrix (F : ℝ × ℂ → ℂ) (μ : ℝ) :
    complexifiedLinearization F μ =
      (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
        (linearization F μ).toLinearMap).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexifiedLinearization, Matrix.map_apply, LinearMap.toMatrix_apply,
      Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

/-- Linearized stability and instability apply to every local ODE representing
the source field near zero. In particular no arbitrary spectral labels or
assumed stability conclusion are substituted for the actual derivative. -/
lemma equilibrium_criteria (F : ℝ × ℂ → ℂ) (μ : ℝ) (A : _root_.D13Unified.AutonomousODE ℂ)
    (hA : ContDiffOn ℝ 1 (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue A) A.domain)
    (h0 : (0 : ℂ) ∈ A.domain)
    (heq : Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue A 0 = 0)
    (heval : Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue A =ᶠ[nhds 0]
      fun z => F (μ, z))
    (hspec : ∀ z : ℂ, Module.End.HasEigenvalue (complexifiedLinearization F μ).toLin' z ↔
      z = eigenvalue (spectralReal F μ) (spectralImag F μ) ∨
      z = star (eigenvalue (spectralReal F μ) (spectralImag F μ))) :
    (spectralReal F μ < 0 → Specs.D13Unified.Ch12.StabilityDefinitions.locallyExponentiallyStableValue
      A hA h0 heq) ∧
    (0 < spectralReal F μ → Specs.D13Unified.Ch12.StabilityDefinitions.unstableValue A hA h0 heq) := by
  have hd : fderiv ℝ (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue A) 0 =
      linearization F μ := heval.fderiv_eq
  have hm : (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
      (fderiv ℝ (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue A) 0).toLinearMap).map
        Complex.ofReal = complexifiedLinearization F μ := by
    rw [hd, complexifiedLinearization_eq_toMatrix]
  refine ⟨?_, ?_⟩
  · intro ha
    apply Ch12.LinearizedStability.linearized_stability Complex.basisOneI A hA h0 heq
    intro z hz
    rw [hm] at hz
    rcases (hspec z).mp hz with he | he <;> rw [he] <;> simpa [eigenvalue] using ha
  · intro ha
    apply (Ch12.LinearizedStability.linearized_instability Complex.basisOneI A hA h0 heq ?_).2
    refine ⟨eigenvalue (spectralReal F μ) (spectralImag F μ), ?_, ?_⟩
    · simpa [eigenvalue] using ha
    · rw [hm]
      exact (hspec _).mpr (Or.inl rfl)

/-- Uniform angular smallness is sufficient for the physical-clock limit.
The remaining application must show that the actual periodic turn satisfies
this smallness as its initial radius tends to zero. -/
lemma uniform_clock_limit (F : ℝ × ℂ → ℂ) (ω : ℝ) (h : SourceHypotheses F ω)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ η > 0, ∃ d > 0, ∀ (μ : ℝ) (u clock : ℝ → ℝ), |μ| < η →
      (∀ θ ∈ Icc 0 turnAngle, |u θ| < d) → clock 0 = 0 →
      (∀ θ ∈ Icc 0 turnAngle, HasDerivWithinAt clock
        (1 / angularVelocity F θ (u θ) μ) (Icc 0 turnAngle) θ) →
      |clock turnAngle - turnAngle / ω| < κ := by
  have ht : 0 < turnAngle := by unfold turnAngle; positivity
  have hω : 0 < ω := h.2.1
  let b := min (ω / 4) (κ * ω ^ 2 / (4 * turnAngle))
  have hb : 0 < b := lt_min (by positivity) (by positivity)
  obtain ⟨η, hη, d, hd, hvel⟩ := uniform_angular_velocity_limit F ω h b hb
  refine ⟨η, hη, d, hd, ?_⟩
  intro μ u clock hμ hu hzero hclock
  have hsmall : ∀ θ ∈ Icc 0 turnAngle, |angularVelocity F θ (u θ) μ - ω| < b :=
    fun θ hθ => hvel μ (u θ) θ hμ (hu θ hθ)
  have hpos : ∀ θ ∈ Icc 0 turnAngle, ω / 2 < angularVelocity F θ (u θ) μ := by
    intro θ hθ
    have hh := (abs_lt.mp (hsmall θ hθ)).1
    have hh' : b ≤ ω / 4 := min_le_left _ _
    linarith [h.2.1]
  have herr := turn_clock_error ω b h.2.1 hb.le
    (fun θ => angularVelocity F θ (u θ) μ) clock hzero hclock hpos
    (fun θ hθ => (hsmall θ hθ).le)
  have hcoeff : (2 * b / ω ^ 2) * turnAngle ≤ κ / 2 := by
    have hbb : b ≤ κ * ω ^ 2 / (4 * turnAngle) := min_le_right _ _
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * turnAngle)).mp hbb
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < ω ^ 2)).mpr
    nlinarith
  exact herr.trans hcoeff |>.trans_lt (by linarith)

/-- Closing a first-ray turn gives a complete solution whose least period is
exactly the physical clock duration. No uniqueness or preexisting orbit is
assumed: exclusion of an earlier ray crossing excludes every smaller period. -/
lemma closedTurn_leastPeriod {F : ℝ × ℂ → ℂ} {ω μ r ρ : ℝ}
    (hr : 0 < r) (hturn : FullAngularTurn F ω μ r r ρ) :
    ∃ (Γ : Set ℂ) (T : ℝ), LeastPeriodOrbit (fun w => transformedField F (μ, w)) Γ T ∧
      (r : ℂ) ∈ Γ ∧ Γ ⊆ Metric.ball 0 ρ ∧
      ∃ (u clock : ℝ → ℝ), clock 0 = 0 ∧ T = clock turnAngle ∧
        (∀ θ ∈ Icc 0 turnAngle, 0 < u θ ∧ u θ < ρ ∧
          HasDerivWithinAt clock (1 / angularVelocity F θ (u θ) μ)
            (Icc 0 turnAngle) θ) := by
  obtain ⟨u, clock, z, hu0, huT, hc0, hT, hmono, hbij, hang,
    hz0, hzT, hphys, hfirst⟩ := hturn
  obtain ⟨w, hwper, heq, hwder, hwimage⟩ := HopfPeriodicOrbitBridge.periodicExtension
    (V := fun w => transformedField F (μ, w)) hT (hzT.trans hz0.symm) (fun t ht => (hphys t ht).2)
  have hw0 : w 0 = (r : ℂ) := (heq ⟨le_rfl, hT.le⟩).trans hz0
  have hray : positiveRay (w 0) := by
    rw [hw0]
    exact ⟨by simp, by simpa using hr⟩
  have hnc : w 0 ≠ w (clock turnAngle / 2) := by
    intro he
    have ht : clock turnAngle / 2 ∈ Ioo 0 (clock turnAngle) := by
      constructor <;> linarith
    apply hfirst _ ht
    rw [← heq (Ioo_subset_Icc_self ht), ← he]
    exact hray
  have hmin : ∀ S : ℝ, 0 < S → Function.Periodic w S → clock turnAngle ≤ S := by
    intro S hS hper
    by_contra hn
    have ht : S ∈ Ioo 0 (clock turnAngle) := ⟨hS, lt_of_not_ge hn⟩
    apply hfirst S ht
    rw [← heq (Ioo_subset_Icc_self ht)]
    have he : w S = w 0 := by simpa using hper 0
    rwa [he]
  refine ⟨range w, clock turnAngle, ⟨hT, w, hwper, hwder,
    ⟨0, clock turnAngle / 2, hnc⟩, rfl, hmin⟩, ⟨0, hw0⟩, ?_, u, clock, hc0, rfl, ?_⟩
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := hwimage hx
    simpa only [Metric.mem_ball, dist_zero_right] using (hphys t ht).1
  · intro θ hθ
    exact ⟨(hang θ hθ).1, (hang θ hθ).2.1, (hang θ hθ).2.2.2.2.1⟩

/-- An actual normal-form coordinate map preserves the least physical period,
not just an arbitrarily chosen period. Injectivity is checked on the same
chart that carries the differential equation. -/
lemma leastPeriod_coordinate {F : ℝ × ℂ → ℂ} {ε ρ μ T : ℝ} {Γ : Set ℂ}
    (hc : CoordinateValidity F ε ρ) (hμ : |μ| < ε)
    (hΓ : Γ ⊆ Metric.ball 0 ρ)
    (hT : LeastPeriodOrbit (fun w => transformedField F (μ, w)) Γ T) :
    LeastPeriodOrbit (fun x => F (μ, x)) (coordinate F μ '' Γ) T := by
  obtain ⟨hTpos, z, hper, hsol, hnc, htrace, hmin⟩ := hT
  have hstay : ∀ t, ‖z t‖ < ρ := by
    intro t
    have hh := hΓ (htrace ▸ mem_range_self t)
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  have htrans := HopfPeriodicOrbitBridge.coordinateTransport F hc hμ
    ⟨hTpos, hper, hsol, hnc⟩ hstay
  refine ⟨hTpos, (fun t => coordinate F μ (z t)), htrans.2.1, htrans.2.2.1,
    htrans.2.2.2, ?_, ?_⟩
  · rw [htrace]
    exact (range_comp (coordinate F μ) z).symm
  · intro S hS hSper
    apply hmin S hS
    obtain ⟨e, he, hsrc, _, _⟩ := hc
    intro t
    have heq : e (μ, z (t + S)) = e (μ, z t) := by
      rw [congrFun he _, congrFun he _]
      exact Prod.ext rfl (hSper t)
    exact congrArg Prod.snd (e.injOn (hsrc ⟨hμ, hstay _⟩) (hsrc ⟨hμ, hstay _⟩) heq)

/-- Least-period and spatial control for every sufficiently small fixed
radius of ANY genuine return map. The small turn is constructed from the
source field, and ODE uniqueness identifies its endpoint with that map.
This does not require the arbitrary ReturnData confinement ball to lie
inside a separately chosen remainder neighborhood. -/
lemma smallFixedReturn_period (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) (h : SourceHypotheses F ω)
    (hε : 0 < ε) (hρ : 0 < ρ) (hd : ReturnData F ω ε ρ δ C P Q)
    (κ b : ℝ) (hκ : 0 < κ) (hb : 0 < b) :
    ∃ η > 0, ∃ τ > 0, η ≤ ε ∧
      ∀ μ r : ℝ, |μ| < η → 0 < r → r < min δ τ → P (r, μ) = r →
        ∃ (Γ : Set ℂ) (T : ℝ),
          LeastPeriodOrbit (fun w => transformedField F (μ, w)) Γ T ∧
          (r : ℂ) ∈ Γ ∧ Γ ⊆ Metric.ball 0 (min ρ b) ∧
          LeastPeriodOrbit (fun x => F (μ, x)) (coordinate F μ '' Γ) T ∧
          |T - turnAngle / ω| < κ := by
  have hs : Specs.D13Unified.Ch16.HopfPeriodicOrbitBridge.SourceHypotheses F ω :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  obtain ⟨εl, hεl, R, hR, hloc⟩ := HopfPeriodicOrbitBridge.sourceLocalLipschitz F ω hs
  obtain ⟨εc, hεc, d, hdp, hclock⟩ := uniform_clock_limit F ω h κ hκ
  let s := min R (min d (min ρ b))
  have hsp : 0 < s := lt_min hR (lt_min hdp (lt_min hρ hb))
  obtain ⟨εs, hεs, τ, hτ, hsmall⟩ := HopfPeriodicOrbitBridge.sourceSmallTurns F ω hs s hsp
  let η := min ε (min εl (min εc εs))
  have hη : 0 < η := lt_min hε (lt_min hεl (lt_min hεc hεs))
  refine ⟨η, hη, τ, hτ, min_le_left _ _, ?_⟩
  intro μ r hμ hr hrt hfix
  have hμε : |μ| < ε := hμ.trans_le (min_le_left _ _)
  have hrest := hμ.trans_le (min_le_right ε _)
  have hμl : |μ| < εl := hrest.trans_le (min_le_left _ _)
  have hrest' := hrest.trans_le (min_le_right εl _)
  have hμc : |μ| < εc := hrest'.trans_le (min_le_left _ _)
  have hμs : |μ| < εs := hrest'.trans_le (min_le_right _ _)
  obtain ⟨p, hturn⟩ := hsmall μ r hμs hr (hrt.trans_le (min_le_right _ _))
  obtain ⟨K, hK⟩ := (hloc μ hμl).2
  have hp : p = r := (HopfPeriodicOrbitBridge.fullAngularTurn_endpoint_eq_confined hK
    (show s ≤ R from min_le_left _ _) hturn
    (hd.turn μ r hμε hr (hrt.trans_le (min_le_left _ _)))).trans hfix
  rw [hp] at hturn
  obtain ⟨Γ, T, hT, hrΓ, hΓ, u, clock, hc0, hTc, hang⟩ := closedTurn_leastPeriod hr hturn
  have hsb : s ≤ min ρ b := (min_le_right R _).trans (min_le_right d _)
  have hΓb : Γ ⊆ Metric.ball 0 (min ρ b) :=
    hΓ.trans (Metric.ball_subset_ball hsb)
  have hΓρ : Γ ⊆ Metric.ball 0 ρ :=
    hΓb.trans (Metric.ball_subset_ball (min_le_left _ _))
  refine ⟨Γ, T, hT, hrΓ, hΓb, leastPeriod_coordinate hd.coordinates hμε hΓρ hT, ?_⟩
  rw [hTc]
  apply hclock μ u clock hμc _ hc0 (fun θ hθ => (hang θ hθ).2.2)
  intro θ hθ
  rw [abs_of_pos (hang θ hθ).1]
  exact (hang θ hθ).2.1.trans_le ((min_le_right R _).trans (min_le_left _ _))

open Specs.D13Unified.Ch01.AutonomousParameters in
/-- Package a continuous field on its actual open domain. -/
def equationOn (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hf : ContinuousOn f U) :
    _root_.D13Unified.AutonomousODE ℂ where
  domain := U
  isOpen_domain := hU
  field := fun z => f z
  continuous_field := continuousOn_iff_continuous_domRestrict.mp hf

/-- Both strict equilibrium conclusions, with a single local state domain for
all small parameters. Smoothness of the actual input field supplies that domain. -/
theorem sourceEquilibria : Equilibria := by
  classical
  intro F ω h
  obtain ⟨R, hR, hregular⟩ := Metric.eventually_nhds_iff.mp (h.1.eventually (by norm_num))
  obtain ⟨εe, hεe, heqnear⟩ := Metric.eventually_nhds_iff.mp h.2.2.2.1
  obtain ⟨_, _, εn, hεn, ρ, _, C, _, _, _, hnormal⟩ :=
    CubicNormalForm.normalForm F ω h.1 h.2.1 h.2.2.1 h.2.2.2.1
  let ε := min εn (min R εe)
  let U : Set ℂ := Metric.ball 0 R
  have hε : 0 < ε := lt_min hεn (lt_min hR hεe)
  have hU : IsOpen U := Metric.isOpen_ball
  have h0U : (0 : ℂ) ∈ U := Metric.mem_ball_self hR
  have hslice (μ : ℝ) (hμ : |μ| < ε) : ContDiffOn ℝ 1 (fun z => F (μ,z)) U := by
    intro z hz
    have hμR : |μ| < R := hμ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hzR : ‖z‖ < R := by simpa only [U, Metric.mem_ball, dist_zero_right] using hz
    have hq : dist (μ,z) (0,0) < R := by
      simpa only [Prod.dist_eq, Real.dist_eq, sub_zero, dist_zero_right, Real.norm_eq_abs] using max_lt hμR hzR
    have hFq := hregular hq
    exact ((hFq.of_le (show (1 : WithTop ℕ∞) ≤ 5 by norm_num)).comp z
      (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  let f : ℝ → ℂ → ℂ := fun μ z => if |μ| < ε then F (μ,z) else 0
  have hcont (μ : ℝ) : ContinuousOn (f μ) U := by
    by_cases hμ : |μ| < ε
    · simpa only [f, if_pos hμ] using (hslice μ hμ).continuousOn
    · simp only [f, if_neg hμ]
      exact continuousOn_const
  let A : ℝ → _root_.D13Unified.AutonomousODE ℂ := fun μ => equationOn (f μ) U hU (hcont μ)
  have heval (μ : ℝ) (hμ : |μ| < ε) (z : ℂ) (hz : z ∈ U) :
      Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue (A μ) z = F (μ,z) := by
    simp only [A, equationOn, Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue,
      hz, dite_true, f, if_pos hμ]
  refine ⟨ε, hε, U, hU, h0U, A, ?_, ?_⟩
  · intro μ hμ
    exact ⟨rfl, heval μ hμ⟩
  · intro μ hμ
    have hA : ContDiffOn ℝ 1
        (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue (A μ)) (A μ).domain :=
      (hslice μ hμ).congr (heval μ hμ)
    have h0 : (0 : ℂ) ∈ (A μ).domain := h0U
    have hμe : dist μ 0 < εe := by
      simpa only [Real.dist_eq, sub_zero] using
        hμ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have heq : Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue (A μ) 0 = 0 :=
      (heval μ hμ 0 h0U).trans (heqnear hμe)
    have hevent : Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue (A μ) =ᶠ[nhds 0]
        fun z => F (μ,z) := Filter.eventually_of_mem (hU.mem_nhds h0U) (heval μ hμ)
    have hμn : |μ| < εn := hμ.trans_le (min_le_left _ _)
    have hs := (hnormal μ hμn).2.2.2.2.1
    exact ⟨hA, h0, heq, equilibrium_criteria F μ (A μ) hA h0 heq hevent hs⟩

/-- Both strict equilibrium conclusions follow on a common local domain. -/
theorem planarHopfEquilibria : Specs.D13Unified.Ch16.PlanarHopf.Equilibria :=
  sourceEquilibria


lemma branchFixedRadii_small (F : ℝ × ℂ → ℂ) (P Q : ℝ × ℝ → ℝ)
    (ε₀ δ₀ ε δ C : ℝ) (ψ : ℝ → ℝ)
    (hbr : BranchDescription F P Q ε₀ δ₀ ε δ C ψ)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ ζ > 0, ∀ μ r : ℝ, |μ| < min ε ζ → r ∈ Ioo 0 δ → P (r, μ) = r → r < τ := by
  obtain ⟨ζ₀, hζ₀, hsmall⟩ := hbr.2.2.2.2.2.2.2.2.2.2.2.2.2 (1 : ℝ) (by norm_num)
  let k := deriv (spectralReal F) 0 / firstLyapunovCoefficient F
  let ζ := min ζ₀ (τ ^ 2 / (|k| + 1))
  have hζ : 0 < ζ := lt_min hζ₀ (div_pos (sq_pos_of_pos hτ) (by positivity))
  refine ⟨ζ, hζ, ?_⟩
  intro μ r hμ hr hfix
  have hμε : |μ| < ε := hμ.trans_le (min_le_left _ _)
  have hμζ : |μ| < ζ := hμ.trans_le (min_le_right _ _)
  have hμζ₀ : |μ| < ζ₀ := hμζ.trans_le (min_le_left _ _)
  have hamp : |r ^ 2 + k * μ| ≤ |μ| := by
    simpa only [one_mul] using hsmall μ r (lt_min hμε hμζ₀) hr hfix
  have hb : r ^ 2 ≤ (|k| + 1) * |μ| := by
    have h₁ := (abs_le.mp hamp).2
    have h₂ := neg_abs_le (k * μ)
    rw [abs_mul] at h₂
    nlinarith
  have hμτ : |μ| < τ ^ 2 / (|k| + 1) := hμζ.trans_le (min_le_right _ _)
  have hb' : (|k| + 1) * |μ| < τ ^ 2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < |k| + 1)).mp hμτ
    nlinarith
  nlinarith [hr.1]


lemma leastPeriodOrbit_isPeriodicOrbit {f : ℂ → ℂ} {Γ : Set ℂ} {T : ℝ}
    (hT : LeastPeriodOrbit f Γ T) : IsPeriodicOrbit f Γ := by
  obtain ⟨hT, z, hper, hsol, hnc, htrace, _⟩ := hT
  exact ⟨z, T, hT, hper, hsol, hnc, htrace⟩

lemma classifiedOrbits_period_limit (F : ℝ × ℂ → ℂ) (ω ε₀ ρ δ₀ C₀ : ℝ)
    (P Q : ℝ × ℝ → ℝ) (ε δ C : ℝ) (ψ : ℝ → ℝ)
    (εc : ℝ) (hεc : εc ≤ ε) (σ : ℝ) (U : Set ℂ) (h : SourceHypotheses F ω)
    (hε₀ : 0 < ε₀) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hret : ReturnData F ω ε₀ ρ δ₀ C₀ P Q)
    (hbr : BranchDescription F P Q ε₀ δ₀ ε δ C ψ)
    (hlift : ∀ μ : ℝ, |μ| < εc → ∀ Γ : Set ℂ,
      IsPeriodicOrbit (fun z => F (μ,z)) Γ → Γ ⊆ U →
      ∃ (Δ : Set ℂ) (r : ℝ),
        IsPeriodicOrbit (fun w => transformedField F (μ,w)) Δ ∧
        Δ ⊆ Metric.ball 0 σ ∧ Γ = coordinate F μ '' Δ ∧
        r ∈ Ioo 0 δ ∧ (r : ℂ) ∈ Δ ∧ P (r,μ) = r)
    (huni : ∀ μ : ℝ, |μ| < εc → ∀ Γ Δ : Set ℂ,
      IsPeriodicOrbit (fun w => transformedField F (μ,w)) Γ → Γ ⊆ Metric.ball 0 σ →
      IsPeriodicOrbit (fun w => transformedField F (μ,w)) Δ → Δ ⊆ Metric.ball 0 σ → Γ = Δ) :
    ∀ κ > 0, ∃ ζ > 0, ∀ μ : ℝ, |μ| < min εc ζ →
      ∀ Γ : Set ℂ, IsPeriodicOrbit (fun z => F (μ,z)) Γ → Γ ⊆ U →
        ∃ T : ℝ, LeastPeriodOrbit (fun z => F (μ,z)) Γ T ∧
          |T - turnAngle / ω| < κ := by
  intro κ hκ
  obtain ⟨η, hη, τ, hτ, hηε, hperiod⟩ :=
    smallFixedReturn_period F ω ε₀ ρ δ₀ C₀ P Q h hε₀ hρ hret κ σ hκ hσ
  obtain ⟨ζ₀, hζ₀, hsmall⟩ :=
    branchFixedRadii_small F P Q ε₀ δ₀ ε δ C ψ hbr (min δ₀ τ)
      (lt_min (hbr.2.2.1.trans_le hbr.2.2.2.1) hτ)
  let ζ := min η ζ₀
  refine ⟨ζ, lt_min hη hζ₀, ?_⟩
  intro μ hμ Γ hΓ hΓU
  have hμc : |μ| < εc := hμ.trans_le (min_le_left _ _)
  have hμε : |μ| < ε := hμc.trans_le hεc
  have hμζ : |μ| < ζ := hμ.trans_le (min_le_right _ _)
  have hμη : |μ| < η := hμζ.trans_le (min_le_left _ _)
  have hμζ₀ : |μ| < ζ₀ := hμζ.trans_le (min_le_right _ _)
  obtain ⟨Δ, r, hΔ, hΔσ, hΓΔ, hrδ, hrΔ, hfix⟩ := hlift μ hμc Γ hΓ hΓU
  have hrsmall : r < min δ₀ τ := hsmall μ r (lt_min hμε hμζ₀) hrδ hfix
  obtain ⟨Λ, T, hT, hrΛ, hΛ, hTor, hTk⟩ := hperiod μ r hμη hrδ.1 hrsmall hfix
  have hΛσ : Λ ⊆ Metric.ball 0 σ := hΛ.trans (Metric.ball_subset_ball (min_le_right _ _))
  have heq : Δ = Λ := huni μ hμc Δ Λ hΔ hΔσ (leastPeriodOrbit_isPeriodicOrbit hT) hΛσ
  refine ⟨T, ?_, hTk⟩
  simpa only [hΓΔ, heq] using hTor


/-- The actual normal-coordinate map uniformly carries a small normal ball
into any prescribed original neighborhood of zero. -/
lemma uniform_coordinate_small (F : ℝ × ℂ → ℂ) {ε ρ : ℝ}
    (hε : 0 < ε) (hρ : 0 < ρ)
    (hc : CoordinateValidity F ε ρ) (V : Set ℂ)
    (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V) :
    ∃ η > 0, ∃ b > 0, η ≤ ε ∧ b ≤ ρ ∧
      ∀ μ w, |μ| < η → ‖w‖ < b → coordinate F μ w ∈ V := by
  obtain ⟨e, he, _, _, hreg⟩ := hc
  have h0 : (0, 0) ∈ stateParameterBox ε ρ := by
    simpa [stateParameterBox] using And.intro hε hρ
  have hcont : ContinuousAt (fun q : ℝ × ℂ => coordinate F q.1 q.2) (0, 0) := by
    simpa only [he, familyCoordinate, Function.comp_def] using
      ((hreg (0, 0) h0).1.continuousAt.snd)
  have hforward : ∀ᶠ q : ℝ × ℂ in nhds (0, 0), coordinate F q.1 q.2 ∈ V :=
    hcont.eventually (hV.mem_nhds (by
      change coordinate F 0 0 ∈ V
      rw [HopfPeriodicOrbitBridge.coordinate_zero]
      exact hV0))
  obtain ⟨a, ha, hmap⟩ := Metric.eventually_nhds_iff.mp hforward
  let η := min ε a
  let b := min ρ a
  refine ⟨η, lt_min hε ha, b, lt_min hρ ha,
    min_le_left _ _, min_le_left _ _, ?_⟩
  intro μ w hμ hw
  apply hmap (y := (μ, w))
  rw [Prod.dist_eq, dist_zero_right, dist_zero_right, Real.norm_eq_abs, max_lt_iff]
  exact ⟨hμ.trans_le (min_le_right _ _), hw.trans_le (min_le_right _ _)⟩


open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch12.StabilityDefinitions

/-- The strict equilibrium criteria hold on every smaller open neighborhood.
This allows the final orbit classification and actual local ODE to use the
same domain, rather than unrelated neighborhoods from separate conclusions. -/
lemma sourceEquilibriaOn (F : ℝ × ℂ → ℂ) (ω : ℝ) (h : SourceHypotheses F ω) :
    ∃ ε > 0, ∃ V : Set ℂ, IsOpen V ∧ 0 ∈ V ∧
      ∀ U : Set ℂ, IsOpen U → 0 ∈ U → U ⊆ V →
      ∃ A : ℝ → _root_.D13Unified.AutonomousODE ℂ,
        (∀ μ : ℝ, |μ| < ε → (A μ).domain = U ∧
          (∀ z ∈ U, autonomousEvalValue (A μ) z = F (μ, z))) ∧
        ∀ μ : ℝ, |μ| < ε →
          ∃ hF : ContDiffOn ℝ 1 (autonomousEvalValue (A μ)) (A μ).domain,
          ∃ h0 : (0 : ℂ) ∈ (A μ).domain,
          ∃ heq : autonomousEvalValue (A μ) 0 = 0,
            (spectralReal F μ < 0 → locallyExponentiallyStableValue (A μ) hF h0 heq) ∧
            (0 < spectralReal F μ → unstableValue (A μ) hF h0 heq) := by
  classical
  obtain ⟨εe, hεe, V, hV, h0V, B, hBeval, hBeq⟩ := sourceEquilibria F ω h
  obtain ⟨_, _, εn, hεn, ρ, _, C, _, _, _, hnormal⟩ :=
    CubicNormalForm.normalForm F ω h.1 h.2.1 h.2.2.1 h.2.2.2.1
  let ε := min εe εn
  have hε : 0 < ε := lt_min hεe hεn
  refine ⟨ε, hε, V, hV, h0V, ?_⟩
  intro U hU h0U hUV
  have hslice (μ : ℝ) (hμ : |μ| < ε) : ContDiffOn ℝ 1 (fun z => F (μ,z)) U := by
    have hμe : |μ| < εe := hμ.trans_le (min_le_left _ _)
    obtain ⟨hB, _, _, _⟩ := hBeq μ hμe
    have hBV : (B μ).domain = V := (hBeval μ hμe).1
    rw [hBV] at hB
    exact (hB.mono hUV).congr (fun z hz => ((hBeval μ hμe).2 z (hUV hz)).symm)
  let f : ℝ → ℂ → ℂ := fun μ z => if |μ| < ε then F (μ,z) else 0
  have hcont (μ : ℝ) : ContinuousOn (f μ) U := by
    by_cases hμ : |μ| < ε
    · simpa only [f, if_pos hμ] using (hslice μ hμ).continuousOn
    · simp only [f, if_neg hμ]
      exact continuousOn_const
  let A : ℝ → _root_.D13Unified.AutonomousODE ℂ := fun μ => equationOn (f μ) U hU (hcont μ)
  have heval (μ : ℝ) (hμ : |μ| < ε) (z : ℂ) (hz : z ∈ U) :
      autonomousEvalValue (A μ) z = F (μ,z) := by
    simp only [A, equationOn, autonomousEvalValue, hz, dite_true, f, if_pos hμ]
  refine ⟨A, (fun μ hμ => ⟨rfl, heval μ hμ⟩), ?_⟩
  intro μ hμ
  have hA : ContDiffOn ℝ 1 (autonomousEvalValue (A μ)) (A μ).domain :=
    (hslice μ hμ).congr (heval μ hμ)
  have h0 : (0 : ℂ) ∈ (A μ).domain := h0U
  have hμe : |μ| < εe := hμ.trans_le (min_le_left _ _)
  obtain ⟨_, _, heqB, _⟩ := hBeq μ hμe
  have heq : autonomousEvalValue (A μ) 0 = 0 := by
    rw [heval μ hμ 0 h0U, ← (hBeval μ hμe).2 0 h0V]
    exact heqB
  have hevent : autonomousEvalValue (A μ) =ᶠ[nhds 0] fun z => F (μ,z) :=
    Filter.eventually_of_mem (hU.mem_nhds h0U) (heval μ hμ)
  have hs := (hnormal μ (hμ.trans_le (min_le_right _ _))).2.2.2.2.1
  exact ⟨hA, h0, heq, equilibrium_criteria F μ (A μ) hA h0 heq hevent hs⟩


/-- All classified original periodic orbits eventually lie in every fixed
open neighborhood of zero. The genuine small turn is identified with the
classified orbit by the uniqueness clause of the section bridge. -/
lemma classifiedOrbits_eventually_contained
    (F : ℝ × ℂ → ℂ) (ω ε₀ ρ δ₀ C₀ : ℝ)
    (P Q : ℝ × ℝ → ℝ) (ε δ C : ℝ) (ψ : ℝ → ℝ)
    (σ : ℝ) (U : Set ℂ) (h : SourceHypotheses F ω)
    (hε₀ : 0 < ε₀) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hret : ReturnData F ω ε₀ ρ δ₀ C₀ P Q)
    (hbr : BranchDescription F P Q ε₀ δ₀ ε δ C ψ)
    (hbridge : OrbitFixedPointBridge F P ε δ σ)
    (hlift : ∀ μ : ℝ, |μ| < ε → ∀ Γ : Set ℂ,
      IsPeriodicOrbit (fun z => F (μ,z)) Γ → Γ ⊆ U →
      ∃ Δ : Set ℂ, IsPeriodicOrbit (fun w => transformedField F (μ,w)) Δ ∧
        Δ ⊆ Metric.ball 0 σ ∧ Γ = coordinate F μ '' Δ)
    (V : Set ℂ) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V) :
    ∃ ζ > 0, ∀ μ : ℝ, |μ| < min ε ζ →
      ∀ Γ : Set ℂ, IsPeriodicOrbit (fun z => F (μ,z)) Γ → Γ ⊆ U → Γ ⊆ V := by
  obtain ⟨ηV, hηV, b, hb, hηVε₀, hbρ, hmap⟩ :=
    uniform_coordinate_small F hε₀ hρ hret.coordinates V hV hV0
  obtain ⟨ηT, hηT, τ, hτ, _, hperiod⟩ :=
    smallFixedReturn_period F ω ε₀ ρ δ₀ C₀ P Q h hε₀ hρ hret
      1 (min σ b) (by norm_num) (lt_min hσ hb)
  obtain ⟨ζr, hζr, hsmall⟩ :=
    branchFixedRadii_small F P Q ε₀ δ₀ ε δ C ψ hbr (min δ₀ τ)
      (lt_min (hbr.2.2.1.trans_le hbr.2.2.2.1) hτ)
  let ζ := min ηV (min ηT ζr)
  refine ⟨ζ, lt_min hηV (lt_min hηT hζr), ?_⟩
  intro μ hμ Γ hΓ hΓU
  have hμε : |μ| < ε := hμ.trans_le (min_le_left _ _)
  have hμζ : |μ| < ζ := hμ.trans_le (min_le_right _ _)
  have hμV : |μ| < ηV := hμζ.trans_le (min_le_left _ _)
  have hμT : |μ| < ηT := (hμζ.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hμr : |μ| < ζr := (hμζ.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  obtain ⟨Δ, hΔ, hΔσ, htrace⟩ := hlift μ hμε Γ hΓ hΓU
  obtain ⟨r, hr, hrΔ, hfix⟩ := (hbridge μ hμε).1 Δ hΔ hΔσ
  have hrt : r < min δ₀ τ := hsmall μ r (lt_min hμε hμr) hr hfix
  obtain ⟨Λ, T, hT, hrΛ, hΛsmall, _, _⟩ := hperiod μ r hμT hr.1 hrt hfix
  have hΛ : IsPeriodicOrbit (fun w => transformedField F (μ,w)) Λ :=
    leastPeriodOrbit_isPeriodicOrbit hT
  have hΛσ : Λ ⊆ Metric.ball 0 σ :=
    hΛsmall.trans (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨Ξ, _, huniq⟩ := (hbridge μ hμε).2 r hr hfix
  have heq : Δ = Λ := (huniq Δ ⟨hΔ, hrΔ, hΔσ⟩).trans
    (huniq Λ ⟨hΛ, hrΛ, hΛσ⟩).symm
  rw [htrace, heq]
  rintro x ⟨w, hw, rfl⟩
  apply hmap μ w hμV
  have hwsmall : ‖w‖ < min ρ (min σ b) := by simpa using hΛsmall hw
  exact hwsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))

open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch12.StabilityDefinitions

/-- The classification, least-period limit, and strict equilibrium conclusions
hold on one common smooth original-state domain. This proper subset still
leaves the two continuous-time orbital stability conclusions to prove. -/
theorem commonDomainGeometryAndPeriods (branch : PeriodicBranch)
    (F : ℝ × ℂ → ℂ) (ω : ℝ) (h : SourceHypotheses F ω) :
    ∃ ε > 0, ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧
    ∃ A : ℝ → _root_.D13Unified.AutonomousODE ℂ,
      (∀ μ : ℝ, |μ| < ε → (A μ).domain = U ∧
        (∀ z ∈ U, autonomousEvalValue (A μ) z = F (μ, z))) ∧
      (∀ μ : ℝ, |μ| < ε →
        ∃ hF : ContDiffOn ℝ 1 (autonomousEvalValue (A μ)) (A μ).domain,
        ∃ h0 : (0 : ℂ) ∈ (A μ).domain,
        ∃ heq : autonomousEvalValue (A μ) 0 = 0,
          (spectralReal F μ < 0 → locallyExponentiallyStableValue (A μ) hF h0 heq) ∧
          (0 < spectralReal F μ → unstableValue (A μ) hF h0 heq) ∧
          ((∃ Γ : Set ℂ, IsPeriodicOrbit (fun z => F (μ,z)) Γ ∧ Γ ⊆ U) ↔
            spectralReal F μ * firstLyapunovCoefficient F < 0) ∧
          (∀ Γ Δ : Set ℂ, IsPeriodicOrbit (fun z => F (μ,z)) Γ → Γ ⊆ U →
            IsPeriodicOrbit (fun z => F (μ,z)) Δ → Δ ⊆ U → Γ = Δ)) ∧
      (∀ κ > 0, ∃ ζ > 0, ∀ μ : ℝ, |μ| < min ε ζ →
        ∀ Γ : Set ℂ, IsPeriodicOrbit (fun z => F (μ,z)) Γ → Γ ⊆ U →
          ∃ T : ℝ, LeastPeriodOrbit (fun z => F (μ,z)) Γ T ∧
            |T - turnAngle / ω| < κ) := by
  obtain ⟨ε₀, hε₀, ρ, hρ, δ₀, hδ₀, C₀, hC₀, P, Q, hret,
    εb, δ, C, ψ, hbr, _, σ, hσ, _, hbridge, hclass, hOrig⟩ := branch F ω h
  obtain ⟨Uo, hUo, h0Uo, hOrig⟩ := hOrig
  have hlift (μ : ℝ) (hμ : |μ| < εb) (Γ : Set ℂ)
      (hΓ : IsPeriodicOrbit (fun z => F (μ,z)) Γ) (hΓU : Γ ⊆ Uo) :
      ∃ Δ : Set ℂ, IsPeriodicOrbit (fun w => transformedField F (μ,w)) Δ ∧
        Δ ⊆ Metric.ball 0 σ ∧ Γ = coordinate F μ '' Δ :=
    (hOrig μ hμ).2.2 Γ hΓ hΓU
  obtain ⟨εe, hεe, V, hV, h0V, hrestrict⟩ := sourceEquilibriaOn F ω h
  obtain ⟨ζV, hζV, hcontain⟩ := classifiedOrbits_eventually_contained
    F ω ε₀ ρ δ₀ C₀ P Q εb δ C ψ σ Uo h hε₀ hρ hσ hret hbr hbridge hlift V hV h0V
  let ε := min εb (min εe ζV)
  have hε : 0 < ε := lt_min hbr.1 (lt_min hεe hζV)
  have hεb : ε ≤ εb := min_le_left _ _
  have hεe' : ε ≤ εe := (min_le_right _ _).trans (min_le_left _ _)
  have hεV : ε ≤ ζV := (min_le_right _ _).trans (min_le_right _ _)
  let U := Uo ∩ V
  have hU : IsOpen U := hUo.inter hV
  have h0U : (0 : ℂ) ∈ U := ⟨h0Uo, h0V⟩
  obtain ⟨A, heval, hequil⟩ := hrestrict U hU h0U inter_subset_right
  refine ⟨ε, hε, U, hU, h0U, A, (fun μ hμ => heval μ (hμ.trans_le hεe')), ?_, ?_⟩
  · intro μ hμ
    have hμb : |μ| < εb := hμ.trans_le hεb
    obtain ⟨hF, h0, heq, hstable, hunstable⟩ := hequil μ (hμ.trans_le hεe')
    refine ⟨hF, h0, heq, hstable, hunstable, ?_, ?_⟩
    · constructor
      · rintro ⟨Γ, hΓ, hΓU⟩
        exact (hOrig μ hμb).1.mp ⟨Γ, hΓ, hΓU.trans inter_subset_left⟩
      · intro hsign
        obtain ⟨Γ, hΓ, hΓUo⟩ := (hOrig μ hμb).1.mpr hsign
        have hΓV := hcontain μ (lt_min hμb (hμ.trans_le hεV)) Γ hΓ hΓUo
        exact ⟨Γ, hΓ, subset_inter hΓUo hΓV⟩
    · intro Γ Δ hΓ hΓU hΔ hΔU
      exact (hOrig μ hμb).2.1 Γ Δ hΓ (hΓU.trans inter_subset_left)
        hΔ (hΔU.trans inter_subset_left)
  · apply classifiedOrbits_period_limit F ω ε₀ ρ δ₀ C₀ P Q εb δ C ψ
      ε hεb σ U h hε₀ hρ hσ hret hbr
    · intro μ hμ Γ hΓ hΓU
      have hμb := hμ.trans_le hεb
      obtain ⟨Δ, hΔ, hΔσ, htrace⟩ := hlift μ hμb Γ hΓ (hΓU.trans inter_subset_left)
      obtain ⟨r, hr, hrΔ, hfix⟩ := (hbridge μ hμb).1 Δ hΔ hΔσ
      exact ⟨Δ, r, hΔ, hΔσ, htrace, hr, hrΔ, hfix⟩
    · intro μ hμ Γ Δ hΓ hΓσ hΔ hΔσ
      exact (hclass μ (hμ.trans_le hεb)).2 Γ Δ hΓ hΓσ hΔ hΔσ


open scoped NNReal

/-- Actual returns from all sufficiently small section radii can be represented
by turns in any prescribed ball of local uniqueness, uniformly in the parameter.
The confinement radius in the original ReturnData need not be this small. -/
lemma confinedReturnTurns (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ)
    (P Q : ℝ × ℝ → ℝ) (h : SourceHypotheses F ω)
    (hε : 0 < ε) (hret : ReturnData F ω ε ρ δ C P Q)
    (η₀ R : ℝ) (hη₀ : 0 < η₀) (hR : 0 < R)
    (hlocal : ∀ μ : ℝ, |μ| < η₀ → ∃ K : ℝ≥0,
      LipschitzOnWith K (fun w => transformedField F (μ,w)) (Metric.closedBall 0 R)) :
    ∃ η > 0, ∃ τ > 0, η ≤ ε ∧ η ≤ η₀ ∧
      ∀ μ r : ℝ, |μ| < η → 0 < r → r < min δ τ →
        FullAngularTurn F ω μ r (P (r, μ)) R := by
  have hs : Specs.D13Unified.Ch16.HopfPeriodicOrbitBridge.SourceHypotheses F ω :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  obtain ⟨εs, hεs, τ, hτ, hturns⟩ :=
    HopfPeriodicOrbitBridge.sourceSmallTurns F ω hs R hR
  let η := min ε (min η₀ εs)
  have hη : 0 < η := lt_min hε (lt_min hη₀ hεs)
  refine ⟨η, hη, τ, hτ, min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro μ r hμ hr hrt
  have hμε : |μ| < ε := hμ.trans_le (min_le_left _ _)
  have hμ₀ : |μ| < η₀ := hμ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hμs : |μ| < εs := hμ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨p, hp⟩ := hturns μ r hμs hr (hrt.trans_le (min_le_right _ _))
  obtain ⟨K, hK⟩ := hlocal μ hμ₀
  have heq : p = P (r, μ) := HopfPeriodicOrbitBridge.fullAngularTurn_endpoint_eq_confined
    hK le_rfl hp (hret.turn μ r hμε hr (hrt.trans_le (min_le_left _ _)))
  rwa [heq] at hp

lemma confinedReturnTurns_eventually {F : ℝ × ℂ → ℂ} {ω μ δ τ R b : ℝ}
    {P : ℝ × ℝ → ℝ} (hb : b ∈ Ioo 0 (min δ τ))
    (hturns : ∀ r : ℝ, 0 < r → r < min δ τ →
      FullAngularTurn F ω μ r (P (r,μ)) R) :
    ∀ᶠ r : ℝ in nhds b, FullAngularTurn F ω μ r (P (r,μ)) R :=
  Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hb) (fun r hr => hturns r hr.1 hr.2)

end D13Unified.Ch16.PlanarHopf


noncomputable section
open scoped NNReal
namespace D13Unified.Ch16.PlanarHopf
open Set Filter
open Specs.D13Unified.Ch16
open CubicHomologicalElimination CubicNormalForm HopfReturnExpansion HopfPeriodicBranch
open Specs.D13Unified.Ch01.AutonomousParameters

/-- A common actual normal-coordinate ODE on an arbitrarily small ball,
with source-derived smoothness and a Lipschitz constant on its closure. -/
lemma sourceNormalEquationData (F : ℝ × ℂ → ℂ) (ω : ℝ) (h : SourceHypotheses F ω)
    (b : ℝ) (hb : 0 < b) :
    ∃ η > 0, ∃ R > 0, R ≤ b ∧
    ∃ A : ℝ → _root_.D13Unified.AutonomousODE ℂ,
      (∀ μ, (A μ).domain = Metric.ball 0 R) ∧
      ∀ μ, |μ| < η →
        ContDiffOn ℝ 1 (autonomousEvalValue (A μ)) (A μ).domain ∧
        (∀ w ∈ (A μ).domain, autonomousEvalValue (A μ) w = transformedField F (μ,w)) ∧
        ∃ K : ℝ≥0, LipschitzOnWith K (fun w => transformedField F (μ,w))
          (Metric.closedBall 0 R) := by
  classical
  have hs : Specs.D13Unified.Ch16.HopfPeriodicOrbitBridge.SourceHypotheses F ω :=
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  obtain ⟨εl, hεl, Rl, hRl, hlocal⟩ := HopfPeriodicOrbitBridge.sourceLocalLipschitz F ω hs
  obtain ⟨_, _, εn, hεn, Rn, hRn, Cn, _, _, hbounds, _⟩ :=
    CubicNormalForm.normalForm F ω h.1 h.2.1 h.2.2.1 h.2.2.2.1
  let η := min εl εn
  let R := min b (min Rl (Rn / 2))
  have hη : 0 < η := lt_min hεl hεn
  have hR : 0 < R := lt_min hb (lt_min hRl (by positivity))
  have hRRl : R ≤ Rl := (min_le_right _ _).trans (min_le_left _ _)
  have hRRn : R < Rn := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hslice (μ : ℝ) (hμ : |μ| < η) :
      ContDiffOn ℝ 1 (fun w => transformedField F (μ,w)) (Metric.ball 0 R) := by
    intro w hw
    have hwR : ‖w‖ < R := by simpa using hw
    have hb := hbounds (μ,w) ⟨hμ.trans_le (min_le_right _ _), hwR.trans hRRn⟩
    exact (hb.2.2.1.of_le (by norm_num)).contDiffWithinAt
  let f : ℝ → ℂ → ℂ := fun μ w => if |μ| < η then transformedField F (μ,w) else 0
  have hf (μ : ℝ) : ContinuousOn (f μ) (Metric.ball 0 R) := by
    by_cases hμ : |μ| < η
    · simpa only [f, ite_eq_left hμ] using (hslice μ hμ).continuousOn
    · simp only [f, ite_eq_right hμ]
      exact continuousOn_const
  let A : ℝ → _root_.D13Unified.AutonomousODE ℂ := fun μ =>
    equationOn (f μ) (Metric.ball 0 R) Metric.isOpen_ball (hf μ)
  have heval (μ : ℝ) (hμ : |μ| < η) (w : ℂ) (hw : w ∈ Metric.ball 0 R) :
      autonomousEvalValue (A μ) w = transformedField F (μ,w) := by
    simp only [A, equationOn, autonomousEvalValue, hw, dite_true, f, ite_eq_left hμ]
  refine ⟨η, hη, R, hR, min_le_left _ _, A, (fun μ => rfl), ?_⟩
  intro μ hμ
  refine ⟨(hslice μ hμ).congr (heval μ hμ), heval μ hμ, ?_⟩
  obtain ⟨K, hK⟩ := (hlocal μ (hμ.trans_le (min_le_left _ _))).2
  exact ⟨K, hK.mono (Metric.closedBall_subset_closedBall hRRl)⟩

end D13Unified.Ch16.PlanarHopf


noncomputable section
namespace D13Unified.Ch16.PlanarHopf
open Set Filter
open Specs.D13Unified.Ch16
open CubicHomologicalElimination CubicNormalForm HopfReturnExpansion HopfPeriodicBranch
open Specs.D13Unified.Ch16.PlanarHopf

lemma leastPeriodOrbit_compact {f : ℂ → ℂ} {Γ : Set ℂ} {T : ℝ}
    (hT : LeastPeriodOrbit f Γ T) : IsCompact Γ := by
  obtain ⟨hT, z, hper, hsol, _, htrace, _⟩ := hT
  rw [htrace]
  exact hper.compact_of_continuous (ne_of_gt hT)
    ((show Differentiable ℝ z from fun t => (hsol t).differentiableAt).continuous)

lemma leastPeriodOrbit_nonempty {f : ℂ → ℂ} {Γ : Set ℂ} {T : ℝ}
    (hT : LeastPeriodOrbit f Γ T) : Γ.Nonempty := by
  obtain ⟨_, z, _, _, _, htrace, _⟩ := hT
  rw [htrace]
  exact ⟨z 0, mem_range_self 0⟩

/-- Every contained original orbit has the same genuine small least-period
representative in normal coordinates. Both its entire trace and its positive
fixed radius can be required to meet arbitrary prescribed small cutoffs. -/
lemma classifiedOrbits_small_representatives
    (F : ℝ × ℂ → ℂ) (ω ε₀ ρ δ₀ C₀ : ℝ)
    (P Q : ℝ × ℝ → ℝ) (ε δ C : ℝ) (ψ : ℝ → ℝ)
    (σ : ℝ) (U : Set ℂ) (h : SourceHypotheses F ω)
    (hε₀ : 0 < ε₀) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hret : ReturnData F ω ε₀ ρ δ₀ C₀ P Q)
    (hbr : BranchDescription F P Q ε₀ δ₀ ε δ C ψ)
    (hbridge : OrbitFixedPointBridge F P ε δ σ)
    (hlift : ∀ μ : ℝ, |μ| < ε → ∀ Γ : Set ℂ,
      IsPeriodicOrbit (fun z => F (μ,z)) Γ → Γ ⊆ U →
      ∃ Δ : Set ℂ, IsPeriodicOrbit (fun w => transformedField F (μ,w)) Δ ∧
        Δ ⊆ Metric.ball 0 σ ∧ Γ = coordinate F μ '' Δ)
    (b δcut : ℝ) (hb : 0 < b) (hδcut : 0 < δcut) :
    ∃ η > 0, η ≤ ε ∧ ∀ μ : ℝ, |μ| < η →
      ∀ Γ : Set ℂ, IsPeriodicOrbit (fun z => F (μ,z)) Γ → Γ ⊆ U →
        ∃ (Δ : Set ℂ) (r T : ℝ),
          LeastPeriodOrbit (fun w => transformedField F (μ,w)) Δ T ∧
          Δ ⊆ Metric.ball 0 (min σ b) ∧ r ∈ Ioo 0 δ ∧ r < δcut ∧
          (r : ℂ) ∈ Δ ∧ P (r,μ) = r ∧ Γ = coordinate F μ '' Δ := by
  obtain ⟨ηT, hηT, τ, hτ, _, hperiod⟩ :=
    smallFixedReturn_period F ω ε₀ ρ δ₀ C₀ P Q h hε₀ hρ hret
      1 (min σ b) (by norm_num) (lt_min hσ hb)
  obtain ⟨ζr, hζr, hsmall⟩ :=
    branchFixedRadii_small F P Q ε₀ δ₀ ε δ C ψ hbr (min δcut (min δ₀ τ))
      (lt_min hδcut (lt_min (hbr.2.2.1.trans_le hbr.2.2.2.1) hτ))
  let η := min ε (min ηT ζr)
  refine ⟨η, lt_min hbr.1 (lt_min hηT hζr), min_le_left _ _, ?_⟩
  intro μ hμ Γ hΓ hΓU
  have hμε : |μ| < ε := hμ.trans_le (min_le_left _ _)
  have hμrest : |μ| < min ηT ζr := hμ.trans_le (min_le_right _ _)
  have hμT : |μ| < ηT := hμrest.trans_le (min_le_left _ _)
  have hμr : |μ| < ζr := hμrest.trans_le (min_le_right _ _)
  obtain ⟨Δ, hΔ, hΔσ, htrace⟩ := hlift μ hμε Γ hΓ hΓU
  obtain ⟨r, hr, hrΔ, hfix⟩ := (hbridge μ hμε).1 Δ hΔ hΔσ
  have hrt : r < min δcut (min δ₀ τ) := hsmall μ r (lt_min hμε hμr) hr hfix
  obtain ⟨Λ, T, hT, hrΛ, hΛsmall, _, _⟩ :=
    hperiod μ r hμT hr.1 (hrt.trans_le (min_le_right _ _)) hfix
  have hΛ : IsPeriodicOrbit (fun w => transformedField F (μ,w)) Λ :=
    leastPeriodOrbit_isPeriodicOrbit hT
  have hΛσ : Λ ⊆ Metric.ball 0 σ :=
    hΛsmall.trans (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨Ξ, _, huniq⟩ := (hbridge μ hμε).2 r hr hfix
  have heq : Δ = Λ := (huniq Δ ⟨hΔ, hrΔ, hΔσ⟩).trans
    (huniq Λ ⟨hΛ, hrΛ, hΛσ⟩).symm
  refine ⟨Λ, r, T, hT, ?_, hr, hrt.trans_le (min_le_left _ _), hrΛ, hfix, ?_⟩
  · exact hΛsmall.trans (Metric.ball_subset_ball (min_le_right _ _))
  · simpa only [heq] using htrace

end D13Unified.Ch16.PlanarHopf


noncomputable section
open Set Filter
open scoped Topology NNReal
namespace D13Unified.Ch16.PlanarHopf
open D13Unified.Ch06.StateDerivative D13Unified.Ch11.Orbits
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Specs.D13Unified.Ch14.OrbitalDefinitions
open Specs.D13Unified.Ch14.ReturnMap
open Specs.D13Unified.Ch16.HopfPeriodicOrbitBridge

/-- An all-time solution contained in the actual domain identifies the maximal
canonical solution and forces its recorded interval to be all of ℝ. -/
lemma complete_solution_eq_flow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : AutonomousODE E)
    (hA : ContDiffOn ℝ 1 A.eval A.domain) (z : ℝ → E)
    (hstay : ∀ t, z t ∈ A.domain)
    (hsol : ∀ t, HasDerivAt z (A.eval (z t)) t) :
    IsComplete A (z 0) ∧ ∀ t, flow A t (z 0) = z t := by
  let J : OpenTimeInterval := ⟨⟨univ, univ_nonempty, ordConnected_univ⟩, isOpen_univ⟩
  have hdiff : Differentiable ℝ z := fun t => (hsol t).differentiableAt
  have hcont : Continuous z := hdiff.continuous
  have hcder : Continuous (deriv z) := by
    have he : deriv z = fun t => A.eval (z t) := funext fun t => (hsol t).deriv
    rw [he]
    exact hA.continuousOn.comp_continuous hcont hstay
  have hc : ContDiff ℝ 1 z := contDiff_one_iff_deriv.mpr ⟨hdiff, hcder⟩
  have hz : classicalIVPOnValue A.toODE J z 0 (z 0) := by
    refine ⟨⟨hc.contDiffOn, fun t _ => hstay t, ?_⟩, mem_univ _, rfl⟩
    intro t _
    simpa only [AutonomousODE.toODE_eval] using hsol t
  have h := (ODE.canonical_solution A.toODE
    (A.locallyLipschitzInState_of_contDiffOn hA) 0 (z 0) (hstay 0)).2.2.2.2.2.1 J z hz
  exact ⟨Subset.antisymm (subset_univ _) h.1, fun t => h.2 (mem_univ t)⟩

/-- A genuine complete periodic solution becomes exactly the canonical orbit,
with every recorded maximal time available. -/
lemma periodic_solution_canonical (A : AutonomousODE ℂ)
    (hA : ContDiffOn ℝ 1 A.eval A.domain) (V : ℂ → ℂ) {z : ℝ → ℂ} {T : ℝ}
    (hz : IsPeriodicSolution V z T) (hstay : ∀ t, z t ∈ A.domain)
    (heval : ∀ t, A.eval (z t) = V (z t)) :
    IsComplete A (z 0) ∧ Function.Periodic (fun t => flow A t (z 0)) T ∧
      ¬ IsConstant A (z 0) ∧ orbit A (z 0) = range z := by
  obtain ⟨hc, he⟩ := complete_solution_eq_flow A hA z hstay
    (fun t => by rw [heval t]; exact hz.2.2.1 t)
  refine ⟨hc, ?_, ?_, ?_⟩
  · intro t
    change flow A (t + T) (z 0) = flow A t (z 0)
    rw [he, he]
    exact hz.2.1 t
  · intro hconst
    obtain ⟨s,t,hne⟩ := hz.2.2.2
    apply hne
    have hs : s ∈ (flowInterval A (z 0)).carrier := by rw [hc]; trivial
    have ht : t ∈ (flowInterval A (z 0)).carrier := by rw [hc]; trivial
    rw [← he s, hconst s hs, ← hconst t ht, he t]
  · unfold orbit
    change (flowInterval A (z 0)).carrier = univ at hc
    rw [hc, image_univ]
    exact congrArg range (funext he)

/-- Angular and affine first returns coincide by uniqueness on their overlap.
Only the angular segment is required to be confined in the Lipschitz ball. -/
lemma angularTurn_eq_firstReturn {F : ℝ × ℂ → ℂ} {ω μ s q R : ℝ} {K : ℝ≥0}
    (A : AutonomousODE ℂ) (hA : ContDiffOn ℝ 1 A.eval A.domain)
    (heval : ∀ z ∈ A.domain, A.eval z =
      Specs.D13Unified.Ch16.CubicNormalForm.transformedField F (μ,z))
    (hV : LipschitzOnWith K
      (fun z => Specs.D13Unified.Ch16.CubicNormalForm.transformedField F (μ,z))
      (Metric.closedBall 0 R))
    (hturn : Specs.D13Unified.Ch16.HopfReturnExpansion.FullAngularTurn F ω μ s q R)
    {b : ℂ} {T : ℝ} (ℓ : ℂ →L[ℝ] ℝ) (d : FirstReturnData 1 A b T ℓ)
    {v : ℓ.ker} (hv : v ∈ d.P.source) (hstart : b + (v : ℂ) = (s : ℂ))
    (hpositive : ∀ w ∈ d.sectionSet,
      Specs.D13Unified.Ch16.HopfReturnExpansion.positiveRay (b + (w : ℂ)))
    (hend : (q : ℂ) ∈ (fun w : ℓ.ker => b + (w : ℂ)) '' d.sectionSet) :
    b + (d.P v : ℂ) = (q : ℂ) := by
  obtain ⟨u, clock, z, hu0, huT, hc0, hTc, hmono, hbij, hang,
    hz0, hzT, hphys, hfirst⟩ := hturn
  let U := clock Specs.D13Unified.Ch16.HopfReturnExpansion.turnAngle
  have hτ : 0 < d.τ v := d.time_positive v hv
  have hS : 0 ≤ min U (d.τ v) := le_min hTc.le hτ.le
  have hstartdom : b + (v : ℂ) ∈ A.domain :=
    d.section_domain v (d.source_section hv)
  have hflow := Ch06.StateDerivative.flow_ivp A hA hstartdom
  have hτT : d.τ v < T + d.δ := (d.time_near v hv).2
  have hdI (t : ℝ) (ht : t ∈ Icc 0 (min U (d.τ v))) :
      t ∈ (flowInterval A (b + (v : ℂ))).carrier :=
    (d.flow_domain v hv t ⟨ht.1, (ht.2.trans (min_le_right _ _)).trans hτT.le⟩).2
  have hcmp : EqOn (fun t => flow A t (b + (v : ℂ))) z
      (Icc 0 (min U (d.τ v))) := by
    apply D13Unified.Ch16.HopfPeriodicOrbitBridge.compactSegments_eq_confined hS hV
    · intro t ht
      exact ((hphys t ⟨ht.1,ht.2.trans (min_le_left _ _)⟩).2).mono
        (Icc_subset_Icc_right (min_le_left _ _))
    · intro t ht
      exact (hphys t ⟨ht.1,ht.2.trans (min_le_left _ _)⟩).1
    · intro t ht
      have hh := hflow.1.2.2 t (hdI t ht)
      have hs := hflow.1.2.1 t (hdI t ht)
      rw [AutonomousODE.toODE_eval, heval _ hs] at hh
      exact hh.hasDerivWithinAt
    · exact (Ch11.Flow.flow_zero A hA _ hstartdom).2.trans (hstart.trans hz0.symm)
  have hclosed : U = d.τ v ∧ EqOn z (fun t => flow A t (b + (v : ℂ)))
      (Icc 0 U) := by
    apply D13Unified.Ch16.HopfPeriodicOrbitBridge.firstReturnSegments_eq hTc hτ
      (fun t ht => (hcmp ht).symm)
    · exact hzT ▸ hend
    · rw [d.map_formula v hv]
      exact ⟨d.P v,d.target_section (d.P.mapsTo hv),rfl⟩
    · intro t ht hh
      apply hfirst t ht
      obtain ⟨w,hw,he⟩ := hh
      rw [← he]
      exact hpositive w hw
    · intro t ht
      exact d.first_return v hv t ht.1 ht.2
  rw [← d.map_formula v hv, ← hclosed.1]
  exact (hclosed.2 ⟨hTc.le,le_rfl⟩).symm.trans hzT

/-- Local identification with the signed-radius return map identifies the
entire derivative on the real transverse line, not just a named multiplier. -/
lemma real_section_derivative {A : AutonomousODE ℂ} {b T : ℝ}
    (d : FirstReturnData 1 A (b : ℂ) T Complex.imCLM)
    (P : ℝ → ℝ) (m : ℝ) (hP : HasDerivAt P m b)
    (hmap : ∀ᶠ v : Complex.imCLM.ker in nhds 0,
      (d.P v : ℂ) = ((P (b + (v : ℂ).re) - b : ℝ) : ℂ)) :
    (fderiv ℝ (d.P : Complex.imCLM.ker → Complex.imCLM.ker) 0).toLinearMap =
      m • LinearMap.id := by
  have hcd : ContDiffAt ℝ 1 (d.P : Complex.imCLM.ker → Complex.imCLM.ker) 0 :=
    d.map_regular.contDiffAt (d.P.open_source.mem_nhds d.source_zero)
  have hDP := (hcd.differentiableAt one_ne_zero).hasFDerivAt
  ext v
  have hline : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).smul_const v using 1 <;> simp
  have hdP : HasFDerivAt (fun w : Complex.imCLM.ker => (d.P w : ℂ))
      (Complex.imCLM.ker.subtypeL.comp (fderiv ℝ (d.P : Complex.imCLM.ker → Complex.imCLM.ker) 0))
      ((fun t : ℝ => t • v) 0) := by
    convert! Complex.imCLM.ker.subtypeL.hasFDerivAt.comp 0 hDP using 1 <;> simp
  have hd := hdP.comp_hasDerivAt 0 hline
  have hreal : HasDerivAt (fun t : ℝ => P (b + t * (v : ℂ).re) - b)
      (m * (v : ℂ).re) 0 := by
    have hin : HasDerivAt (fun t : ℝ => b + t * (v : ℂ).re) (v : ℂ).re 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v : ℂ).re).const_add b
    have hP' : HasDerivAt P m (b + 0 * (v : ℂ).re) := by simpa using hP
    simpa using (hP'.comp 0 hin).sub_const b
  have hrhs := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hreal
  have he : (fun t : ℝ => ((d.P (t • v)) : ℂ)) =ᶠ[nhds 0]
      (fun t : ℝ => ((P (b + t * (v : ℂ).re) - b : ℝ) : ℂ)) := by
    have ht : Tendsto (fun t : ℝ => t • v) (nhds 0) (nhds 0) := by
      convert! (continuous_id.smul (continuous_const (y := v))).continuousAt.tendsto (x := (0 : ℝ)) using 1 <;> simp
    filter_upwards [ht.eventually hmap] with t ht
    convert! ht using 1 <;> simp
  have hvim : (v : ℂ).im = 0 := by exact v.property
  have hval := (hd.congr_of_eventuallyEq he.symm).unique hrhs
  change ((fderiv ℝ (d.P : Complex.imCLM.ker → Complex.imCLM.ker) 0) v : ℂ) =
    m • (v : ℂ)
  calc
    _ = ((m * (v : ℂ).re : ℝ) : ℂ) := by convert! hval using 1 <;> simp
    _ = m • (v : ℂ) := by apply Complex.ext <;> simp [hvim]

/-- Inclusion of the real coordinate into the actual affine-section kernel. -/
def realSection : ℝ →L[ℝ] Complex.imCLM.ker :=
  Complex.ofRealCLM.codRestrict Complex.imCLM.ker (fun r => by simp)

/-- The derivative of the actual Ch14 return is the radial multiplier of a
genuine angular return. Openness of the affine section supplies the endpoint
condition; no continuity of an independently chosen physical clock is assumed. -/
lemma firstReturn_radial_derivative {F : ℝ × ℂ → ℂ} {ω μ b T R : ℝ} {K : ℝ≥0}
    (A : AutonomousODE ℂ) (hA : ContDiffOn ℝ 1 A.eval A.domain)
    (heval : ∀ z ∈ A.domain, A.eval z =
      Specs.D13Unified.Ch16.CubicNormalForm.transformedField F (μ,z))
    (hV : LipschitzOnWith K
      (fun z => Specs.D13Unified.Ch16.CubicNormalForm.transformedField F (μ,z))
      (Metric.closedBall 0 R))
    (d : FirstReturnData 1 A (b : ℂ) T Complex.imCLM)
    (hpositive : ∀ w ∈ d.sectionSet,
      Specs.D13Unified.Ch16.HopfReturnExpansion.positiveRay ((b : ℂ) + (w : ℂ)))
    (P : ℝ → ℝ) (m : ℝ) (hP : HasDerivAt P m b) (hfix : P b = b)
    (hturns : ∀ᶠ s : ℝ in nhds b,
      Specs.D13Unified.Ch16.HopfReturnExpansion.FullAngularTurn F ω μ s (P s) R) :
    (fderiv ℝ (d.P : Complex.imCLM.ker → Complex.imCLM.ker) 0).toLinearMap =
      m • LinearMap.id := by
  apply real_section_derivative d P m hP
  have ht : Tendsto (fun v : Complex.imCLM.ker => b + (v : ℂ).re) (nhds 0) (nhds b) := by
    convert! ((continuous_const (y := b)).add
      (Complex.continuous_re.comp continuous_subtype_val)).continuousAt.tendsto
      (x := (0 : Complex.imCLM.ker)) using 1 <;> simp
  have hPc : Tendsto (fun v : Complex.imCLM.ker => P (b + (v : ℂ).re))
      (nhds 0) (nhds (P b)) := hP.continuousAt.tendsto.comp ht
  have hc : Tendsto (fun v : Complex.imCLM.ker =>
      realSection (P (b + (v : ℂ).re) - b)) (nhds 0) (nhds 0) := by
    convert! realSection.continuous.continuousAt.tendsto.comp
      (hPc.sub (tendsto_const_nhds (x := b))) using 1 <;> simp [hfix]
    congr 1
  have hend : ∀ᶠ v : Complex.imCLM.ker in nhds 0,
      realSection (P (b + (v : ℂ).re) - b) ∈ d.sectionSet :=
    hc.eventually (d.section_open.mem_nhds d.section_zero)
  filter_upwards [d.P.open_source.mem_nhds d.source_zero, ht.eventually hturns, hend]
    with v hv hturn hend
  have hvim : (v : ℂ).im = 0 := by exact v.property
  have hstart : (b : ℂ) + (v : ℂ) = ((b + (v : ℂ).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hvim]
  have hh := angularTurn_eq_firstReturn A hA heval hV hturn Complex.imCLM d hv
    hstart hpositive
    (show ((P (b + (v : ℂ).re) : ℝ) : ℂ) ∈
      (fun w : Complex.imCLM.ker => (b : ℂ) + (w : ℂ)) '' d.sectionSet from
      ⟨realSection (P (b + (v : ℂ).re) - b),hend,by
        change (b : ℂ) + ((P (b + (v : ℂ).re) - b : ℝ) : ℂ) = _
        push_cast
        ring⟩)
  have hsub := congrArg (fun z : ℂ => z - (b : ℂ)) hh
  simpa only [add_sub_cancel_left, ← Complex.ofReal_sub] using hsub

/-- The accepted Ch14 theorems apply directly when the actual affine-section
derivative is a scalar. This keeps the original flow, orbit and time domains. -/
lemma orbital_criteria_of_scalar_return {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (k : ℕ) (hk : 1 ≤ k) (A : AutonomousODE E)
    (hA : ContDiffOn ℝ k A.eval A.domain) {p : E} (hp : p ∈ A.domain)
    {T : ℝ} (hT : 0 < T) (hc : IsComplete A p)
    (hper : Function.Periodic (fun t => flow A t p) T)
    (hmin : ∀ R : ℝ, 0 < R → Function.Periodic (fun t => flow A t p) R → T ≤ R)
    (hnc : ¬ IsConstant A p) (ℓ : E →L[ℝ] ℝ)
    (d : FirstReturnData k A p T ℓ)
    (hdim : Module.finrank ℝ ℓ.ker = 1) (m : ℝ)
    (hder : (fderiv ℝ (d.P : ℓ.ker → ℓ.ker) 0).toLinearMap = m • LinearMap.id)
    (hm : 0 < m) :
    (m < 1 → orbitalAsymptoticallyStableValue A (orbit A p)) ∧
      (1 < m → orbitalUnstableValue A (orbit A p)) := by
  let B := fderiv ℝ (d.P : ℓ.ker → ℓ.ker) 0
  let M := D13Unified.Ch08.MatrixPowerCriteria.complexify
    (LinearMap.toMatrix (Module.finBasis ℝ ℓ.ker) (Module.finBasis ℝ ℓ.ker) B.toLinearMap)
  haveI : NeZero (Module.finrank ℝ ℓ.ker) := ⟨by omega⟩
  have hM : M = algebraMap ℂ (D13Unified.Ch08.MatrixPowerCriteria.CMatrix
      (Module.finrank ℝ ℓ.ker)) (m : ℂ) :=
    D13Unified.Ch14.OrbitalInstability.complexify_scalar B hder
  have hσ : spectrum ℂ M = {(m : ℂ)} := by rw [hM]; exact spectrum.scalar_eq _
  constructor
  · intro hm1
    apply (D13Unified.Ch14.OrbitalStability.orbital_stability k hk A hA p hp T hT hc
      hper hmin hnc ℓ d ?_).2
    change D13Unified.Ch08.MatrixPowerCriteria.StrictSpectrum M
    intro z hz
    have hzμ : z = (m : ℂ) := by simpa only [hσ, mem_singleton_iff] using hz
    rw [hzμ]
    simpa only [Complex.norm_real, Real.norm_of_nonneg hm.le] using hm1
  · intro hm1
    apply (D13Unified.Ch14.OrbitalInstability.orbital_instability k hk A hA p hp T hT hc
      hper hmin hnc ℓ d ?_).2
    refine ⟨(m : ℂ), ?_, ?_⟩
    · exact (D13Unified.Ch08.MatrixPowerCriteria.eigenvalueBridge M _).mpr (by simp [hσ])
    · simpa only [Complex.norm_real, Real.norm_of_nonneg hm.le] using hm1

open Specs.D13Unified.Ch16.CubicNormalForm Specs.D13Unified.Ch16.HopfReturnExpansion
lemma angularTurn_transverse {F : ℝ × ℂ → ℂ} {ω μ b q R : ℝ}
    (hω : 0 < ω) (hturn : FullAngularTurn F ω μ b q R) :
    0 < b ∧ 0 < (transformedField F (μ,(b : ℂ))).im := by
  obtain ⟨u,clock,z,hu0,huT,hc0,hT,hmono,hbij,hang,hz0,hzT,hphys,hfirst⟩ := hturn
  have ht : (0 : ℝ) ∈ Icc 0 turnAngle := ⟨le_rfl, by unfold turnAngle; positivity⟩
  have hb : 0 < b := hu0 ▸ (hang 0 ht).1
  have hav : ω / 2 < angularVelocity F 0 b μ := hu0 ▸ (hang 0 ht).2.2.1
  have hid := D13Unified.Ch16.HopfReturnExpansion.polarVelocityIdentity F μ b 0 hb.ne'
  have hi := congrArg Complex.im hid
  have hfield : (transformedField F (μ,(b : ℂ))).im = b * angularVelocity F 0 b μ := by
    simpa [direction,polarPoint] using hi
  exact ⟨hb, hfield ▸ mul_pos hb (lt_trans (half_pos hω) hav)⟩
lemma real_section_finrank : Module.finrank ℝ Complex.imCLM.ker = 1 := by
  have hne : (Complex.imCLM : ℂ →ₗ[ℝ] ℝ) ≠ 0 := by
    intro h
    have hh := congrArg (fun f : ℂ →ₗ[ℝ] ℝ => f Complex.I) h
    simp at hh
  have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rw [Complex.finrank_real_complex] at hh
  omega

/-- A canonical periodic orbit in normal coordinates satisfies the exact
orbital conclusions from its genuine angular-return multiplier. -/
lemma normal_orbit_criteria {F : ℝ × ℂ → ℂ} {ω μ b T R : ℝ} {K : ℝ≥0}
    (A : AutonomousODE ℂ) (hA : ContDiffOn ℝ 1 A.eval A.domain)
    (heval : ∀ z ∈ A.domain, A.eval z =
      Specs.D13Unified.Ch16.CubicNormalForm.transformedField F (μ,z))
    (hV : LipschitzOnWith K
      (fun z => Specs.D13Unified.Ch16.CubicNormalForm.transformedField F (μ,z))
      (Metric.closedBall 0 R)) (hω : 0 < ω)
    (hbA : (b : ℂ) ∈ A.domain) (hT : 0 < T) (hc : IsComplete A (b : ℂ))
    (hper : Function.Periodic (fun t => flow A t (b : ℂ)) T)
    (hmin : ∀ S : ℝ, 0 < S → Function.Periodic (fun t => flow A t (b : ℂ)) S → T ≤ S)
    (hnc : ¬ IsConstant A (b : ℂ))
    (P : ℝ → ℝ) (m : ℝ) (hm : 0 < m) (hP : HasDerivAt P m b) (hfix : P b = b)
    (hturns : ∀ᶠ s : ℝ in nhds b,
      Specs.D13Unified.Ch16.HopfReturnExpansion.FullAngularTurn F ω μ s (P s) R) :
    (m < 1 → orbitalAsymptoticallyStableValue A (orbit A (b : ℂ))) ∧
      (1 < m → orbitalUnstableValue A (orbit A (b : ℂ))) := by
  obtain ⟨hb, htrans⟩ := angularTurn_transverse hω hturns.self_of_nhds
  have ha : Complex.imCLM (A.eval (b : ℂ)) ≠ 0 := by
    rw [heval _ hbA]
    exact ne_of_gt htrans
  let S : Set Complex.imCLM.ker := {v | 0 < b + (v : ℂ).re}
  have hS : IsOpen S := isOpen_lt continuous_const
    (continuous_const.add (Complex.continuous_re.comp continuous_subtype_val))
  have h0S : (0 : Complex.imCLM.ker) ∈ S := by
    change 0 < b + (0 : ℂ).re
    simpa using hb
  obtain ⟨d, hsub, _⟩ := D13Unified.Ch14.ReturnMap.return_map 1 le_rfl A hA (b : ℂ) hbA
    T hT hc hper hmin hnc Complex.imCLM ha S hS h0S 1 zero_lt_one
  have hpos : ∀ v ∈ d.sectionSet,
      Specs.D13Unified.Ch16.HopfReturnExpansion.positiveRay ((b : ℂ) + (v : ℂ)) := by
    intro v hv
    have hvr : 0 < b + (v : ℂ).re := hsub hv
    have hvi : (v : ℂ).im = 0 := by exact v.property
    exact ⟨by simp [hvi], by simpa using hvr⟩
  have hder := firstReturn_radial_derivative A hA heval hV d hpos P m hP hfix hturns
  exact orbital_criteria_of_scalar_return 1 le_rfl A hA hbA hT hc hper hmin hnc
    Complex.imCLM d real_section_finrank m hder hm

/-- A least-period trace of a complete solution is exactly a canonical orbit,
including the actual maximal interval and the same least physical period. -/
lemma leastPeriodOrbit_canonical (A : AutonomousODE ℂ)
    (hA : ContDiffOn ℝ 1 A.eval A.domain) (V : ℂ → ℂ)
    {Γ : Set ℂ} {T : ℝ}
    (hT : Specs.D13Unified.Ch16.PlanarHopf.LeastPeriodOrbit V Γ T)
    (hΓdom : Γ ⊆ A.domain) (heval : ∀ x ∈ A.domain, A.eval x = V x)
    {p : ℂ} (hp : p ∈ Γ) :
    IsComplete A p ∧ Function.Periodic (fun t => flow A t p) T ∧
      (∀ S : ℝ, 0 < S → Function.Periodic (fun t => flow A t p) S → T ≤ S) ∧
      ¬ IsConstant A p ∧ orbit A p = Γ := by
  obtain ⟨hT,z,hper,hsol,hnc,hΓ,hmin⟩ := hT
  obtain ⟨a,ha⟩ := hΓ ▸ hp
  let w : ℝ → ℂ := fun t => z (t + a)
  have hw : IsPeriodicSolution V w T :=
    D13Unified.Ch16.HopfPeriodicOrbitBridge.periodicSolution_shift
      ⟨hT,hper,hsol,hnc⟩ a
  have hw0 : w 0 = p := by simpa [w] using ha
  have hstay : ∀ t, w t ∈ A.domain := by
    intro t
    apply hΓdom
    rw [hΓ]
    exact ⟨t + a,rfl⟩
  obtain ⟨hc,he⟩ := complete_solution_eq_flow A hA w hstay
    (fun t => by rw [heval _ (hstay t)]; exact hw.2.2.1 t)
  have hcan := periodic_solution_canonical A hA V hw hstay
    (fun t => heval _ (hstay t))
  rw [hw0] at hc he hcan
  refine ⟨hc,hcan.2.1,?_,hcan.2.2.1,?_⟩
  · intro S hS hSper
    apply hmin S hS
    intro t
    have hh := hSper (t - a)
    change flow A ((t - a) + S) p = flow A (t - a) p at hh
    rw [he,he] at hh
    change z (((t - a) + S) + a) = z ((t - a) + a) at hh
    convert! hh using 1 <;> congr 1 <;> ring
  · rw [hcan.2.2.2,hΓ]
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨t + a,rfl⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t - a,by simp [w]⟩

/-- Orbital stability and instability for a physical normal-form orbit trace.
The hypotheses retain the actual equation domain, angular turns and multiplier. -/
lemma normal_leastPeriodOrbit_criteria {F : ℝ × ℂ → ℂ} {ω μ b T R : ℝ} {K : ℝ≥0}
    (A : AutonomousODE ℂ) (hA : ContDiffOn ℝ 1 A.eval A.domain)
    (heval : ∀ z ∈ A.domain, A.eval z = transformedField F (μ,z))
    (hV : LipschitzOnWith K (fun z => transformedField F (μ,z)) (Metric.closedBall 0 R))
    (hω : 0 < ω) {Γ : Set ℂ}
    (hT : Specs.D13Unified.Ch16.PlanarHopf.LeastPeriodOrbit
      (fun z => transformedField F (μ,z)) Γ T)
    (hΓdom : Γ ⊆ A.domain) (hbΓ : (b : ℂ) ∈ Γ)
    (P : ℝ → ℝ) (m : ℝ) (hm : 0 < m) (hP : HasDerivAt P m b) (hfix : P b = b)
    (hturns : ∀ᶠ s : ℝ in nhds b, FullAngularTurn F ω μ s (P s) R) :
    (m < 1 → orbitalAsymptoticallyStableValue A Γ) ∧
      (1 < m → orbitalUnstableValue A Γ) := by
  have hTpos := hT.1
  obtain ⟨hc,hper,hmin,hnc,horbit⟩ := leastPeriodOrbit_canonical A hA
    (fun z => transformedField F (μ,z)) hT hΓdom heval hbΓ
  have hh := normal_orbit_criteria A hA heval hV hω (hΓdom hbΓ) hTpos hc hper hmin hnc
    P m hm hP hfix hturns
  rwa [horbit] at hh

end D13Unified.Ch16.PlanarHopf


noncomputable section
namespace D13Unified.Ch16.PlanarHopf
open Set Filter
open scoped Topology

/-- Continuity only at a compact nonempty set gives uniform control of
distance to its image throughout a sufficiently small metric tube. -/
lemma compact_infDist_map {E G : Type*} [MetricSpace E] [MetricSpace G]
    {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (f : E → G) (hf : ∀ x ∈ K, ContinuousAt f x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ x, Metric.infDist x K < δ →
      Metric.infDist (f x) (f '' K) < ε := by
  have hpre : f ⁻¹' Metric.thickening ε (f '' K) ∈ 𝓝ˢ K := by
    rw [mem_nhdsSet_iff_forall]
    intro x hx
    apply hf x hx
    apply Metric.isOpen_thickening.mem_nhds
    exact (Metric.self_subset_thickening hε _) ⟨x, hx, rfl⟩
  obtain ⟨δ, hδ, hsub⟩ := (Metric.mem_nhdsSet_iff hK).mp hpre
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  apply (Metric.mem_thickening_iff_infDist_lt (hKne.image f)).mp
  exact hsub ((Metric.mem_thickening_iff_infDist_lt hKne).mpr hx)

/-- A compact set inside an open domain has a metric tube inside that
same domain; the nonempty hypothesis makes infDist the real distance. -/
lemma compact_infDist_subset_open {E : Type*} [MetricSpace E]
    {K S : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (hS : IsOpen S) (hKS : K ⊆ S) :
    ∃ δ > 0, ∀ x, Metric.infDist x K < δ → x ∈ S := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hS hKS
  exact ⟨δ, hδ, fun x hx => hsub ((Metric.mem_thickening_iff_infDist_lt hKne).mpr hx)⟩

/-- Near a compact subset of the source of a genuine local chart, both
directions preserve arbitrarily small distance to the compact orbit. -/
lemma partialHomeomorph_compact_metric_control
    {E G : Type*} [MetricSpace E] [MetricSpace G]
    (e : OpenPartialHomeomorph E G) {K : Set E}
    (hK : IsCompact K) (hKne : K.Nonempty) (hKS : K ⊆ e.source) :
    (∀ ε > 0, ∃ δ > 0, ∀ x, Metric.infDist x K < δ →
      x ∈ e.source ∧ Metric.infDist (e x) (e '' K) < ε) ∧
    (∀ ε > 0, ∃ δ > 0, ∀ y, Metric.infDist y (e '' K) < δ →
      ∃ x ∈ e.source, e x = y ∧ Metric.infDist x K < ε) := by
  have hIm : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKS)
  have hImne : (e '' K).Nonempty := hKne.image e
  have hImT : e '' K ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hKS hx)
  have hiImage : e.symm '' (e '' K) = K := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [e.left_inv (hKS hz)] using hz
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.left_inv (hKS hx)⟩
  constructor
  · intro ε hε
    obtain ⟨δ₁, hδ₁, hsource⟩ := compact_infDist_subset_open hK hKne e.open_source hKS
    obtain ⟨δ₂, hδ₂, hmap⟩ := compact_infDist_map hK hKne e
      (fun x hx => e.continuousAt (hKS hx)) ε hε
    exact ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx =>
      ⟨hsource x (hx.trans_le (min_le_left _ _)),
        hmap x (hx.trans_le (min_le_right _ _))⟩⟩
  · intro ε hε
    obtain ⟨δ₁, hδ₁, htarget⟩ := compact_infDist_subset_open hIm hImne e.open_target hImT
    obtain ⟨δ₂, hδ₂, hmap⟩ := compact_infDist_map hIm hImne e.symm
      (fun y hy => e.continuousAt_symm (hImT hy)) ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    intro y hy
    have hyt : y ∈ e.target := htarget y (hy.trans_le (min_le_left _ _))
    refine ⟨e.symm y, e.map_target hyt, e.right_inv hyt, ?_⟩
    simpa only [hiImage] using hmap y (hy.trans_le (min_le_right _ _))

/-- Uniform compact-set control carries convergence of distance to the
orbit through a map continuous at that orbit. -/
lemma tendsto_infDist_image {E G ι : Type*} [MetricSpace E] [MetricSpace G]
    {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (f : E → G) (hf : ∀ x ∈ K, ContinuousAt f x)
    {l : Filter ι} {z : ι → E}
    (hz : Tendsto (fun i => Metric.infDist (z i) K) l (nhds 0)) :
    Tendsto (fun i => Metric.infDist (f (z i)) (f '' K)) l (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmap⟩ := compact_infDist_map hK hKne f hf ε hε
  filter_upwards [hz.eventually (gt_mem_nhds hδ)] with i hi
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg Metric.infDist_nonneg]
    using hmap (z i) hi

/-- Restrict a parameter-preserving genuine product chart to a single
parameter fiber. The source and target retain their actual local domains. -/
def parameterSlice
    (e : OpenPartialHomeomorph (ℝ × ℂ) (ℝ × ℂ))
    (hf : ∀ q : ℝ × ℂ, (e q).1 = q.1)
    (hi : ∀ q ∈ e.target, (e.symm q).1 = q.1)
    (μ : ℝ) : OpenPartialHomeomorph ℂ ℂ where
  toFun := fun w => (e (μ, w)).2
  invFun := fun x => (e.symm (μ, x)).2
  source := {w | (μ, w) ∈ e.source}
  target := {x | (μ, x) ∈ e.target}
  map_source' := by
    intro w hw
    change (μ, (e (μ, w)).2) ∈ e.target
    have hp : (μ, (e (μ, w)).2) = e (μ, w) := by
      exact Prod.ext (hf (μ, w)).symm rfl
    rw [hp]
    exact e.map_source hw
  map_target' := by
    intro x hx
    change (μ, (e.symm (μ, x)).2) ∈ e.source
    have hp : (μ, (e.symm (μ, x)).2) = e.symm (μ, x) := by
      exact Prod.ext (hi (μ, x) hx).symm rfl
    rw [hp]
    exact e.map_target hx
  left_inv' := by
    intro w hw
    have hp : (μ, (e (μ, w)).2) = e (μ, w) := by
      exact Prod.ext (hf (μ, w)).symm rfl
    rw [hp, e.left_inv hw]
  right_inv' := by
    intro x hx
    have hp : (μ, (e.symm (μ, x)).2) = e.symm (μ, x) := by
      exact Prod.ext (hi (μ, x) hx).symm rfl
    rw [hp, e.right_inv hx]
  continuousOn_toFun := by
    intro w hw
    exact ((e.continuousAt hw).comp
      (continuousAt_const.prodMk continuousAt_id)).snd.continuousWithinAt
  continuousOn_invFun := by
    intro x hx
    exact ((e.continuousAt_symm hx).comp
      (continuousAt_const.prodMk continuousAt_id)).snd.continuousWithinAt
  open_source := e.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)

@[simp] lemma parameterSlice_apply
    (e : OpenPartialHomeomorph (ℝ × ℂ) (ℝ × ℂ))
    (hf : ∀ q : ℝ × ℂ, (e q).1 = q.1)
    (hi : ∀ q ∈ e.target, (e.symm q).1 = q.1)
    (μ : ℝ) (w : ℂ) : parameterSlice e hf hi μ w = (e (μ,w)).2 := rfl

@[simp] lemma parameterSlice_symm_apply
    (e : OpenPartialHomeomorph (ℝ × ℂ) (ℝ × ℂ))
    (hf : ∀ q : ℝ × ℂ, (e q).1 = q.1)
    (hi : ∀ q ∈ e.target, (e.symm q).1 = q.1)
    (μ : ℝ) (x : ℂ) : (parameterSlice e hf hi μ).symm x = (e.symm (μ,x)).2 := rfl

/-- The state chart for the actual canonical normal coordinates, extracted
from their parameter-preserving product chart. -/
lemma coordinate_stateChart
    (F : ℝ × ℂ → ℂ)
    (e : OpenPartialHomeomorph (ℝ × ℂ) (ℝ × ℂ))
    (he : (e : ℝ × ℂ → ℝ × ℂ) = Specs.D13Unified.Ch16.CubicNormalForm.familyCoordinate F)
    (hi : ∀ q ∈ e.target, (e.symm q).1 = q.1) (μ : ℝ) :
    ∃ c : OpenPartialHomeomorph ℂ ℂ,
      (c : ℂ → ℂ) = Specs.D13Unified.Ch16.CubicNormalForm.coordinate F μ ∧
      (c.symm : ℂ → ℂ) = (fun x => (e.symm (μ,x)).2) ∧
      c.source = {w | (μ,w) ∈ e.source} ∧ c.target = {x | (μ,x) ∈ e.target} := by
  have hf : ∀ q : ℝ × ℂ, (e q).1 = q.1 := by
    intro q
    rw [he]
    rfl
  refine ⟨parameterSlice e hf hi μ, ?_, rfl, rfl, rfl⟩
  funext w
  change (e (μ,w)).2 = _
  rw [he]
  rfl

/-- The canonical coordinates form a state chart on their entire stated
normal ball, with both genuine C² local maps and the actual field identity. -/
lemma coordinate_ballChart (F : ℝ × ℂ → ℂ) {ε ρ μ : ℝ}
    (hc : Specs.D13Unified.Ch16.CubicNormalForm.CoordinateValidity F ε ρ)
    (hμ : |μ| < ε) :
    ∃ c : OpenPartialHomeomorph ℂ ℂ,
      (c : ℂ → ℂ) = Specs.D13Unified.Ch16.CubicNormalForm.coordinate F μ ∧
      c.source = Metric.ball 0 ρ ∧
      ∀ w ∈ c.source,
        ContDiffAt ℝ 2 (c : ℂ → ℂ) w ∧
        ContDiffAt ℝ 2 c.symm (c w) ∧
        (fderiv ℝ (c : ℂ → ℂ) w).IsInvertible ∧
        fderiv ℝ (c : ℂ → ℂ) w
          (Specs.D13Unified.Ch16.CubicNormalForm.transformedField F (μ,w)) =
          F (μ,c w) := by
  obtain ⟨e, he, hsrc, hi, hreg⟩ := hc
  obtain ⟨c₀, hc₀, hic₀, hsc₀, _⟩ := coordinate_stateChart F e he hi μ
  let c := c₀.restrOpen (Metric.ball 0 ρ) Metric.isOpen_ball
  have hcmap : (c : ℂ → ℂ) = Specs.D13Unified.Ch16.CubicNormalForm.coordinate F μ := hc₀
  have hcs : c.source = Metric.ball 0 ρ := by
    change c₀.source ∩ Metric.ball 0 ρ = Metric.ball 0 ρ
    apply inter_eq_right.mpr
    intro w hw
    rw [hsc₀]
    exact hsrc ⟨hμ, by simpa only [Metric.mem_ball, dist_zero_right] using hw⟩
  refine ⟨c, hcmap, hcs, ?_⟩
  intro w hw
  have hwρ : ‖w‖ < ρ := by simpa only [hcs, Metric.mem_ball, dist_zero_right] using hw
  have hp := hreg (μ,w) ⟨hμ, hwρ⟩
  have hcf : ContDiffAt ℝ 2 (c : ℂ → ℂ) w := by
    have hh := hp.1.snd.comp w (contDiffAt_const.prodMk contDiffAt_id)
    simpa only [he, Specs.D13Unified.Ch16.CubicNormalForm.familyCoordinate,
      Function.comp_def, hcmap] using hh
  have hci : ContDiffAt ℝ 2 c.symm (c w) := by
    change ContDiffAt ℝ 2 c₀.symm (c w)
    have hpoint : (μ,c w) = e (μ,w) := by
      rw [he]
      exact Prod.ext rfl (congrFun hcmap w)
    have hinv : ContDiffAt ℝ 2 (e.symm : ℝ × ℂ → ℝ × ℂ) (μ,c w) :=
      hpoint.symm ▸ hp.2.1
    have hh := hinv.snd.comp (c w) (contDiffAt_const.prodMk contDiffAt_id)
    simpa only [Function.comp_def, ← hic₀] using hh
  refine ⟨hcf, hci, ?_, ?_⟩
  · simpa only [hcmap] using hp.2.2.1
  · simpa only [hcmap] using hp.2.2.2

end D13Unified.Ch16.PlanarHopf


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace D13Unified.Ch16.PlanarHopf
open Set Filter
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Specs.D13Unified.Ch14.OrbitalDefinitions
open Ch06.StateDerivative

lemma forward_flow_transport (A B : AutonomousODE ℂ)
    (hA : ContDiffOn ℝ 1 A.eval A.domain) (hB : ContDiffOn ℝ 1 B.eval B.domain)
    (c : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V)
    (hc : ContDiffOn ℝ 1 c V)
    (hVA : V ⊆ A.domain) (hVB : MapsTo c V B.domain)
    (hconj : ∀ x ∈ V, fderiv ℝ c x (A.eval x) = B.eval (c x))
    (x : ℂ) (hx : x ∈ V) (hforward : forwardCompleteValue A x)
    (hstay : ∀ t : ℝ, 0 ≤ t → flow A t x ∈ V) :
    forwardCompleteValue B (c x) ∧
      ∀ t : ℝ, 0 ≤ t → flow B t (c x) = c (flow A t x) := by
  have hX := flow_ivp A hA (hVA hx)
  have hzero : flow A 0 x = x := hX.2.2
  have hcont : ContinuousAt (fun t => flow A t x) 0 :=
    hX.1.1.continuousOn.continuousAt ((flowInterval A x).isOpen.mem_nhds hX.2.1)
  have hn : ∀ᶠ t in nhds (0 : ℝ),
      t ∈ (flowInterval A x).carrier ∧ flow A t x ∈ V := by
    have hinterval : ∀ᶠ t in nhds (0 : ℝ), t ∈ (flowInterval A x).carrier :=
      (flowInterval A x).isOpen.mem_nhds hX.2.1
    have hzeroV : flow A 0 x ∈ V := by rw [hzero]; exact hx
    exact hinterval.and (hcont.preimage_mem_nhds (hV.mem_nhds hzeroV))
  obtain ⟨r, hr, hnear⟩ := Metric.eventually_nhds_iff.mp hn
  let I : OpenTimeInterval :=
    ⟨⟨Ioi (-r), ⟨0, by simpa using hr⟩, ordConnected_Ioi⟩, isOpen_Ioi⟩
  have hI0 : 0 ∈ I.carrier := by simpa [I] using hr
  have hI (t : ℝ) (ht : t ∈ I.carrier) :
      t ∈ (flowInterval A x).carrier ∧ flow A t x ∈ V := by
    by_cases ht0 : 0 ≤ t
    · exact ⟨hforward.2 ht0, hstay t ht0⟩
    · apply hnear
      rw [Real.dist_eq, sub_zero, abs_of_neg (lt_of_not_ge ht0)]
      change -r < t at ht
      linarith
  have hcomp : classicalIVPOnValue B.toODE I (fun t => c (flow A t x)) 0 (c x) := by
    refine ⟨⟨?_, ?_, ?_⟩, hI0, by simpa only [hzero]⟩
    · exact hc.comp (hX.1.1.mono (fun t ht => (hI t ht).1)) (fun t ht => (hI t ht).2)
    · intro t ht
      exact hVB (hI t ht).2
    · intro t ht
      have hct := (hc.contDiffAt (hV.mem_nhds (hI t ht).2)).differentiableAt (by norm_num)
      have hd := hct.hasFDerivAt.comp_hasDerivAt t (hX.1.2.2 t (hI t ht).1)
      change HasDerivAt (fun s => c (flow A s x))
        ((fderiv ℝ c (flow A t x)) (A.eval (flow A t x))) t at hd
      rw [hconj _ (hI t ht).2] at hd
      exact hd
  have hcx : c x ∈ B.domain := hVB hx
  have hcan := ODE.canonical_solution B.toODE
    (B.locallyLipschitzInState_of_contDiffOn hB) 0 (c x) hcx
  have hcoverage := hcan.2.2.2.2.2.1 I (fun t => c (flow A t x)) hcomp
  have hpositive (t : ℝ) (ht : 0 ≤ t) : t ∈ I.carrier := by
    change -r < t
    linarith
  refine ⟨⟨hcx, fun t ht => hcoverage.1 (hpositive t ht)⟩, ?_⟩
  intro t ht
  exact hcoverage.2 (hpositive t ht)


lemma orbitalLyapunovStable_transport (A B : AutonomousODE ℂ)
    (hA : ContDiffOn ℝ 1 A.eval A.domain) (hB : ContDiffOn ℝ 1 B.eval B.domain)
    (c : ℂ → ℂ) (V Γ : Set ℂ) (hV : IsOpen V)
    (hc : ContDiffOn ℝ 1 c V)
    (hVA : V ⊆ A.domain) (hVB : MapsTo c V B.domain)
    (hconj : ∀ x ∈ V, fderiv ℝ c x (A.eval x) = B.eval (c x))
    (hnearA : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A.domain,
      Metric.infDist x Γ < δ → x ∈ V ∧ Metric.infDist (c x) (c '' Γ) < ε)
    (hnearB : ∀ δ > 0, ∃ ζ > 0, ∀ y ∈ B.domain,
      Metric.infDist y (c '' Γ) < ζ →
        ∃ x ∈ V, c x = y ∧ Metric.infDist x Γ < δ)
    (hstable : orbitalLyapunovStableValue A Γ) :
    orbitalLyapunovStableValue B (c '' Γ) := by
  intro ε hε
  obtain ⟨δm, hδm, hmap⟩ := hnearA ε hε
  obtain ⟨δs, hδs, hsmall⟩ := hstable δm hδm
  obtain ⟨ζ, hζ, hinv⟩ := hnearB δs hδs
  refine ⟨ζ, hζ, ?_⟩
  intro y hy hdist
  obtain ⟨x, hx, hxy, hxd⟩ := hinv y hy hdist
  obtain ⟨hforward, hstayDist⟩ := hsmall x (hVA hx) hxd
  have hxdom (t : ℝ) (ht : 0 ≤ t) : flow A t x ∈ A.domain :=
    (flow_ivp A hA (hVA hx)).1.2.1 t (hforward.2 ht)
  have hstay (t : ℝ) (ht : 0 ≤ t) : flow A t x ∈ V :=
    (hmap _ (hxdom t ht) (hstayDist t ht)).1
  obtain ⟨hBforward, hflow⟩ :=
    forward_flow_transport A B hA hB c V hV hc hVA hVB hconj x hx hforward hstay
  refine ⟨hxy ▸ hBforward, ?_⟩
  intro t ht
  rw [← hxy, hflow t ht]
  exact (hmap _ (hxdom t ht) (hstayDist t ht)).2

lemma orbitalAsymptoticallyStable_transport (A B : AutonomousODE ℂ)
    (hA : ContDiffOn ℝ 1 A.eval A.domain) (hB : ContDiffOn ℝ 1 B.eval B.domain)
    (c : ℂ → ℂ) (V Γ : Set ℂ) (hV : IsOpen V)
    (hc : ContDiffOn ℝ 1 c V)
    (hVA : V ⊆ A.domain) (hVB : MapsTo c V B.domain)
    (hconj : ∀ x ∈ V, fderiv ℝ c x (A.eval x) = B.eval (c x))
    (hnearA : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ A.domain,
      Metric.infDist x Γ < δ → x ∈ V ∧ Metric.infDist (c x) (c '' Γ) < ε)
    (hnearB : ∀ δ > 0, ∃ ζ > 0, ∀ y ∈ B.domain,
      Metric.infDist y (c '' Γ) < ζ →
        ∃ x ∈ V, c x = y ∧ Metric.infDist x Γ < δ)
    (hstable : orbitalAsymptoticallyStableValue A Γ) :
    orbitalAsymptoticallyStableValue B (c '' Γ) := by
  refine ⟨orbitalLyapunovStable_transport A B hA hB c V Γ hV hc hVA hVB hconj
    hnearA hnearB hstable.1, ?_⟩
  obtain ⟨δv, hδv, hmapV⟩ := hnearA 1 (by norm_num)
  obtain ⟨δs, hδs, hsmall⟩ := hstable.1 δv hδv
  obtain ⟨δa, hδa, hattract⟩ := hstable.2
  obtain ⟨ζ, hζ, hinv⟩ := hnearB (min δs δa) (lt_min hδs hδa)
  refine ⟨ζ, hζ, ?_⟩
  intro y hy hdist
  obtain ⟨x, hx, hxy, hxd⟩ := hinv y hy hdist
  obtain ⟨hforward, hlim⟩ := hattract x (hVA hx) (hxd.trans_le (min_le_right _ _))
  have hstayDist := (hsmall x (hVA hx) (hxd.trans_le (min_le_left _ _))).2
  have hxdom (t : ℝ) (ht : 0 ≤ t) : flow A t x ∈ A.domain :=
    (flow_ivp A hA (hVA hx)).1.2.1 t (hforward.2 ht)
  have hstay (t : ℝ) (ht : 0 ≤ t) : flow A t x ∈ V :=
    (hmapV _ (hxdom t ht) (hstayDist t ht)).1
  obtain ⟨hBforward, hflow⟩ :=
    forward_flow_transport A B hA hB c V hV hc hVA hVB hconj x hx hforward hstay
  refine ⟨hxy ▸ hBforward, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  obtain ⟨δm, hδm, hmap⟩ := hnearA ε hε
  have hevent : ∀ᶠ t : ℝ in atTop, Metric.infDist (flow A t x) Γ < δm :=
    hlim.eventually (Iio_mem_nhds hδm)
  have htime : ∀ᶠ t : ℝ in atTop, 0 ≤ t := eventually_atTop.2 ⟨0, fun t ht => ht⟩
  filter_upwards [hevent, htime] with t hdist ht
  rw [← hxy, hflow t ht, Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
  exact (hmap _ (hxdom t ht) hdist).2


lemma orbitalAsymptoticallyStable_partialHomeomorph
    (A B : AutonomousODE ℂ)
    (hA : ContDiffOn ℝ 1 A.eval A.domain) (hB : ContDiffOn ℝ 1 B.eval B.domain)
    (e : OpenPartialHomeomorph ℂ ℂ) (Γ : Set ℂ)
    (hΓ : IsCompact Γ) (hΓne : Γ.Nonempty) (hΓe : Γ ⊆ e.source)
    (hc : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hVA : e.source ⊆ A.domain) (hVB : e.target ⊆ B.domain)
    (hconj : ∀ x ∈ e.source, fderiv ℝ (e : ℂ → ℂ) x (A.eval x) = B.eval (e x))
    (hstable : orbitalAsymptoticallyStableValue A Γ) :
    orbitalAsymptoticallyStableValue B (e '' Γ) := by
  have hm := partialHomeomorph_compact_metric_control e hΓ hΓne hΓe
  apply orbitalAsymptoticallyStable_transport A B hA hB e e.source Γ e.open_source
    hc hVA (fun x hx => hVB (e.map_source hx)) hconj
  · intro ε hε
    obtain ⟨δ, hδ, hh⟩ := hm.1 ε hε
    exact ⟨δ, hδ, fun x _ hx => hh x hx⟩
  · intro ε hε
    obtain ⟨δ, hδ, hh⟩ := hm.2 ε hε
    exact ⟨δ, hδ, fun x _ hx => hh x hx⟩
  · exact hstable

lemma orbitalLyapunovStable_partialHomeomorph_iff
    (A B : AutonomousODE ℂ)
    (hA : ContDiffOn ℝ 1 A.eval A.domain) (hB : ContDiffOn ℝ 1 B.eval B.domain)
    (e : OpenPartialHomeomorph ℂ ℂ) (Γ : Set ℂ)
    (hΓ : IsCompact Γ) (hΓne : Γ.Nonempty) (hΓe : Γ ⊆ e.source)
    (hc : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hci : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    (hVA : e.source ⊆ A.domain) (hVB : e.target ⊆ B.domain)
    (hconj : ∀ x ∈ e.source, fderiv ℝ (e : ℂ → ℂ) x (A.eval x) = B.eval (e x))
    (hconji : ∀ y ∈ e.target,
      fderiv ℝ (e.symm : ℂ → ℂ) y (B.eval y) = A.eval (e.symm y)) :
    orbitalLyapunovStableValue A Γ ↔ orbitalLyapunovStableValue B (e '' Γ) := by
  have hm := partialHomeomorph_compact_metric_control e hΓ hΓne hΓe
  have hIm : IsCompact (e '' Γ) := hΓ.image_of_continuousOn (e.continuousOn.mono hΓe)
  have hImT : e '' Γ ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hΓe hx)
  have hiImage : e.symm '' (e '' Γ) = Γ := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [e.left_inv (hΓe hz)] using hz
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.left_inv (hΓe hx)⟩
  constructor
  · intro hs
    apply orbitalLyapunovStable_transport A B hA hB e e.source Γ e.open_source
      hc hVA (fun x hx => hVB (e.map_source hx)) hconj
    · intro ε hε
      obtain ⟨δ, hδ, hh⟩ := hm.1 ε hε
      exact ⟨δ, hδ, fun x _ hx => hh x hx⟩
    · intro ε hε
      obtain ⟨δ, hδ, hh⟩ := hm.2 ε hε
      exact ⟨δ, hδ, fun x _ hx => hh x hx⟩
    · exact hs
  · intro hs
    have hmi := partialHomeomorph_compact_metric_control e.symm hIm (hΓne.image e) hImT
    have hback : orbitalLyapunovStableValue A (e.symm '' (e '' Γ)) := by
      apply orbitalLyapunovStable_transport B A hB hA e.symm e.target (e '' Γ)
        e.open_target hci hVB (fun y hy => hVA (e.map_target hy)) hconji
      · intro ε hε
        obtain ⟨δ, hδ, hh⟩ := hmi.1 ε hε
        exact ⟨δ, hδ, fun x _ hx => hh x hx⟩
      · intro ε hε
        obtain ⟨δ, hδ, hh⟩ := hmi.2 ε hε
        exact ⟨δ, hδ, fun x _ hx => hh x hx⟩
      · exact hs
    simpa only [hiImage] using hback

lemma orbitalUnstable_partialHomeomorph
    (A B : AutonomousODE ℂ)
    (hA : ContDiffOn ℝ 1 A.eval A.domain) (hB : ContDiffOn ℝ 1 B.eval B.domain)
    (e : OpenPartialHomeomorph ℂ ℂ) (Γ : Set ℂ)
    (hΓ : IsCompact Γ) (hΓne : Γ.Nonempty) (hΓe : Γ ⊆ e.source)
    (hc : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hci : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    (hVA : e.source ⊆ A.domain) (hVB : e.target ⊆ B.domain)
    (hconj : ∀ x ∈ e.source, fderiv ℝ (e : ℂ → ℂ) x (A.eval x) = B.eval (e x))
    (hconji : ∀ y ∈ e.target,
      fderiv ℝ (e.symm : ℂ → ℂ) y (B.eval y) = A.eval (e.symm y))
    (hunstable : orbitalUnstableValue A Γ) : orbitalUnstableValue B (e '' Γ) := by
  intro hs
  exact hunstable ((orbitalLyapunovStable_partialHomeomorph_iff A B hA hB e Γ hΓ hΓne
    hΓe hc hci hVA hVB hconj hconji).mpr hs)

end D13Unified.Ch16.PlanarHopf


noncomputable section
namespace D13Unified.Ch16.PlanarHopf
open Set Filter

/-- The inverse differential identity follows from the genuine local inverse
and the forward identity. It is not an independent conjugacy hypothesis. -/
lemma inverse_chart_pushforward (e : OpenPartialHomeomorph ℂ ℂ)
    (he : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hi : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    (V W : ℂ → ℂ)
    (hpush : ∀ x ∈ e.source, fderiv ℝ (e : ℂ → ℂ) x (V x) = W (e x)) :
    ∀ y ∈ e.target, fderiv ℝ (e.symm : ℂ → ℂ) y (W y) = V (e.symm y) := by
  intro y hy
  let x := e.symm y
  have hx : x ∈ e.source := e.map_target hy
  have hex : e x = y := e.right_inv hy
  have hed : DifferentiableAt ℝ (e : ℂ → ℂ) x :=
    (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by norm_num)
  have hid : DifferentiableAt ℝ (e.symm : ℂ → ℂ) (e x) :=
    (hi.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by norm_num)
  have hleft : (fun z : ℂ => e.symm (e z)) =ᶠ[nhds x] id :=
    Filter.eventually_of_mem (e.open_source.mem_nhds hx) (fun z hz => e.left_inv hz)
  have hcomp : fderiv ℝ (fun z : ℂ => e.symm (e z)) x =
      (fderiv ℝ (e.symm : ℂ → ℂ) (e x)).comp (fderiv ℝ (e : ℂ → ℂ) x) :=
    fderiv_comp x hid hed
  have hinv : (fderiv ℝ (e.symm : ℂ → ℂ) (e x)).comp
      (fderiv ℝ (e : ℂ → ℂ) x) = ContinuousLinearMap.id ℝ ℂ := by
    rw [← hcomp, hleft.fderiv_eq]
    exact fderiv_id
  have hv := congrArg (fun L : ℂ →L[ℝ] ℂ => L (V x)) hinv
  change fderiv ℝ (e.symm : ℂ → ℂ) y (W y) = V x
  rw [← hex, ← hpush x hx]
  exact hv

end D13Unified.Ch16.PlanarHopf


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace D13Unified.Ch16.PlanarHopf
open Set Filter
open Specs.D13Unified.Ch16.CubicNormalForm
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch14.OrbitalDefinitions

lemma coordinate_orbital_transport
    (F : ℝ × ℂ → ℂ) {ε ρ μ R : ℝ}
    (hcoord : CoordinateValidity F ε ρ) (hμ : |μ| < ε) (hRρ : R ≤ ρ)
    (A B : AutonomousODE ℂ)
    (hA : ContDiffOn ℝ 1 A.eval A.domain) (hB : ContDiffOn ℝ 1 B.eval B.domain)
    (hAdom : A.domain = Metric.ball 0 R)
    (hAval : ∀ w ∈ A.domain, A.eval w = transformedField F (μ,w))
    (hBval : ∀ x ∈ B.domain, B.eval x = F (μ,x))
    (Δ Γ : Set ℂ) (hΔ : IsCompact Δ) (hΔne : Δ.Nonempty)
    (hΔA : Δ ⊆ A.domain) (hΓ : Γ = coordinate F μ '' Δ) (hΓB : Γ ⊆ B.domain) :
    (orbitalAsymptoticallyStableValue A Δ → orbitalAsymptoticallyStableValue B Γ) ∧
    (orbitalUnstableValue A Δ → orbitalUnstableValue B Γ) := by
  obtain ⟨c, hc, hcs, hreg⟩ := coordinate_ballChart F hcoord hμ
  let V : Set ℂ := (c.source ∩ c ⁻¹' B.domain) ∩ A.domain
  have hV : IsOpen V := (c.isOpen_inter_preimage B.isOpen_domain).inter A.isOpen_domain
  let e := c.restrOpen V hV
  have hsrcA : e.source ⊆ A.domain := by
    intro w hw
    exact hw.2.2
  have htgtB : e.target ⊆ B.domain := by
    intro y hy
    have hh : c (e.symm y) ∈ B.domain := (e.map_target hy).2.1.2
    have heq : c (e.symm y) = y := e.right_inv hy
    rwa [heq] at hh
  have hΔe : Δ ⊆ e.source := by
    intro w hw
    have hwA : w ∈ A.domain := hΔA hw
    have hwc : w ∈ c.source := by
      rw [hcs]
      exact Metric.ball_subset_ball hRρ (hAdom ▸ hwA)
    have hwB : c w ∈ B.domain := hΓB (hΓ ▸ ⟨w, hw, (congrFun hc w).symm⟩)
    exact ⟨hwc, ⟨⟨hwc, hwB⟩, hwA⟩⟩
  have heC1 : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source := by
    intro w hw
    exact ((hreg w hw.1).1.of_le (by norm_num)).contDiffWithinAt
  have heiC1 : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target := by
    intro y hy
    have hw := e.map_target hy
    have heq : c (e.symm y) = y := e.right_inv hy
    have hci : ContDiffAt ℝ 2 (e.symm : ℂ → ℂ) y := by
      change ContDiffAt ℝ 2 c.symm y
      rw [← heq]
      exact (hreg (e.symm y) hw.1).2.1
    exact (hci.of_le (by norm_num)).contDiffWithinAt
  have hpush : ∀ w ∈ e.source,
      fderiv ℝ (e : ℂ → ℂ) w (A.eval w) = B.eval (e w) := by
    intro w hw
    change fderiv ℝ (c : ℂ → ℂ) w (A.eval w) = B.eval (c w)
    rw [hAval w (hsrcA hw), hBval (c w) hw.2.1.2]
    exact (hreg w hw.1).2.2.2
  have hpushi := inverse_chart_pushforward e heC1 heiC1 A.eval B.eval hpush
  have himage : e '' Δ = Γ := by
    change c '' Δ = Γ
    rw [hc, hΓ]
  constructor
  · intro hs
    have ht := orbitalAsymptoticallyStable_partialHomeomorph A B hA hB e Δ
      hΔ hΔne hΔe heC1 hsrcA htgtB hpush hs
    simpa only [himage] using ht
  · intro hu
    have ht := orbitalUnstable_partialHomeomorph A B hA hB e Δ
      hΔ hΔne hΔe heC1 heiC1 hsrcA htgtB hpush hpushi hu
    simpa only [himage] using ht

end D13Unified.Ch16.PlanarHopf


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace D13Unified.Ch16.PlanarHopf
open Set Filter
open scoped NNReal
open Specs.D13Unified.Ch16
open CubicHomologicalElimination CubicNormalForm HopfReturnExpansion HopfPeriodicBranch
open Specs.D13Unified.Ch16.PlanarHopf
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch12.StabilityDefinitions
open Specs.D13Unified.Ch14.OrbitalDefinitions

/-- Full original continuous-time conclusion, using the complete periodic-branch
premise and actual source-derived normal and original ODEs on common domains. -/
theorem sourceDynamics (branch : PeriodicBranch) : Dynamics := by
  intro F ω h
  obtain ⟨ε₀, hε₀, ρ, hρ, δ₀, hδ₀, C₀, hC₀, P, Q, hret,
    εb, δ, C, ψ, hbr, _, σ, hσ, _, hbridge, hclass, hOrig⟩ := branch F ω h
  obtain ⟨Uo, hUo, h0Uo, hOrig⟩ := hOrig
  have hlift (μ : ℝ) (hμ : |μ| < εb) (Γ : Set ℂ)
      (hΓ : IsPeriodicOrbit (fun z => F (μ,z)) Γ) (hΓU : Γ ⊆ Uo) :
      ∃ Δ : Set ℂ, IsPeriodicOrbit (fun w => transformedField F (μ,w)) Δ ∧
        Δ ⊆ Metric.ball 0 σ ∧ Γ = coordinate F μ '' Δ :=
    (hOrig μ hμ).2.2 Γ hΓ hΓU
  obtain ⟨εe, hεe, V, hV, h0V, hrestrict⟩ := sourceEquilibriaOn F ω h
  obtain ⟨ζV, hζV, hcontain⟩ := classifiedOrbits_eventually_contained
    F ω ε₀ ρ δ₀ C₀ P Q εb δ C ψ σ Uo h hε₀ hρ hσ hret hbr hbridge hlift V hV h0V
  obtain ⟨ηn, hηn, R, hR, hRρ, B, hBdom, hBdata⟩ := sourceNormalEquationData F ω h ρ hρ
  have hlocal (μ : ℝ) (hμ : |μ| < ηn) : ∃ K : ℝ≥0,
      LipschitzOnWith K (fun w => transformedField F (μ,w)) (Metric.closedBall 0 R) :=
    (hBdata μ hμ).2.2
  obtain ⟨ηr, hηr, τ, hτ, hηrε, _, hturns⟩ :=
    confinedReturnTurns F ω ε₀ ρ δ₀ C₀ P Q h hε₀ hret ηn R hηn hR hlocal
  obtain ⟨ηm, hηm, d, hd, _, _, hmult⟩ :=
    sourceMultiplierClassification F ω ε₀ ρ δ₀ C₀ P Q h hε₀ hδ₀ hC₀ hret
  let δcut := min d (min δ₀ τ)
  have hδcut : 0 < δcut := lt_min hd (lt_min hδ₀ hτ)
  obtain ⟨ηs, hηs, hηsb, hreps⟩ := classifiedOrbits_small_representatives
    F ω ε₀ ρ δ₀ C₀ P Q εb δ C ψ σ Uo h hε₀ hρ hσ hret hbr hbridge hlift
      R δcut hR hδcut
  let εg := min εb (min εe ζV)
  have hεg : 0 < εg := lt_min hbr.1 (lt_min hεe hζV)
  let ε := min εg (min ηs (min ηn (min ηr ηm)))
  have hε : 0 < ε := lt_min hεg (lt_min hηs (lt_min hηn (lt_min hηr hηm)))
  have hεg' : ε ≤ εg := min_le_left _ _
  have hεb : ε ≤ εb := hεg'.trans (min_le_left _ _)
  have hεe' : ε ≤ εe := hεg'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεV : ε ≤ ζV := hεg'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hεs : ε ≤ ηs := (min_le_right _ _).trans (min_le_left _ _)
  have hεn : ε ≤ ηn := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεr : ε ≤ ηr := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hεm : ε ≤ ηm := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let U := Uo ∩ V
  have hU : IsOpen U := hUo.inter hV
  have h0U : (0 : ℂ) ∈ U := ⟨h0Uo, h0V⟩
  obtain ⟨A, heval, hequil⟩ := hrestrict U hU h0U inter_subset_right
  refine ⟨ε, hε, U, hU, h0U, A, (fun μ hμ => heval μ (hμ.trans_le hεe')), ?_, ?_⟩
  · intro μ hμ
    have hμb : |μ| < εb := hμ.trans_le hεb
    have hμe : |μ| < εe := hμ.trans_le hεe'
    obtain ⟨hF, h0, heq, hstable, hunstable⟩ := hequil μ hμe
    refine ⟨hF, h0, heq, hstable, hunstable, ?_, ?_, ?_⟩
    · constructor
      · rintro ⟨Γ, hΓ, hΓU⟩
        exact (hOrig μ hμb).1.mp ⟨Γ, hΓ, hΓU.trans inter_subset_left⟩
      · intro hsign
        obtain ⟨Γ, hΓ, hΓUo⟩ := (hOrig μ hμb).1.mpr hsign
        have hΓV := hcontain μ (lt_min hμb (hμ.trans_le hεV)) Γ hΓ hΓUo
        exact ⟨Γ, hΓ, subset_inter hΓUo hΓV⟩
    · intro Γ Δ hΓ hΓU hΔ hΔU
      exact (hOrig μ hμb).2.1 Γ Δ hΓ (hΓU.trans inter_subset_left)
        hΔ (hΔU.trans inter_subset_left)
    · intro Γ hΓ hΓU
      obtain ⟨Δ, r, T, hT, hΔsmall, hrδ, hrcut, hrΔ, hfix, htrace⟩ :=
        hreps μ (hμ.trans_le hεs) Γ hΓ (hΓU.trans inter_subset_left)
      have hΔB : Δ ⊆ (B μ).domain := by
        rw [hBdom]
        exact hΔsmall.trans (Metric.ball_subset_ball (min_le_right _ _))
      obtain ⟨hB, hBval, K, hK⟩ := hBdata μ (hμ.trans_le hεn)
      have hrd : r ∈ Ioo 0 d := ⟨hrδ.1, hrcut.trans_le (min_le_left _ _)⟩
      obtain ⟨hm, hmneg, hmpos⟩ := hmult μ r (hμ.trans_le hεm) hrd hfix
      have hrturn : r ∈ Ioo 0 (min δ₀ τ) := ⟨hrδ.1, hrcut.trans_le (min_le_right _ _)⟩
      have hfullturns : ∀ᶠ s : ℝ in nhds r, FullAngularTurn F ω μ s (P (s,μ)) R :=
        confinedReturnTurns_eventually hrturn (hturns μ · (hμ.trans_le hεr))
      have hμε₀ : |μ| < ε₀ := (hμ.trans_le hεr).trans_le hηrε
      have hq : (r, μ) ∈ returnBox δ₀ ε₀ :=
        ⟨by rw [abs_of_pos hrδ.1]; exact hrturn.2.trans_le (min_le_left _ _), hμε₀⟩
      have hPdiff : DifferentiableAt ℝ (fun s => P (s,μ)) r :=
        ((hret.smooth_map.contDiffAt
          ((HopfPeriodicOrbitBridge.returnBox_isOpen δ₀ ε₀).mem_nhds hq)).differentiableAt
          (by norm_num)).comp r (differentiableAt_id.prodMk (differentiableAt_const μ))
      have hnormal := normal_leastPeriodOrbit_criteria (B μ) hB hBval hK h.2.1 hT hΔB hrΔ
        (fun s => P (s,μ)) (deriv (fun s => P (s,μ)) r) hm hPdiff.hasDerivAt hfix hfullturns
      have hΓA : Γ ⊆ (A μ).domain := by rw [(heval μ hμe).1]; exact hΓU
      have hAval : ∀ x ∈ (A μ).domain, autonomousEvalValue (A μ) x = F (μ,x) := by
        intro x hx
        exact (heval μ hμe).2 x (by rwa [← (heval μ hμe).1])
      have htransport := coordinate_orbital_transport F hret.coordinates hμε₀ hRρ
        (B μ) (A μ) hB hF (hBdom μ) hBval hAval Δ Γ
        (leastPeriodOrbit_compact hT) (leastPeriodOrbit_nonempty hT) hΔB htrace hΓA
      exact ⟨fun hell => htransport.1 (hnormal.1 (hmneg hell)),
        fun hell => htransport.2 (hnormal.2 (hmpos hell))⟩
  · apply classifiedOrbits_period_limit F ω ε₀ ρ δ₀ C₀ P Q εb δ C ψ
      ε hεb σ U h hε₀ hρ hσ hret hbr
    · intro μ hμ Γ hΓ hΓU
      have hμb := hμ.trans_le hεb
      obtain ⟨Δ, hΔ, hΔσ, htrace⟩ := hlift μ hμb Γ hΓ (hΓU.trans inter_subset_left)
      obtain ⟨r, hr, hrΔ, hfix⟩ := (hbridge μ hμb).1 Δ hΔ hΔσ
      exact ⟨Δ, r, hΔ, hΔσ, htrace, hr, hrΔ, hfix⟩
    · intro μ hμ Γ Δ hΓ hΓσ hΔ hΔσ
      exact (hclass μ (hμ.trans_le hεb)).2 Γ Δ hΓ hΓσ hΔ hΔσ

/-- The full nondegenerate planar Hopf theorem, including the least-period
limit and continuous-time orbital stability for the original vector field. -/
theorem planarHopf : Specs.D13Unified.Ch16.PlanarHopf.PlanarHopf :=
  ⟨planarHopfGeometry, sourceDynamics HopfPeriodicBranch.periodicBranch⟩

end D13Unified.Ch16.PlanarHopf
