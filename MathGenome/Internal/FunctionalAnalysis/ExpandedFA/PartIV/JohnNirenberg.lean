import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.JohnNirenberg
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.HardyPAtoms
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.HardyBMODuality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ExpandedFA.PartIV.JohnNirenberg
open ExpandedFA.Hardy
open HardyPAtomsSpec
open HardyPAtoms.Dyadic
open JohnNirenbergSpec

/-- The denominator in the geometric atomic budget is controlled uniformly
as p approaches one. This is the quantitative information needed at the endpoint. -/
lemma inverse_geometric_gap_le {p : ℝ} (hp : 1 < p) :
    (1 - (2 : ℝ) ^ (1 - p))⁻¹ ≤ 2 * (p / (p - 1)) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have ht : 0 < p - 1 := sub_pos.mpr hp
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hexp : (p + 1) / 2 ≤ Real.exp (Real.log 2 * (p - 1)) := by
    have := Real.add_one_le_exp (Real.log 2 * (p - 1))
    nlinarith [mul_le_mul_of_nonneg_right hlog ht.le]
  have hpow : (2 : ℝ) ^ (1 - p) ≤ 2 / (p + 1) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    rw [show Real.log 2 * (1 - p) = -(Real.log 2 * (p - 1)) by ring,
      Real.exp_neg]
    have := (inv_le_inv₀ (Real.exp_pos _) (by positivity : 0 < (p+1)/2)).mpr hexp
    simpa only [inv_div, one_div] using this
  have hgap : 0 < 1 - (2 : ℝ) ^ (1 - p) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hlow : (p - 1) / (2 * p) ≤ 1 - (2 : ℝ) ^ (1 - p) := by
    have hmid : (p - 1) / (2 * p) ≤ (p - 1) / (p + 1) := by
      apply div_le_div_of_nonneg_left ht.le (by positivity)
      linarith
    have heq : (p - 1) / (p + 1) = 1 - 2 / (p + 1) := by
      field_simp
      ring
    linarith
  have hi := (inv_le_inv₀ hgap (by positivity : 0 < (p-1)/(2*p))).mpr hlow
  calc
    (1 - (2 : ℝ) ^ (1 - p))⁻¹ ≤ ((p - 1) / (2 * p))⁻¹ := hi
    _ = 2 * (p / (p - 1)) := by rw [inv_div]; ring

/-- The accepted telescoping proof gives a dimension-only constant times
p/(p-1), uniformly across all p > 1 and both scalar fields. -/
theorem quantitative_atom_bound : QuantitativeAtomBound := by
  intro d
  let I : ℝ := (2 : ℝ)^d * initialRadiusFactor d ^ d
  let K : ℝ := volume.real (Metric.ball (0 : HardyPAtomsSpec.Point d) ((d : ℝ)+1)) *
    (3 * (2 : ℝ)^d)
  have hI : 0 ≤ I := mul_nonneg (by positivity)
    (pow_nonneg (initialRadiusFactor_pos d).le d)
  have hK : 0 ≤ K := mul_nonneg ENNReal.toReal_nonneg (by positivity)
  refine ⟨I + 2*K + 1, by positivity, ?_⟩
  intro p hp 𝕜 _ a
  by_cases hd0 : d = 0
  · subst d
    have ha : a.val = 0 := HardyPAtoms.zero_dim_mean_zero a.val a.property.2.1
    refine ⟨0, by simp [ha], ?_⟩
    simp only [norm_zero]
    positivity
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  obtain ⟨c, r, hr, hs, hsize⟩ := a.property.2.2
  have hV : 0 < volume.real (Metric.ball c r) := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  have hinit := initial_goodPart_hardy hd a.val a.property.2.1 c r hr hs
    (HardyPAtoms.pAtom_norm_le_one hp a)
  obtain ⟨u, hu, hn⟩ := hardy_of_goodApprox hd hp a.val a.property.1
    ((volume.real (Metric.ball c r))⁻¹) (inv_pos.mpr hV) I hinit
  refine ⟨u, hu, ?_⟩
  have hden : 0 < 1 - (2 : ℝ) ^ (1-p) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hfactor := normalized_budget_factor hp hV ENNReal.toReal_nonneg hsize
  have hdiv : (eLpNorm a.val (ENNReal.ofReal p) volume).toReal ^ p *
      (volume.real (Metric.ball c r))⁻¹ ^ (1-p) / (1 - (2 : ℝ) ^ (1-p)) ≤
        (1 - (2 : ℝ) ^ (1-p))⁻¹ := by
    simpa only [one_div] using (div_le_div_iff_of_pos_right hden).mpr hfactor
  have hmul := mul_le_mul_of_nonneg_left
    (hdiv.trans (inverse_geometric_gap_le hp)) hK
  have hratio : 1 ≤ p / (p - 1) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  have hIratio := mul_le_mul_of_nonneg_left hratio hI
  change ‖u‖ ≤ I + K * _ at hn
  nlinarith

/-- Remove the normalization of the atom without losing the dependence on p.
The zero function is handled separately, so the bound is exactly homogeneous. -/
theorem ball_hardy_bound : BallHardyBound := by
  intro d
  obtain ⟨A, hA, hbound⟩ := quantitative_atom_bound d
  refine ⟨A, hA, ?_⟩
  intro p hp 𝕜 _ f hf hz c r hr hs
  by_cases hzero : f = 0
  · refine ⟨0, by simpa using hzero.symm, ?_⟩
    simp only [norm_zero]
    positivity
  let V : ℝ := volume.real (Metric.ball c r)
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  let b : ℝ := V ^ (1 / p - 1)
  have hb : 0 < b := Real.rpow_pos_of_pos hV _
  let N : ℝ := (eLpNorm f (ENNReal.ofReal p) volume).toReal
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hN : 0 < N := by
    apply ENNReal.toReal_pos _ hf.eLpNorm_ne_top
    intro he
    apply hzero
    exact Lp.ext (((eLpNorm_eq_zero_iff (by positivity : ENNReal.ofReal p ≠ 0)).mp he).trans
      (Lp.coeFn_zero 𝕜 1 volume).symm)
  let t : ℝ := N / b
  have ht : 0 < t := div_pos hN hb
  let k : 𝕜 := (t : 𝕜)
  have hk : k ≠ 0 := RCLike.ofReal_ne_zero.mpr ht.ne'
  have hkn : ‖k‖ = t := by
    change ‖(t : 𝕜)‖ = t
    rw [RCLike.norm_ofReal, abs_of_pos ht]
  have hsm : ⇑(k⁻¹ • f) =ᵐ[volume] k⁻¹ • ⇑f := Lp.coeFn_smul _ _
  have hm : MemLp (⇑(k⁻¹ • f)) (ENNReal.ofReal p) volume :=
    (hf.const_smul k⁻¹).ae_eq hsm.symm
  have hn : (eLpNorm (⇑(k⁻¹ • f)) (ENNReal.ofReal p) volume).toReal ≤ b := by
    rw [eLpNorm_congr_ae hsm, eLpNorm_const_smul, ENNReal.toReal_mul,
      ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _), norm_inv, hkn]
    change t⁻¹ * N ≤ b
    apply (inv_mul_le_iff₀ ht).mpr
    dsimp [t]
    rw [div_mul_cancel₀ _ hb.ne']
  have hi0 : (∫ x, (k⁻¹ • f) x) = 0 := by
    rw [integral_congr_ae hsm]
    change (∫ x, k⁻¹ • f x) = 0
    rw [integral_smul, hz, smul_zero]
  have hsup : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → (k⁻¹ • f) x = 0 := by
    filter_upwards [hsm, hs] with x hx hxs
    intro hxB
    simp [hx, hxs hxB]
  let a : PAtom d p 𝕜 := ⟨k⁻¹ • f, hm, hi0, c, r, hr, hsup, hn⟩
  obtain ⟨u, hu, hnu⟩ := hbound p hp 𝕜 a
  refine ⟨k • u, ?_, ?_⟩
  · rw [map_smul, hu]
    exact smul_inv_smul₀ hk f
  · calc
      ‖k • u‖ = t * ‖u‖ := by rw [norm_smul, hkn]
      _ ≤ t * (A * (p / (p - 1))) := mul_le_mul_of_nonneg_left hnu ht.le
      _ = A * (p / (p - 1)) * V ^ (1 - 1 / p) * N := by
        have hv : b⁻¹ = V ^ (1 - 1 / p) := by
          dsimp [b]
          rw [← Real.rpow_neg hV.le]
          congr 1
          ring
        dsimp [t]
        rw [div_eq_mul_inv, hv]
        ring

/-- Vanishing BMO seminorm gives vanishing oscillation about every ball mean. -/
theorem zero_seminorm_moments : ZeroSeminormMoments := by
  intro d 𝕜 _ g hg c r hr q hq A
  have he := ae_eq_ballMean_of_bmoENorm_zero g.property.1 hg c hr
  have hpow : (fun x => oscillation g.val c r x ^ q) =ᵐ[volume.restrict (Metric.ball c r)]
      (fun _ => (0 : ℝ)) := by
    apply (ae_restrict_iff' measurableSet_ball).mpr
    filter_upwards [he] with x hx hxc
    simp [oscillation, show g.val x = BMOQuotientSpec.MeanValue g.val c r from hx hxc,
      Real.zero_rpow (by linarith : q ≠ 0)]
  refine ⟨(integrable_zero _ _ _).congr hpow.symm, ?_⟩
  rw [integral_congr_ae hpow]
  simp only [integral_zero, mul_zero, hg, ENNReal.toReal_zero]
  rw [Real.zero_rpow (one_div_ne_zero (by linarith : q ≠ 0))]

/-- At exponent one, the desired estimate is exactly the accepted BMO formula. -/
theorem first_moment : FirstMoment := by
  intro d 𝕜 _ g c r hr
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := (volume : Measure (Hardy.Point d)))
      (x := c) (r := r))⟩
  have hi := ((integrableOn_ball_of_locallyIntegrable g.property.1 c r).sub
    (integrable_const (BMOQuotientSpec.MeanValue g.val c r))).norm
  refine ⟨?_, ?_⟩
  · change Integrable (fun x => ‖g.val x - BMOQuotientSpec.MeanValue g.val c r‖ ^ (1 : ℝ)) _
    simpa only [Real.rpow_one, Pi.sub_apply] using hi
  · simp only [Real.rpow_one, div_one, mul_one, one_mul]
    have h := meanOscillation_le_bmoENorm g.val c hr
    rw [meanOscillation, meanOscillation_formula g.val g.property.1 c r hr] at h
    have ht := ENNReal.toReal_mono g.property.2.ne h
    rwa [ENNReal.toReal_ofReal (by positivity)] at ht

/-- On a bounded, ball-supported, mean-zero input, the Hardy functional is
an ordinary integral. This bridges the source pairing to the accepted quotient,
using a single normalized infinity-atom. -/
lemma bmoFunctional_apply_bounded_ball {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (g : BMOQuotientSpec.BMOFunctionValue d 𝕜) (f : L1 d 𝕜)
    (hz : (∫ x, f x) = 0) (c : Hardy.Point d) (r : ℝ) (hr : 0 < r)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ᵐ x ∂volume, ‖f x‖ ≤ M)
    (u : H1 d 𝕜) (hu : AtomicHardySpaceSpec.EmbeddingValue volume u = f) :
    Integrable (fun x => f x * g.val x) volume ∧
      HardyBMODuality.bmoFunctional g u = ∫ x, f x * g.val x := by
  let V := volume.real (Metric.ball c r)
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  let t : ℝ := M * V + 1
  have ht : 0 < t := by dsimp [t]; positivity
  let k : 𝕜 := (t : 𝕜)
  have hk : k ≠ 0 := RCLike.ofReal_ne_zero.mpr ht.ne'
  have hkn : ‖k‖ = t := by simp [k, RCLike.norm_ofReal, ht.le]
  have hm : AEStronglyMeasurable (fun x => k⁻¹ * f x) volume :=
    (Lp.aestronglyMeasurable f).const_mul _
  have hi : (∫ x, k⁻¹ * f x) = 0 := by rw [integral_const_mul, hz, mul_zero]
  obtain ⟨a, ha⟩ := AtomicHardySpace.euclidean_atom_realization d
    (fun x => k⁻¹ * f x) hm hi ⟨c, r, hr, by
      filter_upwards [hs, hb] with x hxs hxb
      refine ⟨fun hxc => by simp [hxs hxc], ?_⟩
      rw [norm_mul, norm_inv, hkn]
      apply (inv_mul_le_iff₀ ht).mpr
      calc
        ‖f x‖ ≤ M := hxb
        _ ≤ t * V⁻¹ := by
          dsimp [t]
          rw [add_mul, mul_assoc, mul_inv_cancel₀ hV.ne', mul_one]
          exact le_add_of_nonneg_right (by positivity)⟩
  have he : k • a.val = f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul k a.val, ha] with x hx hxa
    simp only [hx, Pi.smul_apply, hxa, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hk, one_mul]
  have hue : u = k • AtomicHardySpace.atomElement volume a := by
    apply (AtomicHardySpace.embedding_properties (𝕜 := 𝕜) volume).1
    rw [hu, map_smul, AtomicHardySpace.embedding_atomElement, he]
  have hfinite : AtomicHardySpaceSpec.EmbeddingValue volume u =
      ∑ b ∈ ({a} : Finset (InfinityAtom d 𝕜)), k • b.val := by
    simpa only [Finset.sum_singleton] using hu.trans he.symm
  have hrep := HardyBMODuality.bmoFunctional_represents g {a} (fun _ => k) u hfinite
  simpa only [hu] using hrep

/-- The quantitative local Hardy estimate controls ordinary bounded tests.
The constant here is uniform in p, before choosing a conjugate exponent. -/
lemma bounded_ball_pairing_bound (d : ℕ) : ∃ A : ℝ, 0 < A ∧
    ∀ (p : ℝ), 1 < p → ∀ (𝕜 : Type) [RCLike 𝕜]
      (g : BMOQuotientSpec.BMOFunctionValue d 𝕜) (f : L1 d 𝕜),
    MemLp f (ENNReal.ofReal p) volume → (∫ x, f x) = 0 →
    ∀ (c : Hardy.Point d) (r : ℝ), 0 < r →
    (∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0) →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume, ‖f x‖ ≤ M) →
      Integrable (fun x => f x * g.val x) volume ∧
      ‖∫ x, f x * g.val x‖ ≤ A * (p / (p - 1)) *
        (volume.real (Metric.ball c r)) ^ (1 - 1 / p) *
        (eLpNorm f (ENNReal.ofReal p) volume).toReal *
        (BMOQuotientSpec.BMOENormValue g.val).toReal := by
  obtain ⟨A, hA, hball⟩ := ball_hardy_bound d
  refine ⟨4*A, by positivity, ?_⟩
  intro p hp 𝕜 _ g f hf hz c r hr hs hb
  obtain ⟨M, hM, hb⟩ := hb
  obtain ⟨u, hu, hn⟩ := hball p hp 𝕜 f hf hz c r hr hs
  obtain ⟨hi, he⟩ := bmoFunctional_apply_bounded_ball g f hz c r hr hs M hM hb u hu
  refine ⟨hi, ?_⟩
  rw [← he]
  calc
    ‖HardyBMODuality.bmoFunctional g u‖ ≤ ‖HardyBMODuality.bmoFunctional g‖ * ‖u‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (4 * (bmoENorm g.val).toReal) *
        (A * (p / (p - 1)) * (volume.real (Metric.ball c r)) ^ (1 - 1 / p) *
        (eLpNorm f (ENNReal.ofReal p) volume).toReal) :=
      mul_le_mul (HardyBMODuality.bmoFunctional_norm g) hn (norm_nonneg u) (by positivity)
    _ = _ := by unfold bmoENorm; ring

/-- Subtract the mean without losing support, cancellation, or more than a
factor two in the local Lp norm. All equalities are on actual L¹ classes. -/
lemma center_ball_test {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ} (hp : 1 < p) (f : L1 d 𝕜)
    (hf : MemLp f (ENNReal.ofReal p) volume)
    (c : Hardy.Point d) (r : ℝ) (hr : 0 < r)
    (hs : ∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0) :
    ∃ F : L1 d 𝕜,
      (F : Hardy.Point d → 𝕜) =ᵐ[volume]
        (fun x => f x - (Metric.ball c r).indicator
          (fun _ => (volume.real (Metric.ball c r))⁻¹ • ∫ y, f y) x) ∧
      (∫ x, F x) = 0 ∧ MemLp F (ENNReal.ofReal p) volume ∧
      (eLpNorm F (ENNReal.ofReal p) volume).toReal ≤
        2 * (eLpNorm f (ENNReal.ofReal p) volume).toReal ∧
      (∀ᵐ x ∂volume, x ∉ Metric.ball c r → F x = 0) := by
  let V := volume.real (Metric.ball c r)
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  let m : 𝕜 := V⁻¹ • ∫ x, f x
  let G : L1 d 𝕜 := indicatorConstLp (s := Metric.ball c r) 1 measurableSet_ball measure_ball_ne_top m
  have hG : (G : Hardy.Point d → 𝕜) =ᵐ[volume]
      (Metric.ball c r).indicator (fun _ => m) := indicatorConstLp_coeFn
  have hGp : MemLp G (ENNReal.ofReal p) volume := by
    apply (memLp_indicator_const (ENNReal.ofReal p) measurableSet_ball.nullMeasurableSet m
      (Or.inr measure_ball_ne_top)).ae_eq hG.symm
  have hmean : (∫ x, G x) = ∫ x, f x := by
    rw [integral_congr_ae hG, integral_indicator measurableSet_ball, setIntegral_const]
    change V • (V⁻¹ • ∫ x, f x) = _
    rw [smul_inv_smul₀ hV.ne']
  have hGN : (eLpNorm G (ENNReal.ofReal p) volume).toReal = ‖m‖ * V ^ (1 / p) := by
    rw [eLpNorm_congr_ae hG, eLpNorm_indicator_const measurableSet_ball.nullMeasurableSet
      (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_mul, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _),
      ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by linarith : 0 ≤ p)]
    rfl
  have hnormInt : ‖∫ x, f x‖ ≤ ‖f‖ := by
    rw [L1.norm_eq_integral_norm]
    exact norm_integral_le_integral_norm _
  have hm : ‖m‖ ≤ V⁻¹ * ((eLpNorm f (ENNReal.ofReal p) volume).toReal *
      V ^ (1 - 1 / p)) := by
    dsimp only [m]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hV.le)]
    exact mul_le_mul_of_nonneg_left
      (hnormInt.trans (HardyPAtoms.ball_holder hp f hf c r hr hs)) (inv_nonneg.mpr hV.le)
  have hconst : (eLpNorm G (ENNReal.ofReal p) volume).toReal ≤
      (eLpNorm f (ENNReal.ofReal p) volume).toReal := by
    rw [hGN]
    calc
      ‖m‖ * V ^ (1 / p) ≤ (V⁻¹ *
          ((eLpNorm f (ENNReal.ofReal p) volume).toReal * V ^ (1 - 1 / p))) * V ^ (1 / p) :=
        mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hV.le _)
      _ = (eLpNorm f (ENNReal.ofReal p) volume).toReal := by
        rw [mul_assoc, mul_assoc, ← Real.rpow_add hV,
          sub_add_cancel, Real.rpow_one]
        field_simp
  have hF : ⇑(f - G) =ᵐ[volume] (fun x => f x - (Metric.ball c r).indicator (fun _ => m) x) := by
    filter_upwards [Lp.coeFn_sub f G, hG] with x hx hxG
    simp only [hx, Pi.sub_apply, hxG]
  have hFp : MemLp (⇑(f - G)) (ENNReal.ofReal p) volume :=
    (hf.sub hGp).ae_eq (Lp.coeFn_sub f G).symm
  refine ⟨f - G, hF, ?_, hFp, ?_, ?_⟩
  · rw [integral_congr_ae (Lp.coeFn_sub f G)]
    change (∫ x, f x - G x) = 0
    rw [integral_sub (L1.integrable_coeFn f) (L1.integrable_coeFn G), hmean, sub_self]
  · have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
    have htri := eLpNorm_sub_le (f := (f : Hardy.Point d → 𝕜))
      (g := (G : Hardy.Point d → 𝕜)) (μ := volume) hp1
    have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨hf.eLpNorm_ne_top, hGp.eLpNorm_ne_top⟩) htri
    rw [ENNReal.toReal_add hf.eLpNorm_ne_top hGp.eLpNorm_ne_top] at hh
    rw [eLpNorm_congr_ae (Lp.coeFn_sub f G)]
    linarith
  · filter_upwards [hF, hs] with x hx hxs hxB
    change (f - G : L1 d 𝕜) x = 0
    rw [hx, hxs hxB, Set.indicator_of_notMem hxB, sub_self]

/-- Mean subtraction transfers the mean-zero Hardy test bound to arbitrary
bounded tests supported on the ball. This is the local dual estimate. -/
lemma supported_ball_pairing_bound (d : ℕ) : ∃ A : ℝ, 0 < A ∧
    ∀ (p : ℝ), 1 < p → ∀ (𝕜 : Type) [RCLike 𝕜]
      (g : BMOQuotientSpec.BMOFunctionValue d 𝕜) (f : L1 d 𝕜),
    MemLp f (ENNReal.ofReal p) volume →
    ∀ (c : Hardy.Point d) (r : ℝ), 0 < r →
    (∀ᵐ x ∂volume, x ∉ Metric.ball c r → f x = 0) →
    (∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂volume, ‖f x‖ ≤ M) →
      Integrable (fun x => f x * (g.val x - ballMean g.val c r)) volume ∧
      ‖∫ x, f x * (g.val x - ballMean g.val c r)‖ ≤ A * (p / (p - 1)) *
        (volume.real (Metric.ball c r)) ^ (1 - 1 / p) *
        (eLpNorm f (ENNReal.ofReal p) volume).toReal *
        (BMOQuotientSpec.BMOENormValue g.val).toReal := by
  obtain ⟨A, hA, hpair⟩ := bounded_ball_pairing_bound d
  refine ⟨2*A, by positivity, ?_⟩
  intro p hp 𝕜 _ g f hf c r hr hs hb
  obtain ⟨M, hM, hfb⟩ := hb
  let B := Metric.ball c r
  let V := volume.real B
  let m : 𝕜 := V⁻¹ • ∫ x, f x
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  obtain ⟨F, he, hz, hFp, hFn, hFs⟩ := center_ball_test hp f hf c r hr hs
  have hFb : ∀ᵐ x ∂volume, ‖F x‖ ≤ M + ‖m‖ := by
    filter_upwards [he, hfb] with x hx hxb
    rw [hx]
    change ‖f x - B.indicator (fun _ => m) x‖ ≤ _
    apply (norm_sub_le _ _).trans
    apply add_le_add hxb
    by_cases hxB : x ∈ B
    · simp only [Set.indicator_of_mem hxB, le_refl]
    · simp only [Set.indicator_of_notMem hxB, norm_zero, norm_nonneg]
  obtain ⟨hFi, hFn'⟩ := hpair p hp 𝕜 g F hFp hz c r hr hFs
    ⟨M + ‖m‖, by positivity, hFb⟩
  have hfgi : IntegrableOn (fun x => f x * g.val x) B volume := by
    have h := (integrableOn_ball_of_locallyIntegrable g.property.1 c r).mul_bdd
      (Lp.aestronglyMeasurable f).restrict (ae_restrict_of_ae hfb)
    simpa only [mul_comm, B, IntegrableOn] using h
  have hfg : Integrable (fun x => f x * g.val x) volume := by
    apply (hfgi.integrable_indicator measurableSet_ball).congr
    filter_upwards [hs] with x hx
    by_cases hxB : x ∈ B
    · simp [hxB]
    · simp [hxB, hx hxB]
  have hG : Integrable (fun x => B.indicator (fun _ => m) x * g.val x) volume := by
    have hi : IntegrableOn (fun x => m * g.val x) B volume :=
      (integrableOn_ball_of_locallyIntegrable g.property.1 c r).const_mul m
    apply (hi.integrable_indicator measurableSet_ball).congr
    filter_upwards with x
    by_cases hxB : x ∈ B <;> simp [hxB]
  have hprod : (fun x => F x * g.val x) =ᵐ[volume]
      (fun x => f x * g.val x - B.indicator (fun _ => m) x * g.val x) := by
    filter_upwards [he] with x hx
    change F x * g.val x = _
    rw [hx, sub_mul]
  have hmprod : (∫ x, B.indicator (fun _ => m) x * g.val x) =
      (∫ x, f x) * ballMean g.val c r := by
    have hi : (fun x => B.indicator (fun _ => m) x * g.val x) =
        B.indicator (fun x => m * g.val x) := by
      funext x
      by_cases hxB : x ∈ B <;> simp [hxB]
    rw [hi, integral_indicator measurableSet_ball, integral_const_mul]
    dsimp [m, ballMean, BMOQuotientSpec.MeanValue]
    simp only [Algebra.smul_def, RCLike.algebraMap_eq_ofReal]
    ring
  have hmean := (L1.integrable_coeFn f).mul_const (ballMean g.val c r)
  have heq : (∫ x, F x * g.val x) = ∫ x, f x * (g.val x - ballMean g.val c r) := by
    rw [integral_congr_ae hprod, integral_sub hfg hG, hmprod]
    rw [show (fun x => f x * (g.val x - ballMean g.val c r)) =
      (fun x => f x * g.val x - f x * ballMean g.val c r) by funext x; ring,
      integral_sub hfg hmean, integral_mul_const]
  refine ⟨?_, ?_⟩
  · convert hfg.sub hmean using 1
    funext x
    simp only [Pi.sub_apply]
    ring
  · rw [← heq]
    apply hFn'.trans
    have hpos : 0 ≤ A * (p / (p-1)) * (volume.real (Metric.ball c r)) ^ (1 - 1/p) := by
      positivity
    have hnn := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hFn hpos)
      (ENNReal.toReal_nonneg (a := BMOQuotientSpec.BMOENormValue g.val))
    convert hnn using 1 <;> ring

/-- A local duality criterion proved from bounded tests. Cut off the density,
use the exact Lp pairing norm and density of simple functions, then apply Fatou.
No Lq membership of the original density is assumed. -/
lemma memLp_of_bounded_tests {X : Type} [MeasurableSpace X]
    {𝕜 : Type} [RCLike 𝕜] (μ : Measure X) [IsFiniteMeasure μ]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (w : X → 𝕜) (hw : AEStronglyMeasurable w μ)
    (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ (f : X → 𝕜), MemLp f p μ →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ M) →
      Integrable (fun x => f x * w x) μ ∧
        ‖∫ x, f x * w x ∂μ‖ ≤ D * (eLpNorm f p μ).toReal) :
    MemLp w q μ ∧ eLpNorm w q μ ≤ ENNReal.ofReal D := by
  let S : ℕ → Set X := fun n => {x | ‖w x‖ ≤ (n : ℝ)}
  have hS (n : ℕ) : NullMeasurableSet (S n) μ :=
    nullMeasurableSet_le hw.norm.aemeasurable aemeasurable_const
  let W : ℕ → X → 𝕜 := fun n => (S n).indicator w
  have hWb (n : ℕ) (x : X) : ‖W n x‖ ≤ n := by
    by_cases hx : x ∈ S n
    · simpa only [W, Set.indicator_of_mem hx] using (show ‖w x‖ ≤ n from hx)
    · simp only [W, Set.indicator_of_notMem hx, norm_zero, Nat.cast_nonneg]
  have hW (n : ℕ) : MemLp (W n) q μ :=
    MemLp.of_bound (hw.indicator₀ (hS n)) n (Filter.Eventually.of_forall (hWb n))
  have hnorm (n : ℕ) : eLpNorm (W n) q μ ≤ ENNReal.ofReal D := by
    let g : Lp 𝕜 q μ := (hW n).toLp (W n)
    let L : Lp 𝕜 p μ →L[𝕜] 𝕜 :=
      FunctionSpaces.ScalarLpIntegralPairingSpec.IntegralPairingValue μ p q g
    have hg : ‖g‖ ≤ D := by
      rw [← FunctionSpaces.lp_pairing_exact_norm μ p q hp (Or.inl inferInstance) g]
      change ‖L‖ ≤ D
      apply L.opNorm_le_bound hD
      intro f
      refine (Lp.simpleFunc.denseRange (E := 𝕜) (μ := μ) hp).induction_on f
        (isClosed_le (L.continuous.norm) (continuous_const.mul continuous_norm)) ?_
      intro sf
      let s : SimpleFunc X 𝕜 := Lp.simpleFunc.toSimpleFunc sf
      let t : X → 𝕜 := (S n).indicator s
      have htp : MemLp t p μ := (Lp.simpleFunc.memLp sf).indicator (hS n)
      obtain ⟨M, hMb⟩ := s.exists_forall_norm_le
      have htb : ∀ᵐ x ∂μ, ‖t x‖ ≤ max M 0 := by
        filter_upwards with x
        by_cases hx : x ∈ S n
        · change ‖(S n).indicator s x‖ ≤ max M 0
          rw [Set.indicator_of_mem hx]
          exact (hMb x).trans (le_max_left _ _)
        · simp only [t, Set.indicator_of_notMem hx, norm_zero, le_max_iff, le_refl, or_true]
      obtain ⟨_, htest⟩ := hbound t htp ⟨max M 0, le_max_right _ _, htb⟩
      have he : L (sf : Lp 𝕜 p μ) = ∫ x, t x * w x ∂μ := by
        rw [show L (sf : Lp 𝕜 p μ) = ∫ x, (sf : Lp 𝕜 p μ) x * g x ∂μ from
          (FunctionSpaces.lp_pairing_integral μ p q g sf).2]
        apply integral_congr_ae
        filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun sf, (hW n).coeFn_toLp] with x hsx hwx
        rw [← hsx, hwx]
        change s x * (S n).indicator w x = (S n).indicator s x * w x
        by_cases hx : x ∈ S n <;> simp [hx]
      have htN : (eLpNorm t p μ).toReal ≤ ‖(sf : Lp 𝕜 p μ)‖ := by
        change (eLpNorm t p μ).toReal ≤ ‖sf‖
        rw [Lp.simpleFunc.norm_toSimpleFunc sf]
        exact ENNReal.toReal_mono (Lp.simpleFunc.memLp sf).eLpNorm_ne_top
          (eLpNorm_indicator_le s (hS n))
      rw [he]
      exact htest.trans (mul_le_mul_of_nonneg_left htN hD)
    rw [Lp.norm_toLp] at hg
    rw [← ENNReal.ofReal_toReal (hW n).eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hg
  have hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => W n x) Filter.atTop (nhds (w x)) := by
    filter_upwards with x
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_ge ‖w x‖
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hx : x ∈ S n := hN.trans (by exact_mod_cast hn)
    exact (Set.indicator_of_mem hx w).symm
  have hfinal : eLpNorm w q μ ≤ ENNReal.ofReal D :=
    Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hnorm)
      (fun n => (hW n).aestronglyMeasurable) hw hlim
  exact ⟨hfinal.trans_lt ENNReal.ofReal_lt_top, hfinal⟩

/-- All finite real moments, with a single dimension constant and the
quantitative linear dependence on the exponent. -/
theorem moment_bound : MomentBound := by
  intro d
  obtain ⟨A, hA, htest⟩ := supported_ball_pairing_bound d
  refine ⟨A+1, by positivity, ?_⟩
  intro 𝕜 _ g c r hr q hq
  rcases eq_or_lt_of_le hq with hq1 | hq1
  · subst q
    have h := first_moment d 𝕜 g c r hr
    refine ⟨h.1, h.2.trans ?_⟩
    simp only [one_mul, mul_one]
    have hN := ENNReal.toReal_nonneg (a := BMOQuotientSpec.BMOENormValue g.val)
    nlinarith
  let p := Real.conjExponent q
  have hpq : Real.HolderConjugate p q := (Real.HolderConjugate.conjExponent hq1).symm
  have hp : 1 < p := hpq.lt
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  let P := ENNReal.ofReal p
  let Q := ENNReal.ofReal q
  have hp1 : (1 : ℝ≥0∞) ≤ P := by
    simpa only [P, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  have hq1' : (1 : ℝ≥0∞) ≤ Q := by
    simpa only [Q, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  letI : Fact (1 ≤ P) := ⟨hp1⟩
  letI : Fact (1 ≤ Q) := ⟨hq1'⟩
  letI : ENNReal.HolderConjugate P Q := hpq.ennrealOfReal
  let B := Metric.ball c r
  let V := volume.real B
  let μ : Measure (Hardy.Point d) := volume.restrict B
  let w : Hardy.Point d → 𝕜 := fun x => g.val x - ballMean g.val c r
  let N := (BMOQuotientSpec.BMOENormValue g.val).toReal
  let D := A * q * V ^ (1 / q) * N
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  have hD : 0 ≤ D := by dsimp [D, N]; positivity
  haveI : IsFiniteMeasure μ := ⟨by
    dsimp [μ]
    simpa using (measure_ball_lt_top (μ := (volume : Measure (Hardy.Point d)))
      (x := c) (r := r))⟩
  have hw : AEStronglyMeasurable w μ :=
    g.property.1.aestronglyMeasurable.restrict.sub aestronglyMeasurable_const
  have hbounded (f : Hardy.Point d → 𝕜) (hf : MemLp f P μ)
      (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ M) :
      Integrable (fun x => f x * w x) μ ∧
        ‖∫ x, f x * w x ∂μ‖ ≤ D * (eLpNorm f P μ).toReal := by
    obtain ⟨M, hM, hb⟩ := hb
    have hrawp : MemLp (B.indicator f) P volume :=
      (memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).mpr hf
    have hrawi : Integrable (B.indicator f) volume := by
      have hfi : IntegrableOn f B volume := hf.integrable hp1
      exact hfi.integrable_indicator measurableSet_ball
    let F : L1 d 𝕜 := hrawi.toL1 (B.indicator f)
    have hF : (F : Hardy.Point d → 𝕜) =ᵐ[volume] B.indicator f := hrawi.coeFn_toL1
    have hFp : MemLp F (ENNReal.ofReal p) volume := hrawp.ae_eq hF.symm
    have hFs : ∀ᵐ x ∂volume, x ∉ B → F x = 0 := by
      filter_upwards [hF] with x hx hxB
      rw [hx, Set.indicator_of_notMem hxB]
    have hFb : ∀ᵐ x ∂volume, ‖F x‖ ≤ M := by
      have hblocal : ∀ᵐ x ∂volume, x ∈ B → ‖f x‖ ≤ M :=
        (ae_restrict_iff' measurableSet_ball).mp hb
      filter_upwards [hF, hblocal] with x hx hxb
      by_cases hxB : x ∈ B
      · simpa only [hx, Set.indicator_of_mem hxB] using hxb hxB
      · simpa only [hx, Set.indicator_of_notMem hxB, norm_zero] using hM
    obtain ⟨hFi, hn⟩ := htest p hp 𝕜 g F hFp c r hr hFs ⟨M, hM, hFb⟩
    have hprod : (fun x => F x * w x) =ᵐ[volume] B.indicator (fun x => f x * w x) := by
      filter_upwards [hF] with x hx
      rw [hx]
      by_cases hxB : x ∈ B <;> simp [hxB]
    have hi : Integrable (fun x => f x * w x) μ :=
      (integrable_indicator_iff measurableSet_ball).mp (hFi.congr hprod)
    have he : (∫ x, F x * w x) = ∫ x, f x * w x ∂μ := by
      rw [integral_congr_ae hprod, integral_indicator measurableSet_ball]
    have hnorm : (eLpNorm F (ENNReal.ofReal p) volume).toReal =
        (eLpNorm f P μ).toReal := by
      rw [eLpNorm_congr_ae hF,
        eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet]
    refine ⟨hi, ?_⟩
    rw [← he]
    apply hn.trans_eq
    rw [hnorm, ← hpq.conjugate_eq]
    have hexp : 1 - 1 / p = 1 / q := by simpa only [one_div] using hpq.one_sub_inv
    rw [hexp]
    dsimp [D, V, B, N]
    ring
  obtain ⟨hwp, hnorm⟩ := memLp_of_bounded_tests μ P Q ENNReal.ofReal_ne_top w hw D hD hbounded
  have hn : (eLpNorm w Q μ).toReal ≤ D := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    simpa only [ENNReal.toReal_ofReal hD] using h
  have hi : IntegrableOn (fun x => oscillation g.val c r x ^ q) B volume := by
    have h := hwp.integrable_norm_rpow (by dsimp [Q]; positivity) ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal hq0.le, Q, w, oscillation, ballMean,
      μ, IntegrableOn] using h
  have he : (eLpNorm w Q μ).toReal =
      (∫ x, oscillation g.val c r x ^ q ∂μ) ^ (1 / q) := by
    rw [hwp.eLpNorm_eq_integral_rpow_norm (by dsimp [Q]; positivity) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)]
    simp only [Q, ENNReal.toReal_ofReal hq0.le, w, oscillation, ballMean, one_div]
  refine ⟨hi, ?_⟩
  have hIN : 0 ≤ ∫ x, oscillation g.val c r x ^ q ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  calc
    (V⁻¹ * ∫ x, oscillation g.val c r x ^ q ∂μ) ^ (1 / q) =
        (V ^ (1 / q))⁻¹ * (eLpNorm w Q μ).toReal := by
      rw [Real.mul_rpow (inv_nonneg.mpr hV.le) hIN, Real.inv_rpow hV.le, he]
    _ ≤ (V ^ (1 / q))⁻¹ * D :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (Real.rpow_nonneg hV.le _))
    _ = A * q * N := by
      dsimp [D]
      have hpow : V ^ (1 / q) ≠ 0 := (Real.rpow_pos_of_pos hV _).ne'
      field_simp
    _ ≤ (A+1) * q * N := by
      dsimp [N]
      nlinarith [ENNReal.toReal_nonneg (a := BMOQuotientSpec.BMOENormValue g.val)]

/-- Linear growth of integer moments gives a uniform exponential average.
This abstract step is independent of the BMO argument. -/
lemma exponential_of_integer_moments {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (u : X → ℝ) (K : ℝ) (hK : 0 < K)
    (hu : ∀ x, 0 ≤ u x)
    (hm : ∀ n : ℕ, Integrable (fun x => u x ^ n) μ ∧
      (∫ x, u x ^ n ∂μ) ≤ μ.real Set.univ * (K * n) ^ n) :
    Integrable (fun x => Real.exp (u x / (2 * Real.exp 1 * K))) μ ∧
      (∫ x, Real.exp (u x / (2 * Real.exp 1 * K)) ∂μ) ≤
        2 * μ.real Set.univ := by
  let a : ℝ := (2 * Real.exp 1 * K)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  let F : ℕ → X → ℝ := fun n x => (a * u x) ^ n / (n.factorial : ℝ)
  have hF (n : ℕ) : Integrable (F n) μ := by
    simpa only [F, mul_pow, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      ((hm n).1.const_mul (a ^ n / (n.factorial : ℝ)))
  have hnon (n : ℕ) (x : X) : 0 ≤ F n x :=
    div_nonneg (pow_nonneg (mul_nonneg ha.le (hu x)) n) (Nat.cast_nonneg _)
  have hnorm (n : ℕ) : (∫ x, ‖F n x‖ ∂μ) = ∫ x, F n x ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => Real.norm_of_nonneg (hnon n x)
  have hcoef : a * K * Real.exp 1 = (1 / 2 : ℝ) := by
    dsimp [a]
    field_simp
  have hb (n : ℕ) : (∫ x, F n x ∂μ) ≤ μ.real Set.univ * (1 / 2 : ℝ)^n := by
    calc
      (∫ x, F n x ∂μ) = (a ^ n / (n.factorial : ℝ)) * (∫ x, u x ^ n ∂μ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        dsimp [F]
        rw [mul_pow]
        ring
      _ ≤ (a ^ n / (n.factorial : ℝ)) * (μ.real Set.univ * (K * n) ^ n) :=
        mul_le_mul_of_nonneg_left (hm n).2 (by positivity)
      _ = μ.real Set.univ * (a*K)^n * ((n : ℝ)^n / (n.factorial : ℝ)) := by
        rw [mul_pow, mul_pow]
        ring
      _ ≤ μ.real Set.univ * (a*K)^n * Real.exp (n : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n)
          (by positivity)
      _ = μ.real Set.univ * (1 / 2 : ℝ)^n := by
        rw [show (n : ℝ) = (n : ℝ) * 1 by ring, Real.exp_nat_mul, mul_assoc,
          ← mul_pow, hcoef]
  have hsgeo : Summable (fun n : ℕ => μ.real Set.univ * (1 / 2 : ℝ)^n) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  have hs : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg (F n x))
      (fun n => ?_) hsgeo
    rw [hnorm]
    exact hb n
  have he (x : X) : (∑' n, F n x) = Real.exp (u x / (2 * Real.exp 1 * K)) := by
    rw [show u x / (2 * Real.exp 1 * K) = a * u x by dsimp [a]; ring]
    exact by
      simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp (a * u x)).tsum_eq
  have hi := (integrable_tsum_of_summable_integral_norm F hF hs).1
  refine ⟨by simpa only [he] using hi, ?_⟩
  calc
    (∫ x, Real.exp (u x / (2 * Real.exp 1 * K)) ∂μ) = ∑' n, ∫ x, F n x ∂μ := by
      rw [integral_tsum_of_summable_integral_norm hF hs]
      simp only [he]
    _ ≤ ∑' n, μ.real Set.univ * (1 / 2 : ℝ)^n :=
      (hs.congr (fun n => hnorm n)).tsum_le_tsum hb hsgeo
    _ = 2 * μ.real Set.univ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
      ring

/-- Integer moment specialization and absolute convergence of the exponential
series give constants uniform in the ball and in the BMO function. -/
theorem moment_to_exponential : MomentToExponential := by
  intro hm d
  obtain ⟨A, hA, hmoment⟩ := hm d
  refine ⟨(2 * Real.exp 1 * A)⁻¹, 2, by positivity, by norm_num, ?_⟩
  intro 𝕜 _ g c r hr hne
  let V : ℝ := volume.real (Metric.ball c r)
  let N : ℝ := (BMOQuotientSpec.BMOENormValue g.val).toReal
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hr).ne' measure_ball_ne_top
  have hN : 0 < N := ENNReal.toReal_pos hne g.property.2.ne
  let μ : Measure (Hardy.Point d) := volume.restrict (Metric.ball c r)
  haveI : IsFiniteMeasure μ := ⟨by
    dsimp [μ]
    simpa using (measure_ball_lt_top (μ := (volume : Measure (Hardy.Point d)))
      (x := c) (r := r))⟩
  have hreal : μ.real Set.univ = V := by simp [μ, V, Measure.real]
  have hi (n : ℕ) : Integrable (fun x => oscillation g.val c r x ^ n) μ ∧
      (∫ x, oscillation g.val c r x ^ n ∂μ) ≤ μ.real Set.univ * (A * N * n) ^ n := by
    by_cases hn0 : n = 0
    · subst n
      simp
    have hn : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    have hnpos : (0 : ℝ) < n := by linarith
    have h := hmoment 𝕜 g c r hr n hn
    have hI : 0 ≤ V⁻¹ * ∫ x, oscillation g.val c r x ^ n ∂μ := by
      apply mul_nonneg (inv_nonneg.mpr hV.le)
      exact integral_nonneg fun x => pow_nonneg (norm_nonneg _) _
    have h2 : (V⁻¹ * ∫ x, oscillation g.val c r x ^ n ∂μ) ^ (1 / (n : ℝ)) ≤
        A * (n : ℝ) * N := by
      simpa only [V, μ, N, Real.rpow_natCast] using h.2
    have hpow := Real.rpow_le_rpow
      (Real.rpow_nonneg hI (1 / (n : ℝ))) h2 hnpos.le
    simp only [one_div, Real.rpow_inv_rpow hI (ne_of_gt hnpos), Real.rpow_natCast] at hpow
    have hpow' : V⁻¹ * (∫ x, oscillation g.val c r x ^ n ∂μ) ≤ (A * N * n)^n := by
      simpa only [V, μ, Real.rpow_natCast, mul_assoc, mul_comm, mul_left_comm] using hpow
    refine ⟨by simpa only [Real.rpow_natCast, IntegrableOn, μ] using h.1, ?_⟩
    rw [hreal]
    exact (inv_mul_le_iff₀ hV).mp hpow'
  obtain ⟨hint, hbound⟩ := exponential_of_integer_moments μ
    (oscillation g.val c r) (A*N) (mul_pos hA hN)
    (fun x => norm_nonneg _) hi
  have he (x : Hardy.Point d) :
      oscillation g.val c r x / (2 * Real.exp 1 * (A*N)) =
        (2 * Real.exp 1 * A)⁻¹ * oscillation g.val c r x / N := by
    field_simp
  refine ⟨by simpa only [he, N, μ, IntegrableOn] using hint, ?_⟩
  change V⁻¹ * _ ≤ 2
  have hh : (∫ x, Real.exp ((2 * Real.exp 1 * A)⁻¹ *
      oscillation g.val c r x / N) ∂μ) ≤ V * 2 := by
    simpa only [he, hreal, mul_comm] using hbound
  exact (inv_mul_le_iff₀ hV).mpr hh

/-- Exponential integrability follows from the quantitative moment theorem. -/
theorem exponential_bound : ExponentialBound := moment_to_exponential moment_bound

end ExpandedFA.PartIV.JohnNirenberg
