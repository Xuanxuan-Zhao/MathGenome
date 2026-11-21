import MathGenome.Internal.FourierSobolev.Specs.P102.U3.PeriodicConjugationBound
import MathGenome.Internal.FourierSobolev.P102.U3.RieszTransforms
import MathGenome.Internal.FourierSobolev.P102.Periodic.Foundation
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace P102.U3.PeriodicConjugationBound
open P102.Specs.U3 (Euclidean)
open P102.Specs.U3.Riesz (line kernelValue truncation)

/-- The exact coordinate equivalence used by the upstream Hilbert theorem. -/
def lineEquiv : ℝ ≃ₗᵢ[ℝ] Euclidean 1 where
  toLinearEquiv := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm.toLinearEquiv
  norm_map' x := by
    change ‖WithLp.toLp 2 (Function.const (Fin 1) x)‖ = ‖x‖
    simp [PiLp.norm_toLp_const]

@[simp] theorem lineEquiv_apply (x : ℝ) : lineEquiv x = line x := rfl

@[simp] theorem lineEquiv_symm_apply (x : Euclidean 1) : lineEquiv.symm x = x 0 := rfl

theorem line_measurePreserving :
    MeasurePreserving line (volume : Measure ℝ) (volume : Measure (Euclidean 1)) :=
  lineEquiv.measurePreserving

theorem line_symm_measurePreserving :
    MeasurePreserving (fun x : Euclidean 1 => x 0) volume (volume : Measure ℝ) :=
  lineEquiv.symm.measurePreserving

@[simp] theorem norm_line (x : ℝ) : ‖line x‖ = |x| := by
  simpa only [lineEquiv_apply, Real.norm_eq_abs] using lineEquiv.norm_map x

/-- Ordinary real-line truncations are exactly the Euclidean truncations,
including their cutoff set, Lebesgue measure, and the factor 1/π. -/
theorem truncation_line (ε : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    truncation (0 : Fin 1) ε (fun y => f (y 0)) (line x) =
      ∫ t in {t : ℝ | ε < |t|}, ((1 / (Real.pi * t) : ℝ) : ℂ) * f (x - t) := by
  have h := line_measurePreserving.setIntegral_preimage_emb
    lineEquiv.toMeasurableEquiv.measurableEmbedding
    (fun z : Euclidean 1 => (kernelValue 1 0 z : ℂ) * f ((line x - z) 0))
    {z : Euclidean 1 | ε < ‖z‖}
  have hk := P102.U3.RieszTransforms.hilbert_theorem.1.2.1
  have hcoord (t : ℝ) : (line x - line t) 0 = x - t := rfl
  simpa only [truncation, Set.preimage_ofPred_eq, norm_line, hk, hcoord] using h.symm

/-- The authorized Euclidean theorem transported to ordinary real Lebesgue
measure. The finite bound is uniform over all inputs; no periodic estimate is
used. The output is a representative of the bounded Lp action. -/
theorem real_hilbert_bound (p : P102.U2.CZLpData.Exponent) :
    ∃ C : ℝ≥0, ∀ (f : ℝ → ℂ), MemLp f p.val volume →
      ∃ g : ℝ → ℂ, MemLp g p.val volume ∧
        eLpNorm g p.val volume ≤ (C : ℝ≥0∞) * eLpNorm f p.val volume ∧
        (∀ ε : ℝ, 0 < ε → ∀ x : ℝ, IntegrableOn
          (fun t : ℝ => ((1 / (Real.pi * t) : ℝ) : ℂ) * f (x - t))
          {t : ℝ | ε < |t|}) ∧
        (∀ᵐ x ∂(volume : Measure ℝ),
          Tendsto (fun ε => ∫ t in {t : ℝ | ε < |t|},
            ((1 / (Real.pi * t) : ℝ) : ℂ) * f (x - t)) (𝓝[>] 0) (𝓝 (g x))) := by
  obtain ⟨_T, _S, R, _C₁, _C, _hT, _hTnorm, _hcompat, _hweak, _huniq,
    _hRnorm, _hagree, _hpair, _hend, hconv, _hunique⟩ :=
    P102.U3.RieszTransforms.hilbert_theorem.2
  refine ⟨‖R p‖₊, ?_⟩
  intro f hf
  let fE : Euclidean 1 → ℂ := fun y => f (y 0)
  have hfE : MemLp fE p.val volume := hf.comp_measurePreserving line_symm_measurePreserving
  let u := R p (hfE.toLp fE)
  let g : ℝ → ℂ := fun x => u (line x)
  have hg : MemLp g p.val volume := (Lp.memLp u).comp_measurePreserving line_measurePreserving
  have hinput : eLpNorm fE p.val volume = eLpNorm f p.val volume :=
    eLpNorm_comp_measurePreserving hf.aestronglyMeasurable line_symm_measurePreserving
  have houtput : eLpNorm g p.val volume = eLpNorm u p.val volume :=
    eLpNorm_comp_measurePreserving (Lp.memLp u).aestronglyMeasurable line_measurePreserving
  obtain ⟨hi, _hm, hlim, _hnorm⟩ := hconv p fE hfE
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · rw [houtput, ← Lp.enorm_def]
    calc
      ‖u‖ₑ ≤ ‖R p‖ₑ * ‖hfE.toLp fE‖ₑ := (R p).le_opENorm _
      _ = (‖R p‖₊ : ℝ≥0∞) * eLpNorm f p.val volume := by
        rw [Lp.enorm_toLp hfE, hinput]
        rfl
  · intro ε hε x
    have h := line_measurePreserving.integrableOn_comp_preimage
      lineEquiv.toMeasurableEquiv.measurableEmbedding
      (f := fun z : Euclidean 1 => (kernelValue 1 0 z : ℂ) * fE (line x - z))
      (s := {z : Euclidean 1 | ε < ‖z‖})
    have hk := P102.U3.RieszTransforms.hilbert_theorem.1.2.1
    have hcoord (t : ℝ) : fE (line x - line t) = f (x - t) := rfl
    simpa only [Function.comp_def, Set.preimage_ofPred_eq, norm_line, hk, hcoord] using
      h.mpr (hi ε hε (line x))
  · have hl := line_measurePreserving.quasiMeasurePreserving.ae hlim
    filter_upwards [hl] with x hx
    simpa only [fE, truncation_line] using hx

lemma cot_sub_inv_bound (y : ℝ) (hy : |y| ≤ Real.pi / 2) :
    |Real.cot y - 1 / y| ≤ 4 := by
  by_cases h0 : y = 0
  · subst y
    simp [Real.cot_eq_cos_div_sin]
  have hy0 : 0 < |y| := abs_pos.mpr h0
  have hy2 : |y| ≤ 2 := by linarith [Real.pi_lt_four]
  have hs := Real.mul_abs_le_abs_sin hy
  have hs0 : 0 < |Real.sin y| := lt_of_lt_of_le (by positivity) hs
  have hsne : Real.sin y ≠ 0 := abs_pos.mp hs0
  have hc : |Real.cos y - 1| ≤ |y| := by
    simpa using Real.abs_cos_sub_cos_le y 0
  have hnum : |y * Real.cos y - Real.sin y| ≤ 2 * |y| ^ 2 := by
    calc
      _ = |y * (Real.cos y - 1) + (y - Real.sin y)| := by congr 1; ring
      _ ≤ |y * (Real.cos y - 1)| + |y - Real.sin y| := abs_add_le _ _
      _ ≤ |y| * |y| + |y| ^ 3 / 6 := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg _)) (Real.abs_sub_sin_le y)
      _ ≤ 2 * |y| ^ 2 := by
        have hcube : |y| ^ 3 ≤ 2 * |y| ^ 2 := by nlinarith [sq_nonneg |y|, mul_nonneg (sq_nonneg |y|) (sub_nonneg.mpr hy2)]
        nlinarith [sq_nonneg |y|]
  have hden : (1/2 : ℝ) * |y| ^ 2 ≤ |y * Real.sin y| := by
    rw [abs_mul]
    have hp : (1/2 : ℝ) ≤ 2 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      linarith [Real.pi_lt_four]
    have hs' : (1/2 : ℝ) * |y| ≤ |Real.sin y| :=
      (mul_le_mul_of_nonneg_right hp (abs_nonneg _)).trans hs
    nlinarith [mul_nonneg (abs_nonneg y) (sub_nonneg.mpr hs')]
  rw [Real.cot_eq_cos_div_sin, div_sub_div _ _ hsne h0, abs_div]
  apply (div_le_iff₀ (abs_pos.mpr (mul_ne_zero hsne h0))).mpr
  rw [abs_mul, mul_comm |Real.sin y| |y|] at *
  nlinarith [show |Real.cos y * y - Real.sin y * 1| = |y * Real.cos y - Real.sin y| by congr 1; ring]

lemma coordinate_remainder_bound (T : ℝ) (hT : 0 < T) (t : ℝ)
    (ht : |t| ≤ T / 2) :
    |T⁻¹ * Real.cot (Real.pi * t / T) - 1 / (Real.pi * t)| ≤ 4 / T := by
  have harg : |Real.pi * t / T| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hT,
      div_le_iff₀ hT]
    nlinarith [Real.pi_pos]
  have heq : T⁻¹ * Real.cot (Real.pi * t / T) - 1 / (Real.pi * t) =
      T⁻¹ * (Real.cot (Real.pi * t / T) - 1 / (Real.pi * t / T)) := by
    by_cases ht0 : t = 0
    · simp [ht0]
    · field_simp
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hT)]
  calc
    _ ≤ T⁻¹ * 4 := mul_le_mul_of_nonneg_left (cot_sub_inv_bound _ harg) (inv_nonneg.mpr hT.le)
    _ = 4 / T := by ring

lemma coordinate_remainder_integrable (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => T⁻¹ * Real.cot (Real.pi * t / T) - 1 / (Real.pi * t))
      (Icc (-(T / 2)) (T / 2)) := by
  apply IntegrableOn.of_bound (by simp) (C := 4 / T)
  · simp only [Real.cot_eq_cos_div_sin]
    exact (by fun_prop : Measurable (fun t : ℝ =>
      T⁻¹ * (Real.cos (Real.pi * t / T) / Real.sin (Real.pi * t / T)) -
        1 / (Real.pi * t))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs]
    exact coordinate_remainder_bound T hT t (abs_le.mpr ht)

open P102.Periodic.Expected
variable (T : ℝ) [Fact (0 < T)]

/-- Normalization on the real line is useful for all localization estimates. -/
def normalizedLine : Measure ℝ := ENNReal.ofReal T⁻¹ • volume

def periodPiece (a : ℝ) (f : Circle T → ℂ) : ℝ → ℂ :=
  (Ioc a (a + T)).indicator (fun t => f (t : Circle T))

lemma periodPiece_norm (a : ℝ) (p : ℝ≥0∞) (f : Circle T → ℂ)
    (hf : AEStronglyMeasurable f (haar T)) :
    eLpNorm (periodPiece T a f) p (normalizedLine T) = eLpNorm f p (haar T) := by
  rw [periodPiece, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc.nullMeasurableSet]
  change eLpNorm (f ∘ (fun t : ℝ => (t : Circle T))) p
    ((ENNReal.ofReal T⁻¹ • volume).restrict (Ioc a (a + T))) = _
  rw [Measure.restrict_smul]
  exact eLpNorm_comp_measurePreserving hf (P102.Periodic.interval_measure T a)

/-- Three neighboring periods suffice for x∈(0,T), |t|<T/2. -/
def localized (f : Circle T → ℂ) : ℝ → ℂ :=
  periodPiece T (-T) f + periodPiece T 0 f + periodPiece T T f

lemma localized_norm_le (p : P102.U2.CZLpData.Exponent) (f : Circle T → ℂ)
    (hf : AEStronglyMeasurable f (haar T)) :
    eLpNorm (localized T f) p.val (normalizedLine T) ≤
      3 * eLpNorm f p.val (haar T) := by
  calc
    _ ≤ eLpNorm (periodPiece T (-T) f + periodPiece T 0 f) p.val (normalizedLine T) +
        eLpNorm (periodPiece T T f) p.val (normalizedLine T) := eLpNorm_add_le (f := periodPiece T (-T) f + periodPiece T 0 f) (g := periodPiece T T f) p.one_lt.le
    _ ≤ (eLpNorm (periodPiece T (-T) f) p.val (normalizedLine T) +
        eLpNorm (periodPiece T 0 f) p.val (normalizedLine T)) +
        eLpNorm (periodPiece T T f) p.val (normalizedLine T) :=
      add_le_add (eLpNorm_add_le (μ := normalizedLine T) (f := periodPiece T (-T) f) (g := periodPiece T 0 f) p.one_lt.le) le_rfl
    _ = _ := by
      rw [periodPiece_norm T (-T) p.val f hf, periodPiece_norm T 0 p.val f hf,
        periodPiece_norm T T p.val f hf]
      simp only [show (3 : ℝ≥0∞) = 1+1+1 by norm_num, add_mul, one_mul]

lemma localized_eq (f : Circle T → ℂ) (y : ℝ) :
    localized T f y = (Ioc (-T) (2*T)).indicator (fun t => f (t : Circle T)) y := by
  have hT : 0 < T := Fact.out
  simp only [localized, periodPiece, Pi.add_apply, neg_add_cancel, zero_add,
    ← two_mul, Set.indicator_apply, mem_Ioc]
  split_ifs <;> grind

lemma localized_agrees (f : Circle T → ℂ) (x t : ℝ)
    (hx : x ∈ Ioo 0 T) (ht : |t| < T/2) :
    localized T f (x-t) = f ((x : Circle T) - (t : Circle T)) := by
  have hT : 0 < T := Fact.out
  have hm : x-t ∈ Ioc (-T) (2*T) := by
    obtain ⟨hx0, hxT⟩ := hx
    obtain ⟨ht0, htT⟩ := abs_lt.mp ht
    constructor <;> linarith
  rw [localized_eq, Set.indicator_of_mem hm]
  congr 1

/-- The local real-line singular kernel, with pointwise subtraction. -/
def linePart (f : Circle T → ℂ) (x : Circle T) : ℂ :=
  ∫ t in Ioo (-(T / 2)) (T / 2),
    ((1 / (Real.pi * t) : ℝ) : ℂ) * (f (x - (t : Circle T)) - f x)

/-- The bounded difference between the periodic and real-line kernels. -/
def remainderPart (f : Circle T → ℂ) (x : Circle T) : ℂ :=
  ∫ t in Ioo (-(T / 2)) (T / 2),
    ((T⁻¹ * Real.cot (Real.pi * t / T) - 1 / (Real.pi * t) : ℝ) : ℂ) *
      (f (x - (t : Circle T)) - f x)

/-- A proof-internal estimate, including the integral existence used in assembly. -/
def LineEstimate (p : P102.U2.CZLpData.Exponent) : Prop :=
  ∃ A : ℝ≥0, ∀ c : ℤ →₀ ℂ,
    (∀ x : Circle T, IntegrableOn (fun t : ℝ =>
      ((1 / (Real.pi * t) : ℝ) : ℂ) *
        (synthesis T c (x - (t : Circle T)) - synthesis T c x))
      (Ioo (-(T / 2)) (T / 2))) ∧
    eLpNorm (linePart T (synthesis T c)) p.val (haar T) ≤
      (A : ℝ≥0∞) * eLpNorm (synthesis T c) p.val (haar T)

/-- A proof-internal estimate for the integrable kernel remainder. -/
def RemainderEstimate (p : P102.U2.CZLpData.Exponent) : Prop :=
  ∃ B : ℝ≥0, ∀ c : ℤ →₀ ℂ,
    (∀ x : Circle T, IntegrableOn (fun t : ℝ =>
      ((T⁻¹ * Real.cot (Real.pi * t / T) - 1 / (Real.pi * t) : ℝ) : ℂ) *
        (synthesis T c (x - (t : Circle T)) - synthesis T c x))
      (Ioo (-(T / 2)) (T / 2))) ∧
    eLpNorm (remainderPart T (synthesis T c)) p.val (haar T) ≤
      (B : ℝ≥0∞) * eLpNorm (synthesis T c) p.val (haar T)

/-- Combine two proved physical estimates for the canonical cancelled integral. -/
theorem assemble (p : P102.U2.CZLpData.Exponent)
    (hline : LineEstimate T p) (hrem : RemainderEstimate T p) :
    P102.Periodic.Conjugation.CancelledBound T p := by
  obtain ⟨A, hA⟩ := hline
  obtain ⟨B, hB⟩ := hrem
  refine ⟨A + B, ?_⟩
  intro c
  obtain ⟨hiA, hnA⟩ := hA c
  obtain ⟨hiB, hnB⟩ := hB c
  have hsplit : P102.Periodic.Conjugation.cancelledValue T (synthesis T c) =
      linePart T (synthesis T c) + remainderPart T (synthesis T c) := by
    funext x
    simp only [P102.Periodic.Conjugation.cancelledValue,
      P102.Periodic.Conjugation.coordinateKernel, neg_div, Pi.add_apply]
    rw [linePart, remainderPart, ← integral_add (hiA x) (hiB x)]
    apply integral_congr_ae
    filter_upwards [] with t
    push_cast
    ring
  rw [hsplit]
  calc
    _ ≤ eLpNorm (linePart T (synthesis T c)) p.val (haar T) +
        eLpNorm (remainderPart T (synthesis T c)) p.val (haar T) :=
      eLpNorm_add_le p.one_lt.le
    _ ≤ (A : ℝ≥0∞) * eLpNorm (synthesis T c) p.val (haar T) +
        (B : ℝ≥0∞) * eLpNorm (synthesis T c) p.val (haar T) := add_le_add hnA hnB
    _ = _ := by rw [ENNReal.coe_add, add_mul]

end P102.U3.PeriodicConjugationBound

namespace P102.U3.PeriodicConjugationBound
open P102.Periodic.Expected

 theorem line_cancel_integrable {f : ℝ → ℂ} (hf : Continuous f)
    (hd : DifferentiableAt ℝ f 0) (a b : ℝ) :
    IntegrableOn (fun t : ℝ => ((1 / (Real.pi * t) : ℝ) : ℂ) * (f t - f 0))
      (Ioo a b) volume := by
  have hc : Continuous (fun t : ℝ => (Real.pi⁻¹ : ℝ) • dslope f 0 t) := by
    have hs : Continuous (dslope f 0) := continuous_iff_continuousAt.mpr fun t => by
      by_cases ht : t = 0
      · subst t; exact continuousAt_dslope_same.mpr hd
      · exact (continuousAt_dslope_of_ne ht).mpr hf.continuousAt
    exact hs.const_smul (Real.pi⁻¹ : ℝ)
  have hi : IntegrableOn (fun t : ℝ => (Real.pi⁻¹ : ℝ) • dslope f 0 t) (Icc a b) volume :=
    hc.continuousOn.integrableOn_Icc
  refine (hi.mono_set Ioo_subset_Icc_self).congr ?_
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht
  rw [dslope_of_ne _ ht, slope_def_module]
  simp only [sub_zero, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    one_div, mul_inv_rev]
  ring

 theorem synthesis_coordinate_differentiable (T : ℝ) (c : ℤ →₀ ℂ) (x : Circle T) :
    Differentiable ℝ (fun t : ℝ => synthesis T c (x - (t : Circle T))) := by
  induction x using QuotientAddGroup.induction_on with | H x =>
    change Differentiable ℝ (fun t : ℝ =>
      (Finsupp.linearCombination ℂ (mode T)) c ((x : Circle T) - (t : Circle T)))
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, ContinuousMap.coe_sum,
      Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    apply Differentiable.fun_sum
    intro n hn
    simp only [← QuotientAddGroup.mk_sub, mode, fourier_coe_apply]
    fun_prop

end P102.U3.PeriodicConjugationBound

namespace P102.U3.PeriodicConjugationBound

 theorem tendsto_integral_cutoff {a b : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ioo a b) volume) :
    Tendsto (fun ε : ℝ => ∫ t in Ioo a b ∩ {t : ℝ | ε < |t|}, f t)
      (𝓝[>] 0) (𝓝 (∫ t in Ioo a b, f t)) := by
  have hm (ε : ℝ) : MeasurableSet {t : ℝ | ε < |t|} := by measurability
  have hi (ε : ℝ) :
      (∫ t in Ioo a b ∩ {t : ℝ | ε < |t|}, f t) =
        ∫ t in Ioo a b, ({t : ℝ | ε < |t|}).indicator f t := by
    rw [integral_indicator (hm ε), Measure.restrict_restrict (hm ε), inter_comm]
  simp_rw [hi]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t‖)
  · exact Eventually.of_forall fun ε => hf.aestronglyMeasurable.indicator (hm ε)
  · exact Eventually.of_forall fun ε => Eventually.of_forall fun t =>
      norm_indicator_le_norm_self _ t
  · exact hf.norm
  · filter_upwards [(volume.restrict (Ioo a b)).ae_ne 0] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_lt_nhds (abs_pos.mpr ht)).filter_mono nhdsWithin_le_nhds] with ε hε
    simp only [indicator_of_mem (show t ∈ {t : ℝ | ε < |t|} from hε) f]

end P102.U3.PeriodicConjugationBound

namespace P102.U3.PeriodicConjugationBound

 theorem integral_lineKernel_cutoff_eq_zero (A ε : ℝ) :
    (∫ t in Ioo (-A) A ∩ {t : ℝ | ε < |t|}, ((1 / (Real.pi * t) : ℝ) : ℂ)) = 0 := by
  let S := Ioo (-A) A ∩ {t : ℝ | ε < |t|}
  let K := fun t : ℝ => ((1 / (Real.pi * t) : ℝ) : ℂ)
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hneg (t : ℝ) : -t ∈ S ↔ t ∈ S := by
    simp only [S, mem_inter_iff, mem_Ioo, mem_ofPred_eq, abs_neg]
    constructor <;> intro h <;> refine ⟨⟨?_, ?_⟩, h.2⟩ <;> linarith [h.1.1, h.1.2]
  have hK (t : ℝ) : K (-t) = -K t := by simp [K]
  have hi := integral_neg_eq_self (S.indicator K) (volume : Measure ℝ)
  have heq : (fun t : ℝ => S.indicator K (-t)) = fun t => -S.indicator K t := by
    funext t
    by_cases ht : t ∈ S
    · rw [indicator_of_mem ht, indicator_of_mem ((hneg t).mpr ht), hK]
    · rw [indicator_of_notMem ht, indicator_of_notMem (mt (hneg t).mp ht), neg_zero]
  rw [heq, integral_neg, integral_indicator hS] at hi
  dsimp [S, K] at hi
  linear_combination (-1 / 2 : ℂ) * hi

end P102.U3.PeriodicConjugationBound

namespace P102.U3.PeriodicConjugationBound

 theorem line_truncation_integrable {f : ℝ → ℂ} (hf : Continuous f)
    (A ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => ((1 / (Real.pi * t) : ℝ) : ℂ) * f t)
      (Ioo (-A) A ∩ {t : ℝ | ε < |t|}) volume := by
  let S := Icc (-A) A ∩ {t : ℝ | ε ≤ |t|}
  have hS : IsCompact S := isCompact_Icc.inter_right
    (isClosed_le continuous_const continuous_abs)
  have hK : ContinuousOn (fun t : ℝ => ((1 / (Real.pi * t) : ℝ) : ℂ)) S := by
    apply Complex.continuous_ofReal.comp_continuousOn
    apply continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    intro t ht
    exact mul_ne_zero Real.pi_ne_zero (by
      have hp : 0 < |t| := hε.trans_le ht.2
      exact abs_pos.mp hp)
  have hi : IntegrableOn (fun t : ℝ => ((1 / (Real.pi * t) : ℝ) : ℂ) * f t) S volume :=
    (hK.mul hf.continuousOn).integrableOn_compact hS
  exact hi.mono_set fun t ht => ⟨⟨ht.1.1.le, ht.1.2.le⟩, (show ε < |t| from ht.2).le⟩

 theorem line_truncation_eq_cancelled {f : ℝ → ℂ} (hf : Continuous f)
    (A ε : ℝ) (hε : 0 < ε) :
    (∫ t in Ioo (-A) A ∩ {t : ℝ | ε < |t|}, ((1 / (Real.pi * t) : ℝ) : ℂ) * f t) =
    ∫ t in Ioo (-A) A ∩ {t : ℝ | ε < |t|},
      ((1 / (Real.pi * t) : ℝ) : ℂ) * (f t - f 0) := by
  have hi := line_truncation_integrable hf A ε hε
  have hK : IntegrableOn (fun t : ℝ => ((1 / (Real.pi * t) : ℝ) : ℂ))
      (Ioo (-A) A ∩ {t : ℝ | ε < |t|}) volume := by
    simpa only [mul_one] using line_truncation_integrable continuous_const A ε hε (f := fun _ => 1)
  have h := integral_sub hi (hK.mul_const (f 0))
  simp_rw [← mul_sub] at h
  rw [integral_mul_const, integral_lineKernel_cutoff_eq_zero, zero_mul, sub_zero] at h
  exact h.symm

 theorem line_truncation_tendsto_cancelled {f : ℝ → ℂ} (hf : Continuous f)
    (hd : DifferentiableAt ℝ f 0) (A : ℝ) :
    Tendsto (fun ε : ℝ => ∫ t in Ioo (-A) A ∩ {t : ℝ | ε < |t|},
      ((1 / (Real.pi * t) : ℝ) : ℂ) * f t) (𝓝[>] 0)
      (𝓝 (∫ t in Ioo (-A) A, ((1 / (Real.pi * t) : ℝ) : ℂ) * (f t - f 0))) := by
  apply (tendsto_integral_cutoff (line_cancel_integrable hf hd (-A) A)).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (line_truncation_eq_cancelled hf A ε hε).symm

end P102.U3.PeriodicConjugationBound

namespace P102.U3.PeriodicConjugationBound
open P102.Periodic.Expected

 theorem line_synthesis_cancel_integrable (T : ℝ) (c : ℤ →₀ ℂ) (x : Circle T) :
    IntegrableOn (fun t : ℝ => ((1 / (Real.pi * t) : ℝ) : ℂ) *
      (synthesis T c (x - (t : Circle T)) - synthesis T c x))
      (Ioo (-(T / 2)) (T / 2)) volume := by
  have hd := synthesis_coordinate_differentiable T c x
  simpa using
    line_cancel_integrable hd.continuous (hd.differentiableAt) (-(T / 2)) (T / 2)

 theorem line_synthesis_truncation_tendsto_cancelled (T : ℝ) (c : ℤ →₀ ℂ) (x : Circle T) :
    Tendsto (fun ε : ℝ => ∫ t in Ioo (-(T / 2)) (T / 2) ∩ {t : ℝ | ε < |t|},
      ((1 / (Real.pi * t) : ℝ) : ℂ) * synthesis T c (x - (t : Circle T)))
      (𝓝[>] 0) (𝓝 (∫ t in Ioo (-(T / 2)) (T / 2),
        ((1 / (Real.pi * t) : ℝ) : ℂ) *
          (synthesis T c (x - (t : Circle T)) - synthesis T c x))) := by
  have hd := synthesis_coordinate_differentiable T c x
  simpa using
    line_truncation_tendsto_cancelled hd.continuous hd.differentiableAt (T / 2)

end P102.U3.PeriodicConjugationBound

namespace P102.U3.PeriodicConjugationBound
open P102.Periodic.Expected
variable (T : ℝ) [Fact (0 < T)]

lemma remainderPart_measurable (f : C(Circle T, ℂ)) :
    StronglyMeasurable (remainderPart T f) := by
  have hm : StronglyMeasurable (fun z : Circle T × ℝ =>
      (((T⁻¹ * Real.cot (Real.pi * z.2 / T) - 1 / (Real.pi * z.2)) : ℝ) : ℂ) *
        (f (z.1 - (z.2 : Circle T)) - f z.1)) := by
    apply Measurable.stronglyMeasurable
    simp only [Real.cot_eq_cos_div_sin]
    fun_prop
  exact hm.integral_prod_right'

lemma remainder_integrable (f : C(Circle T, ℂ)) (x : Circle T) :
    IntegrableOn (fun t : ℝ =>
      (((T⁻¹ * Real.cot (Real.pi * t / T) - 1 / (Real.pi * t)) : ℝ) : ℂ) *
        (f (x - (t : Circle T)) - f x))
      (Ioo (-(T / 2)) (T / 2)) := by
  have hT : 0 < T := Fact.out
  apply IntegrableOn.of_bound (by simp) (C := (4/T) * (2*‖f‖))
  · apply Measurable.aestronglyMeasurable
    simp only [Real.cot_eq_cos_div_sin]
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul (coordinate_remainder_bound T Fact.out t (abs_le.mpr ⟨ht.1.le, ht.2.le⟩))
      ?_ (norm_nonneg _) (by positivity)
    calc
      ‖f (x - (t : Circle T)) - f x‖ ≤ ‖f (x - (t : Circle T))‖ + ‖f x‖ := norm_sub_le _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
      _ = _ := by ring


lemma remainder_norm (f : C(Circle T, ℂ)) (x : Circle T) :
    ‖remainderPart T f x‖ ≤ 4 * ((∫ y, ‖f y‖ ∂haar T) + ‖f x‖) := by
  have hT : 0 < T := Fact.out
  have hcont : Continuous (fun t : ℝ => ‖f (x - (t : Circle T))‖) := by fun_prop
  have hi : IntegrableOn (fun t : ℝ => ‖f (x - (t : Circle T))‖)
      (Ioo (-(T/2)) (T/2)) := hcont.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hmajor : IntegrableOn (fun t : ℝ => (4/T) * (‖f (x - (t : Circle T))‖ + ‖f x‖))
      (Ioo (-(T/2)) (T/2)) := (hi.add (integrableOn_const (by simp))).const_mul _
  have hbound : ‖remainderPart T f x‖ ≤
      ∫ t in Ioo (-(T/2)) (T/2), (4/T) * (‖f (x - (t : Circle T))‖ + ‖f x‖) := by
    apply norm_integral_le_of_norm_le hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (coordinate_remainder_bound T hT t (abs_le.mpr ⟨ht.1.le, ht.2.le⟩))
      (norm_sub_le _ _) (norm_nonneg _) (by positivity)
  have hmean : T⁻¹ * (∫ t in Ioo (-(T/2)) (T/2), ‖f (x - (t : Circle T))‖) =
      ∫ y, ‖f y‖ ∂haar T := by
    rw [← integral_sub_left_eq_self (fun y => ‖f y‖) (haar T) x]
    rw [AddCircle.integral_haarAddCircle,
      ← AddCircle.intervalIntegral_preimage T (-(T/2)) (fun y => ‖f (x-y)‖)]
    rw [intervalIntegral.integral_of_le (by linarith : -(T/2) ≤ -(T/2)+T),
      integral_Ioc_eq_integral_Ioo]
    simp only [show -(T/2)+T = T/2 by ring, smul_eq_mul]
  calc
    _ ≤ _ := hbound
    _ = (4/T) * ((∫ t in Ioo (-(T/2)) (T/2), ‖f (x - (t : Circle T))‖) + T * ‖f x‖) := by
      rw [integral_const_mul, integral_add hi (integrableOn_const (by simp)), integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo]
      rw [show T/2 - -(T/2) = T by ring, ENNReal.toReal_ofReal hT.le]
      rfl
    _ = 4 * ((∫ y, ‖f y‖ ∂haar T) + ‖f x‖) := by
      rw [← hmean]
      field_simp

lemma remainder_norm_le (p : P102.U2.CZLpData.Exponent) (f : C(Circle T, ℂ)) :
    eLpNorm (remainderPart T f) p.val (haar T) ≤ 8 * eLpNorm f p.val (haar T) := by
  have hp0 : p.val ≠ 0 := ne_of_gt (zero_lt_one.trans p.one_lt)
  have hf : Integrable f (haar T) := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hm : AEStronglyMeasurable f (haar T) := f.continuous.aestronglyMeasurable
  calc
    _ ≤ eLpNorm (fun x => 4 * ((∫ y, ‖f y‖ ∂haar T) + ‖f x‖)) p.val (haar T) :=
      eLpNorm_mono_real (remainderPart_measurable T f).aestronglyMeasurable (remainder_norm T f)
    _ = 4 * eLpNorm (fun x => (∫ y, ‖f y‖ ∂haar T) + ‖f x‖) p.val (haar T) := by
      change eLpNorm ((4 : ℝ) • (fun x : Circle T => (∫ y, ‖f y‖ ∂haar T) + ‖f x‖)) p.val (haar T) = _
      rw [eLpNorm_const_smul]
      norm_num [Real.enorm_eq_ofReal]
    _ ≤ 4 * (eLpNorm (fun _ : Circle T => ∫ y, ‖f y‖ ∂haar T) p.val (haar T) +
        eLpNorm (fun x => ‖f x‖) p.val (haar T)) :=
      mul_le_mul_right (eLpNorm_add_le p.one_lt.le) _
    _ = 4 * (eLpNorm f 1 (haar T) + eLpNorm f p.val (haar T)) := by
      rw [eLpNorm_const _ hp0 (NeZero.ne _), measure_univ, ENNReal.one_rpow, mul_one,
        enorm_integral_norm_eq_lintegral_enorm hf, ← eLpNorm_one_eq_lintegral_enorm hm,
        eLpNorm_norm f hm]
    _ ≤ 4 * (eLpNorm f p.val (haar T) + eLpNorm f p.val (haar T)) :=
      by
        gcongr
        exact eLpNorm_le_eLpNorm_of_exponent_le p.one_lt.le
    _ = _ := by rw [← two_mul]; ring

theorem remainder_estimate (p : P102.U2.CZLpData.Exponent) : RemainderEstimate T p := by
  refine ⟨8, fun c => ⟨remainder_integrable T (synthesis T c), ?_⟩⟩
  simpa only [ENNReal.coe_ofNat] using remainder_norm_le T p (synthesis T c)


end P102.U3.PeriodicConjugationBound

namespace P102.U3.PeriodicConjugationBound
open P102.Periodic.Expected
variable (T : ℝ) [Fact (0 < T)]
lemma memLp_normalized_iff (p : ℝ≥0∞) (f : ℝ → ℂ) :
    MemLp f p (normalizedLine T) ↔ MemLp f p volume := by
  have hT : 0 < T := Fact.out
  have hc : ENNReal.ofReal T⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr hT)).ne'
  constructor
  · intro hf
    have h := hf.smul_measure (c := (ENNReal.ofReal T⁻¹)⁻¹) (by simp [hc])
    simpa only [normalizedLine, smul_smul, ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top,
      one_smul] using h
  · intro hf
    exact hf.smul_measure ENNReal.ofReal_ne_top

lemma normalized_hilbert_bound (p : P102.U2.CZLpData.Exponent) :
    ∃ C : ℝ≥0, ∀ (f : ℝ → ℂ), MemLp f p.val (normalizedLine T) →
      ∃ g : ℝ → ℂ, MemLp g p.val (normalizedLine T) ∧
        eLpNorm g p.val (normalizedLine T) ≤
          (C : ℝ≥0∞) * eLpNorm f p.val (normalizedLine T) ∧
        (∀ ε : ℝ, 0 < ε → ∀ x : ℝ, IntegrableOn
          (fun t : ℝ => ((1 / (Real.pi * t) : ℝ) : ℂ) * f (x - t))
          {t : ℝ | ε < |t|}) ∧
        (∀ᵐ x ∂(volume : Measure ℝ),
          Tendsto (fun ε => ∫ t in {t : ℝ | ε < |t|},
            ((1 / (Real.pi * t) : ℝ) : ℂ) * f (x - t)) (𝓝[>] 0) (𝓝 (g x))) := by
  obtain ⟨C, hC⟩ := real_hilbert_bound p
  refine ⟨C, ?_⟩
  intro f hf
  obtain ⟨g, hg, hnorm, hi, hlim⟩ := hC f ((memLp_normalized_iff T p.val f).mp hf)
  refine ⟨g, (memLp_normalized_iff T p.val g).mpr hg, ?_, hi, hlim⟩
  have hc : ENNReal.ofReal T⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr
    (inv_pos.mpr (Fact.out : 0 < T))).ne'
  simp only [normalizedLine, eLpNorm_smul_measure_of_ne_zero hc, smul_eq_mul]
  calc
    _ ≤ (ENNReal.ofReal T⁻¹) ^ (1 / p.val).toReal *
        ((C : ℝ≥0∞) * eLpNorm f p.val volume) := by gcongr
    _ = _ := by ring

lemma localized_one_norm_le (p : P102.U2.CZLpData.Exponent) (f : Circle T → ℂ)
    (hf : AEStronglyMeasurable f (haar T)) :
    eLpNorm (localized T f) 1 (normalizedLine T) ≤
      3 * eLpNorm f p.val (haar T) := by
  calc
    _ ≤ eLpNorm (periodPiece T (-T) f + periodPiece T 0 f) 1 (normalizedLine T) +
        eLpNorm (periodPiece T T f) 1 (normalizedLine T) :=
      eLpNorm_add_le (f := periodPiece T (-T) f + periodPiece T 0 f)
        (g := periodPiece T T f) le_rfl
    _ ≤ (eLpNorm (periodPiece T (-T) f) 1 (normalizedLine T) +
        eLpNorm (periodPiece T 0 f) 1 (normalizedLine T)) +
        eLpNorm (periodPiece T T f) 1 (normalizedLine T) :=
      add_le_add (eLpNorm_add_le (μ := normalizedLine T)
        (f := periodPiece T (-T) f) (g := periodPiece T 0 f) le_rfl) le_rfl
    _ = 3 * eLpNorm f 1 (haar T) := by
      rw [periodPiece_norm T (-T) 1 f hf, periodPiece_norm T 0 1 f hf,
        periodPiece_norm T T 1 f hf]
      simp only [show (3 : ℝ≥0∞) = 1+1+1 by norm_num, add_mul, one_mul]
    _ ≤ _ := by gcongr; exact eLpNorm_le_eLpNorm_of_exponent_le p.one_lt.le

lemma tail_kernel_bound (t : ℝ) (ht : T / 2 ≤ |t|) :
    ‖((1 / (Real.pi * t) : ℝ) : ℂ)‖ ≤ 2 / (Real.pi * T) := by
  have hT : 0 < T := Fact.out
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_one, abs_mul,
    abs_of_pos Real.pi_pos]
  calc
    1 / (Real.pi * |t|) ≤ 1 / (Real.pi * (T / 2)) :=
      one_div_le_one_div_of_le (mul_pos Real.pi_pos (half_pos hT))
        (mul_le_mul_of_nonneg_left ht Real.pi_pos.le)
    _ = _ := by field_simp

lemma tail_integrable (f : Circle T → ℂ)
    (hf : Integrable (localized T f) volume) (x : ℝ) :
    IntegrableOn (fun t : ℝ => ((1 / (Real.pi * t) : ℝ) : ℂ) *
      localized T f (x - t)) {t : ℝ | T / 2 ≤ |t|} := by
  have hs : MeasurableSet {t : ℝ | T / 2 ≤ |t|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  apply (hf.comp_sub_left x).integrableOn.bdd_mul
    (c := 2 / (Real.pi * T))
  · exact (by fun_prop : Measurable (fun t : ℝ =>
      ((1 / (Real.pi * t) : ℝ) : ℂ))).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem hs] with t ht
    exact tail_kernel_bound T t ht

lemma tail_enorm_bound (p : P102.U2.CZLpData.Exponent) (f : Circle T → ℂ)
    (hf : AEStronglyMeasurable f (haar T))
    (hfL : AEStronglyMeasurable (localized T f) volume) (x : ℝ) :
    ‖∫ t in {t : ℝ | T / 2 ≤ |t|},
      ((1 / (Real.pi * t) : ℝ) : ℂ) * localized T f (x - t)‖ₑ ≤
      ENNReal.ofReal (6 / Real.pi) * eLpNorm f p.val (haar T) := by
  have hT : 0 < T := Fact.out
  have hc : ENNReal.ofReal T⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr hT)).ne'
  have hs : MeasurableSet {t : ℝ | T / 2 ≤ |t|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  calc
    _ ≤ ∫⁻ t in {t : ℝ | T / 2 ≤ |t|},
        ‖((1 / (Real.pi * t) : ℝ) : ℂ) * localized T f (x - t)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in {t : ℝ | T / 2 ≤ |t|},
        ENNReal.ofReal (2 / (Real.pi * T)) * ‖localized T f (x-t)‖ₑ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hs] with t ht
      rw [enorm_mul]
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (tail_kernel_bound T t ht)
    _ ≤ ∫⁻ t, ENNReal.ofReal (2 / (Real.pi * T)) *
        ‖localized T f (x-t)‖ₑ := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = ENNReal.ofReal (2 / (Real.pi * T)) * eLpNorm (localized T f) 1 volume := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_sub_left_eq_self (fun y : ℝ => ‖localized T f y‖ₑ) x,
        eLpNorm_one_eq_lintegral_enorm hfL]
    _ = ENNReal.ofReal (2 / Real.pi) *
        eLpNorm (localized T f) 1 (normalizedLine T) := by
      rw [normalizedLine, eLpNorm_one_smul_measure, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 / Real.pi)]
      congr 2
      field_simp
    _ ≤ ENNReal.ofReal (2 / Real.pi) * (3 * eLpNorm f p.val (haar T)) :=
      by gcongr; exact localized_one_norm_le T p f hf
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_ofNat 3,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 / Real.pi)]
      congr 2
      ring

lemma localized_memLp (p : P102.U2.CZLpData.Exponent) (f : Circle T → ℂ)
    (hf : MemLp f p.val (haar T)) :
    MemLp (localized T f) p.val (normalizedLine T) := by
  exact (localized_norm_le T p f hf.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top (by norm_num) hf.eLpNorm_lt_top)

lemma localized_integrable (p : P102.U2.CZLpData.Exponent) (f : Circle T → ℂ)
    (hf : MemLp f p.val (haar T)) :
    Integrable (localized T f) volume := by
  apply memLp_one_iff_integrable.mp
  apply (memLp_normalized_iff T 1 (localized T f)).mp
  exact (localized_one_norm_le T p f hf.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top (by norm_num) hf.eLpNorm_lt_top)

lemma tail_stronglyMeasurable (f : Circle T → ℂ)
    (hfL : Measurable (localized T f)) :
    StronglyMeasurable (fun x : ℝ => ∫ t in {t : ℝ | T / 2 ≤ |t|},
      ((1 / (Real.pi * t) : ℝ) : ℂ) * localized T f (x-t)) := by
  have hM : Measurable (fun z : ℝ × ℝ =>
      ((1 / (Real.pi * z.2) : ℝ) : ℂ) * localized T f (z.1-z.2)) := by
    exact (by fun_prop : Measurable (fun z : ℝ × ℝ =>
      ((1 / (Real.pi * z.2) : ℝ) : ℂ))).mul
        (hfL.comp (measurable_fst.sub measurable_snd))
  exact hM.stronglyMeasurable.integral_prod_right

lemma normalizedLine_period_mass : normalizedLine T (Ioc 0 T) = 1 := by
  have hT : 0 < T := Fact.out
  change ENNReal.ofReal T⁻¹ * volume (Ioc 0 T) = 1
  rw [Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (inv_nonneg.mpr hT.le),
    inv_mul_cancel₀ hT.ne', ENNReal.ofReal_one]

lemma tail_lp_bound (p : P102.U2.CZLpData.Exponent) (f : Circle T → ℂ)
    (hf : AEStronglyMeasurable f (haar T))
    (hfL : Measurable (localized T f)) :
    eLpNorm (fun x : ℝ => ∫ t in {t : ℝ | T / 2 ≤ |t|},
      ((1 / (Real.pi * t) : ℝ) : ℂ) * localized T f (x-t))
      p.val ((normalizedLine T).restrict (Ioc 0 T)) ≤
      ENNReal.ofReal (6 / Real.pi) * eLpNorm f p.val (haar T) := by
  have h := eLpNorm_le_of_ae_enorm_bound
    (p := p.val) ((tail_stronglyMeasurable T f hfL).aestronglyMeasurable
      (μ := (normalizedLine T).restrict (Ioc 0 T)))
    (Filter.Eventually.of_forall (tail_enorm_bound T p f hf hfL.aestronglyMeasurable))
  simpa only [Measure.restrict_apply_univ, normalizedLine_period_mass T,
    ENNReal.one_rpow, smul_eq_mul, mul_one] using h

lemma localized_measurable_of_continuous (f : Circle T → ℂ) (hf : Continuous f) :
    Measurable (localized T f) := by
  have hm : Measurable (fun y : ℝ => f (y : Circle T)) :=
    (hf.comp (AddCircle.continuous_mk' T)).measurable
  exact ((hm.indicator measurableSet_Ioc).add
    (hm.indicator measurableSet_Ioc)).add (hm.indicator measurableSet_Ioc)

end P102.U3.PeriodicConjugationBound

namespace P102.U3.PeriodicConjugationBound
open P102.Periodic.Expected
variable (T : ℝ) [Fact (0 < T)]

lemma linePart_measurable (f : Circle T → ℂ) (hf : Continuous f) :
    Measurable (linePart T f) := by
  have hm : Measurable (fun z : Circle T × ℝ =>
      ((1 / (Real.pi * z.2) : ℝ) : ℂ) *
        (f (z.1 - (z.2 : Circle T)) - f z.1)) := by
    have hq : Measurable (fun z : Circle T × ℝ => (z.2 : Circle T)) :=
      (AddCircle.continuous_mk' T).measurable.comp measurable_snd
    exact (by fun_prop : Measurable (fun z : Circle T × ℝ =>
      ((1 / (Real.pi * z.2) : ℝ) : ℂ))).mul
        ((hf.measurable.comp (measurable_fst.sub hq)).sub
          (hf.measurable.comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma linePart_period_norm (p : ℝ≥0∞) (f : Circle T → ℂ) (hf : Continuous f) :
    eLpNorm (fun x : ℝ => linePart T f (x : Circle T)) p
      ((normalizedLine T).restrict (Ioc 0 T)) =
    eLpNorm (linePart T f) p (haar T) := by
  change eLpNorm ((linePart T f) ∘ (fun x : ℝ => (x : Circle T))) p _ = _
  rw [normalizedLine, Measure.restrict_smul]
  simpa only [zero_add] using eLpNorm_comp_measurePreserving
    (linePart_measurable T f hf).aestronglyMeasurable (P102.Periodic.interval_measure T 0)

end P102.U3.PeriodicConjugationBound

namespace P102.U3.PeriodicConjugationBound
open P102.Periodic.Expected
variable (T : ℝ) [Fact (0 < T)]

instance normalizedLine_nullSingletonClass : NullSingletonClass (normalizedLine T) := by
  constructor
  intro x
  simp [normalizedLine, Measure.smul_apply]

lemma linePart_period_norm_open (p : ℝ≥0∞) (f : Circle T → ℂ) (hf : Continuous f) :
    eLpNorm (fun x : ℝ => linePart T f (x : Circle T)) p
      ((normalizedLine T).restrict (Ioo 0 T)) =
    eLpNorm (linePart T f) p (haar T) := by
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := normalizedLine T))]
  exact linePart_period_norm T p f hf

lemma normalized_period_mass : (normalizedLine T).restrict (Ioo 0 T) univ = 1 := by
  have hT : 0 < T := Fact.out
  simp only [Measure.restrict_apply_univ, normalizedLine, Measure.smul_apply,
    smul_eq_mul, Real.volume_Ioo, sub_zero]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ T⁻¹)]
  simp [ne_of_gt hT]

/-- Norm control can be proved on one open period with the normalized real measure. -/
lemma linePart_norm_of_ae_bound (p : P102.U2.CZLpData.Exponent)
    (f : Circle T → ℂ) (hf : Continuous f) (g : ℝ → ℂ)
    (hg : AEStronglyMeasurable g (normalizedLine T)) (D : ℝ≥0∞)
    (hbound : ∀ᵐ (x : ℝ) ∂((normalizedLine T).restrict (Ioo 0 T)),
      ‖linePart T f (x : Circle T)‖ₑ ≤ ‖g x‖ₑ + D) :
    eLpNorm (linePart T f) p.val (haar T) ≤
      eLpNorm g p.val (normalizedLine T) + D := by
  rw [← linePart_period_norm_open T p.val f hf]
  calc
    _ ≤ eLpNorm (fun x : ℝ => ‖g x‖ₑ + D) p.val
        ((normalizedLine T).restrict (Ioo 0 T)) :=
      eLpNorm_mono_enorm_ae
        ((linePart_measurable T f hf).comp (AddCircle.continuous_mk' T).measurable).aestronglyMeasurable
        (by simpa using hbound)
    _ ≤ eLpNorm (fun x : ℝ => ‖g x‖ₑ) p.val
        ((normalizedLine T).restrict (Ioo 0 T)) +
        eLpNorm (fun _ : ℝ => D) p.val ((normalizedLine T).restrict (Ioo 0 T)) :=
      eLpNorm_add_le (f := fun x : ℝ => ‖g x‖ₑ) (g := fun _ : ℝ => D) p.one_lt.le
    _ ≤ eLpNorm g p.val (normalizedLine T) + D := by
      rw [eLpNorm_enorm g hg.restrict, eLpNorm_const' D (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne,
        normalized_period_mass T, ENNReal.one_rpow, mul_one, enorm_eq_self]
      exact add_le_add (eLpNorm_mono_measure g Measure.restrict_le_self) le_rfl

end P102.U3.PeriodicConjugationBound

namespace P102.U3.PeriodicConjugationBound
open P102.Periodic.Expected
variable (T : ℝ) [Fact (0 < T)]

 theorem localized_truncation_split (f : Circle T → ℂ) (x ε : ℝ)
    (hx : x ∈ Ioo 0 T) (hε : 0 < ε) (hεT : ε < T / 2)
    (hi : IntegrableOn (fun t : ℝ => ((1 / (Real.pi * t) : ℝ) : ℂ) *
      localized T f (x - t)) {t : ℝ | ε < |t|} volume) :
    (∫ t in {t : ℝ | ε < |t|}, ((1 / (Real.pi * t) : ℝ) : ℂ) * localized T f (x - t)) =
      (∫ t in Ioo (-(T / 2)) (T / 2) ∩ {t : ℝ | ε < |t|},
        ((1 / (Real.pi * t) : ℝ) : ℂ) * f ((x : Circle T) - (t : Circle T))) +
      ∫ t in {t : ℝ | T / 2 ≤ |t|},
        ((1 / (Real.pi * t) : ℝ) : ℂ) * localized T f (x - t) := by
  let L := Ioo (-(T / 2)) (T / 2) ∩ {t : ℝ | ε < |t|}
  let B := {t : ℝ | T / 2 ≤ |t|}
  have hBsub : B ⊆ {t : ℝ | ε < |t|} := fun t ht => hεT.trans_le ht
  have hLsub : L ⊆ {t : ℝ | ε < |t|} := inter_subset_right
  have hmeas : MeasurableSet B := by dsimp [B]; measurability
  have hdisj : Disjoint L B := by
    rw [disjoint_left]
    intro t ht hBt
    have hLt : |t| < T / 2 := abs_lt.mpr ht.1
    exact (not_lt_of_ge hBt) hLt
  have hunion : {t : ℝ | ε < |t|} = L ∪ B := by
    ext t
    constructor
    · intro ht
      by_cases htT : |t| < T / 2
      · exact Or.inl ⟨abs_lt.mp htT, ht⟩
      · exact Or.inr (le_of_not_gt htT)
    · rintro (ht | ht)
      · exact ht.2
      · exact hBsub ht
  conv_lhs => rw [hunion, setIntegral_union hdisj hmeas (hi.mono_set hLsub) (hi.mono_set hBsub)]
  congr 1
  apply setIntegral_congr_fun (measurableSet_Ioo.inter
    (isOpen_lt continuous_const continuous_abs).measurableSet)
  intro t ht
  dsimp only
  rw [localized_agrees T f x t hx (abs_lt.mpr ht.1)]

 theorem line_synthesis_eq_hilbert_sub_tail (c : ℤ →₀ ℂ) (g : ℝ → ℂ)
    (hi : ∀ ε : ℝ, 0 < ε → ∀ x : ℝ,
      IntegrableOn (fun t : ℝ => ((1 / (Real.pi * t) : ℝ) : ℂ) *
        localized T (synthesis T c) (x - t)) {t : ℝ | ε < |t|} volume)
    (hlim : ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun ε : ℝ => ∫ t in {t : ℝ | ε < |t|},
        ((1 / (Real.pi * t) : ℝ) : ℂ) * localized T (synthesis T c) (x - t))
        (𝓝[>] 0) (𝓝 (g x))) :
    ∀ᵐ x : ℝ ∂volume.restrict (Ioo 0 T),
      linePart T (synthesis T c) (x : Circle T) = g x -
        ∫ t in {t : ℝ | T / 2 ≤ |t|},
          ((1 / (Real.pi * t) : ℝ) : ℂ) * localized T (synthesis T c) (x - t) := by
  filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem measurableSet_Ioo] with x hxlim hx
  have hlocal := line_synthesis_truncation_tendsto_cancelled T c (x : Circle T)
  change Tendsto _ _ (𝓝 (linePart T (synthesis T c) (x : Circle T))) at hlocal
  have hs := hlocal.add_const (∫ t in {t : ℝ | T / 2 ≤ |t|},
    ((1 / (Real.pi * t) : ℝ) : ℂ) * localized T (synthesis T c) (x - t))
  have hfull := hs.congr' (show ∀ᶠ ε : ℝ in 𝓝[>] 0,
    (∫ t in Ioo (-(T / 2)) (T / 2) ∩ {t : ℝ | ε < |t|},
      ((1 / (Real.pi * t) : ℝ) : ℂ) * synthesis T c ((x : Circle T) - (t : Circle T))) +
    (∫ t in {t : ℝ | T / 2 ≤ |t|},
      ((1 / (Real.pi * t) : ℝ) : ℂ) * localized T (synthesis T c) (x - t)) =
    ∫ t in {t : ℝ | ε < |t|},
      ((1 / (Real.pi * t) : ℝ) : ℂ) * localized T (synthesis T c) (x - t) from by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (half_pos (Fact.out : 0 < T))).filter_mono nhdsWithin_le_nhds]
        with ε hε hεT
      exact (localized_truncation_split T (synthesis T c) x ε hx hε hεT (hi ε hε x)).symm)
  have heq := tendsto_nhds_unique hfull hxlim
  exact eq_sub_iff_add_eq.mpr heq

end P102.U3.PeriodicConjugationBound

namespace P102.U3.PeriodicConjugationBound
open P102.Periodic.Expected
variable (T : ℝ) [Fact (0 < T)]

theorem line_estimate (p : P102.U2.CZLpData.Exponent) : LineEstimate T p := by
  obtain ⟨C, hC⟩ := normalized_hilbert_bound T p
  let D : ℝ≥0 := ⟨6 / Real.pi, by positivity⟩
  have hD : ENNReal.ofReal (6 / Real.pi) = (D : ℝ≥0∞) := by
    exact (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (D : ℝ) = (D : ℝ≥0∞))
  refine ⟨3 * C + D, fun c => ⟨line_synthesis_cancel_integrable T c, ?_⟩⟩
  have hf : MemLp (synthesis T c) p.val (haar T) :=
    (synthesis T c).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hF := localized_memLp T p (synthesis T c) hf
  obtain ⟨g, hg, hn, hi, hlim⟩ := hC (localized T (synthesis T c)) hF
  have heq := line_synthesis_eq_hilbert_sub_tail T c g hi hlim
  have heq' : ∀ᵐ (x : ℝ) ∂((normalizedLine T).restrict (Ioo 0 T)),
      linePart T (synthesis T c) (x : Circle T) = g x -
        ∫ t in {t : ℝ | T / 2 ≤ |t|},
          ((1 / (Real.pi * t) : ℝ) : ℂ) * localized T (synthesis T c) (x - t) := by
    rw [normalizedLine, Measure.restrict_smul]
    exact Measure.ae_smul_measure heq _
  have hb : ∀ᵐ (x : ℝ) ∂((normalizedLine T).restrict (Ioo 0 T)),
      ‖linePart T (synthesis T c) (x : Circle T)‖ₑ ≤
        ‖g x‖ₑ + (D : ℝ≥0∞) * eLpNorm (synthesis T c) p.val (haar T) := by
    filter_upwards [heq'] with x hx
    rw [hx]
    apply enorm_sub_le.trans
    apply add_le_add le_rfl
    rw [← hD]
    exact tail_enorm_bound T p (synthesis T c) hf.aestronglyMeasurable
      ((memLp_normalized_iff T p.val _).mp hF).aestronglyMeasurable x
  calc
    _ ≤ eLpNorm g p.val (normalizedLine T) +
        (D : ℝ≥0∞) * eLpNorm (synthesis T c) p.val (haar T) :=
      linePart_norm_of_ae_bound T p (synthesis T c) (synthesis T c).continuous
        g hg.aestronglyMeasurable _ hb
    _ ≤ (C : ℝ≥0∞) * eLpNorm (localized T (synthesis T c)) p.val (normalizedLine T) +
        (D : ℝ≥0∞) * eLpNorm (synthesis T c) p.val (haar T) := add_le_add hn le_rfl
    _ ≤ (C : ℝ≥0∞) * (3 * eLpNorm (synthesis T c) p.val (haar T)) +
        (D : ℝ≥0∞) * eLpNorm (synthesis T c) p.val (haar T) := by
      gcongr
      exact localized_norm_le T p (synthesis T c) hf.aestronglyMeasurable
    _ = _ := by push_cast; ring

end P102.U3.PeriodicConjugationBound

namespace P102.Periodic.Conjugation

theorem cancelled_bound : Expected.CancelledBoundStatement := by
  intro T _inst p
  exact P102.U3.PeriodicConjugationBound.assemble T p
    (P102.U3.PeriodicConjugationBound.line_estimate T p)
    (P102.U3.PeriodicConjugationBound.remainder_estimate T p)

end P102.Periodic.Conjugation
