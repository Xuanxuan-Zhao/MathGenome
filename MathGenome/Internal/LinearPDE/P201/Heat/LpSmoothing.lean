import MathGenome.Internal.LinearPDE.P201.Heat.GaussianSemigroup
import MathGenome.Internal.LinearPDE.P201Specs.Heat.LpSmoothing
import MathGenome.Internal.FourierSobolev.P102.U3.Gaussian
import MathGenome.Internal.FourierSobolev.P102.U2.Young
import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Batteries.Tactic.OpenPrivate

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal ContDiff NNReal Topology
namespace P201.Heat

abbrev heatMixedDerivative : P201Specs.Heat.heatMixedDerivativeType :=
  @P201Specs.Heat.heatMixedDerivative

abbrev gaussianMixedDerivative : P201Specs.Heat.gaussianMixedDerivativeType :=
  @P201Specs.Heat.gaussianMixedDerivative

open private realGaussianSchwartz from MathGenome.Internal.FourierSobolev.P102.U3.Gaussian

/-- A Schwartz realization with the manuscript's exact normalization. -/
lemma gaussianSchwartz (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ Φ : SchwartzMap (Space n) ℝ, (Φ : Space n → ℝ) = gaussianKernel n t := by
  let Φ := realGaussianSchwartz n (show 0 < (1 : ℝ) / (4 * t) by positivity)
  refine ⟨((4 * Real.pi * t) ^ (-(n : ℝ) / 2)) • Φ, ?_⟩
  funext x
  change (4 * Real.pi * t) ^ (-(n : ℝ) / 2) *
    Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) = gaussianKernel n t x
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  congr 2
  ring

/-- Every finite word of coordinate derivatives preserves Schwartz space. -/
lemma schwartzPartialWord {n : ℕ} (Φ : SchwartzMap (Space n) ℝ) (l : List (Fin n)) :
    ∃ Ψ : SchwartzMap (Space n) ℝ,
      (Ψ : Space n → ℝ) = P102.U4.partialWord Φ l := by
  induction l with
  | nil => exact ⟨Φ, rfl⟩
  | cons i l ih =>
    obtain ⟨Ψ, hΨ⟩ := ih
    refine ⟨SchwartzMap.evalCLM ℝ (Space n) ℝ (coordinate n i)
      (SchwartzMap.fderivCLM ℝ (Space n) ℝ Ψ), ?_⟩
    funext x
    change fderiv ℝ (Ψ : Space n → ℝ) x (coordinate n i) =
      fderiv ℝ (P102.U4.partialWord Φ l) x (coordinate n i)
    rw [hΨ]

theorem gaussianSpatialSchwartz : P201Specs.Heat.gaussianSpatialSchwartzStatement := by
  intro n t ht α
  obtain ⟨Φ, hΦ⟩ := gaussianSchwartz n ht
  obtain ⟨Ψ, hΨ⟩ := schwartzPartialWord Φ (α.sort (· ≤ ·))
  refine ⟨Ψ, ?_⟩
  rw [hΨ, hΦ]
  rfl

theorem gaussianSpatialMemLp : P201Specs.Heat.gaussianSpatialMemLpStatement := by
  intro n t ht α r
  obtain ⟨Φ, hΦ⟩ := gaussianSpatialSchwartz n t ht α
  rw [← hΦ]
  exact Φ.memLp r

theorem heatConvolutionEverywhere : P201Specs.Heat.heatConvolutionEverywhereStatement := by
  intro n 𝕜 _ p _ g t ht x
  have hk := gaussianSpatialMemLp n t ht 0 p.conjExponent
  simp only [P201Specs.multiPartial, P102.U4.multiPartial, Multiset.sort_zero,
    P102.U4.partialWord] at hk
  have hi := MeasureTheory.ConvolutionExists.of_memLp_memLp
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜) hk (Lp.memLp g) x
  change Integrable (fun y => gaussianKernel n t y • g (x - y)) at hi
  simpa only [sub_sub_cancel] using hi.comp_sub_left x

@[simp] lemma heatMixedDerivative_zero {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (g : Space n → 𝕜) (t : ℝ) :
    heatMixedDerivative 0 0 g t = heatConvolution t g := by
  funext x
  simp [heatMixedDerivative, P201Specs.Heat.heatMixedDerivative,
    P201Specs.multiPartial, P102.U4.multiPartial, P102.U4.partialWord]

theorem heatDiagonalZeroEstimate : P201Specs.Heat.heatDiagonalZeroEstimateStatement := by
  intro n hn 𝕜 _ p _ g t ht
  obtain ⟨S, _, _, hb, hr, _, _⟩ := lpSemigroup n hn 𝕜 p
  let τ : ℝ≥0 := ⟨t, ht.le⟩
  have hτ : τ ≠ 0 := by
    intro h
    have hreal := congrArg (fun s : ℝ≥0 => (s : ℝ)) h
    exact ht.ne' hreal
  have hrep := hr τ g
  simp only [P201Specs.Heat.heatFlow, ite_eq_right_iff.mpr (fun h => (hτ h).elim)] at hrep
  change MemLp (heatMixedDerivative 0 0 g t) p (spatialMeasure n) ∧
    (eLpNorm (heatMixedDerivative 0 0 g t) p (spatialMeasure n)).toReal ≤ ‖g‖
  rw [heatMixedDerivative_zero]
  refine ⟨(Lp.memLp (S τ g)).ae_eq hrep, ?_⟩
  calc
    _ = ‖S τ g‖ := by
      rw [Lp.norm_def]
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae hrep).symm
    _ ≤ ‖g‖ := hb τ g

/-- Young's inequality for a real scalar kernel and either real or complex
data, in the shared Euclidean coordinates and with both infinite endpoints. -/
lemma scalarKernelYoung {n : ℕ} {𝕜 : Type} [RCLike 𝕜] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hs : 1 + q⁻¹ = r⁻¹ + p⁻¹) {k : Space n → ℝ} {g : Space n → 𝕜}
    (hk : MemLp k r (spatialMeasure n)) (hg : MemLp g p (spatialMeasure n)) :
    MemLp (fun x => ∫ y, k (x - y) • g y) q (spatialMeasure n) ∧
      eLpNorm (fun x => ∫ y, k (x - y) • g y) q (spatialMeasure n) ≤
        eLpNorm k r (spatialMeasure n) * eLpNorm g p (spatialMeasure n) := by
  have hk' : MemLp (fun x => (k x : 𝕜)) r (spatialMeasure n) := hk.ofReal
  have hn : eLpNorm (fun x => (k x : 𝕜)) r (spatialMeasure n) =
      eLpNorm k r (spatialMeasure n) :=
    eLpNorm_congr_norm_ae hk'.aestronglyMeasurable hk.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp [Real.norm_eq_abs])
  obtain ⟨_, hm, hb, _⟩ := P102.U2.Young.young (spatialMeasure n) hr hp hq hs hk' hg
  rw [hn] at hb
  simpa only [RCLike.real_smul_eq_coe_mul] using And.intro hm hb

/-- The convolution exponent exists for all ordered exponents, including
`p = q = ∞` and `p = 1, q = ∞`. No finite-exponent division is needed. -/
lemma smoothingYoungExponent {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∃ r : ℝ≥0∞, 1 ≤ r ∧ 1 + q⁻¹ = r⁻¹ + p⁻¹ ∧
      1 - r⁻¹.toReal = p⁻¹.toReal - q⁻¹.toReal := by
  let r : ℝ≥0∞ := (1 + q⁻¹ - p⁻¹)⁻¹
  have hr : 1 ≤ r := by
    apply ENNReal.one_le_inv.mpr
    apply tsub_le_iff_right.mpr
    simpa only [add_comm] using add_le_add_left (ENNReal.inv_le_inv.mpr hpq) 1
  have he : 1 + q⁻¹ = r⁻¹ + p⁻¹ := by
    dsimp [r]
    rw [inv_inv, tsub_add_cancel_of_le]
    exact (ENNReal.inv_le_one.mpr hp).trans le_self_add
  refine ⟨r, hr, he, ?_⟩
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le hp)
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le (hp.trans hpq))
  have hr0 : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le hr)
  have hreal := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.inv_ne_top.mpr hq0),
    ENNReal.toReal_add (ENNReal.inv_ne_top.mpr hr0) (ENNReal.inv_ne_top.mpr hp0),
    ENNReal.toReal_one] at hreal
  linarith

/-- Assembly of the quantitative theorem from kernel bounds and differentiation. -/
lemma heatMixedEstimate_of_kernelBounds
    (hkernel : P201Specs.Heat.gaussianMixedBoundStatement)
    (hdiff : P201Specs.Heat.heatDifferentiationUnderIntegralStatement) :
    P201Specs.Heat.heatMixedEstimateStatement := by
  intro n hn 𝕜 _ p q _ hpq α j
  obtain ⟨r, hr, he, hrec⟩ := smoothingYoungExponent (Fact.out : 1 ≤ p) hpq
  obtain ⟨C, hC, hbound⟩ := hkernel n hn α j r hr
  refine ⟨C, hC, ?_⟩
  intro g t ht
  obtain ⟨hk, hb⟩ := hbound t ht
  have hq : 1 ≤ q := (Fact.out : 1 ≤ p).trans hpq
  obtain ⟨hm, hy⟩ := scalarKernelYoung (Fact.out : 1 ≤ p) hq hr he hk (Lp.memLp g)
  have hfun : P201Specs.Heat.heatMixedDerivative α j g t =
      fun x => ∫ y, P201Specs.Heat.gaussianMixedDerivative α j t (x - y) • g y := by
    funext x
    exact hdiff n hn 𝕜 p g α j t ht x
  rw [hfun]
  refine ⟨hm, ?_⟩
  have hnorm := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hk.eLpNorm_ne_top (Lp.memLp g).eLpNorm_ne_top) hy
  rw [ENNReal.toReal_mul, ← Lp.norm_def] at hnorm
  have hexp : -(j : ℝ) - (α.card : ℝ) / 2 - (n : ℝ) / 2 * (1 - r⁻¹.toReal) =
      P201Specs.Heat.heatSmoothingExponent α j p q := by
    rw [hrec]
    rfl
  rw [hexp] at hb
  exact hnorm.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg g))

/-- Dilation of an arbitrary `Lʳ` profile, with the essential-supremum endpoint. -/
lemma memLp_dilate {n : ℕ} {r : ℝ≥0∞} {f : Space n → ℝ}
    (hf : MemLp f r (spatialMeasure n)) {c : ℝ} (hc : c ≠ 0) :
    MemLp (fun x => f (c • x)) r (spatialMeasure n) := by
  have hm := Measure.map_addHaar_smul (spatialMeasure n) hc
  have hf' := hf.smul_measure (c := ENNReal.ofReal |(c ^ Module.finrank ℝ (Space n))⁻¹|)
    ENNReal.ofReal_ne_top
  rw [← hm] at hf'
  exact hf'.comp_of_map (measurable_const_smul c).aemeasurable

lemma eLpNorm_dilate {n : ℕ} {r : ℝ≥0∞} {f : Space n → ℝ}
    (hf : MemLp f r (spatialMeasure n)) {c : ℝ} (hc : 0 < c) :
    (eLpNorm (fun x => f (c • x)) r (spatialMeasure n)).toReal =
      c ^ (-(n : ℝ) * r⁻¹.toReal) * (eLpNorm f r (spatialMeasure n)).toReal := by
  have hm := Measure.map_addHaar_smul (spatialMeasure n) hc.ne'
  have hpos : 0 < |(c ^ Module.finrank ℝ (Space n))⁻¹| := by positivity
  have hmeas := hf.aestronglyMeasurable.smul_measure
    (ENNReal.ofReal |(c ^ Module.finrank ℝ (Space n))⁻¹|)
  rw [← hm] at hmeas
  have hnorm := eLpNorm_map_measure (p := r) hmeas
    (measurable_const_smul c).aemeasurable
  rw [hm, eLpNorm_smul_measure_of_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hpos))] at hnorm
  simp only [Function.comp_def] at hnorm
  rw [← hnorm, smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hpos.le]
  simp only [one_div, finrank_euclideanSpace, Fintype.card_fin]
  rw [abs_of_pos (by positivity : 0 < (c ^ n)⁻¹), Real.inv_rpow (pow_nonneg hc.le _),
    ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← Real.rpow_neg hc.le]
  congr 2
  ring

/-- Differentiation of a scalar multiple along a coordinate word. -/
lemma partialWord_const_smul {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ) (l : List (Fin n)) :
    P102.U4.partialWord (a • f) l = a • P102.U4.partialWord f l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    funext x
    change fderiv ℝ (P102.U4.partialWord (a • f) l) x (coordinate n i) = _
    rw [ih, fderiv_const_smul ((P102.U4.partialWord_contDiff hf l).differentiable
      (by simp) x)]
    rfl

/-- The exact self-similar formula for the normalized Gaussian. -/
lemma gaussianKernel_scale {n : ℕ} {t : ℝ} (ht : 0 < t) :
    gaussianKernel n t = fun x => t ^ (-(n : ℝ) / 2) *
      gaussianKernel n 1 ((Real.sqrt t)⁻¹ • x) := by
  funext x
  unfold gaussianKernel P201Specs.Heat.gaussianKernel
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
    Real.sq_sqrt ht.le]
  rw [show 4 * Real.pi * t = t * (4 * Real.pi * 1) by ring,
    Real.mul_rpow ht.le (by positivity)]
  rw [mul_assoc]
  congr 1
  congr 1
  field_simp

/-- Spatial derivatives have a fixed Schwartz profile at unit time. -/
lemma gaussianSpatial_scale {n : ℕ} (α : MultiIndex n) {t : ℝ} (ht : 0 < t) :
    multiPartial (gaussianKernel n t) α = fun x =>
      t ^ (-(n : ℝ) / 2 - (α.card : ℝ) / 2) *
        multiPartial (gaussianKernel n 1) α ((Real.sqrt t)⁻¹ • x) := by
  obtain ⟨Φ, hΦ⟩ := gaussianSchwartz n (t := 1) (by norm_num)
  have hf : ContDiff ℝ (⊤ : ℕ∞) (gaussianKernel n 1) := hΦ ▸ Φ.smooth ⊤
  have hscale := gaussianKernel_scale (n := n) ht
  change P102.U4.partialWord (gaussianKernel n t) (α.sort (· ≤ ·)) = _
  rw [hscale]
  change P102.U4.partialWord
    ((t ^ (-(n : ℝ) / 2)) • (fun x => gaussianKernel n 1 ((Real.sqrt t)⁻¹ • x))) _ = _
  have hfd : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Space n => gaussianKernel n 1 ((Real.sqrt t)⁻¹ • x)) :=
    hf.comp (contDiff_id.const_smul _)
  rw [partialWord_const_smul hfd, P102.U4.partialWord_dilate hf]
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, Multiset.length_sort]
  rw [← mul_assoc]
  congr 1
  rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le,
    ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
  congr 1
  ring

/-- Exact `Lʳ` scaling of every spatial kernel derivative, also for `r = ∞`. -/
lemma gaussianSpatialNorm_scale {n : ℕ} (α : MultiIndex n) (r : ℝ≥0∞)
    {t : ℝ} (ht : 0 < t) :
    (eLpNorm (multiPartial (gaussianKernel n t) α) r (spatialMeasure n)).toReal =
      (eLpNorm (multiPartial (gaussianKernel n 1) α) r (spatialMeasure n)).toReal *
        t ^ (-(α.card : ℝ) / 2 - (n : ℝ) / 2 * (1 - r⁻¹.toReal)) := by
  have hf := gaussianSpatialMemLp n 1 (by norm_num) α r
  rw [gaussianSpatial_scale α ht]
  change (eLpNorm ((t ^ (-(n : ℝ) / 2 - (α.card : ℝ) / 2)) •
    (fun x => multiPartial (gaussianKernel n 1) α ((Real.sqrt t)⁻¹ • x))) r
      (spatialMeasure n)).toReal = _
  rw [eLpNorm_const_smul, ENNReal.toReal_mul]
  simp only [enorm, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht _)]
  rw [eLpNorm_dilate hf (inv_pos.mpr (Real.sqrt_pos.mpr ht)),
    Real.inv_rpow (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul ht.le, ← Real.rpow_neg ht.le]
  rw [← mul_assoc, mul_comm (t ^ _ * t ^ _) (eLpNorm _ r _).toReal, ← Real.rpow_add ht]
  congr 2
  ring

/-- Euler differentiation preserves Schwartz space. -/
def schwartzEuler {n : ℕ} (Φ : SchwartzMap (Space n) ℝ) :
    SchwartzMap (Space n) ℝ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.id ℝ (Space n →L[ℝ] ℝ))
    Function.HasTemperateGrowth.id (SchwartzMap.fderivCLM ℝ (Space n) ℝ Φ)

@[simp] lemma schwartzEuler_apply {n : ℕ} (Φ : SchwartzMap (Space n) ℝ) (x : Space n) :
    schwartzEuler Φ x = fderiv ℝ (Φ : Space n → ℝ) x x := rfl

/-- Time differentiation of a self-similar Schwartz profile. -/
lemma hasDerivAt_selfSimilar {n : ℕ} (Φ : SchwartzMap (Space n) ℝ)
    (a : ℝ) (x : Space n) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => s ^ a * Φ (s ^ (-(1 / 2 : ℝ)) • x))
      (t ^ (a - 1) * (a * Φ (t ^ (-(1 / 2 : ℝ)) • x) -
        (1 / 2 : ℝ) * schwartzEuler Φ (t ^ (-(1 / 2 : ℝ)) • x))) t := by
  have hpow := (hasDerivAt_id t).rpow_const (p := a) (Or.inl ht.ne')
  have hinner := ((hasDerivAt_id t).rpow_const (p := -(1 / 2 : ℝ))
    (Or.inl ht.ne')).smul_const x
  have hcomp := Φ.differentiableAt.hasFDerivAt.comp_hasDerivAt t hinner
  convert hpow.mul hcomp using 1
  · rfl
  · simp only [schwartzEuler_apply, Function.comp_apply, id_eq,
      map_smul, smul_eq_mul, one_mul]
    rw [Real.rpow_sub ht, Real.rpow_one,
      Real.rpow_sub ht, Real.rpow_one]
    ring

/-- Every mixed derivative has a Schwartz profile with the exact parabolic order. -/
lemma gaussianMixedProfile {n : ℕ} (α : MultiIndex n) (j : ℕ) :
    ∃ Φ : SchwartzMap (Space n) ℝ, ∀ t : ℝ, 0 < t → ∀ x,
      gaussianMixedDerivative α j t x =
        t ^ (-(n : ℝ) / 2 - (α.card : ℝ) / 2 - (j : ℝ)) *
          Φ (t ^ (-(1 / 2 : ℝ)) • x) := by
  induction j with
  | zero =>
    obtain ⟨Φ, hΦ⟩ := gaussianSpatialSchwartz n 1 (by norm_num) α
    refine ⟨Φ, fun t ht x => ?_⟩
    change multiPartial (gaussianKernel n t) α x = _
    rw [gaussianSpatial_scale α ht]
    simp only [Nat.cast_zero, sub_zero, Real.sqrt_eq_rpow,
      ← Real.rpow_neg ht.le]
    exact congrArg (t ^ (-(n : ℝ) / 2 - (α.card : ℝ) / 2) * ·)
      (congrFun hΦ.symm _)
  | succ j ih =>
    obtain ⟨Φ, hΦ⟩ := ih
    let a : ℝ := -(n : ℝ) / 2 - (α.card : ℝ) / 2 - (j : ℝ)
    refine ⟨a • Φ - (1 / 2 : ℝ) • schwartzEuler Φ, fun t ht x => ?_⟩
    have heq : (fun s => gaussianMixedDerivative α j s x) =ᶠ[𝓝 t]
        (fun s => s ^ a * Φ (s ^ (-(1 / 2 : ℝ)) • x)) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs using hΦ s hs x
    change iteratedDeriv (j + 1) (fun s => multiPartial (gaussianKernel n s) α x) t = _
    rw [iteratedDeriv_succ]
    change deriv (fun s => gaussianMixedDerivative α j s x) t = _
    rw [heq.deriv_eq, (hasDerivAt_selfSimilar Φ a x ht).deriv]
    simp only [sub_apply, smul_apply, smul_eq_mul]
    congr 2
    dsimp [a]
    push_cast
    ring

/-- The `Lʳ` norm of a self-similar Schwartz profile, with no finite-exponent restriction. -/
lemma selfSimilar_memLp_norm {n : ℕ} (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (r : ℝ≥0∞) {t : ℝ} (ht : 0 < t) :
    MemLp (fun x => t ^ a * Φ (t ^ (-(1 / 2 : ℝ)) • x)) r (spatialMeasure n) ∧
      (eLpNorm (fun x => t ^ a * Φ (t ^ (-(1 / 2 : ℝ)) • x)) r
        (spatialMeasure n)).toReal =
        (eLpNorm Φ r (spatialMeasure n)).toReal * t ^ (a + (n : ℝ) / 2 * r⁻¹.toReal) := by
  have hf : MemLp (Φ : Space n → ℝ) r (spatialMeasure n) := Φ.memLp r
  refine ⟨(memLp_dilate hf (Real.rpow_pos_of_pos ht _).ne').const_smul (t ^ a), ?_⟩
  change (eLpNorm ((t ^ a) • (fun x => Φ (t ^ (-(1 / 2 : ℝ)) • x))) r
    (spatialMeasure n)).toReal = _
  rw [eLpNorm_const_smul, ENNReal.toReal_mul]
  simp only [enorm, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht _)]
  rw [eLpNorm_dilate hf (Real.rpow_pos_of_pos ht _), ← Real.rpow_mul ht.le,
    ← mul_assoc, mul_comm (t ^ _ * t ^ _) (eLpNorm _ r _).toReal, ← Real.rpow_add ht]
  congr 2
  ring

/-- All mixed Gaussian derivatives satisfy the source's full time rate. -/
theorem gaussianMixedBound : P201Specs.Heat.gaussianMixedBoundStatement := by
  intro n _ α j r _
  obtain ⟨Φ, hΦ⟩ := gaussianMixedProfile α j
  refine ⟨(eLpNorm Φ r (spatialMeasure n)).toReal, ENNReal.toReal_nonneg, fun t ht => ?_⟩
  have heq : gaussianMixedDerivative α j t = fun x =>
      t ^ (-(n : ℝ) / 2 - (α.card : ℝ) / 2 - (j : ℝ)) *
        Φ (t ^ (-(1 / 2 : ℝ)) • x) := funext (hΦ t ht)
  change MemLp (gaussianMixedDerivative α j t) r (spatialMeasure n) ∧
    (eLpNorm (gaussianMixedDerivative α j t) r (spatialMeasure n)).toReal ≤ _
  rw [heq]
  obtain ⟨hm, hn⟩ := selfSimilar_memLp_norm Φ _ r ht
  refine ⟨hm, le_of_eq ?_⟩
  rw [hn]
  congr 2
  ring

/-- An integrable polynomial envelope in every conjugate exponent. -/
lemma polynomialWeight_memLp (n : ℕ) (r : ℝ≥0∞) (hr : 1 ≤ r) :
    MemLp (fun y : Space n => (1 + ‖y‖) ^ (-(n + 1 : ℝ))) r (spatialMeasure n) := by
  have hm : AEStronglyMeasurable
      (fun y : Space n => (1 + ‖y‖) ^ (-(n + 1 : ℝ))) (spatialMeasure n) := by
    apply Continuous.aestronglyMeasurable
    have hc : Continuous (fun y : Space n => (1 : ℝ) + ‖y‖) :=
      continuous_const.add continuous_norm
    exact hc.rpow_const (fun y => Or.inl (ne_of_gt (by positivity)))
  by_cases hrtop : r = (⊤ : ℝ≥0∞)
  · subst r
    refine memLp_top_of_bound hm 1 (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (neg_nonpos.mpr (by positivity))
  · have hr0 : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le hr)
    apply (integrable_norm_rpow_iff hm hr0 hrtop).mp
    have hrreal : 1 ≤ r.toReal := by
      simpa using ENNReal.toReal_mono hrtop hr
    have hint := integrable_one_add_norm (E := Space n) (μ := spatialMeasure n)
      (r := (n + 1 : ℝ) * r.toReal) (by
        simp only [finrank_euclideanSpace, Fintype.card_fin]
        have hh := mul_le_mul_of_nonneg_left hrreal (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
        linarith)
    convert hint using 1
    funext y
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _),
      ← Real.rpow_mul (by positivity)]
    congr 1
    ring

/-- A Schwartz function admits a uniform polynomial bound under translations
and dilations with bounded inverse scale. -/
lemma schwartz_shift_bound {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : SchwartzMap (Space n) F) (N : ℕ) {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x y : Space n) (c : ℝ), ‖x‖ ≤ R → 0 < c → c⁻¹ ≤ S →
      ‖Φ (c • (x - y))‖ ≤ C * (1 + ‖y‖) ^ (-(N : ℝ)) := by
  let K := 2 ^ N * (Finset.Iic (N, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Φ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨(1 + R + S) ^ N * K, by positivity, fun x y c hx hc hcs => ?_⟩
  have hscale : 1 + ‖y‖ ≤ (1 + R + S) * (1 + ‖c • (x - y)‖) := by
    have hnorm : ‖x - y‖ = c⁻¹ * ‖c • (x - y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      field_simp
    have htri : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
      have := norm_sub_le x (x - y)
      simpa only [sub_sub_cancel] using this
    have hprod := mul_le_mul_of_nonneg_right hcs (norm_nonneg (c • (x - y)))
    rw [hnorm] at htri
    nlinarith [norm_nonneg (c • (x - y)), mul_nonneg hR (norm_nonneg (c • (x - y)))]
  have hbound : (1 + ‖c • (x - y)‖) ^ N * ‖Φ (c • (x - y))‖ ≤ K := by
    simpa only [norm_iteratedFDeriv_zero] using
      Φ.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) le_rfl le_rfl (c • (x - y))
  have hmul : (1 + ‖y‖) ^ N * ‖Φ (c • (x - y))‖ ≤ (1 + R + S) ^ N * K := by
    calc
      _ ≤ ((1 + R + S) * (1 + ‖c • (x - y)‖)) ^ N * ‖Φ (c • (x - y))‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hscale N) (norm_nonneg _)
      _ = (1 + R + S) ^ N * ((1 + ‖c • (x - y)‖) ^ N * ‖Φ (c • (x - y))‖) := by
        rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  exact (le_mul_inv_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hmul)

/-- A self-similar Schwartz family has a local polynomial majorant, uniformly
in both the time and the evaluation point. -/
lemma selfSimilar_local_bound {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : SchwartzMap (Space n) F) (a : ℝ) (N : ℕ) (z₀ : Space n × ℝ) (ht : 0 < z₀.2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z : Space n × ℝ in 𝓝 z₀, ∀ y : Space n,
      ‖z.2 ^ a • Φ (z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y))‖ ≤
        C * (1 + ‖y‖) ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := schwartz_shift_bound Φ N
    (R := ‖z₀.1‖ + 1) (S := Real.sqrt z₀.2 + 1) (by positivity) (by positivity)
  let B := ‖z₀.2 ^ a‖ + 1
  refine ⟨B * C, by dsimp [B]; positivity, ?_⟩
  have hpow : ∀ᶠ z : Space n × ℝ in 𝓝 z₀, ‖z.2 ^ a‖ < B :=
    (continuousAt_snd.rpow_const (Or.inl ht.ne')).norm.eventually
      (gt_mem_nhds (by dsimp [B]; linarith))
  have hsqrt : ∀ᶠ z : Space n × ℝ in 𝓝 z₀, Real.sqrt z.2 < Real.sqrt z₀.2 + 1 :=
    (Real.continuous_sqrt.continuousAt.comp continuousAt_snd).eventually
      (gt_mem_nhds (by change Real.sqrt z₀.2 < Real.sqrt z₀.2 + 1; linarith))
  have hx : ∀ᶠ z : Space n × ℝ in 𝓝 z₀, ‖z.1‖ < ‖z₀.1‖ + 1 :=
    continuousAt_fst.norm.eventually (gt_mem_nhds (by linarith))
  filter_upwards [continuousAt_snd.eventually (Ioi_mem_nhds ht), hpow, hsqrt, hx]
    with z hzt hzp hzs hzx y
  have hinv : (z.2 ^ (-(1 / 2 : ℝ)))⁻¹ ≤ Real.sqrt z₀.2 + 1 := by
    rw [← Real.rpow_neg (le_of_lt hzt), neg_neg, ← Real.sqrt_eq_rpow]
    exact hzs.le
  have hb' := hb z.1 y (z.2 ^ (-(1 / 2 : ℝ))) hzx.le
    (Real.rpow_pos_of_pos hzt _) hinv
  rw [norm_smul]
  calc
    _ ≤ B * (C * (1 + ‖y‖) ^ (-(N : ℝ))) :=
      mul_le_mul hzp.le hb' (norm_nonneg _) (by dsimp [B]; positivity)
    _ = _ := by ring

/-- The Schwartz profile of a time derivative. -/
def schwartzTimeStep {n : ℕ} (a : ℝ) (Φ : SchwartzMap (Space n) ℝ) :
    SchwartzMap (Space n) ℝ := a • Φ - (1 / 2 : ℝ) • schwartzEuler Φ

@[simp] lemma schwartzTimeStep_apply {n : ℕ} (a : ℝ) (Φ : SchwartzMap (Space n) ℝ)
    (x : Space n) : schwartzTimeStep a Φ x = a * Φ x - (1 / 2 : ℝ) * fderiv ℝ Φ x x := rfl

def selfSimilarKernel {n : ℕ} (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (z : Space n × ℝ) (y : Space n) : ℝ :=
  z.2 ^ a * Φ (z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y))

def selfSimilarKernelDerivative {n : ℕ} (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (z : Space n × ℝ) (y : Space n) : (Space n × ℝ) →L[ℝ] ℝ :=
  (z.2 ^ (a - 1 / 2)) • ((fderiv ℝ Φ (z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y))).comp
    (ContinuousLinearMap.fst ℝ (Space n) ℝ)) +
  (z.2 ^ (a - 1) * schwartzTimeStep a Φ (z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y))) •
    (ContinuousLinearMap.snd ℝ (Space n) ℝ)

lemma hasFDerivAt_selfSimilarKernel {n : ℕ} (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (z : Space n × ℝ) (y : Space n) (ht : 0 < z.2) :
    HasFDerivAt (selfSimilarKernel Φ a · y) (selfSimilarKernelDerivative Φ a z y) z := by
  have hp := (hasFDerivAt_snd (p := z)).rpow_const (p := a) (Or.inl ht.ne')
  have hi := ((hasFDerivAt_snd (p := z)).rpow_const (p := -(1 / 2 : ℝ))
    (Or.inl ht.ne')).smul ((hasFDerivAt_fst (p := z)).sub_const y)
  have hc := Φ.differentiableAt.hasFDerivAt.comp z hi
  apply (hp.mul hc).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [selfSimilarKernelDerivative, schwartzTimeStep_apply,
    add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply,
    Function.comp_apply, Pi.smul_apply', map_add, map_smul, smul_eq_mul]
  simp only [Real.rpow_sub ht, Real.rpow_one, Real.rpow_neg ht.le]
  ring

lemma selfSimilarKernelDerivative_bound {n : ℕ} (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (z : Space n × ℝ) (y : Space n) :
    ‖selfSimilarKernelDerivative Φ a z y‖ ≤
      ‖z.2 ^ (a - 1 / 2) • (SchwartzMap.fderivCLM ℝ (Space n) ℝ Φ)
        (z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y))‖ +
      ‖z.2 ^ (a - 1) • schwartzTimeStep a Φ (z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y))‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  dsimp only [selfSimilarKernelDerivative]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  change ‖((z.2 ^ (a - 1 / 2)) • fderiv ℝ Φ (z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y))) v.1 +
    (z.2 ^ (a - 1) * schwartzTimeStep a Φ (z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y))) * v.2‖ ≤ _
  refine (norm_add_le _ _).trans ?_
  calc
    _ ≤ ‖((z.2 ^ (a - 1 / 2)) • fderiv ℝ Φ (z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y)))‖ * ‖v.1‖ +
        ‖z.2 ^ (a - 1) * schwartzTimeStep a Φ (z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y))‖ * ‖v.2‖ :=
      add_le_add (ContinuousLinearMap.le_opNorm _ _) (norm_mul _ _).le
    _ ≤ _ := by
      rw [add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le v) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_snd_le v) (norm_nonneg _))

lemma selfSimilarKernelDerivative_local_bound {n : ℕ} (Φ : SchwartzMap (Space n) ℝ)
    (a : ℝ) (N : ℕ) (z₀ : Space n × ℝ) (ht : 0 < z₀.2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z : Space n × ℝ in 𝓝 z₀, ∀ y : Space n,
      ‖selfSimilarKernelDerivative Φ a z y‖ ≤ C * (1 + ‖y‖) ^ (-(N : ℝ)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := selfSimilar_local_bound
    (SchwartzMap.fderivCLM ℝ (Space n) ℝ Φ) (a - 1 / 2) N z₀ ht
  obtain ⟨C₂, hC₂, h₂⟩ := selfSimilar_local_bound (schwartzTimeStep a Φ) (a - 1) N z₀ ht
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  filter_upwards [h₁, h₂] with z hz₁ hz₂ y
  exact (selfSimilarKernelDerivative_bound Φ a z y).trans
    ((add_le_add (hz₁ y) (hz₂ y)).trans_eq (add_mul _ _ _).symm)

lemma gaussianSpatialConvolution_integrable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n))
    (α : MultiIndex n) {t : ℝ} (ht : 0 < t) (x : Space n) :
    Integrable (fun y => multiPartial (gaussianKernel n t) α (x-y) • g y)
      (spatialMeasure n) := by
  have hk := gaussianSpatialMemLp n t ht α p.conjExponent
  have hi := MeasureTheory.ConvolutionExists.of_memLp_memLp
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜) hk (Lp.memLp g) x
  change Integrable (fun y => multiPartial (gaussianKernel n t) α y • g (x - y)) at hi
  simpa only [sub_sub_cancel] using hi.comp_sub_left x

lemma heatEquation_of_differentiation
    (hdiff : P201Specs.Heat.heatDifferentiationUnderIntegralStatement)
    (n : ℕ) (hn : 1 ≤ n) (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) (t : ℝ) (ht : 0 < t) (x : Space n) :
    deriv (fun s => heatConvolution s g x) t = laplacian (heatConvolution t g) x := by
  have htime := hdiff n hn 𝕜 p g 0 1 t ht x
  simp only [P201Specs.Heat.heatMixedDerivative, P201Specs.Heat.gaussianMixedDerivative,
    iteratedDeriv_one, P201Specs.multiPartial, P102.U4.multiPartial,
    Multiset.sort_zero, P102.U4.partialWord] at htime
  rw [htime]
  simp_rw [gaussianHeatEquation n hn t ht]
  change (∫ y, (∑ i : Fin n, multiPartial (gaussianKernel n t) ({i,i} : MultiIndex n) (x-y)) • g y) =
    ∑ i : Fin n, multiPartial (heatConvolution t g) ({i,i} : MultiIndex n) x
  simp_rw [Finset.sum_smul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact (hdiff n hn 𝕜 p g ({i,i} : MultiIndex n) 0 t ht x).symm
  · intro i _
    exact gaussianSpatialConvolution_integrable p g _ ht x

lemma gaussianKernel_eq_selfSimilarKernel {n : ℕ} (Φ : SchwartzMap (Space n) ℝ)
    (hΦ : (Φ : Space n → ℝ) = gaussianKernel n 1)
    (z : Space n × ℝ) (ht : 0 < z.2) (y : Space n) :
    gaussianKernel n z.2 (z.1-y) = selfSimilarKernel Φ (-(n : ℝ)/2) z y := by
  rw [gaussianKernel_scale ht]
  unfold selfSimilarKernel
  rw [← hΦ]
  simp only [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le]


def selfSimilarConvolution {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Φ : SchwartzMap (Space n) ℝ) (a : ℝ) (g : Space n → 𝕜)
    (z : Space n × ℝ) : 𝕜 :=
  ∫ y, selfSimilarKernel Φ a z y • g y ∂spatialMeasure n

lemma polynomialWeight_mul_lp_integrable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) (C : ℝ) :
    Integrable (fun y : Space n => C * (1 + ‖y‖) ^ (-(n + 1 : ℝ)) * ‖g y‖)
      (spatialMeasure n) := by
  have hr : 1 ≤ p.conjExponent := by
    simp only [ENNReal.conjExponent]
    exact le_self_add
  have h := (polynomialWeight_memLp n p.conjExponent hr).integrable_mul (MeasureTheory.Lp.memLp g).norm
  convert h.const_mul C using 1
  funext y
  simp only [Pi.mul_apply]
  ring

lemma selfSimilarKernel_continuous {n : ℕ} (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (z : Space n × ℝ) : Continuous (selfSimilarKernel Φ a z) := by
  unfold selfSimilarKernel
  exact continuous_const.mul (Φ.continuous.comp (by fun_prop))

lemma selfSimilarKernelDerivative_continuous {n : ℕ} (Φ : SchwartzMap (Space n) ℝ)
    (a : ℝ) (z : Space n × ℝ) : Continuous (selfSimilarKernelDerivative Φ a z) := by
  unfold selfSimilarKernelDerivative
  have hc : Continuous (fun y : Space n => z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y)) :=
    by fun_prop
  apply Continuous.add
  · have hd := ((SchwartzMap.fderivCLM ℝ (Space n) ℝ Φ).continuous.comp hc).clm_comp_const
      (ContinuousLinearMap.fst ℝ (Space n) ℝ)
    exact (continuous_const (y := z.2 ^ (a - 1 / 2))).smul hd
  · exact (continuous_const.mul ((schwartzTimeStep a Φ).continuous.comp hc)).smul continuous_const

lemma selfSimilarConvolution_integrable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) (z : Space n × ℝ) (ht : 0 < z.2) :
    Integrable (fun y => selfSimilarKernel Φ a z y • g y) (spatialMeasure n) := by
  obtain ⟨C, hC, hb⟩ := selfSimilar_local_bound Φ a (n+1) z ht
  have hzb := hb.self_of_nhds
  refine (polynomialWeight_mul_lp_integrable g C).mono'
    ((selfSimilarKernel_continuous Φ a z).aestronglyMeasurable.smul (MeasureTheory.Lp.memLp g).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul]
  have h := hzb y
  simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

lemma selfSimilarConvolutionDerivative_integrable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) (z : Space n × ℝ) (ht : 0 < z.2) :
    Integrable (fun y => (selfSimilarKernelDerivative Φ a z y).smulRight (g y))
      (spatialMeasure n) := by
  obtain ⟨C, hC, hb⟩ := selfSimilarKernelDerivative_local_bound Φ a (n+1) z ht
  have hzb := hb.self_of_nhds
  refine (polynomialWeight_mul_lp_integrable g C).mono'
    ((ContinuousLinearMap.smulRightL ℝ (Space n × ℝ) 𝕜).aestronglyMeasurable_comp₂
      (selfSimilarKernelDerivative_continuous Φ a z).aestronglyMeasurable
      (MeasureTheory.Lp.memLp g).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [ContinuousLinearMap.norm_smulRight_apply]
  have h := hzb y
  simp only [Nat.cast_add, Nat.cast_one] at h
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

lemma hasFDerivAt_selfSimilarConvolution {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) (z : Space n × ℝ) (ht : 0 < z.2) :
    HasFDerivAt (selfSimilarConvolution Φ a g)
      (∫ y, (selfSimilarKernelDerivative Φ a z y).smulRight (g y) ∂spatialMeasure n) z := by
  obtain ⟨C, hC, hb⟩ := selfSimilarKernelDerivative_local_bound Φ a (n+1) z ht
  let s : Set (Space n × ℝ) := {w | 0 < w.2 ∧ ∀ y,
    ‖selfSimilarKernelDerivative Φ a w y‖ ≤ C * (1 + ‖y‖) ^ (-(n + 1 : ℝ))}
  have hs : s ∈ 𝓝 z := by
    filter_upwards [continuousAt_snd.eventually (Ioi_mem_nhds ht), hb] with w hwt hwb
    exact ⟨hwt, by simpa only [Nat.cast_add, Nat.cast_one] using hwb⟩
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hs
    (Eventually.of_forall fun w => (selfSimilarKernel_continuous Φ a w).aestronglyMeasurable.smul
      (MeasureTheory.Lp.memLp g).aestronglyMeasurable)
    (selfSimilarConvolution_integrable Φ a g z ht)
    ((ContinuousLinearMap.smulRightL ℝ (Space n × ℝ) 𝕜).aestronglyMeasurable_comp₂
      (selfSimilarKernelDerivative_continuous Φ a z).aestronglyMeasurable
      (MeasureTheory.Lp.memLp g).aestronglyMeasurable)
    (Eventually.of_forall fun y w hw => by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right (hw.2 y) (norm_nonneg _))
    (polynomialWeight_mul_lp_integrable g C)
    (Eventually.of_forall fun y w hw => (hasFDerivAt_selfSimilarKernel Φ a w y hw.1).smul_const (g y))

lemma fderiv_selfSimilarConvolution_apply {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) (z v : Space n × ℝ) (ht : 0 < z.2) :
    fderiv ℝ (selfSimilarConvolution Φ a g) z v =
      selfSimilarConvolution
        (SchwartzMap.evalCLM ℝ (Space n) ℝ v.1 (SchwartzMap.fderivCLM ℝ (Space n) ℝ Φ))
        (a - 1 / 2) g z +
      v.2 • selfSimilarConvolution (schwartzTimeStep a Φ) (a - 1) g z := by
  rw [(hasFDerivAt_selfSimilarConvolution Φ a g z ht).fderiv,
    ContinuousLinearMap.integral_apply (selfSimilarConvolutionDerivative_integrable Φ a g z ht)]
  let Ψ := SchwartzMap.evalCLM ℝ (Space n) ℝ v.1 (SchwartzMap.fderivCLM ℝ (Space n) ℝ Φ)
  have h₁ := selfSimilarConvolution_integrable Ψ (a - 1 / 2) g z ht
  have h₂ := selfSimilarConvolution_integrable (schwartzTimeStep a Φ) (a - 1) g z ht
  change _ = (∫ y, selfSimilarKernel Ψ (a - 1 / 2) z y • g y ∂spatialMeasure n) +
    v.2 • (∫ y, selfSimilarKernel (schwartzTimeStep a Φ) (a - 1) z y • g y ∂spatialMeasure n)
  have h₂' : Integrable (fun y => v.2 • (selfSimilarKernel (schwartzTimeStep a Φ) (a - 1) z y • g y))
      (spatialMeasure n) := by
    apply (h₂.smul v.2).congr
    exact Eventually.of_forall fun y => by simp [smul_smul]
  rw [← integral_smul, ← integral_add h₁ h₂']
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    simp only [selfSimilarKernelDerivative, ContinuousLinearMap.smulRight_apply,
      add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', smul_eq_mul, selfSimilarKernel]
    change ((z.2 ^ (a - 1 / 2)) * fderiv ℝ Φ
      (z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y)) v.1 +
        (z.2 ^ (a - 1) * schwartzTimeStep a Φ
          (z.2 ^ (-(1 / 2 : ℝ)) • (z.1 - y))) * v.2) • g y = _
    simp only [add_smul, mul_smul]
    congr 1
    simp only [smul_smul]
    congr 1; ring

lemma contDiffOn_selfSimilarConvolution {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n)) :
    ContDiffOn ℝ ∞ (selfSimilarConvolution Φ a g) {z | 0 < z.2} := by
  have hopen : IsOpen {z : Space n × ℝ | 0 < z.2} :=
    isOpen_lt continuous_const continuous_snd
  have hdiff : ∀ (Ψ : SchwartzMap (Space n) ℝ) (b : ℝ),
      DifferentiableOn ℝ (selfSimilarConvolution Ψ b g) {z | 0 < z.2} := by
    intro Ψ b z hz
    exact (hasFDerivAt_selfSimilarConvolution Ψ b g z hz).differentiableAt.differentiableWithinAt
  have hnat : ∀ k : ℕ, ∀ (Ψ : SchwartzMap (Space n) ℝ) (b : ℝ),
      ContDiffOn ℝ k (selfSimilarConvolution Ψ b g) {z | 0 < z.2} := by
    intro k
    induction k with
    | zero =>
      intro Ψ b
      exact contDiffOn_zero.mpr (hdiff Ψ b).continuousOn
    | succ k ih =>
      intro Ψ b
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_apply hopen.uniqueDiffOn]
      refine ⟨hdiff Ψ b, by simp, fun v => ?_⟩
      have hh := (ih (SchwartzMap.evalCLM ℝ (Space n) ℝ v.1
        (SchwartzMap.fderivCLM ℝ (Space n) ℝ Ψ)) (b - 1 / 2)).add
        ((ih (schwartzTimeStep b Ψ) (b - 1)).const_smul v.2)
      apply hh.congr
      intro z hz
      rw [fderivWithin_of_isOpen hopen hz]
      exact (fderiv_selfSimilarConvolution_apply Ψ b g z v hz)
  exact contDiffOn_infty.mpr fun k => hnat k Φ a


lemma heatConvolution_eq_selfSimilar {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Φ : SchwartzMap (Space n) ℝ) (hΦ : (Φ : Space n → ℝ) = gaussianKernel n 1)
    (g : Space n → 𝕜) (z : Space n × ℝ) (ht : 0 < z.2) :
    heatConvolution z.2 g z.1 = selfSimilarConvolution Φ (-(n : ℝ)/2) g z := by
  apply integral_congr_ae
  exact Eventually.of_forall fun y => congrArg (fun r : ℝ => r • g y)
    (gaussianKernel_eq_selfSimilarKernel Φ hΦ z ht y)

theorem heatSmoothRepresentative : P201Specs.Heat.heatSmoothRepresentativeStatement := by
  intro n _ 𝕜 _ p _ g
  refine ⟨fun t ht x => heatConvolutionEverywhere n 𝕜 p g t ht x, ?_⟩
  obtain ⟨Φ, hΦ⟩ := gaussianSchwartz n (t := 1) (by norm_num)
  apply (contDiffOn_selfSimilarConvolution Φ (-(n : ℝ)/2) g).congr
  intro z hz
  exact heatConvolution_eq_selfSimilar Φ hΦ g z hz


def schwartzCoordinate {n : ℕ} (Φ : SchwartzMap (Space n) ℝ) (v : Space n) :
    SchwartzMap (Space n) ℝ :=
  SchwartzMap.evalCLM ℝ (Space n) ℝ v (SchwartzMap.fderivCLM ℝ (Space n) ℝ Φ)

@[simp] lemma schwartzCoordinate_apply {n : ℕ} (Φ : SchwartzMap (Space n) ℝ)
    (v x : Space n) : schwartzCoordinate Φ v x = fderiv ℝ Φ x v := rfl

lemma fderiv_selfSimilarProfile {n : ℕ} (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    {t : ℝ} (ht : 0 < t) (x v : Space n) :
    fderiv ℝ (fun x : Space n => t ^ a * Φ (t ^ (-(1 / 2 : ℝ)) • x)) x v =
      t ^ (a - 1 / 2) * schwartzCoordinate Φ v (t ^ (-(1 / 2 : ℝ)) • x) := by
  have hc := (Φ.differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul (t ^ (-(1 / 2 : ℝ))))).const_mul (t ^ a)
  have heq : fderiv ℝ (fun x : Space n => t ^ a * Φ (t ^ (-(1 / 2 : ℝ)) • x)) x =
      (t ^ a) • (fderiv ℝ Φ (t ^ (-(1 / 2 : ℝ)) • x)).comp
        ((t ^ (-(1 / 2 : ℝ))) • ContinuousLinearMap.id ℝ (Space n)) := by
    simpa only [Function.comp_def, Pi.smul_apply, id_eq] using hc.fderiv
  rw [heq]
  simp only [schwartzCoordinate_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  rw [show a - 1 / 2 = a + -(1 / 2 : ℝ) by ring, Real.rpow_add ht]
  ring

section ConvolutionDerivatives
variable (n : ℕ) (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
variable (g : MeasureTheory.Lp 𝕜 p (spatialMeasure n))
lemma selfSimilarConvolution_fderiv_profile (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (z : Space n × ℝ) (ht : 0 < z.2) (v : Space n × ℝ) :
    fderiv ℝ (selfSimilarConvolution Φ a g) z v =
      selfSimilarConvolution (schwartzCoordinate Φ v.1) (a - 1 / 2) g z +
        v.2 • selfSimilarConvolution (schwartzTimeStep a Φ) (a - 1) g z :=
  fderiv_selfSimilarConvolution_apply Φ a g z v ht

lemma fderiv_selfSimilarConvolution_spatial (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    {t : ℝ} (ht : 0 < t) (x v : Space n) :
    fderiv ℝ (fun x => selfSimilarConvolution Φ a g (x, t)) x v =
      selfSimilarConvolution (schwartzCoordinate Φ v) (a - 1 / 2) g (x, t) := by
  have hc := (hasFDerivAt_selfSimilarConvolution Φ a g (x, t) ht).comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (c := t) x))
  have heq : fderiv ℝ (fun x => selfSimilarConvolution Φ a g (x, t)) x =
      (∫ y, (selfSimilarKernelDerivative Φ a (x,t) y).smulRight (g y) ∂spatialMeasure n).comp
        ((ContinuousLinearMap.id ℝ (Space n)).prod 0) := by
    simpa only [Function.comp_def, id_eq] using hc.fderiv
  rw [heq]
  change (∫ y, (selfSimilarKernelDerivative Φ a (x,t) y).smulRight (g y) ∂spatialMeasure n) (v,0) = _
  rw [← (hasFDerivAt_selfSimilarConvolution Φ a g (x, t) ht).fderiv]
  simpa using selfSimilarConvolution_fderiv_profile n 𝕜 p g Φ a (x, t) ht (v, 0)

lemma deriv_selfSimilarConvolution_time (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    {t : ℝ} (ht : 0 < t) (x : Space n) :
    deriv (fun s => selfSimilarConvolution Φ a g (x, s)) t =
      selfSimilarConvolution (schwartzTimeStep a Φ) (a - 1) g (x, t) := by
  have hc := (hasFDerivAt_selfSimilarConvolution Φ a g (x, t) ht).comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  change deriv (selfSimilarConvolution Φ a g ∘ Prod.mk x) t = _
  rw [hc.deriv]
  rw [← (hasFDerivAt_selfSimilarConvolution Φ a g (x, t) ht).fderiv]
  rw [selfSimilarConvolution_fderiv_profile n 𝕜 p g Φ a (x, t) ht (0, 1)]
  have hz : schwartzCoordinate Φ (0 : Space n) = 0 := by
    ext y
    simp
  simp only [hz, one_smul]
  change (∫ y, selfSimilarKernel 0 (a - 1 / 2) (x, t) y • g y ∂spatialMeasure n) + _ = _
  simp [selfSimilarKernel]


lemma selfSimilar_partialWord_profile (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (l : List (Fin n)) :
    ∃ (Ψ : SchwartzMap (Space n) ℝ) (b : ℝ),
      (∀ t : ℝ, 0 < t → P102.U4.partialWord
        (fun x : Space n => t ^ a * Φ (t ^ (-(1 / 2 : ℝ)) • x)) l =
          fun x => t ^ b * Ψ (t ^ (-(1 / 2 : ℝ)) • x)) ∧
      (∀ t : ℝ, 0 < t → P102.U4.partialWord
        (fun x : Space n => selfSimilarConvolution Φ a g (x,t)) l =
          fun x => selfSimilarConvolution Ψ b g (x,t)) := by
  induction l with
  | nil => exact ⟨Φ, a, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨Ψ, b, hkernel, hconv⟩ := ih
    refine ⟨schwartzCoordinate Ψ (coordinate n i), b - 1/2, ?_, ?_⟩
    · intro t ht
      funext x
      change fderiv ℝ (P102.U4.partialWord _ l) x (coordinate n i) = _
      rw [hkernel t ht, fderiv_selfSimilarProfile Ψ b ht]
    · intro t ht
      funext x
      change fderiv ℝ (P102.U4.partialWord _ l) x (coordinate n i) = _
      rw [hconv t ht, fderiv_selfSimilarConvolution_spatial n 𝕜 p g Ψ b ht]

lemma partialWord_selfSimilarConvolution (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (l : List (Fin n)) {t : ℝ} (ht : 0 < t) (x : Space n) :
    P102.U4.partialWord (fun x : Space n => selfSimilarConvolution Φ a g (x,t)) l x =
      ∫ y, P102.U4.partialWord
        (fun x : Space n => t ^ a * Φ (t ^ (-(1/2 : ℝ)) • x)) l (x-y) • g y
          ∂spatialMeasure n := by
  obtain ⟨Ψ, b, hkernel, hconv⟩ := selfSimilar_partialWord_profile n 𝕜 p g Φ a l
  rw [hconv t ht, hkernel t ht]
  rfl

lemma deriv_convolution_of_selfSimilarProfile (K : ℝ → Space n → ℝ)
    (Φ : SchwartzMap (Space n) ℝ) (a : ℝ)
    (hK : ∀ s : ℝ, 0 < s → ∀ y, K s y = s ^ a * Φ (s ^ (-(1/2 : ℝ)) • y))
    {t : ℝ} (ht : 0 < t) (x : Space n) :
    deriv (fun s => ∫ y, K s (x-y) • g y ∂spatialMeasure n) t =
      ∫ y, deriv (fun s => K s (x-y)) t • g y ∂spatialMeasure n := by
  have heq : (fun s => ∫ y, K s (x-y) • g y ∂spatialMeasure n) =ᶠ[𝓝 t]
      (fun s => selfSimilarConvolution Φ a g (x,s)) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      change K s (x-y) • g y = _
      rw [hK s hs]
      rfl
  rw [heq.deriv_eq, deriv_selfSimilarConvolution_time n 𝕜 p g Φ a ht]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    have hky : (fun s => K s (x-y)) =ᶠ[𝓝 t]
        (fun s => s ^ a * Φ (s ^ (-(1/2 : ℝ)) • (x-y))) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs using hK s hs (x-y)
    change selfSimilarKernel (schwartzTimeStep a Φ) (a-1) (x,t) y • g y =
      deriv (fun s => K s (x-y)) t • g y
    rw [hky.deriv_eq, (hasDerivAt_selfSimilar Φ a (x-y) ht).deriv]
    rfl


lemma heatSpatialDerivativeUnderIntegral (α : MultiIndex n) {t : ℝ} (ht : 0 < t)
    (x : Space n) :
    multiPartial (heatConvolution t g) α x =
      ∫ y, multiPartial (gaussianKernel n t) α (x-y) • g y ∂spatialMeasure n := by
  obtain ⟨Φ, hΦ⟩ := gaussianSchwartz n (t := 1) (by norm_num)
  have hk : gaussianKernel n t =
      fun w => t ^ (-(n : ℝ)/2) * Φ (t ^ (-(1/2 : ℝ)) • w) := by
    funext w
    simpa only [sub_zero, selfSimilarKernel] using
      gaussianKernel_eq_selfSimilarKernel Φ hΦ (w,t) ht 0
  have hc : heatConvolution t g =
      fun w => selfSimilarConvolution Φ (-(n : ℝ)/2) g (w,t) := by
    funext w
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      change gaussianKernel n t (w-y) • g y = _
      rw [gaussianKernel_eq_selfSimilarKernel Φ hΦ (w,t) ht y]
  change P102.U4.partialWord (heatConvolution t g) (α.sort (· ≤ ·)) x =
    ∫ y, P102.U4.partialWord (gaussianKernel n t) (α.sort (· ≤ ·)) (x-y) • g y
      ∂spatialMeasure n
  rw [hc, partialWord_selfSimilarConvolution n 𝕜 p g Φ _ _ ht, hk]

end ConvolutionDerivatives

theorem heatDifferentiationUnderIntegral :
    P201Specs.Heat.heatDifferentiationUnderIntegralStatement := by
  intro n _ 𝕜 _ p _ g α j
  induction j with
  | zero =>
    intro t ht x
    exact heatSpatialDerivativeUnderIntegral n 𝕜 p g α ht x
  | succ j ih =>
    intro t ht x
    change iteratedDeriv (j+1) (fun s => multiPartial (heatConvolution s g) α x) t = _
    rw [iteratedDeriv_succ]
    change deriv (fun s => heatMixedDerivative α j g s x) t = _
    have heq : (fun s => heatMixedDerivative α j g s x) =ᶠ[𝓝 t]
        (fun s => ∫ y, gaussianMixedDerivative α j s (x-y) • g y ∂spatialMeasure n) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs using ih s hs x
    rw [heq.deriv_eq]
    obtain ⟨Φ, hΦ⟩ := gaussianMixedProfile α j
    rw [deriv_convolution_of_selfSimilarProfile n 𝕜 p g
      (fun s y => gaussianMixedDerivative α j s y) Φ _ hΦ ht]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      change deriv (fun s => gaussianMixedDerivative α j s (x-y)) t • g y =
        gaussianMixedDerivative α (j+1) t (x-y) • g y
      rw [gaussianMixedDerivative, P201Specs.Heat.gaussianMixedDerivative, iteratedDeriv_succ]
      rfl


variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
def directionalWord (f : E → F) : List E → E → F
  | [] => f
  | v :: l => fun x => fderiv ℝ (directionalWord f l) x v
lemma directionalWord_smooth {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (l : List E) :
    ContDiffOn ℝ (⊤ : ℕ∞) (directionalWord f l) s := by
  induction l with
  | nil => exact hf
  | cons v l ih => exact (ih.fderiv_of_isOpen hs (by simp)).clm_apply contDiffOn_const
lemma directionalWord_congr {s : Set E} (hs : IsOpen s) {f g : E → F}
    (hfg : EqOn f g s) (l : List E) : EqOn (directionalWord f l) (directionalWord g l) s := by
  induction l with
  | nil => exact hfg
  | cons v l ih =>
    intro x hx
    change fderiv ℝ (directionalWord f l) x v = fderiv ℝ (directionalWord g l) x v
    apply congrArg (fun L : E →L[ℝ] F => L v)
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hs.mem_nhds hx] with y hy using ih hy
lemma directionalWord_append (f : E → F) (l l' : List E) :
    directionalWord f (l ++ l') = directionalWord (directionalWord f l') l := by
  induction l with
  | nil => rfl
  | cons v l ih => simp only [List.cons_append, directionalWord, ih]
lemma directionalWord_perm {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) {l l' : List E} (hp : l.Perm l') :
    EqOn (directionalWord f l) (directionalWord f l') s := by
  induction hp with
  | nil => exact fun _ _ => rfl
  | cons v h ih => exact directionalWord_congr hs ih [v]
  | swap v w l =>
    intro x hx
    have hg := (directionalWord_smooth hs hf l).contDiffAt (hs.mem_nhds hx)
    have hd : DifferentiableAt ℝ (fderiv ℝ (directionalWord f l)) x :=
      (hg.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero
    simp only [directionalWord]
    rw [fderiv_clm_apply hd (differentiableAt_const w),
      fderiv_clm_apply hd (differentiableAt_const v)]
    simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply] using hg.isSymmSndFDerivAt (by simp) w v
  | trans h h' ih ih' => exact fun _ hx => (ih hx).trans (ih' hx)
lemma directionalWord_sum {ι : Type*} {s : Set E} (hs : IsOpen s)
    (I : Finset ι) (f : ι → E → F) (hf : ∀ i ∈ I, ContDiffOn ℝ (⊤ : ℕ∞) (f i) s)
    (l : List E) : EqOn (directionalWord (fun x => ∑ i ∈ I, f i x) l)
      (fun x => ∑ i ∈ I, directionalWord (f i) l x) s := by
  induction l with
  | nil => exact fun _ _ => rfl
  | cons v l ih =>
    intro x hx
    change fderiv ℝ (directionalWord (fun x => ∑ i ∈ I, f i x) l) x v = _
    have heq := directionalWord_congr hs ih [v] hx
    change fderiv ℝ (directionalWord (fun x => ∑ i ∈ I, f i x) l) x v =
      fderiv ℝ (fun x => ∑ i ∈ I, directionalWord (f i) l x) x v at heq
    rw [heq, fderiv_fun_sum]
    · simp only [sum_apply, directionalWord]
    · intro i hi
      exact ((directionalWord_smooth hs (hf i hi) l).contDiffAt
        (hs.mem_nhds hx)).differentiableAt (by simp)

variable {ι : Type*} [Fintype ι]
def directionalLaplacian (v : ι → E) (f : E → F) : E → F :=
  fun x => ∑ i, directionalWord f [v i, v i] x
lemma directionalLaplacian_smooth {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (v : ι → E) :
    ContDiffOn ℝ (⊤ : ℕ∞) (directionalLaplacian v f) s := by
  exact ContDiffOn.sum (fun i _ => directionalWord_smooth hs hf [v i, v i])
lemma directionalLaplacian_congr {s : Set E} (hs : IsOpen s) {f g : E → F}
    (hfg : EqOn f g s) (v : ι → E) :
    EqOn (directionalLaplacian v f) (directionalLaplacian v g) s := by
  intro x hx
  apply Finset.sum_congr rfl
  intro i hi
  exact directionalWord_congr hs hfg [v i, v i] hx
lemma directionalWord_laplacian {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (v : ι → E) (l : List E) :
    EqOn (directionalWord (directionalLaplacian v f) l)
      (directionalLaplacian v (directionalWord f l)) s := by
  intro x hx
  have heq := directionalWord_sum hs Finset.univ
    (fun i => directionalWord f [v i, v i])
    (fun i _ => directionalWord_smooth hs hf [v i, v i]) l hx
  change directionalWord (directionalLaplacian v f) l x = _ at heq
  rw [heq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← directionalWord_append, ← directionalWord_append]
  exact directionalWord_perm hs hf List.perm_append_comm hx
lemma directional_time_laplacian {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (v : ι → E) (w : E)
    (hheat : EqOn (directionalWord f [w]) (directionalLaplacian v f) s)
    (l : List E) (j : ℕ) :
    EqOn (directionalWord f (List.replicate j w ++ l))
      ((directionalLaplacian v)^[j] (directionalWord f l)) s := by
  induction j with
  | zero => simp only [List.replicate_zero, List.nil_append, Function.iterate_zero, id_eq]; exact fun _ _ => rfl
  | succ j ih =>
    intro x hx
    have hperm : (List.replicate (j + 1) w ++ l).Perm
        ((List.replicate j w ++ l) ++ [w]) := by
      rw [List.replicate_succ, List.cons_append]
      simpa only [List.append_nil] using (List.perm_middle (a := w) (l₁ := List.replicate j w ++ l) (l₂ := [])).symm
    have heq := directionalWord_perm hs hf hperm hx
    rw [directionalWord_append f (List.replicate j w ++ l) [w]] at heq
    rw [heq, directionalWord_congr hs hheat (List.replicate j w ++ l) hx,
      directionalWord_laplacian hs hf v (List.replicate j w ++ l) hx,
      Function.iterate_succ_apply']
    exact directionalLaplacian_congr hs ih v hx

open P201
lemma directionalWord_spatial {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space n × ℝ → 𝕜}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {z | 0 < z.2})
    (l : List (Fin n)) {t : ℝ} (ht : 0 < t) (x : Space n) :
    directionalWord f (l.map (fun i => (coordinate n i, (0 : ℝ)))) (x, t) =
      P102.U4.partialWord (fun y => f (y, t)) l x := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    have hs : IsOpen {z : Space n × ℝ | 0 < z.2} := isOpen_lt continuous_const continuous_snd
    have hd := (((directionalWord_smooth hs hf (l.map (fun i => (coordinate n i, (0 : ℝ))))).contDiffAt (hs.mem_nhds ht)).differentiableAt
      (by simp)).hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))
    have heq : P102.U4.partialWord (fun y => f (y, t)) l =
        fun y => directionalWord f (l.map (fun i => (coordinate n i, (0 : ℝ)))) (y, t) :=
      funext (fun y => (ih y).symm)
    change fderiv ℝ (directionalWord f (l.map (fun i => (coordinate n i, (0 : ℝ))))) (x,t)
      (coordinate n i, 0) = _
    change _ = fderiv ℝ (P102.U4.partialWord (fun y => f (y, t)) l) x (coordinate n i)
    simp only [Function.comp_def, id_eq] at hd
    rw [heq, hd.fderiv]
    rfl
lemma directionalWord_time {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space n × ℝ → 𝕜}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {z | 0 < z.2})
    (j : ℕ) {t : ℝ} (ht : 0 < t) (x : Space n) :
    directionalWord f (List.replicate j (0, (1 : ℝ))) (x, t) =
      iteratedDeriv j (fun s => f (x, s)) t := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    have hs : IsOpen {z : Space n × ℝ | 0 < z.2} := isOpen_lt continuous_const continuous_snd
    have hd := (((directionalWord_smooth hs hf (List.replicate j (0, (1 : ℝ)))).contDiffAt
      (hs.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
    have heq : (fun s => iteratedDeriv j (fun s => f (x, s)) s) =ᶠ[𝓝 t]
        (fun s => directionalWord f (List.replicate j (0, (1 : ℝ))) (x, s)) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs using (ih hs).symm
    simp only [Function.comp_def, id_eq] at hd
    rw [iteratedDeriv_succ, heq.deriv_eq, hd.deriv]
    rfl

lemma directionalLaplacian_spatial {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space n × ℝ → 𝕜}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {z | 0 < z.2})
    {t : ℝ} (ht : 0 < t) (x : Space n) :
    directionalLaplacian (fun i : Fin n => (coordinate n i, (0 : ℝ))) f (x,t) =
      laplacian (fun y => f (y,t)) x := by
  apply Finset.sum_congr rfl
  intro i hi
  have heq := directionalWord_spatial hf [i,i] ht x
  change directionalWord f [(coordinate n i, 0), (coordinate n i, 0)] (x,t) =
    P102.U4.partialWord (fun y => f (y,t)) (({i,i} : MultiIndex n).sort (· ≤ ·)) x
  have hs : ({i, i} : MultiIndex n).sort (· ≤ ·) = [i, i] := by
    rw [Multiset.insert_eq_cons, Multiset.sort_cons (r := (· ≤ ·)) (a := i) (s := {i}) (by simp), Multiset.sort_singleton]
  rw [hs]
  exact heq
lemma directionalLaplacian_iterate_smooth {s : Set E} (hs : IsOpen s) {f : E → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) (v : ι → E) (j : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) ((directionalLaplacian v)^[j] f) s := by
  induction j with
  | zero => exact hf
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact directionalLaplacian_smooth hs ih v
lemma directionalLaplacian_iterate_spatial {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space n × ℝ → 𝕜}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {z | 0 < z.2})
    (j : ℕ) {t : ℝ} (ht : 0 < t) (x : Space n) :
    ((directionalLaplacian (fun i : Fin n => (coordinate n i, (0 : ℝ))))^[j] f) (x,t) =
      (laplacian^[j]) (fun y => f (y,t)) x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    have hs : IsOpen {z : Space n × ℝ | 0 < z.2} := isOpen_lt continuous_const continuous_snd
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      directionalLaplacian_spatial (directionalLaplacian_iterate_smooth hs hf _ j) ht]
    congr 2
    exact funext ih
lemma iteratedDeriv_partialWord_laplacian_of_heatEquation {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space n × ℝ → 𝕜}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {z | 0 < z.2})
    (hheat : ∀ (t : ℝ), 0 < t → ∀ x : Space n,
      deriv (fun s => f (x,s)) t = laplacian (fun y => f (y,t)) x)
    (l : List (Fin n)) (j : ℕ) {t : ℝ} (ht : 0 < t) (x : Space n) :
    iteratedDeriv j (fun s => P102.U4.partialWord (fun y => f (y,s)) l x) t =
      (laplacian^[j]) (P102.U4.partialWord (fun y => f (y,t)) l) x := by
  have hs : IsOpen {z : Space n × ℝ | 0 < z.2} := isOpen_lt continuous_const continuous_snd
  let v : Fin n → Space n × ℝ := fun i => (coordinate n i, (0 : ℝ))
  let w : Space n × ℝ := (0,1)
  let L := l.map v
  have hheat' : EqOn (directionalWord f [w]) (directionalLaplacian v f) {z | 0 < z.2} := by
    intro z hz
    have htime := directionalWord_time hf 1 hz z.1
    simp only [iteratedDeriv_one] at htime
    have hspace := directionalLaplacian_spatial hf hz z.1
    change directionalWord f [w] z = directionalLaplacian v f z
    simpa only [List.replicate_one, iteratedDeriv_one, v, w, Prod.mk.eta] using
      htime.trans ((hheat z.2 hz z.1).trans hspace.symm)
  have hmain := directional_time_laplacian hs hf v w hheat' L j (x := (x,t)) ht
  rw [directionalWord_append] at hmain
  have hL := directionalWord_smooth hs hf L
  rw [directionalWord_time hL j ht x,
    directionalLaplacian_iterate_spatial hL j ht x] at hmain
  have heq : (fun s => directionalWord f L (x,s)) =ᶠ[𝓝 t]
      (fun s => P102.U4.partialWord (fun y => f (y,s)) l x) := by
    filter_upwards [Ioi_mem_nhds ht] with s hst
    exact directionalWord_spatial hf l hst x
  have heq' : (fun y => directionalWord f L (y,t)) =
      P102.U4.partialWord (fun y => f (y,t)) l :=
    funext (fun y => directionalWord_spatial hf l ht y)
  rw [heq.iteratedDeriv_eq j, heq'] at hmain
  exact hmain
lemma heatTimeLaplacian_of_smooth_differentiation
    (hsmooth : P201Specs.Heat.heatSmoothRepresentativeStatement)
    (hdiff : P201Specs.Heat.heatDifferentiationUnderIntegralStatement) :
    P201Specs.Heat.heatTimeLaplacianStatement := by
  intro n hn 𝕜 _ p _ g α j t ht x
  have hf := (hsmooth n hn 𝕜 p g).2
  have hheat := heatEquation_of_differentiation hdiff n hn 𝕜 p g
  exact iteratedDeriv_partialWord_laplacian_of_heatEquation hf hheat
    (α.sort (· ≤ ·)) j ht x

/-- The full mixed derivative estimate, with all exponent endpoints. -/
theorem heatMixedEstimate : P201Specs.Heat.heatMixedEstimateStatement :=
  heatMixedEstimate_of_kernelBounds gaussianMixedBound heatDifferentiationUnderIntegral

/-- Every time derivative is the corresponding spatial Laplacian power. -/
theorem heatTimeLaplacian : P201Specs.Heat.heatTimeLaplacianStatement :=
  heatTimeLaplacian_of_smooth_differentiation heatSmoothRepresentative
    heatDifferentiationUnderIntegral

/-- Positive-time smoothness, mixed estimates, and all time/Laplacian identities
for the canonical Gaussian convolution. -/
theorem lpSmoothing : P201Specs.Heat.lpSmoothingStatement :=
  ⟨heatSmoothRepresentative, heatMixedEstimate, heatTimeLaplacian⟩

end P201.Heat
