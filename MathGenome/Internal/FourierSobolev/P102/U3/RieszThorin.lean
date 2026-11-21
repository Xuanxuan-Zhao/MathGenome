import MathGenome.Internal.FourierSobolev.Specs.P102.U3.RieszThorin
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
Riesz–Thorin for an operator defined only on finite-measure-support simple
functions. We reuse the finite power families, three-lines estimates, scalar
norm interpolation and norm-detection lemmas of the pinned MathGenome library.
The common-sum-domain operator from that library's full theorem is not assumed.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Topology
universe u v
namespace P102.U3
namespace RieszThorin
open RieszThorinSpec
open ExpandedFA.Interpolation

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

lemma endpoint_memLp {p q : ℝ≥0∞} {M : ℝ}
    {T : Initial μ →ₗ[ℂ] (Y →ₘ[ν] ℂ)} (hT : EndpointBound T p q M)
    (s : Initial μ) : MemLp (T s) q ν :=
  (hT s).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (finiteSimple_memLp μ s p).eLpNorm_lt_top)

lemma initial_output_memLp {p₀ p₁ q₀ q₁ q : ℝ≥0∞} {M₀ M₁ θ : ℝ}
    (T : Initial μ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀) (h₁ : EndpointBound T p₁ q₁ M₁)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hq : Interpolates q₀ q₁ q θ)
    (s : Initial μ) : MemLp (T s) q ν := by
  refine (lp_norm_interpolation ν q₀ q₁ q θ hθ₀ hθ₁ hq (T s)
      (T s).aestronglyMeasurable).trans_lt ?_
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hθ₁.le) (endpoint_memLp h₀ s).eLpNorm_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg hθ₀.le (endpoint_memLp h₁ s).eLpNorm_ne_top)

/-- The integral is bilinear already on the original simple-function domain. -/
def initialPairing {p q : ℝ≥0∞} [Fact (1 ≤ q)] {M : ℝ}
    (T : Initial μ →ₗ[ℂ] (Y →ₘ[ν] ℂ)) (hT : EndpointBound T p q M) :
    Initial μ →ₗ[ℂ] Initial ν →ₗ[ℂ] ℂ where
  toFun s :=
    { toFun h := ∫ y, T s y * h.val y ∂ν
      map_add' := by
        intro h k
        change (∫ y, T s y * (h.val + k.val) y ∂ν) = _
        simp only [SimpleFunc.coe_add, Pi.add_apply, mul_add]
        exact integral_add
          ((endpoint_memLp hT s).integrable_mul (finiteSimple_memLp ν h (ENNReal.conjExponent q)))
          ((endpoint_memLp hT s).integrable_mul (finiteSimple_memLp ν k (ENNReal.conjExponent q)))
      map_smul' := by
        intro c h
        change (∫ y, T s y * (c • h.val) y ∂ν) = c • _
        simp only [SimpleFunc.coe_smul, Pi.smul_apply, smul_eq_mul]
        simp_rw [mul_left_comm (T s _) c]
        exact integral_const_mul c _ }
  map_add' := by
    intro s t
    ext h
    change (∫ y, T (s + t) y * h.val y ∂ν) =
      (∫ y, T s y * h.val y ∂ν) + (∫ y, T t y * h.val y ∂ν)
    rw [map_add]
    calc
      _ = ∫ y, (T s y * h.val y + T t y * h.val y) ∂ν := by
        apply integral_congr_ae
        filter_upwards [AEEqFun.coeFn_add (T s) (T t)] with y hy
        simp [hy, add_mul]
      _ = _ := integral_add
        ((endpoint_memLp hT s).integrable_mul (finiteSimple_memLp ν h (ENNReal.conjExponent q)))
        ((endpoint_memLp hT t).integrable_mul (finiteSimple_memLp ν h (ENNReal.conjExponent q)))
  map_smul' := by
    intro c s
    ext h
    change (∫ y, T (c • s) y * h.val y ∂ν) = c • (∫ y, T s y * h.val y ∂ν)
    rw [map_smul]
    simp only [smul_eq_mul]
    rw [← integral_const_mul c]
    apply integral_congr_ae
    filter_upwards [AEEqFun.coeFn_smul c (T s)] with y hy
    simp [hy, mul_assoc]

lemma pairing_endpoint_le {p₀ q₀ p q r : ℝ≥0∞} [Fact (1 ≤ q₀)]
    [ENNReal.HolderConjugate q r] {M₀ M : ℝ}
    (T : Initial μ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀) (hT : EndpointBound T p q M) (hM : 0 ≤ M)
    (s : Initial μ) (h : Initial ν)
    (hs : eLpNorm s.val p μ ≤ 1) (hh : eLpNorm h.val r ν ≤ 1) :
    ‖initialPairing T h₀ s h‖ ≤ M := by
  have he : ‖initialPairing T h₀ s h‖ₑ ≤ ENNReal.ofReal M := by
    calc
      _ ≤ eLpNorm (T s) q ν * eLpNorm h.val r ν :=
        enorm_integral_mul_le_eLpNorm_mul_eLpNorm ν q r (T s) h.val
          (T s).aestronglyMeasurable h.val.aestronglyMeasurable
      _ ≤ (ENNReal.ofReal M * eLpNorm s.val p μ) * 1 := mul_le_mul' (hT s) hh
      _ ≤ _ := by simpa using mul_le_mul' (le_refl (ENNReal.ofReal M)) hs
  simpa only [toReal_enorm, ENNReal.toReal_ofReal hM] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top he

open SimpleInterpolation in
/-- Three lines applied to the two finite exponential families. Both remain
inside the original initial domain for every complex parameter. -/
lemma pairing_interpolation
    (p₀ p₁ q₀ q₁ p r₀ r₁ r : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₀)]
    [ENNReal.HolderConjugate q₀ r₀] [ENNReal.HolderConjugate q₁ r₁]
    (θ M₀ M₁ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hp : Interpolates p₀ p₁ p θ) (hr : Interpolates r₀ r₁ r θ)
    (hpz : p ≠ 0) (hpt : p ≠ ∞) (hrz : r ≠ 0) (hrt : r ≠ ∞)
    (T : Initial μ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀) (h₁ : EndpointBound T p₁ q₁ M₁)
    (s : Initial μ) (h : Initial ν)
    (hs : eLpNorm s.val p μ ≤ 1) (hh : eLpNorm h.val r ν ≤ 1) :
    ‖initialPairing T h₀ s h‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  classical
  have hp₀z : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hp₁z : p₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
  have hr₀z : r₀ ≠ 0 := ENNReal.HolderConjugate.ne_zero r₀ q₀
  have hr₁z : r₁ ≠ 0 := ENNReal.HolderConjugate.ne_zero r₁ q₁
  let fp := fun z => finitePowerFamily μ s
    (interpolationParam p.toReal (p₀⁻¹).toReal (p₁⁻¹).toReal z)
  let gp := fun z => finitePowerFamily ν h
    (interpolationParam r.toReal (r₀⁻¹).toReal (r₁⁻¹).toReal z)
  let B := initialPairing T h₀
  have hleft (t : ℝ) : ‖B (fp ((t : ℂ) * Complex.I)) (gp ((t : ℂ) * Complex.I))‖ ≤ M₀ := by
    apply pairing_endpoint_le (r := r₀) T h₀ h₀ hM₀
    · exact finitePowerFamily_left_le_one μ s p₀ p₁ p hpz hpt hp₀z hs t
    · exact finitePowerFamily_left_le_one ν h r₀ r₁ r hrz hrt hr₀z hh t
  have hright (t : ℝ) : ‖B (fp (1 + (t : ℂ) * Complex.I)) (gp (1 + (t : ℂ) * Complex.I))‖ ≤ M₁ := by
    apply pairing_endpoint_le (r := r₁) T h₀ h₁ hM₁
    · exact finitePowerFamily_right_le_one μ s p₀ p₁ p hpz hpt hp₁z hs t
    · exact finitePowerFamily_right_le_one ν h r₀ r₁ r hrz hrt hr₁z hh t
  have hbound : ‖B (fp (θ : ℂ)) (gp (θ : ℂ))‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
    simp only [fp, gp, finitePowerFamily_eq_sum] at hleft hright ⊢
    exact three_lines_bilinear_exponential_sum s.val.range h.val.range B
      (fun c => finitePowerAtom μ s c) (fun c => finitePowerAtom ν h c)
      (fun c => Real.log ‖c‖ * p.toReal * ((p₁⁻¹).toReal - (p₀⁻¹).toReal))
      (fun c => ((Real.log ‖c‖ * (p.toReal * (p₀⁻¹).toReal - 1) : ℝ) : ℂ))
      (fun c => Real.log ‖c‖ * r.toReal * ((r₁⁻¹).toReal - (r₀⁻¹).toReal))
      (fun c => ((Real.log ‖c‖ * (r.toReal * (r₀⁻¹).toReal - 1) : ℝ) : ℂ))
      M₀ M₁ θ hleft hright hθ₀ hθ₁
  simpa only [fp, gp, finitePowerFamily_center μ s p₀ p₁ p θ
      hθ₀.le hθ₁.le hp₀z hp₁z hpz hpt hp,
    finitePowerFamily_center ν h r₀ r₁ r θ
      hθ₀.le hθ₁.le hr₀z hr₁z hrz hrt hr] using hbound

/-- For q ≠ 1 the conjugate exponent is finite, so the ordinary finite-p
density of simple tests detects the full norm, including q = ∞. -/
lemma unit_bound_ne_one [SigmaFinite ν]
    (p₀ p₁ q₀ q₁ p q : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (θ M₀ M₁ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hp : Interpolates p₀ p₁ p θ) (hq : Interpolates q₀ q₁ q θ)
    (hpt : p ≠ ∞) (hq1 : q ≠ 1)
    (T : Initial μ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀) (h₁ : EndpointBound T p₁ q₁ M₁)
    (s : Initial μ) (hs : eLpNorm s.val p μ ≤ 1) :
    eLpNorm (T s) q ν ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) := by
  let r₀ := ENNReal.conjExponent q₀
  let r₁ := ENNReal.conjExponent q₁
  let r := ENNReal.conjExponent q
  have : Fact (1 ≤ r) := ⟨ENNReal.HolderConjugate.one_le r q⟩
  have hpz : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hrz : r ≠ 0 := ENNReal.HolderConjugate.ne_zero r q
  have hrt : r ≠ ∞ := (ENNReal.HolderConjugate.ne_top_iff_ne_one r q).mpr hq1
  have hr : Interpolates r₀ r₁ r θ :=
    interpolates_conjugates q₀ q₁ q r₀ r₁ r θ hθ₀.le hθ₁.le hq
  have hm := initial_output_memLp T h₀ h₁ hθ₀ hθ₁ hq s
  let g : Lp ℂ q ν := ⟨T s, Lp.mem_Lp_iff_memLp.mpr hm⟩
  have hgn : ‖g‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
    apply NormDetection.norm_le_of_simple_unit_tests ν r q hrt g _ (by positivity)
    intro h hh hhn
    have hc := pairing_interpolation p₀ p₁ q₀ q₁ p r₀ r₁ r θ M₀ M₁
      hθ₀ hθ₁ hM₀ hM₁ hp hr hpz hpt hrz hrt T h₀ h₁ s ⟨h, hh⟩ hs hhn
    change ‖∫ y, T s y * h y ∂ν‖ ≤ _ at hc
    simpa only [mul_comm] using hc
  apply (ENNReal.toReal_le_toReal hm.eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
  simpa only [g, Lp.norm_def, ENNReal.toReal_ofReal (by positivity :
    0 ≤ M₀ ^ (1 - θ) * M₁ ^ θ)] using hgn

/-- Regard the original outputs as Lq classes once their finiteness is proved. -/
def outputToLp (T : Initial μ →ₗ[ℂ] (Y →ₘ[ν] ℂ)) (q : ℝ≥0∞)
    (hT : ∀ s, MemLp (T s) q ν) : Initial μ →ₗ[ℂ] Lp ℂ q ν where
  toFun s := ⟨T s, Lp.mem_Lp_iff_memLp.mpr (hT s)⟩
  map_add' s t := Subtype.ext (T.map_add s t)
  map_smul' c s := Subtype.ext (T.map_smul c s)

open SimpleInterpolation in
/-- When q = 1, both output endpoints are L1. A fixed bounded test gives a
linear functional, so only the input exponential family is needed. -/
lemma unit_bound_one
    (p₀ p₁ p : ℝ≥0∞) [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ p)]
    (θ M₀ M₁ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hp : Interpolates p₀ p₁ p θ) (hpt : p ≠ ∞)
    (T : Initial μ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ 1 M₀) (h₁ : EndpointBound T p₁ 1 M₁)
    (s : Initial μ) (hs : eLpNorm s.val p μ ≤ 1) :
    eLpNorm (T s) 1 ν ≤ ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) := by
  classical
  have hpz : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp₀z : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hp₁z : p₁ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₁)).ne'
  let U := outputToLp T 1 (endpoint_memLp h₀)
  have hn : ‖U s‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
    apply NormDetection.norm_one_le_of_unit_tests ν (U s) _ (by positivity)
    intro h hh
    let L : Initial μ →ₗ[ℂ] ℂ :=
      (((D11.Ch20.IntegralPairing.pairing ν ∞ 1).flip h).toLinearMap).comp U
    have hL (t : Initial μ) : L t = ∫ y, h y * T t y ∂ν :=
      (D11.Ch20.IntegralPairing.pairing_eq_integral ν ∞ 1 (U t) h).2
    have hend (a : ℝ≥0∞) (M : ℝ) (hM : 0 ≤ M) (hT : EndpointBound T a 1 M)
        (t : Initial μ) (ht : eLpNorm t.val a μ ≤ 1) : ‖L t‖ ≤ M := by
      have hbound : eLpNorm (T t) 1 ν ≤ ENNReal.ofReal M :=
        (hT t).trans (by simpa only [mul_one] using mul_le_mul' le_rfl ht)
      have hUn : ‖U t‖ ≤ M := by
        change (eLpNorm (T t) 1 ν).toReal ≤ M
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
          (ENNReal.toReal_ofReal hM)
      have hc := D11.Ch20.IntegralPairing.norm_pairing_apply_le ν ∞ 1 (U t) h
      exact hc.trans ((mul_le_of_le_one_right (norm_nonneg _) hh).trans hUn)
    let fp := fun z => finitePowerFamily μ s
      (interpolationParam p.toReal (p₀⁻¹).toReal (p₁⁻¹).toReal z)
    have hleft (t : ℝ) : ‖L (fp ((t : ℂ) * Complex.I))‖ ≤ M₀ :=
      hend p₀ M₀ hM₀ h₀ _ (finitePowerFamily_left_le_one μ s p₀ p₁ p hpz hpt hp₀z hs t)
    have hright (t : ℝ) : ‖L (fp (1 + (t : ℂ) * Complex.I))‖ ≤ M₁ :=
      hend p₁ M₁ hM₁ h₁ _ (finitePowerFamily_right_le_one μ s p₀ p₁ p hpz hpt hp₁z hs t)
    have heq (z : ℂ) : L (fp z) =
        ∑ c ∈ s.val.range, L (finitePowerAtom μ s c) *
          Complex.exp (((Real.log ‖c‖ * p.toReal * ((p₁⁻¹).toReal - (p₀⁻¹).toReal) : ℝ) : ℂ) * z +
            ((Real.log ‖c‖ * (p.toReal * (p₀⁻¹).toReal - 1) : ℝ) : ℂ)) := by
      dsimp only [fp]
      rw [finitePowerFamily_eq_sum, map_sum]
      simp only [map_smul, smul_eq_mul, mul_comm]
    have hc : ‖L (fp (θ : ℂ))‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
      simp_rw [heq] at hleft hright ⊢
      exact three_lines_finite_exponential_sum s.val.range
        (fun c => L (finitePowerAtom μ s c))
        (fun c => ((Real.log ‖c‖ * (p.toReal * (p₀⁻¹).toReal - 1) : ℝ) : ℂ))
        (fun c => Real.log ‖c‖ * p.toReal * ((p₁⁻¹).toReal - (p₀⁻¹).toReal))
        M₀ M₁ θ hleft hright hθ₀ hθ₁
    have hcenter : fp (θ : ℂ) = s :=
      finitePowerFamily_center μ s p₀ p₁ p θ hθ₀.le hθ₁.le hp₀z hp₁z hpz hpt hp
    change ‖∫ y, h y * T s y ∂ν‖ ≤ _
    simpa only [hcenter, hL] using hc
  apply (ENNReal.toReal_le_toReal (endpoint_memLp h₀ s).eLpNorm_ne_top
    ENNReal.ofReal_ne_top).mp
  change (eLpNorm (T s) 1 ν).toReal ≤ _ at hn
  simpa only [ENNReal.toReal_ofReal (by positivity :
    0 ≤ M₀ ^ (1 - θ) * M₁ ^ θ)] using hn

/-- Homogeneity upgrades the unit-ball estimate. The zero seminorm case is
handled using the actual endpoint bound, which forces a zero output a.e. -/
lemma bound_of_unit_bound {p₀ q₀ p q : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ q₀)] [Fact (1 ≤ p)]
    {M₀ C : ℝ} (T : Initial μ →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T p₀ q₀ M₀)
    (hunit : ∀ s : Initial μ, eLpNorm s.val p μ ≤ 1 → eLpNorm (T s) q ν ≤ ENNReal.ofReal C)
    (s : Initial μ) : eLpNorm (T s) q ν ≤ ENNReal.ofReal C * eLpNorm s.val p μ := by
  have hpz : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hp₀z : p₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p₀)).ne'
  have hq₀z : q₀ ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ q₀)).ne'
  have hmem := finiteSimple_memLp μ s p
  by_cases hn : eLpNorm s.val p μ = 0
  · have hae : (s.val : X → ℂ) =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff hpz).mp hn
    have hzero : eLpNorm s.val p₀ μ = 0 := (eLpNorm_eq_zero_iff hp₀z).mpr hae
    have hzout : eLpNorm (T s) q₀ ν = 0 := by
      apply le_zero_iff.mp
      simpa only [hzero, mul_zero] using h₀ s
    have hout : (T s : Y → ℂ) =ᵐ[ν] 0 := (eLpNorm_eq_zero_iff hq₀z).mp hzout
    rw [eLpNorm_congr_ae hout, eLpNorm_zero]
    exact zero_le
  let a : ℂ := ((eLpNorm s.val p μ).toReal : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (ENNReal.toReal_ne_zero.mpr ⟨hn, hmem.eLpNorm_ne_top⟩)
  have han : ‖a‖ₑ = eLpNorm s.val p μ := by
    rw [← ofReal_norm]
    simp only [a, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
  let t : Initial μ := a⁻¹ • s
  have ht : eLpNorm t.val p μ ≤ 1 := by
    change eLpNorm (a⁻¹ • (s.val : X → ℂ)) p μ ≤ 1
    rw [eLpNorm_const_smul, enorm_inv ha, han,
      ENNReal.inv_mul_cancel hn hmem.eLpNorm_ne_top]
  have hvec : s = a • t := by simp [t, smul_smul, ha]
  have hb := hunit t ht
  rw [hvec, T.map_smul, eLpNorm_congr_ae (AEEqFun.coeFn_smul a _), eLpNorm_const_smul]
  calc
    _ ≤ ‖a‖ₑ * ENNReal.ofReal C := mul_le_mul' le_rfl hb
    _ = ENNReal.ofReal C * eLpNorm (a • t).val p μ := by
      rw [← hvec, han, mul_comm]

/-- Sharp Riesz–Thorin inequality on the manuscript's initial domain. -/
theorem simple_estimate : SimpleEstimate.{u,v} := by
  intro X Y _ _ μ ν _ _ p₀ p₁ q₀ q₁ p q _ _ _ _ _ _ θ M₀ M₁
    hθ₀ hθ₁ hM₀ hM₁ hp hq T h₀ h₁ s
  by_cases hpt : p = ∞
  · subst p
    obtain ⟨rfl, rfl⟩ := (interpolates_top_iff p₀ p₁ θ hθ₀ hθ₁).mp hp
    exact interpolate_output_bounds ν q₀ q₁ q θ M₀ M₁ hθ₀ hθ₁ hM₀ hM₁ hq
      (T s) (T s).aestronglyMeasurable (eLpNorm s.val ∞ μ) (h₀ s) (h₁ s)
  apply bound_of_unit_bound T h₀ _ s
  intro t ht
  by_cases hqone : q = 1
  · subst q
    obtain ⟨rfl, rfl⟩ := (interpolates_one_iff q₀ q₁ θ hθ₀ hθ₁).mp hq
    exact unit_bound_one p₀ p₁ p θ M₀ M₁ hθ₀ hθ₁ hM₀ hM₁ hp hpt T h₀ h₁ t ht
  · exact unit_bound_ne_one p₀ p₁ q₀ q₁ p q θ M₀ M₁ hθ₀ hθ₁ hM₀ hM₁
      hp hq hpt hqone T h₀ h₁ t ht

/-- The common operator on all L∞ satisfies the same sharp estimate. -/
theorem infinity_action : InfinityAction.{u,v} := by
  intro X Y _ _ μ ν _ _ q₀ q₁ q _ _ _ θ M₀ M₁ hθ₀ hθ₁ hM₀ hM₁ hq T h₀ h₁ f
  have hb := interpolate_output_bounds ν q₀ q₁ q θ M₀ M₁ hθ₀ hθ₁ hM₀ hM₁ hq
    (T f) (T f).aestronglyMeasurable (eLpNorm f ∞ μ) (h₀ f) (h₁ f)
  exact ⟨hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f)), hb⟩

/-- Precisely the finite-support initial functions are dense at finite p.
No assertion of density in L∞ is used. -/
lemma initialToLp_dense (p : ℝ≥0∞) [Fact (1 ≤ p)] (hpt : p ≠ ∞) :
    DenseRange (initialToLp μ p) := by
  have hpz : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hsub : (Lp.simpleFunc ℂ p μ : Set (Lp ℂ p μ)) ⊆ Set.range (initialToLp μ p) := by
    rintro f ⟨s, hs⟩
    have hae : (s : X → ℂ) =ᵐ[μ] (f : X → ℂ) := by
      rw [← hs]
      exact (AEEqFun.coeFn_mk _ _).symm
    have hsmem : MemLp s p μ := (Lp.memLp f).ae_eq hae.symm
    have hsfin : s.FinMeasSupp μ := (SimpleFunc.memLp_iff_finMeasSupp hpz hpt).mp hsmem
    exact ⟨⟨s, hsfin⟩, Subtype.ext hs⟩
  intro f
  exact closure_mono hsub ((Lp.simpleFunc.dense (E := ℂ) (μ := μ) hpt) f)

/-- The complete finite-input extension and uniqueness statement. -/
theorem finite_extension : FiniteExtension.{u,v} := by
  intro X Y _ _ μ ν _ _ p₀ p₁ q₀ q₁ p q _ _ _ _ _ _ θ M₀ M₁
    hθ₀ hθ₁ hM₀ hM₁ hp hq hpt T h₀ h₁
  let C := M₀ ^ (1 - θ) * M₁ ^ θ
  have hC : 0 ≤ C := by positivity
  have hsharp (s : Initial μ) :
      eLpNorm (T s) q ν ≤ ENNReal.ofReal C * eLpNorm s.val p μ :=
    simple_estimate μ ν p₀ p₁ q₀ q₁ p q θ M₀ M₁ hθ₀ hθ₁ hM₀ hM₁ hp hq T h₀ h₁ s
  have hmem (s : Initial μ) : MemLp (T s) q ν :=
    (hsharp s).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (finiteSimple_memLp μ s p).eLpNorm_lt_top)
  let U := outputToLp T q hmem
  let e := initialToLp μ p
  have hd : DenseRange e := initialToLp_dense p hpt
  have hb (s : Initial μ) : ‖U s‖ ≤ C * ‖e s‖ := by
    have hin : ‖e s‖ = (eLpNorm s.val p μ).toReal := by
      rw [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_ae (AEEqFun.coeFn_mk _ _)
    change (eLpNorm (T s) q ν).toReal ≤ C * ‖e s‖
    rw [hin]
    have ht := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (finiteSimple_memLp μ s p).eLpNorm_ne_top)
      (hsharp s)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using ht
  let S := U.extendOfNorm e
  refine ⟨S, LinearMap.opNorm_extendOfNorm_le hd hC hb, ?_, ?_⟩
  · intro s
    have he := LinearMap.extendOfNorm_eq hd ⟨C, hb⟩ s
    exact congrArg (fun f : Lp ℂ q ν => (f : Y →ₘ[ν] ℂ)) he
  · intro R hR
    have hcomp : R.toLinearMap.comp e = U := by
      apply LinearMap.ext
      intro s
      exact Subtype.ext (hR s)
    exact (LinearMap.extendOfNorm_unique hd C hb R hcomp).symm

end RieszThorin
end P102.U3
