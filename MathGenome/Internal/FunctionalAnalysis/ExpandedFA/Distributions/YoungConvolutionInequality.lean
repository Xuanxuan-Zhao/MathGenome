import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.YoungConvolutionInequality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.ConvolutionEndpointBounds
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Interpolation.RieszThorin

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
/-!
The endpoint estimates and Riesz–Thorin are independent accepted inputs. The
common-domain operator below is given by the actual convolution integral, with
absolute existence proved on that domain before invoking its linearity.
The last step applies the complex result to the moduli to cover either field.
-/
namespace ExpandedFA.Distributions
open ConvolutionEndpointBoundsSpec YoungConvolutionInequalitySpec
open Interpolation.RieszThorinSpec

private abbrev Space (d : ℕ) := Fin d → ℝ

/-- The a.e. absolute-existence domain of convolution by a fixed kernel. -/
def convolutionDomain {d : ℕ} (g : Space d → ℂ) :
    Submodule ℂ (Space d →ₘ[volume] ℂ) where
  carrier := {f | ∀ᵐ x ∂volume, Integrable (fun y => f y * g (x-y))}
  zero_mem' := by
    change ∀ᵐ x ∂volume, Integrable (fun y => (0 : Space d →ₘ[volume] ℂ) y * g (x-y))
    have he := (convolution_representative_independence
      (0 : Space d →ₘ[volume] ℂ) 0 g g AEEqFun.coeFn_zero ae_eq_rfl).1
    exact Eventually.of_forall fun x => (he x).mpr (by simp)
  add_mem' := by
    intro f h hf hh
    have he := (convolution_representative_independence
      (f+h) (fun y => f y + h y) g g (AEEqFun.coeFn_add f h) ae_eq_rfl).1
    change ∀ᵐ x ∂volume, Integrable (fun y => (f+h) y * g (x-y))
    filter_upwards [hf, hh] with x hx hx'
    apply (he x).mpr
    exact (MeasureTheory.Integrable.add hx hx').congr
      (Eventually.of_forall fun y => (add_mul (f y) (h y) (g (x-y))).symm)
  smul_mem' := by
    intro c f hf
    have he := (convolution_representative_independence
      (c • f) (fun y => c * f y) g g (AEEqFun.coeFn_smul c f) ae_eq_rfl).1
    change ∀ᵐ x ∂volume, Integrable (fun y => (c • f) y * g (x-y))
    filter_upwards [hf] with x hx
    apply (he x).mpr
    simpa only [mul_assoc] using hx.const_mul c

/-- A single linear map on the entire absolute-existence domain; this avoids
choosing separate, potentially incompatible endpoint extensions. -/
def convolutionDomainMap {d : ℕ} (g : Space d → ℂ)
    (hg : AEStronglyMeasurable g volume) :
    convolutionDomain g →ₗ[ℂ] (Space d →ₘ[volume] ℂ) where
  toFun f := AEEqFun.mk (ConvolutionValue (f : Space d →ₘ[volume] ℂ) g)
    ((f : Space d →ₘ[volume] ℂ).aestronglyMeasurable.convolution
      (ContinuousLinearMap.mul ℂ ℂ) hg)
  map_add' f h := by
    apply AEEqFun.ext
    have he := (convolution_representative_independence
      ((f+h : convolutionDomain g) : Space d →ₘ[volume] ℂ)
      (fun y => (f : Space d →ₘ[volume] ℂ) y + (h : Space d →ₘ[volume] ℂ) y)
      g g (AEEqFun.coeFn_add _ _) ae_eq_rfl).2
    refine (AEEqFun.coeFn_mk _ _).trans ?_
    refine EventuallyEq.trans ?_ (((AEEqFun.coeFn_mk _ _).add (AEEqFun.coeFn_mk _ _)).symm.trans (AEEqFun.coeFn_add _ _).symm)
    · filter_upwards [f.property, h.property] with x hx hx'
      rw [he]
      simpa only [Pi.add_apply, ConvolutionValue, add_mul] using integral_add hx hx'
  map_smul' c f := by
    apply AEEqFun.ext
    have he := (convolution_representative_independence
      ((c • f : convolutionDomain g) : Space d →ₘ[volume] ℂ)
      (fun y => c * (f : Space d →ₘ[volume] ℂ) y)
      g g (AEEqFun.coeFn_smul _ _) ae_eq_rfl).2
    refine (AEEqFun.coeFn_mk _ _).trans ?_
    refine EventuallyEq.trans ?_ (((AEEqFun.coeFn_mk _ _).const_smul c).symm.trans (AEEqFun.coeFn_smul _ _).symm)
    · exact Eventually.of_forall fun x => by
        rw [he]
        simp only [Pi.smul_apply, ConvolutionValue, mul_assoc, integral_const_mul, smul_eq_mul]

lemma convolution_sum_le_domain {d : ℕ} (q t : ℝ≥0∞) [t.HolderConjugate q]
    (g : Space d → ℂ) (hg : MemLp g q volume) :
    SumSpace volume 1 t ≤ convolutionDomain g := by
  apply sup_le
  · intro f hf
    exact (young_l1_lp_endpoint q (ENNReal.HolderConjugate.one_le q t) f g
      hf hg).1
  · intro f hf
    change ∀ᵐ x ∂volume, Integrable (fun y => f y * g (x-y))
    exact Eventually.of_forall
      (young_holder_endpoint t q f g hf hg).1

/-- The convolution operator used for both interpolation endpoints. -/
def convolutionSumMap {d : ℕ} (q t : ℝ≥0∞) [t.HolderConjugate q]
    (g : Space d → ℂ) (hg : MemLp g q volume) :
    SumSpace (volume : Measure (Space d)) 1 t →ₗ[ℂ] (Space d →ₘ[volume] ℂ) :=
  (convolutionDomainMap g hg.aestronglyMeasurable).comp
    (Submodule.inclusion (convolution_sum_le_domain q t g hg))

lemma convolutionSumMap_coe {d : ℕ} (q t : ℝ≥0∞) [t.HolderConjugate q]
    (g : Space d → ℂ) (hg : MemLp g q volume) (f : SumSpace (volume : Measure (Space d)) 1 t) :
    (convolutionSumMap q t g hg f : Space d → ℂ) =ᵐ[volume]
      ConvolutionValue (f : Space d →ₘ[volume] ℂ) g :=
  AEEqFun.coeFn_mk _ _

lemma convolutionSumMap_endpoints {d : ℕ} (q t : ℝ≥0∞) [t.HolderConjugate q]
    (g : Space d → ℂ) (hg : MemLp g q volume) :
    EndpointBound (convolutionSumMap q t g hg) 1 q (eLpNorm g q volume).toReal ∧
    EndpointBound (convolutionSumMap q t g hg) t ∞ (eLpNorm g q volume).toReal := by
  constructor
  · intro f hf
    obtain ⟨_, _, hm, hb⟩ := young_l1_lp_endpoint q
      (ENNReal.HolderConjugate.one_le q t) (f : Space d →ₘ[volume] ℂ) g hf hg
    have he := convolutionSumMap_coe q t g hg f
    refine ⟨hm.ae_eq he.symm, ?_⟩
    rw [eLpNorm_congr_ae he, ENNReal.ofReal_toReal hg.ne]
    simpa only [mul_comm] using hb
  · intro f hf
    obtain ⟨_, _, hm, _, hb⟩ := young_holder_endpoint t q
      (f : Space d →ₘ[volume] ℂ) g hf hg
    have he := convolutionSumMap_coe q t g hg f
    refine ⟨hm.ae_eq he.symm, ?_⟩
    rw [eLpNorm_congr_ae he, ENNReal.ofReal_toReal hg.ne]
    simpa only [mul_comm] using hb

lemma young_complex_interpolated {d : ℕ} (p q r t : ℝ≥0∞)
    [t.HolderConjugate q] (hp : 1 ≤ p) (hr : 1 ≤ r)
    (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hpi : Interpolates 1 t p θ) (hri : Interpolates q ∞ r θ)
    (f g : Space d → ℂ) (hf : MemLp f p volume) (hg : MemLp g q volume) :
    (∀ᵐ x ∂volume, Integrable (fun y => f y * g (x-y))) ∧
    MemLp (ConvolutionValue f g) r volume ∧
    eLpNorm (ConvolutionValue f g) r volume ≤ eLpNorm f p volume * eLpNorm g q volume := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : Fact (1 ≤ r) := ⟨hr⟩
  let : Fact (1 ≤ t) := ⟨ENNReal.HolderConjugate.one_le t q⟩
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q t⟩
  let M := (eLpNorm g q volume).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  obtain ⟨h₀, h₁⟩ := convolutionSumMap_endpoints q t g hg
  obtain ⟨hF, hmem, hb⟩ := Interpolation.riesz_thorin volume volume 1 t q ∞ p r
    θ M M hθ₀ hθ₁ hM hM hpi hri (convolutionSumMap q t g hg) h₀ h₁ (hf.toLp f)
  let F : SumSpace (volume : Measure (Space d)) 1 t := ⟨(hf.toLp f : Space d →ₘ[volume] ℂ), hF⟩
  have hff : (F : Space d →ₘ[volume] ℂ) =ᵐ[volume] f := hf.coeFn_toLp
  have hc := convolution_representative_independence
    (F : Space d →ₘ[volume] ℂ) f g g hff ae_eq_rfl
  have he := (convolutionSumMap_coe q t g hg F).trans (EventuallyEq.of_eq hc.2)
  have hiF : ∀ᵐ x ∂volume, Integrable (fun y => (F : Space d →ₘ[volume] ℂ) y * g (x-y)) :=
    (convolution_sum_le_domain q t g hg) hF
  have hi : ∀ᵐ x ∂volume, Integrable (fun y => f y * g (x-y)) :=
    hiF.mono (fun x hx => (hc.1 x).mp hx)
  have hm := hmem.ae_eq he
  refine ⟨hi, hm, ?_⟩
  have hpow : M ^ (1-θ) * M ^ θ = M := by
    by_cases hMz : M = 0
    · simp [hMz, Real.zero_rpow (sub_pos.mpr hθ₁).ne', Real.zero_rpow hθ₀.ne']
    · rw [← Real.rpow_add (lt_of_le_of_ne hM (Ne.symm hMz)), sub_add_cancel, Real.rpow_one]
  rw [hpow] at hb
  rw [← eLpNorm_congr_ae he]
  apply (ENNReal.toReal_le_toReal hmem.ne (ENNReal.mul_ne_top hf.ne hg.ne)).mp
  simpa only [ENNReal.toReal_mul, Lp.norm_toLp, mul_comm] using hb

/-- The interior Young relation lies on the segment between the two endpoint
bounds for convolution by g. Reciprocals use 1/∞ = 0. -/
lemma young_interpolation_parameters (p q r : ℝ≥0∞)
    (hp : 1 < p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hrt : r ≠ ∞)
    (hrel : 1 + r⁻¹ = p⁻¹ + q⁻¹) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      Interpolates 1 (ENNReal.conjExponent q) p θ ∧ Interpolates q ∞ r θ := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans hp)
  have hq0 : q ≠ 0 := ne_of_gt (zero_lt_one.trans_le hq)
  have hr0 : r ≠ 0 := ne_of_gt (zero_lt_one.trans_le hr)
  have hpn : p⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hp0
  have hqn : q⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hq0
  have hrn : r⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hr0
  have hpr : p⁻¹.toReal < 1 := by
    exact (ENNReal.toReal_lt_toReal hpn ENNReal.one_ne_top).mpr (by simpa using ENNReal.inv_lt_inv.mpr hp)
  have hrr : 0 < r⁻¹.toReal := ENNReal.toReal_pos (by simpa using hrt) hrn
  have hR : 1 + r⁻¹.toReal = p⁻¹.toReal + q⁻¹.toReal := by
    have H := congrArg ENNReal.toReal hrel
    simpa only [ENNReal.toReal_add ENNReal.one_ne_top hrn,
      ENNReal.toReal_add hpn hqn, ENNReal.toReal_one] using H
  have hqr : 0 < q⁻¹.toReal := by linarith [ENNReal.toReal_nonneg (a := p⁻¹)]
  let θ := 1 - r⁻¹.toReal / q⁻¹.toReal
  have hθ₀ : 0 < θ := by dsimp [θ]; exact sub_pos.mpr ((div_lt_one hqr).mpr (by linarith))
  have hθ₁ : θ < 1 := by dsimp [θ]; linarith [div_pos hrr hqr]
  have : q.HolderConjugate (ENNReal.conjExponent q) := .conjExponent hq
  have htn : (ENNReal.conjExponent q)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr
    (ENNReal.HolderConjugate.ne_zero (ENNReal.conjExponent q) q)
  have htR : (ENNReal.conjExponent q)⁻¹.toReal = 1 - q⁻¹.toReal := by
    have H := congrArg ENNReal.toReal
      (ENNReal.HolderConjugate.inv_add_inv_eq_one q (ENNReal.conjExponent q))
    rw [ENNReal.toReal_add hqn htn, ENNReal.toReal_one] at H
    linarith
  have hmul : (1-θ) * q⁻¹.toReal = r⁻¹.toReal := by
    dsimp [θ]
    field_simp
    ring
  refine ⟨θ, hθ₀, hθ₁, ?_, ?_⟩
  · unfold Interpolates
    apply (ENNReal.toReal_eq_toReal_iff' hpn ?_).mp
    · simp only [inv_one, mul_one]
      rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htn),
        ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hθ₁.le),
        ENNReal.toReal_ofReal hθ₀.le, htR]
      nlinarith
    · exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp),
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top htn⟩
  · unfold Interpolates
    simp only [ENNReal.inv_top, mul_zero, add_zero]
    apply (ENNReal.toReal_eq_toReal_iff' hrn
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hqn)).mp
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hθ₁.le)] using hmul.symm

lemma young_complex {d : ℕ} (p q r : ℝ≥0∞)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hrel : 1 + r⁻¹ = p⁻¹ + q⁻¹)
    (f g : Space d → ℂ) (hf : MemLp f p volume) (hg : MemLp g q volume) :
    (∀ᵐ x ∂volume, Integrable (fun y => f y * g (x-y))) ∧
    MemLp (ConvolutionValue f g) r volume ∧
    eLpNorm (ConvolutionValue f g) r volume ≤ eLpNorm f p volume * eLpNorm g q volume := by
  by_cases hrt : r = ∞
  · subst r
    have : p.HolderConjugate q := ENNReal.holderConjugate_iff.mpr (by simpa using hrel.symm)
    obtain ⟨hi, _, hm, _, hb⟩ := young_holder_endpoint p q f g hf hg
    exact ⟨Eventually.of_forall hi, hm, hb⟩
  by_cases hp1 : p = 1
  · subst p
    have hrq : r = q := by
      apply inv_injective
      exact (ENNReal.add_left_inj ENNReal.one_ne_top).mp (by simpa only [inv_one, add_comm] using hrel)
    subst r
    obtain ⟨hi, _, hm, hb⟩ := young_l1_lp_endpoint q hq f g hf hg
    exact ⟨hi, hm, hb⟩
  have hp' : 1 < p := lt_of_le_of_ne hp (Ne.symm hp1)
  obtain ⟨θ, hθ₀, hθ₁, hpi, hri⟩ := young_interpolation_parameters p q r hp' hq hr hrt hrel
  have : q.HolderConjugate (ENNReal.conjExponent q) := .conjExponent hq
  exact young_complex_interpolated p q r (ENNReal.conjExponent q) hp hr θ hθ₀ hθ₁ hpi hri f g hf hg

/-- Complexifying the modulus preserves every Lp norm and reduces both scalar
fields to the complex interpolation theorem without loss in the constant. -/
lemma eLpNorm_complex_norm {X : Type} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (f : X → 𝕜) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => (‖f x‖ : ℂ)) p μ = eLpNorm f p μ := by
  apply eLpNorm_congr_norm_ae (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.norm) hf
  exact Eventually.of_forall fun x => by simp

/-- Full Young inequality for arbitrary representatives and both scalar fields. -/
theorem young_convolution : Young := by
  intro d 𝕜 _ p q r hp hq hr hrel f g hf hg
  let F : Space d → ℂ := fun x => (‖f x‖ : ℂ)
  let G : Space d → ℂ := fun x => (‖g x‖ : ℂ)
  have hFn : eLpNorm F p volume = eLpNorm f p volume :=
    eLpNorm_complex_norm volume p f hf.aestronglyMeasurable
  have hGn : eLpNorm G q volume = eLpNorm g q volume :=
    eLpNorm_complex_norm volume q g hg.aestronglyMeasurable
  have hF : MemLp F p volume := by rw [memLp_iff, hFn]; exact hf
  have hG : MemLp G q volume := by rw [memLp_iff, hGn]; exact hg
  obtain ⟨hi, hm, hb⟩ := young_complex p q r hp hq hr hrel F G hF hG
  have hi' : ∀ᵐ x ∂volume, Integrable (fun y => f y * g (x-y)) := by
    filter_upwards [hi] with x hx
    have hn : Integrable (fun y => ‖f y * g (x-y)‖) := by
      have H := hx.norm
      simpa only [F, G, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_norm] using H
    apply (integrable_norm_iff ?_).mp hn
    exact hf.aestronglyMeasurable.mul
      (hg.aestronglyMeasurable.comp_measurePreserving (volume.measurePreserving_sub_left x))
  have hmeas : AEStronglyMeasurable (ConvolutionValue f g) volume :=
    hf.aestronglyMeasurable.convolution (ContinuousLinearMap.mul 𝕜 𝕜) hg.aestronglyMeasurable
  have hdom : ∀ᵐ x ∂volume, ‖ConvolutionValue f g x‖ ≤ ‖ConvolutionValue F G x‖ := by
    filter_upwards [hi'] with x hx
    have he : ConvolutionValue F G x = (∫ y, ‖f y * g (x-y)‖ : ℝ) := by
      simp only [ConvolutionValue, F, G, ← Complex.ofReal_mul, ← norm_mul,
        integral_complex_ofReal]
    rw [he, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg (fun y => norm_nonneg (f y * g (x-y))))]
    exact norm_integral_le_integral_norm _
  have hbound := (eLpNorm_mono_ae hmeas hdom).trans hb
  rw [hFn, hGn] at hbound
  exact ⟨hi', hmeas, hbound.trans_lt (ENNReal.mul_lt_top hf hg), hbound⟩

/-- On ordinary a.e. quotient spaces, convolution has the same norm bound and
is uniquely determined by its integral representative. -/
theorem lp_convolution_young_bound : YoungQuotientBound := by
  intro d 𝕜 _ p q r _ _ _ hrel f g
  obtain ⟨_, _, hc, hb⟩ := young_convolution p q r Fact.out Fact.out Fact.out hrel
    f g (Lp.memLp f) (Lp.memLp g)
  refine ⟨hc.toLp (ConvolutionValue f g), ⟨hc.coeFn_toLp, ?_⟩, ?_⟩
  · rw [Lp.norm_toLp, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.memLp f).ne (Lp.memLp g).ne) hb
  · intro h hh
    exact Lp.ext (hh.1.trans hc.coeFn_toLp.symm)

end ExpandedFA.Distributions
