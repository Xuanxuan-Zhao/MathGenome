import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardySupportBridge
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyExponentialFactor
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyHalfPlaneRepresentation
import Mathlib.Analysis.Convolution

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology Real ENNReal
namespace ExpandedFA.PartIV.HardySupportBridge
open HardyDiskSpec HardyHalfPlaneRepresentationSpec HardyCayleySpec
open HardyExponentialFactor HardyFactorization

lemma exponentialInner_add (a b : ℝ) (z : ℂ) :
    exponentialInner (a + b) z = exponentialInner a z * exponentialInner b z := by
  unfold exponentialInner
  rw [ofReal_add, mul_add, add_mul, Complex.exp_add]

lemma exponentialInner_zero (z : ℂ) : exponentialInner 0 z = 1 := by
  simp [exponentialInner]

lemma exponentialInner_cancel (a : ℝ) (z : ℂ) :
    exponentialInner (-a) z * exponentialInner a z = 1 := by
  rw [← exponentialInner_add, neg_add_cancel, exponentialInner_zero]

lemma isH2_congr {F G : ℂ → ℂ} (he : EqOn F G upperHalfPlane) :
    IsH2 F ↔ IsH2 G := by
  have hs (y : ℝ) (hy : 0 < y) : slice F y = slice G y := by
    funext x
    exact he (by simpa [upperHalfPlane] using hy)
  constructor <;> rintro ⟨hd, C, hC, hn⟩
  · refine ⟨hd.congr he.symm, C, hC, ?_⟩
    intro y hy
    simpa only [← hs y hy] using hn y hy
  · refine ⟨hd.congr he, C, hC, ?_⟩
    intro y hy
    simpa only [hs y hy] using hn y hy

lemma coefficient_congr {F G : ℂ → ℂ} {a : ℝ} (he : EqOn F G upperHalfPlane)
    (ha : HasCoefficient F a) : HasCoefficient G a := by
  obtain ⟨g, hg, μ, hμ, heq⟩ := ha
  refine ⟨g, ?_, μ, hμ, heq⟩
  intro w hw
  rw [hg hw]
  unfold transform
  rw [he (HardyCayley.cayley_mem hw)]

lemma atom_singular (b : ℝ) (_hb : 0 ≤ b) :
    SingularMeasure (ENNReal.ofReal b • Measure.dirac (1 : _root_.Circle)) := by
  refine ⟨(Measure.dirac (1 : _root_.Circle)).smul_finite ENNReal.ofReal_ne_top, ?_⟩
  apply Measure.MutuallySingular.smul
  have hmass : PositiveHarmonic.circleHaar {1} = 0 := by
    let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    have hi : Infinite (Ico (0 : ℝ) (0 + 2 * Real.pi)) :=
      infinite_coe_iff.mpr (Ico_infinite (by positivity))
    let : Infinite (AddCircle (2 * Real.pi)) := (AddCircle.equivIco (2 * Real.pi) 0).infinite_iff.mpr hi
    let : Infinite _root_.Circle :=
      (AddCircle.homeomorphCircle (by positivity : 2 * Real.pi ≠ 0)).toEquiv.infinite_iff.mp
        inferInstance
    let μ : Measure _root_.Circle := Measure.haarMeasure ⊤
    let : IsProbabilityMeasure μ := PositiveHarmonic.circleHaar_probability
    change μ {1} = 0
    by_contra hn
    exact measure_ne_top μ univ (infinite_univ.meas_eq_top
      ⟨μ {1}, hn, fun x _ => (Measure.haar_singleton μ x).ge⟩)
  exact ⟨{1}ᶜ, (measurableSet_singleton _).compl, by simp, by simpa using hmass⟩

lemma coefficient_nonzero {F : ℂ → ℂ} {a : ℝ} (ha : HasCoefficient F a) :
    ∃ z ∈ upperHalfPlane, F z ≠ 0 := by
  obtain ⟨g, hg, μ, hμg, heq⟩ := ha
  obtain ⟨i, o, c, hi, ho, hμ, hc, hprod, hm⟩ := hμg
  by_contra! hn
  apply HardyExponentialFactor.factor_nonzero hi ho hprod
  apply HardyDisk.evaluation_injective g 0
  intro w hw
  rw [hg hw]
  simp [transform, hn _ (HardyCayley.cayley_mem hw), HardyDiskSpec.eval]

lemma insert_exponential {F : ℂ → ℂ} {a : ℝ} (ha : HasCoefficient F a)
    (b : ℝ) (hb : 0 ≤ b) :
    IsH2 (fun z => exponentialInner b z * F z) ∧
      HasCoefficient (fun z => exponentialInner b z * F z) (b + a) := by
  obtain ⟨g, hg, μ, hμg, rfl⟩ := ha
  obtain ⟨i, o, c, hi, ho, hμ, hc, hprod, hm⟩ := hμg
  let δ : Measure _root_.Circle := ENNReal.ofReal b • Measure.dirac 1
  have hδ : SingularMeasure δ := atom_singular b hb
  let := hμ.1
  let := hδ.1
  obtain ⟨s, hs, hsn, hse⟩ := HardyFactorization.singular_converse δ hδ 1 (by simp)
  let k := Beurling.innerMul i hi s
  have hk : IsInner k := HardyExponentialFactor.inner_product hi hs
  have hke (w : ℂ) (hw : w ∈ disk) : eval k w = eval i w * eval s w :=
    Beurling.innerMul_evaluation i hi s w hw
  have hkcan (w : ℂ) : BlaschkeProducts.canonicalProduct k w =
      BlaschkeProducts.canonicalProduct i w := by
    apply HardyExponentialFactor.canonicalProduct_eq_of_orders _ w
    intro z hz
    rw [HardyExponentialFactor.orders_mul (BlaschkeProducts.inner_nonzero i hi)
      (BlaschkeProducts.inner_nonzero s hs) hke z hz]
    have he : analyticOrderNatAt (eval s) z = 0 := by
      unfold analyticOrderNatAt
      rw [analyticOrderAt_eq_zero.mpr (Or.inr (hsn z hz))]
      rfl
    rw [he, add_zero]
  let h := Beurling.innerMul k hk o
  have hhe (w : ℂ) (hw : w ∈ disk) : eval h w = eval k w * eval o w :=
    Beurling.innerMul_evaluation k hk o w hw
  have hmeasure : HasSingularMeasure h (μ + δ) := by
    refine ⟨k, o, c, hk, ho, ⟨inferInstance, hμ.2.add_left hδ.2⟩, hc, hhe, ?_⟩
    intro w hw
    rw [hke w hw, hm w hw, hse hw, hkcan w]
    rw [show c = c * 1 from (mul_one c).symm,
      HardyExponentialFactor.singularFactor_mul μ δ c 1 hw]
    simp only [mul_one]
    ring
  have hexp (w : ℂ) (hw : w ∈ disk) :
      eval h w = exponentialInner b (cayley w) * eval g w := by
    rw [hhe w hw, hke w hw, hse hw, hprod w hw,
      HardyExponentialFactor.atom_factor b hb w hw]
    ring
  have ht : EqOn (eval h) (transform (fun z => exponentialInner b z * F z)) disk := by
    intro w hw
    rw [hexp w hw, hg hw]
    unfold transform
    ring
  refine ⟨(HardyCayley.correspondence _).mpr ⟨h, ht, fun j hj =>
    HardyDisk.evaluation_injective j h (hj.trans ht.symm)⟩, h, ht, μ + δ, hmeasure, ?_⟩
  unfold atomMass
  simp only [measureReal_def, Measure.add_apply]
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top δ _)]
  simp [δ, ENNReal.toReal_ofReal hb, add_comm]

theorem exponential_threshold : Spec.ExponentialThreshold := by
  intro F hF a ha b hb
  constructor
  · intro hshift
    have hn : ∃ z ∈ upperHalfPlane, exponentialInner (-b) z * F z ≠ 0 := by
      obtain ⟨z, hz, hne⟩ := coefficient_nonzero ha
      exact ⟨z, hz, mul_ne_zero (Complex.exp_ne_zero _) hne⟩
    obtain ⟨d, hd, hcoeff⟩ := HardyExponentialFactor.coefficient_existence _ hshift hn
    have hinsert := (insert_exponential hcoeff b hb).2
    have he : EqOn (fun z => exponentialInner b z * (exponentialInner (-b) z * F z))
        F upperHalfPlane := by
      intro z hz
      dsimp only
      rw [← mul_assoc, mul_comm (exponentialInner b z), exponentialInner_cancel, one_mul]
    have huniq := HardyExponentialFactor.coefficient_uniqueness F (b + d) a
      (coefficient_congr he hinsert) ha
    linarith
  · intro hba
    obtain ⟨ha0, H, hH, hzero, he⟩ := HardyExponentialFactor.exponential_extraction F a ha
    have hinsert := (insert_exponential hzero (a - b) (sub_nonneg.mpr hba)).1
    apply (isH2_congr (G := fun z => exponentialInner (a - b) z * H z) ?_).mpr hinsert
    intro z hz
    dsimp only
    rw [he hz, ← mul_assoc, ← exponentialInner_add]
    congr 2
    ring

lemma supportedAbove_mono {f : ℝ → ℂ} {c d : ℝ} (hc : SupportedAbove f c)
    (hd : d ≤ c) : SupportedAbove f d :=
  hc.mono (fun _ ht h => ht (h.trans_le hd))

lemma supportedAbove_congr {f g : ℝ → ℂ} (he : f =ᵐ[volume] g) (c : ℝ) :
    SupportedAbove f c ↔ SupportedAbove g c := by
  constructor <;> intro h <;> filter_upwards [he, h] with t ht hz
  · simpa only [← ht] using hz
  · simpa only [ht] using hz

lemma translate_memLp {f : ℝ → ℂ} (hf : MemLp f 2 volume) (c : ℝ) :
    MemLp (translate f c) 2 volume :=
  hf.comp_measurePreserving (measurePreserving_add_right volume c)

lemma translate_supportedAbove (f : ℝ → ℂ) (b c : ℝ) :
    SupportedAbove (translate f b) c ↔ SupportedAbove f (b + c) := by
  constructor
  · intro h
    have hh := (measurePreserving_sub_right volume b).quasiMeasurePreserving.ae h
    filter_upwards [hh] with t ht hlt
    simpa [translate] using ht (by linarith)
  · intro h
    have hh := (measurePreserving_add_right volume b).quasiMeasurePreserving.ae h
    filter_upwards [hh] with t ht hlt
    exact ht (by linarith)

lemma laplace_eq_integral {f : ℝ → ℂ} (hf : SupportedAbove f 0) (z : ℂ) :
    laplace f z = ∫ t : ℝ, kernel z t * f t := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [hf, volume.ae_ne 0] with t ht hn hnot
  rw [ht (lt_of_le_of_ne (not_lt.mp hnot) hn), mul_zero]

/-- Translation to the right of a causal density, extended by zero. -/
def causalDelay (f : ℝ → ℂ) (c : ℝ) (t : ℝ) : ℂ :=
  (Ioi c).indicator (fun t => f (t - c)) t

lemma causalDelay_eq (f : ℝ → ℂ) (c t : ℝ) :
    causalDelay f c t = (Ioi 0).indicator f (t - c) := by
  simp only [causalDelay, indicator_apply, mem_Ioi, sub_pos]

lemma causalDelay_memLp {f : ℝ → ℂ} (hf : MemLp f 2 positiveMeasure) (c : ℝ) :
    MemLp (causalDelay f c) 2 volume := by
  have h := (HardyHalfPlaneRepresentation.extended_memLp f hf).comp_measurePreserving
    (measurePreserving_sub_right volume c)
  simpa only [Function.comp_def, ← causalDelay_eq] using h

lemma causalDelay_supportedAbove (f : ℝ → ℂ) (c : ℝ) :
    SupportedAbove (causalDelay f c) c := by
  apply Eventually.of_forall
  intro t ht
  exact indicator_of_notMem (not_lt.mpr ht.le) _

lemma kernel_add (z : ℂ) (t c : ℝ) :
    kernel z (t + c) = exponentialInner (2 * Real.pi * c) z * kernel z t := by
  unfold kernel exponentialInner
  rw [ofReal_add, ofReal_mul, ofReal_mul, ofReal_ofNat, mul_add]
  rw [show 2 * (Real.pi : ℂ) * I * z * (c : ℂ) =
    I * (2 * (Real.pi : ℂ) * (c : ℂ)) * z by ring, Complex.exp_add]
  ring

lemma laplace_causalDelay (f : ℝ → ℂ) {c : ℝ} (hc : 0 ≤ c) (z : ℂ) :
    laplace (causalDelay f c) z = exponentialInner (2 * Real.pi * c) z * laplace f z := by
  rw [laplace_eq_integral (supportedAbove_mono (causalDelay_supportedAbove f c) hc)]
  rw [← integral_add_right_eq_self (fun t : ℝ => kernel z t * causalDelay f c t) c]
  have he (t : ℝ) : kernel z (t + c) * causalDelay f c (t + c) =
      exponentialInner (2 * Real.pi * c) z * (Ioi 0).indicator (fun t => kernel z t * f t) t := by
    rw [causalDelay_eq, add_sub_cancel_right, kernel_add]
    by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [ht, mul_assoc]
  simp_rw [he]
  rw [integral_const_mul, integral_indicator measurableSet_Ioi]
  rfl

lemma causalDelay_translate {f : ℝ → ℂ} {c : ℝ} (hf : SupportedAbove f c) :
    causalDelay (translate f c) c =ᵐ[volume] f := by
  filter_upwards [hf, volume.ae_ne c] with t ht hn
  by_cases htc : c < t
  · simp [causalDelay, htc, translate]
  · rw [causalDelay, indicator_of_notMem (show t ∉ Ioi c from htc)]
    exact (ht (lt_of_le_of_ne (not_lt.mp htc) hn)).symm

lemma laplace_congr {f g : ℝ → ℂ} (he : f =ᵐ[positiveMeasure] g) (z : ℂ) :
    laplace f z = laplace g z := by
  apply integral_congr_ae
  exact he.mono (fun t ht => congrArg (kernel z t * ·) ht)

theorem support_criterion : Spec.SupportCriterion := by
  intro f hf hcausal c hc
  constructor
  · intro hsupport
    have ht : MemLp (translate f c) 2 positiveMeasure := (translate_memLp hf c).restrict _
    apply (isH2_congr (G := laplace (translate f c)) ?_).mpr
      (HardyHalfPlaneRepresentation.laplace_isH2 _ ht)
    intro z hz
    dsimp only
    rw [← laplace_congr (ae_restrict_of_ae (causalDelay_translate hsupport)) z,
      laplace_causalDelay _ hc z, ← mul_assoc, exponentialInner_cancel, one_mul]
  · intro hshift
    obtain ⟨g, hg, hge⟩ := HardyHalfPlaneRepresentation.representation_converse hshift
    have hdmem := causalDelay_memLp hg c
    have hrep : Represents (laplace f) (causalDelay g c) := by
      refine ⟨hdmem.restrict _, ?_⟩
      intro z hz
      rw [laplace_causalDelay g hc z, ← hge z hz]
      dsimp only
      rw [← mul_assoc, mul_comm (exponentialInner (2 * Real.pi * c) z),
        exponentialInner_cancel, one_mul]
    have he := HardyHalfPlaneRepresentation.representation_unique _ _ _
      ⟨hf.restrict _, fun _ _ => rfl⟩ hrep
    have he' := (ae_restrict_iff' measurableSet_Ioi).mp he
    have hd := causalDelay_supportedAbove g c
    filter_upwards [hcausal, he', hd, volume.ae_ne 0] with t ht heq hd0 hn htc
    by_cases hp : 0 < t
    · rw [heq hp]
      exact hd0 htc
    · exact ht (lt_of_le_of_ne (not_lt.mp hp) hn)

lemma zero_of_laplace_zero {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hc : SupportedAbove f 0) (hz : ∀ z ∈ upperHalfPlane, laplace f z = 0) :
    f =ᵐ[volume] 0 := by
  have hrep : Represents (laplace f) (0 : ℝ → ℂ) := by
    refine ⟨MemLp.zero, ?_⟩
    intro z hz0
    simpa [laplace] using hz z hz0
  have he := HardyHalfPlaneRepresentation.representation_unique _ _ _
    ⟨hf.restrict _, fun _ _ => rfl⟩ hrep
  have he' := (ae_restrict_iff' measurableSet_Ioi).mp he
  filter_upwards [he', hc, volume.ae_ne 0] with t ht hc0 hn
  by_cases hp : 0 < t
  · exact ht hp
  · exact hc0 (lt_of_le_of_ne (not_lt.mp hp) hn)

lemma laplace_nonzero {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hc : SupportedAbove f 0) (hn : ¬ (f =ᵐ[volume] 0)) :
    ∃ z ∈ upperHalfPlane, laplace f z ≠ 0 := by
  by_contra! hz
  exact hn (zero_of_laplace_zero hf hc hz)

lemma endpoint_of_coefficient {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hc : SupportedAbove f 0) {a : ℝ} (ha : HasCoefficient (laplace f) a) :
    IsLeftEndpoint f (a / (2 * Real.pi)) := by
  have ha0 : 0 ≤ a := (HardyExponentialFactor.exponential_extraction _ _ ha).1
  have hH := HardyHalfPlaneRepresentation.laplace_isH2 f (hf.restrict (Ioi 0))
  intro c
  by_cases hc0 : 0 ≤ c
  · rw [support_criterion f hf hc c hc0,
      exponential_threshold (laplace f) hH a ha (2 * Real.pi * c) (by positivity)]
    rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi), mul_comm c]
  · have hsc := supportedAbove_mono hc (le_of_not_ge hc0)
    have hle : c ≤ a / (2 * Real.pi) :=
      (le_of_not_ge hc0).trans (div_nonneg ha0 (by positivity))
    exact iff_of_true hsc hle

lemma translate_nonzero {f : ℝ → ℂ} (hn : ¬ (f =ᵐ[volume] 0)) (b : ℝ) :
    ¬ (translate f b =ᵐ[volume] 0) := by
  intro he
  apply hn
  have hh := (measurePreserving_sub_right volume b).quasiMeasurePreserving.ae he
  change ∀ᵐ t, f t = 0
  simpa [translate] using hh

theorem endpoint_coefficient : Spec.EndpointCoefficient := by
  intro f hf hn b hb
  have ht := translate_memLp hf b
  have htc : SupportedAbove (translate f b) 0 := by
    simpa only [add_zero] using (translate_supportedAbove f b 0).mpr (by simpa using hb)
  obtain ⟨a, ha0, ha⟩ := HardyExponentialFactor.coefficient_existence _
    (HardyHalfPlaneRepresentation.laplace_isH2 _ (ht.restrict _))
    (laplace_nonzero ht htc (translate_nonzero hn b))
  refine ⟨a, ha0, ha, ?_⟩
  have he := endpoint_of_coefficient ht htc ha
  intro c
  have h := he (c - b)
  rw [translate_supportedAbove, add_sub_cancel] at h
  exact h.trans (by constructor <;> intro hh <;> linarith)

lemma convolution_eq_native (f g : ℝ → ℂ) :
    convolution f g = MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume := rfl

lemma convolution_supportedAbove {f g : ℝ → ℂ} {a b : ℝ}
    (hf : SupportedAbove f a) (hg : SupportedAbove g b) :
    SupportedAbove (convolution f g) (a + b) := by
  apply Eventually.of_forall
  intro x hx
  apply integral_eq_zero_of_ae
  have hg' := (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hg
  filter_upwards [hf, hg'] with t hft hgt
  by_cases ht : t < a
  · simp [hft ht]
  · simp [hgt (by linarith : x - t < b)]

lemma convolution_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (convolution f g) := by
  rw [convolution_eq_native]
  exact hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg

/-- L¹ integrability and the L²–L² uniform bound suffice here for L² membership. -/
lemma convolution_memLp {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume) :
    MemLp (convolution f g) 2 volume := by
  let L := ContinuousLinearMap.mul ℂ ℂ
  let B : ℝ≥0∞ := ‖L‖ₑ * eLpNorm f 2 volume * eLpNorm g 2 volume
  have hB : B ≠ ∞ := by dsimp [B]; finiteness
  have hbound (x : ℝ) : ‖convolution f g x‖ ≤ B.toReal := by
    have hb := MeasureTheory.enorm_convolution_le (p := 2) (q := 2) L hf2.aestronglyMeasurable
      hg2.aestronglyMeasurable x
    change ‖convolution f g x‖ₑ ≤ B at hb
    simpa using ENNReal.toReal_mono hB hb
  have hi := convolution_integrable hf hg
  apply (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
  apply (hi.norm.mul_const B.toReal).mono'
    (hi.aestronglyMeasurable.norm.pow 2)
  apply Eventually.of_forall
  intro x
  change ‖‖convolution f g x‖ ^ 2‖ ≤ ‖convolution f g x‖ * B.toReal
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg (convolution f g x))]

lemma weighted_integrable {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hc : SupportedAbove f 0) {z : ℂ} (hz : z ∈ upperHalfPlane) :
    Integrable (fun t => kernel z t * f t) volume := by
  have hi := HardyHalfPlaneRepresentation.absolute_convergence f (hf.restrict _) z hz
  have he : (Ioi (0 : ℝ)).indicator (fun t => kernel z t * f t) =ᵐ[volume]
      (fun t => kernel z t * f t) := by
    filter_upwards [hc, volume.ae_ne 0] with t ht hn
    by_cases hp : 0 < t
    · simp [hp]
    · simp [hp, ht (lt_of_le_of_ne (not_lt.mp hp) hn)]
  exact ((integrable_indicator_iff measurableSet_Ioi).mpr hi).congr he

lemma kernel_convolution (f g : ℝ → ℂ) (z : ℂ) :
    convolution (fun t => kernel z t * f t) (fun t => kernel z t * g t) =
      (fun x => kernel z x * convolution f g x) := by
  funext x
  unfold convolution
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  have he : kernel z x = kernel z t * kernel z (x - t) := by
    have h := kernel_add z (x - t) t
    rw [sub_add_cancel] at h
    have hk : exponentialInner (2 * Real.pi * t) z = kernel z t := by
      simp only [exponentialInner, kernel, ofReal_mul, ofReal_ofNat]
      congr 1
      ring
    simpa [hk] using h
  rw [he]
  ring

lemma laplace_convolution {f g : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hfc : SupportedAbove f 0) (hgc : SupportedAbove g 0)
    {z : ℂ} (hz : z ∈ upperHalfPlane) :
    laplace (convolution f g) z = laplace f z * laplace g z := by
  rw [laplace_eq_integral (by simpa using convolution_supportedAbove hfc hgc),
    ← kernel_convolution]
  exact (MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (weighted_integrable hf hfc hz) (weighted_integrable hg hgc hz)).trans (by
      rw [← laplace_eq_integral hfc, ← laplace_eq_integral hgc]
      rfl)

lemma coefficient_product {F G : ℂ → ℂ} (hF : IsH2 F) (hG : IsH2 G)
    (hFG : IsH2 (fun z => F z * G z)) {a b : ℝ}
    (ha : HasCoefficient F a) (hb : HasCoefficient G b) :
    HasCoefficient (fun z => F z * G z) (a + b) := by
  obtain ⟨f₁, hf₁, μ, hμ, haeq⟩ := ha
  obtain ⟨f₂, hf₂, ν, hν, hbeq⟩ := hb
  obtain ⟨f, hf, _⟩ := (HardyCayley.correspondence _).mp hFG
  have he (w : ℂ) (hw : w ∈ disk) :
      eval f w = (1 - w) * eval f₁ w * eval f₂ w / normalization := by
    rw [hf hw, HardyExponentialFactor.disk_product F G w hw, ← hf₁ hw, ← hf₂ hw]
  have hm := HardyExponentialFactor.singular_measure_product hμ hν he
  have hc : HasCoefficient (fun z => F z * G z) (atomMass (μ + ν)) :=
    ⟨f, hf, μ + ν, hm, rfl⟩
  have heq := HardyExponentialFactor.coefficient_additivity F G hF hG hFG a b
    (atomMass (μ + ν)) ⟨f₁, hf₁, μ, hμ, haeq⟩ ⟨f₂, hf₂, ν, hν, hbeq⟩ hc
  rwa [heq] at hc

lemma density_nonzero_of_coefficient {f : ℝ → ℂ} {a : ℝ}
    (ha : HasCoefficient (laplace f) a) : ¬ (f =ᵐ[volume] 0) := by
  intro he
  obtain ⟨z, hz, hne⟩ := coefficient_nonzero ha
  have h := laplace_congr (ae_restrict_of_ae he) z
  exact hne (h.trans (by simp [laplace]))

lemma causal_convolution_endpoints {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume)
    (hfn : ¬ (f =ᵐ[volume] 0)) (hgn : ¬ (g =ᵐ[volume] 0))
    (hfc : SupportedAbove f 0) (hgc : SupportedAbove g 0) :
    ¬ (convolution f g =ᵐ[volume] 0) ∧
      ∃ a b : ℝ, IsLeftEndpoint f a ∧ IsLeftEndpoint g b ∧
        IsLeftEndpoint (convolution f g) (a + b) := by
  have hHf := HardyHalfPlaneRepresentation.laplace_isH2 f (hf2.restrict _)
  have hHg := HardyHalfPlaneRepresentation.laplace_isH2 g (hg2.restrict _)
  have hconv := convolution_memLp hf hg hf2 hg2
  have hconvc : SupportedAbove (convolution f g) 0 := by
    simpa using convolution_supportedAbove hfc hgc
  have hHconv := HardyHalfPlaneRepresentation.laplace_isH2 (convolution f g) (hconv.restrict _)
  have he : EqOn (laplace (convolution f g)) (fun z => laplace f z * laplace g z)
      upperHalfPlane := fun _ hz => laplace_convolution hf2 hg2 hfc hgc hz
  have hHprod := (isH2_congr he).mp hHconv
  obtain ⟨a, ha0, ha⟩ := HardyExponentialFactor.coefficient_existence _ hHf
    (laplace_nonzero hf2 hfc hfn)
  obtain ⟨b, hb0, hb⟩ := HardyExponentialFactor.coefficient_existence _ hHg
    (laplace_nonzero hg2 hgc hgn)
  have hab : HasCoefficient (laplace (convolution f g)) (a + b) :=
    coefficient_congr he.symm (coefficient_product hHf hHg hHprod ha hb)
  refine ⟨density_nonzero_of_coefficient hab, a / (2 * Real.pi), b / (2 * Real.pi),
    endpoint_of_coefficient hf2 hfc ha, endpoint_of_coefficient hg2 hgc hb, ?_⟩
  simpa only [add_div] using endpoint_of_coefficient hconv hconvc hab

lemma convolution_translate (f g : ℝ → ℂ) (a b : ℝ) :
    convolution (translate f a) (translate g b) = translate (convolution f g) (a + b) := by
  funext x
  change (∫ t : ℝ, f (t + a) * g (x - t + b)) =
    ∫ t : ℝ, f t * g (x + (a + b) - t)
  rw [← integral_add_right_eq_self (fun t : ℝ => f t * g (x + (a + b) - t)) a]
  congr 1
  funext t
  congr 2
  ring

lemma endpoint_translate {f : ℝ → ℂ} {b a : ℝ}
    (he : IsLeftEndpoint (translate f b) a) : IsLeftEndpoint f (b + a) := by
  intro c
  have h := he (c - b)
  rw [translate_supportedAbove, add_sub_cancel] at h
  exact h.trans (by constructor <;> intro hh <;> linarith)

theorem endpoint_from_coefficient : Spec.EndpointOfCoefficient := by
  intro f hf b hb a ha
  refine ⟨(HardyExponentialFactor.exponential_extraction _ _ ha).1, ?_⟩
  apply endpoint_translate
  apply endpoint_of_coefficient (translate_memLp hf b) _ ha
  rwa [translate_supportedAbove, add_zero]

theorem convolution_endpoints : Spec.ConvolutionEndpoints := by
  intro f g hf hg hf2 hg2 hfn hgn hfb hgb
  obtain ⟨a, hfa⟩ := hfb
  obtain ⟨b, hgb⟩ := hgb
  have hfc : SupportedAbove (translate f a) 0 := by
    rw [translate_supportedAbove, add_zero]
    exact hfa
  have hgc : SupportedAbove (translate g b) 0 := by
    rw [translate_supportedAbove, add_zero]
    exact hgb
  obtain ⟨hn, u, v, hu, hv, huv⟩ := causal_convolution_endpoints
    (hf.comp_add_right a) (hg.comp_add_right b)
    (translate_memLp hf2 a) (translate_memLp hg2 b)
    (translate_nonzero hfn a) (translate_nonzero hgn b) hfc hgc
  change ¬ (convolution (translate f a) (translate g b) =ᵐ[volume] 0) at hn
  change IsLeftEndpoint (convolution (translate f a) (translate g b)) (u + v) at huv
  rw [convolution_translate] at hn huv
  refine ⟨convolution_memLp hf hg hf2 hg2, ?_, a + u, b + v,
    endpoint_translate hu, endpoint_translate hv, ?_⟩
  · intro hz
    exact hn ((measurePreserving_add_right volume (a + b)).quasiMeasurePreserving.ae hz)
  · convert endpoint_translate huv using 1; ring

lemma endpoint_unique {f : ℝ → ℂ} {a b : ℝ}
    (ha : IsLeftEndpoint f a) (hb : IsLeftEndpoint f b) : a = b :=
  le_antisymm ((hb a).mp ((ha a).mpr le_rfl)) ((ha b).mp ((hb b).mpr le_rfl))

theorem endpoint_addition : Spec.EndpointAddition := by
  intro f g hf hg hf2 hg2 hfn hgn a b ha hb
  obtain ⟨hm, hn, u, v, hu, hv, huv⟩ := convolution_endpoints f g hf hg hf2 hg2 hfn hgn
    ⟨a, (ha a).mpr le_rfl⟩ ⟨b, (hb b).mpr le_rfl⟩
  rw [endpoint_unique hu ha, endpoint_unique hv hb] at huv
  exact ⟨hm, hn, huv⟩

end ExpandedFA.PartIV.HardySupportBridge
