import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.AbelAmplitude
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.AbelInversion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.FirstKindSmooth

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.PartV.AbelAmplitude
open FractionalIntegrals.Spec

@[simp] theorem amplitude_zero (α : ℝ) {𝕜 : Type} [RCLike 𝕜]
    (k : ℝ × ℝ → 𝕜) (u : ℝ → 𝕜) : amplitudeValue α k u 0 = 0 := by
  simp [amplitudeValue]

/-- The degenerate interval leaves the unknown's value unrestricted. -/
theorem singleton_classification : Spec.SingletonClassification := by
  intro 𝕜 _ α k g
  have heq (u : C(Icc (0 : ℝ) 0, 𝕜)) :
      AmplitudeEquation (le_refl 0) α k g u ↔ g ⟨0, by simp⟩ = 0 := by
    constructor
    · intro hu
      have h := hu ⟨0, by simp⟩
      simpa using h.symm
    · intro hg t
      have ht : t = ⟨0, by simp⟩ := Subtype.ext (le_antisymm t.property.2 t.property.1)
      subst t
      simpa using hg.symm
  refine ⟨heq, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨u, hu⟩
    exact (heq u).mp hu
  · intro hg
    exact ⟨0, (heq 0).mpr hg⟩
  · intro hg hu
    obtain ⟨u, _, huniq⟩ := hu
    have h0 := huniq (ContinuousMap.const _ 0) ((heq _).mpr hg)
    have h1 := huniq (ContinuousMap.const _ 1) ((heq _).mpr hg)
    exact zero_ne_one (congrArg (fun f : C(Icc (0 : ℝ) 0, 𝕜) => f ⟨0, by simp⟩)
      (h0.trans h1.symm))


/-- Both endpoint singularities of the Beta weight are integrable. -/
lemma betaWeight_integrable {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    IntegrableOn (betaWeight α) (Ioc (0 : ℝ) 1) := by
  have hi := (BetaSemigroup.beta_scaled_integrable (sub_pos.mpr hα1) hα
    (show (0 : ℝ) < 1 by norm_num)).1
  convert hi using 1
  ext r
  dsimp [betaWeight]
  rw [show 1-α-1 = -α by ring, mul_comm]

lemma betaWeight_mass {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    (∫ r in Ioc (0 : ℝ) 1, betaWeight α r) =
      Real.Gamma (1-α) * Real.Gamma α := by
  have hb := BetaSemigroup.beta_scaled (sub_pos.mpr hα1) hα
    (show (0 : ℝ) < 1 by norm_num)
  have he : (fun r : ℝ => betaWeight α r) =
      (fun r : ℝ => r ^ (α-1) * (1-r) ^ ((1-α)-1)) := by
    ext r
    dsimp [betaWeight]
    rw [show 1-α-1 = -α by ring, mul_comm]
  rw [he, hb]
  simp [show (1-α)+α = 1 by ring]

lemma weighted_integrable {𝕜 : Type} [RCLike 𝕜] {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (f : C(Icc (0 : ℝ) 1, 𝕜)) :
    IntegrableOn (fun r => betaWeight α r •
      continuousExtension (by norm_num : (0 : ℝ) ≤ 1) f r) (Ioc (0 : ℝ) 1) := by
  exact (betaWeight_integrable hα hα1).smul_bdd ‖f‖
    (f.continuous.comp continuous_projIcc).aestronglyMeasurable
    (Eventually.of_forall (fun r => f.norm_coe_le_norm _))

/-- Integration against the fixed Beta weight is a bounded real-linear map.
This permits differentiation of the compact family in the uniform norm. -/
def betaIntegralCLM {𝕜 : Type} [RCLike 𝕜] {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) : C(Icc (0 : ℝ) 1, 𝕜) →L[ℝ] 𝕜 :=
  LinearMap.mkContinuous
    ({ toFun := fun f => ∫ r in Ioc (0 : ℝ) 1, betaWeight α r •
          continuousExtension (by norm_num) f r
       map_add' := fun f g => by
         change (∫ r in Ioc (0 : ℝ) 1, betaWeight α r •
           (continuousExtension (by norm_num) f r + continuousExtension (by norm_num) g r)) = _
         simp_rw [smul_add]
         exact integral_add (weighted_integrable hα hα1 f) (weighted_integrable hα hα1 g)
       map_smul' := fun c f => by
         change (∫ r in Ioc (0 : ℝ) 1, betaWeight α r •
           (c • continuousExtension (by norm_num) f r)) = c • _
         simp_rw [smul_comm (betaWeight α _) c]
         exact integral_smul c _ } : C(Icc (0 : ℝ) 1, 𝕜) →ₗ[ℝ] 𝕜)
    (∫ r in Ioc (0 : ℝ) 1, ‖betaWeight α r‖) (fun f => by
      change ‖∫ r in Ioc (0 : ℝ) 1, betaWeight α r •
        continuousExtension (by norm_num) f r‖ ≤ _
      rw [← integral_mul_const]
      apply norm_integral_le_of_norm_le ((betaWeight_integrable hα hα1).norm.mul_const ‖f‖)
      exact Eventually.of_forall (fun r => (norm_smul _ _).le.trans
        (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _))))

/-- Rescaling the inner variable keeps its second argument fixed. -/
def betaAffine (p : ℝ × ℝ) (r : ℝ) : ℝ × ℝ :=
  (p.2+(p.1-p.2)*r, p.2)

lemma contDiff_betaAffine (m : ℕ) :
    ContDiff ℝ m (fun z : (ℝ × ℝ) × ℝ => betaAffine z.1 z.2) := by
  exact ((contDiff_snd.comp contDiff_fst).add
    (((contDiff_fst.comp contDiff_fst).sub (contDiff_snd.comp contDiff_fst)).mul
      contDiff_snd)).prodMk (contDiff_snd.comp contDiff_fst)

def betaParameterDomain (U : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {p | ∀ r : Icc (0 : ℝ) 1, betaAffine p r ∈ U}

lemma isOpen_betaParameterDomain {U : Set (ℝ × ℝ)} (hU : IsOpen U) :
    IsOpen (betaParameterDomain U) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hc : Continuous (fun z : (ℝ × ℝ) × Icc (0 : ℝ) 1 => betaAffine z.1 z.2) :=
    (contDiff_betaAffine 0).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have h := (isCompact_univ : IsCompact (univ : Set (Icc (0 : ℝ) 1))).eventually_forall_of_forall_eventually
    (x₀ := p) (P := fun q r => betaAffine q r ∈ U)
    (fun r _ => hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (hp r)))
  exact h.mono (fun q hq r => hq r (mem_univ r))

lemma triangle_subset_betaParameterDomain {T : ℝ} {U : Set (ℝ × ℝ)}
    (hsub : volterraTriangle 0 T ⊆ U) : volterraTriangle 0 T ⊆ betaParameterDomain U := by
  intro p hp r
  apply hsub
  dsimp [betaAffine, volterraTriangle] at *
  refine ⟨hp.1, ?_, ?_⟩
  · nlinarith [r.property.1, hp.2.1]
  · nlinarith [r.property.2, hp.2.1, hp.2.2]

/-- Arbitrary fallback values outside the open parameter domain have no effect
on smoothness or on the original triangle. -/
def betaKernelFamily {𝕜 : Type} [RCLike 𝕜] (k : ℝ × ℝ → 𝕜)
    (p : ℝ × ℝ) : C(Icc (0 : ℝ) 1, 𝕜) :=
  ContinuousMap.mkD (fun r => k (betaAffine p r)) 0

lemma betaKernelFamily_contDiffOn {𝕜 : Type} [RCLike 𝕜] {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (k : ℝ × ℝ → 𝕜) (hk : ContDiffOn ℝ 1 k U) :
    ContDiffOn ℝ 1 (betaKernelFamily k) (betaParameterDomain U) := by
  let A := fun z : (ℝ × ℝ) × ℝ => betaAffine z.1 z.2
  have hA := contDiff_betaAffine 1
  have hg : ContDiffOn ℝ 1 (fun z => k (A z)) (A ⁻¹' U) :=
    hk.comp hA.contDiffOn (fun _ hz => hz)
  apply CompactParameter.contDiffOn_of_ambient 1 continuous_subtype_val
    (isOpen_betaParameterDomain hU) (hU.preimage hA.continuous)
    (fun p hp r => hp r) hg
  intro p hp r
  apply ContinuousMap.mkD_apply_of_continuous
  exact hk.continuousOn.comp_continuous
    ((contDiff_betaAffine 0).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)) hp

lemma betaIntegralCLM_family {𝕜 : Type} [RCLike 𝕜] {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {U : Set (ℝ × ℝ)}
    (k : ℝ × ℝ → 𝕜) (hk : ContinuousOn k U) {p : ℝ × ℝ}
    (hp : p ∈ betaParameterDomain U) :
    (Real.Gamma (1-α))⁻¹ • betaIntegralCLM (𝕜 := 𝕜) hα hα1 (betaKernelFamily k p) =
      transformedKernel α k p := by
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  have hc : Continuous (fun r : Icc (0 : ℝ) 1 => k (betaAffine p r)) :=
    hk.comp_continuous ((contDiff_betaAffine 0).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)) hp
  simp only [continuousExtension, projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) ⟨hr.1.le, hr.2⟩]
  rw [betaKernelFamily, ContinuousMap.mkD_apply_of_continuous hc]
  rfl

/-- The source's full transformed kernel has a C¹ extension to an open
neighborhood, and its diagonal is exactly Γ(α) times the original diagonal. -/
theorem kernel_regularity : Spec.KernelRegularity := by
  intro 𝕜 _ α T hα hα1 hT U hU hsub k hk
  constructor
  · refine ⟨betaParameterDomain U, isOpen_betaParameterDomain hU,
      triangle_subset_betaParameterDomain hsub, ?_⟩
    have h := (betaIntegralCLM (𝕜 := 𝕜) hα hα1).contDiff.comp_contDiffOn
      (betaKernelFamily_contDiffOn hU k hk)
    apply ((contDiffOn_const : ContDiffOn ℝ 1 (fun _ : ℝ × ℝ => (Real.Gamma (1-α))⁻¹) (betaParameterDomain U)).smul h).congr
    intro p hp
    exact (betaIntegralCLM_family hα hα1 k hk.continuousOn hp).symm
  · intro t
    simp only [transformedKernel, sub_self, zero_mul, add_zero]
    rw [integral_smul_const, betaWeight_mass hα hα1, smul_smul,
      ← mul_assoc, inv_mul_cancel₀ (Real.Gamma_pos_of_pos (sub_pos.mpr hα1)).ne', one_mul]


/-- A bounded continuous amplitude has an absolutely convergent power integral. -/
lemma amplitude_integrable_bounded {𝕜 : Type} [RCLike 𝕜] {α : ℝ}
    (hα : 0 < α) {k : ℝ × ℝ → 𝕜} (hk : Continuous k)
    {u : ℝ → 𝕜} (hu : Continuous u) {M N : ℝ}
    (hkB : ∀ p, ‖k p‖ ≤ M) (huB : ∀ s, ‖u s‖ ≤ N) (t : ℝ) :
    IntegrableOn (fun s => (t-s) ^ (α-1) • (k (t,s) * u s)) (Ioc 0 t) := by
  apply (FractionalIntegrals.reflected_power_integrable hα).smul_bdd (M*N)
    ((hk.comp (continuous_const.prodMk continuous_id)).mul hu).aestronglyMeasurable
  exact Eventually.of_forall (fun s => by
    change ‖k (t,s) * u s‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hkB _) (huB _) (norm_nonneg _) ((norm_nonneg (k (t,s))).trans (hkB _)))

/-- Reflection leaves a fixed integrable singularity and a moving cutoff. -/
lemma amplitude_reflect {𝕜 : Type} [RCLike 𝕜] (α : ℝ)
    (k : ℝ × ℝ → 𝕜) (u : ℝ → 𝕜) {t : ℝ} (ht : 0 ≤ t) :
    amplitudeValue α k u t =
      ∫ r in Ioc 0 t, r ^ (α-1) • (k (t,t-r) * u (t-r)) := by
  exact FractionalIntegrals.powerValue_reflect α (fun s => k (t,s) * u s) ht

/-- Dominated convergence gives continuity, including the initial endpoint. -/
lemma continuous_amplitude_bounded {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) {k : ℝ × ℝ → 𝕜} (hk : Continuous k)
    {u : ℝ → 𝕜} (hu : Continuous u) {M N : ℝ}
    (hkB : ∀ p, ‖k p‖ ≤ M) (huB : ∀ s, ‖u s‖ ≤ N) :
    ContinuousOn (amplitudeValue α k u) (Icc (0 : ℝ) T) := by
  let F : ℝ → ℝ → 𝕜 := fun t r =>
    r ^ (α-1) • (if r ≤ t then k (t,t-r) * u (t-r) else 0)
  have hm (t : ℝ) : AEStronglyMeasurable (F t) (volume.restrict (Ioc 0 T)) := by
    exact (FractionalIntegrals.power_integrable (T := T) hα).aestronglyMeasurable.smul
      (Measurable.ite (measurableSet_le measurable_id measurable_const)
        (((hk.comp (continuous_const.prodMk (continuous_const.sub continuous_id))).mul
          (hu.comp (continuous_const.sub continuous_id))).measurable)
        measurable_const).aestronglyMeasurable
  have hb (t : ℝ) : ∀ᵐ r ∂volume.restrict (Ioc 0 T),
      ‖F t r‖ ≤ r ^ (α-1) * (M*N) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    dsimp [F]
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hr.1.le _)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hr.1.le _)
    split_ifs
    · rw [norm_mul]
      exact mul_le_mul (hkB _) (huB _) (norm_nonneg _)
        ((norm_nonneg (k (t,t-r))).trans (hkB _))
    · simpa using mul_nonneg ((norm_nonneg (k (0,0))).trans (hkB _))
        ((norm_nonneg (u 0)).trans (huB _))
  have hc : Continuous (fun t => ∫ r in Ioc 0 T, F t r) := by
    apply continuous_iff_continuousAt.mpr
    intro t₀
    apply continuousAt_of_dominated (Eventually.of_forall hm)
      (Eventually.of_forall hb) ((FractionalIntegrals.power_integrable hα).mul_const (M*N))
    filter_upwards [ae_restrict_of_ae (volume.ae_ne t₀)] with r hr
    have hec : ContinuousAt
        (fun t => r ^ (α-1) • (k (t,t-r) * u (t-r))) t₀ :=
      continuousAt_const.smul ((hk.continuousAt.comp
        (continuousAt_id.prodMk (continuousAt_id.sub continuousAt_const))).mul
          (hu.continuousAt.comp (continuousAt_id.sub continuousAt_const)))
    rcases lt_or_gt_of_ne hr with hrt | htr
    · apply hec.congr
      filter_upwards [eventually_gt_nhds hrt] with t ht
      simp [F, ht.le]
    · apply (continuousAt_const (y := (0 : 𝕜))).congr
      filter_upwards [eventually_lt_nhds htr] with t ht
      simp [F, not_le.mpr ht]
  apply hc.continuousOn.congr
  intro t ht
  rw [amplitude_reflect α k u ht.1]
  have he : F t = (Iic t).indicator
      (fun r : ℝ => r ^ (α-1) • (k (t,t-r) * u (t-r))) := by
    ext r
    simp only [F, indicator_apply, mem_Iic]
    split_ifs <;> simp_all
  change _ = ∫ r in Ioc 0 T, F t r
  rw [he, setIntegral_indicator measurableSet_Iic]
  have hi : Ioc (0 : ℝ) T ∩ Iic t = Ioc 0 t := by
    ext r
    simp only [mem_inter_iff, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨⟨hr, _⟩, hrt⟩; exact ⟨hr, hrt⟩
    · rintro ⟨hr, hrt⟩; exact ⟨⟨hr, hrt.trans ht.2⟩, hrt⟩
  rw [hi]


/-- Clamping to the closed triangle supplies a globally continuous bounded
representative without imposing any regularity beyond the original triangle. -/
lemma amplitude_continuous_integrable {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (k : ℝ × ℝ → 𝕜)
    (hk : ContinuousOn k (volterraTriangle 0 T))
    (u : C(Icc (0 : ℝ) T, 𝕜)) :
    ContinuousOn (amplitudeValue α k (continuousExtension hT u)) (Icc 0 T) ∧
    ∀ t ∈ Icc (0 : ℝ) T, IntegrableOn (fun s => (t-s) ^ (α-1) •
      (k (t,s) * continuousExtension hT u s)) (Ioc 0 t) := by
  let K : C(volterraTriangle 0 T, 𝕜) := ⟨fun p => k p, hk.domRestrict⟩
  let k' : ℝ × ℝ → 𝕜 := fun p => K (volterraTriangleClamp hT p)
  have hkc : Continuous k' := K.continuous.comp (continuous_volterraTriangleClamp hT)
  have hkB : ∀ p, ‖k' p‖ ≤ ‖K‖ := fun p => K.norm_coe_le_norm _
  have he (p : ℝ × ℝ) (hp : p ∈ volterraTriangle 0 T) : k' p = k p := by
    change K (volterraTriangleClamp hT (⟨p,hp⟩ : volterraTriangle 0 T)) = _
    rw [volterraTriangleClamp_coe]
    rfl
  have hae (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      (fun s => (t-s) ^ (α-1) • (k' (t,s) * continuousExtension hT u s))
        =ᵐ[volume.restrict (Ioc 0 t)]
      (fun s => (t-s) ^ (α-1) • (k (t,s) * continuousExtension hT u s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [he (t,s) ⟨hs.1.le, hs.2, ht.2⟩]
  constructor
  · apply (continuous_amplitude_bounded hα hkc (FractionalIntegrals.continuous_extension hT u)
      hkB (FractionalIntegrals.extension_norm_le hT u)).congr
    intro t ht
    exact (integral_congr_ae (hae t ht)).symm
  · intro t ht
    exact (amplitude_integrable_bounded hα hkc (FractionalIntegrals.continuous_extension hT u)
      hkB (FractionalIntegrals.extension_norm_le hT u) t).congr (hae t ht)

/-- The upper section of the integration triangle, with endpoints treated
by the nonatomic Lebesgue measure. -/
lemma triangle_upper_section {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {s t : ℝ} (hs : 0 ≤ s) :
    (IntegrableOn (fun v => if s < v then f v else 0) (Ioc 0 t) ↔
      IntegrableOn f (Ioc s t)) ∧
    ((∫ v in Ioc 0 t, if s < v then f v else 0) = ∫ v in Ioc s t, f v) := by
  have he : (fun v => if s < v then f v else 0) = (Ioi s).indicator f := rfl
  have hi : Ioc (0 : ℝ) t ∩ Ioi s = Ioc s t := by
    rw [Ioc_inter_Ioi, sup_eq_right.mpr hs]
  rw [he, integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet,
    inter_comm (Ioi s), hi, setIntegral_indicator measurableSet_Ioi, hi]
  exact ⟨Iff.rfl, rfl⟩

lemma triangle_lower_section {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {v t : ℝ} (hv : v ≤ t) :
    (∫ s in Ioc 0 t, if s < v then f s else 0) = ∫ s in Ioc 0 v, f s := by
  have he : (fun s => if s < v then f s else 0) =ᵐ[volume.restrict (Ioc 0 t)]
      (Iic v).indicator f := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne v)] with s hs
    simp only [indicator_apply, mem_Iic]
    simp only [lt_iff_le_and_ne, and_iff_left hs]
  rw [integral_congr_ae he, setIntegral_indicator measurableSet_Iic,
    Ioc_inter_Iic, inf_eq_right.mpr hv]

/-- Absolute integrability of the positive Beta majorant on the square.
In the order s then v its inner integral is constant a.e. -/
lemma beta_triangle_integrable {α t : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Integrable (fun z : ℝ × ℝ => if z.1 < z.2 then
      (t-z.2) ^ (-α) * (z.2-z.1) ^ (α-1) else 0)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
  let B : ℝ × ℝ → ℝ := fun z => if z.1 < z.2 then
    (t-z.2) ^ (-α) * (z.2-z.1) ^ (α-1) else 0
  have hB : Measurable B := by
    apply Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (((measurable_const.sub measurable_snd).pow_const _).mul
        ((measurable_snd.sub measurable_fst).pow_const _)) measurable_const
  apply (integrable_prod_iff hB.aestronglyMeasurable).mpr
  have hb (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) t) :
      IntegrableOn (fun v => (t-v) ^ (-α) * (v-s) ^ (α-1)) (Ioc s t) ∧
      (∫ v in Ioc s t, (t-v) ^ (-α) * (v-s) ^ (α-1)) =
        Real.Gamma (1-α) * Real.Gamma α := by
    have h := BetaSemigroup.beta_convolution (1-α) α s t (sub_pos.mpr hα1) hα hs.2
    simpa [show 1-α-1 = -α by ring, show (1-α)+α = 1 by ring] using h
  have hmem : ∀ᵐ s ∂volume.restrict (Ioc 0 t), s ∈ Ioo (0 : ℝ) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne t)] with s hs hne
    exact ⟨hs.1, lt_of_le_of_ne hs.2 hne⟩
  constructor
  · filter_upwards [hmem] with s hs
    exact (triangle_upper_section _ hs.1.le).1.mpr (hb s hs).1
  · apply (integrable_const (Real.Gamma (1-α) * Real.Gamma α)).congr
    filter_upwards [hmem] with s hs
    change Real.Gamma (1-α) * Real.Gamma α = ∫ v in Ioc 0 t, ‖B (s,v)‖
    have hn : ∀ᵐ v ∂volume.restrict (Ioc 0 t), ‖B (s,v)‖ = B (s,v) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      apply Real.norm_of_nonneg
      dsimp [B]
      split_ifs with hsv
      · exact mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hv.2) _)
          (Real.rpow_nonneg (sub_pos.mpr hsv).le _)
      · exact le_rfl
    rw [integral_congr_ae hn, (triangle_upper_section _ hs.1.le).2, (hb s hs).2]

/-- Rescaling the inner integral cancels all powers of t-s against the
Jacobian, retaining the genuine two-variable amplitude. -/
lemma beta_rescale_amplitude {𝕜 : Type} [RCLike 𝕜] (α : ℝ)
    (k : ℝ × ℝ → 𝕜) {s t : ℝ} (hst : s < t) :
    (∫ v in Ioc s t, ((t-v) ^ (-α) * (v-s) ^ (α-1)) • k (v,s)) =
      ∫ r in Ioc (0 : ℝ) 1, betaWeight α r • k (s+(t-s)*r,s) := by
  let f : ℝ → 𝕜 := fun v => ((t-v) ^ (-α) * (v-s) ^ (α-1)) • k (v,s)
  have hd : 0 < t-s := sub_pos.mpr hst
  have hc := intervalIntegral.smul_integral_comp_add_mul f (t-s) s (a := 0) (b := 1)
  simp only [mul_zero, add_zero, mul_one, show s+(t-s) = t by ring] at hc
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le hst.le] at hc
  change (∫ v in Ioc s t, f v) = _
  rw [← hc, ← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  dsimp [f]
  rw [smul_smul, show t-(s+(t-s)*r) = (t-s)*(1-r) by ring,
    show s+(t-s)*r-s = (t-s)*r by ring,
    Real.mul_rpow hd.le (sub_nonneg.mpr hr.2), Real.mul_rpow hd.le hr.1.le]
  congr 1
  have hp : (t-s) * ((t-s)^(-α) * (t-s)^(α-1)) = 1 := by
    rw [← Real.rpow_add hd, show -α+(α-1) = -1 by ring, Real.rpow_neg_one,
      mul_inv_cancel₀ hd.ne']
  dsimp [betaWeight]
  calc
    _ = ((t-s) * ((t-s)^(-α) * (t-s)^(α-1))) *
        ((1-r)^(-α) * r^(α-1)) := by ring
    _ = _ := by rw [hp, one_mul]

/-- The bounded amplitude is dominated by the absolutely integrable Beta
majorant before the order of integration is exchanged. -/
lemma amplitude_triangle_integrable {𝕜 : Type} [RCLike 𝕜] {α t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {k : ℝ × ℝ → 𝕜} (hk : Continuous k)
    {u : ℝ → 𝕜} (hu : Continuous u) {M N : ℝ}
    (hkB : ∀ p, ‖k p‖ ≤ M) (huB : ∀ s, ‖u s‖ ≤ N) :
    Integrable (fun z : ℝ × ℝ => if z.1 < z.2 then
      ((t-z.2)^(-α) * (z.2-z.1)^(α-1)) • (k (z.2,z.1) * u z.1) else 0)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
  have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => if z.1 < z.2 then
      ((t-z.2)^(-α) * (z.2-z.1)^(α-1)) • (k (z.2,z.1) * u z.1) else 0)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      ((((measurable_const.sub measurable_snd).pow_const _).mul
        ((measurable_snd.sub measurable_fst).pow_const _)).smul
          (((hk.comp (continuous_snd.prodMk continuous_fst)).mul (hu.comp continuous_fst)).measurable))
      measurable_const
  apply ((beta_triangle_integrable hα hα1).mul_const (M*N)).mono' hm
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Ioc 0 t))
    (ν := volume.restrict (Ioc 0 t))).ae (ae_restrict_mem measurableSet_Ioc)] with z hv
  split_ifs with hz
  · have hpos : 0 ≤ (t-z.2)^(-α) * (z.2-z.1)^(α-1) :=
      mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hv.2) _)
        (Real.rpow_nonneg (sub_pos.mpr hz).le _)
    rw [norm_smul, Real.norm_of_nonneg hpos, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hkB _) (huB _) (norm_nonneg _)
        ((norm_nonneg (k (z.2,z.1))).trans (hkB _))) hpos
  · simp

/-- Complementary fractional composition for bounded continuous inputs.
Absolute Fubini is established before using the rescaling identity. -/
lemma composition_bounded {𝕜 : Type} [RCLike 𝕜] {α t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (_ht : 0 ≤ t)
    {k : ℝ × ℝ → 𝕜} (hk : Continuous k)
    {u : ℝ → 𝕜} (hu : Continuous u) {M N : ℝ}
    (hkB : ∀ p, ‖k p‖ ≤ M) (huB : ∀ s, ‖u s‖ ≤ N) :
    fractionalValue (1-α) (amplitudeValue α k u) t =
      ∫ s in Ioc 0 t, transformedKernel α k (t,s) * u s := by
  let H : ℝ → ℝ → 𝕜 := fun s v => if s < v then
    ((t-v)^(-α) * (v-s)^(α-1)) • (k (v,s) * u s) else 0
  have hi : Integrable (Function.uncurry H)
      ((volume.restrict (Ioc 0 t)).prod (volume.restrict (Ioc 0 t))) :=
    amplitude_triangle_integrable hα hα1 hk hu hkB huB
  have hleft : (∫ v in Ioc 0 t, ∫ s in Ioc 0 t, H s v) =
      ∫ v in Ioc 0 t, (t-v)^(-α) • amplitudeValue α k u v := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    have he : (fun s => H s v) = fun s => (t-v)^(-α) •
        (if s < v then (v-s)^(α-1) • (k (v,s) * u s) else 0) := by
      funext s
      dsimp [H]
      split_ifs <;> simp [mul_smul]
    dsimp only
    rw [he, integral_smul, triangle_lower_section _ hv.2]
    rfl
  have hright : (∫ s in Ioc 0 t, ∫ v in Ioc 0 t, H s v) =
      ∫ s in Ioc 0 t,
        (∫ r in Ioc (0 : ℝ) 1, betaWeight α r • k (s+(t-s)*r,s)) * u s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (volume.ae_ne t)] with s hs hne
    have hst : s < t := lt_of_le_of_ne hs.2 hne
    change (∫ v in Ioc 0 t, if s < v then
      ((t-v)^(-α) * (v-s)^(α-1)) • (k (v,s) * u s) else 0) = _
    rw [(triangle_upper_section _ hs.1.le).2,
      ← beta_rescale_amplitude α k hst, ← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    exact (smul_mul_assoc _ _ _).symm
  change (Real.Gamma (1-α))⁻¹ •
    (∫ v in Ioc 0 t, (t-v)^((1-α)-1) • amplitudeValue α k u v) = _
  rw [show (1-α)-1 = -α by ring, ← hleft, ← integral_integral_swap hi, hright,
    ← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  exact (smul_mul_assoc _ _ _).symm

/-- The transformed kernel depends only on values on the original triangle. -/
lemma transformedKernel_congr {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    {k l : ℝ × ℝ → 𝕜} (he : EqOn k l (volterraTriangle 0 T))
    {p : ℝ × ℝ} (hp : p ∈ volterraTriangle 0 T) :
    transformedKernel α k p = transformedKernel α l p := by
  unfold transformedKernel
  apply congrArg (fun a : 𝕜 => (Real.Gamma (1-α))⁻¹ • a)
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  exact congrArg (fun a : 𝕜 => betaWeight α r • a)
    (he (triangle_subset_betaParameterDomain (Subset.refl _) hp ⟨r, hr.1.le, hr.2⟩))

/-- The analytic bridge holds for every continuous two-variable amplitude,
with no hypothesis about its behavior off the closed triangle. -/
theorem composition_identity : Spec.CompositionIdentity := by
  intro 𝕜 _ α T hα hα1 hT k hk u
  obtain ⟨hc, hi⟩ := amplitude_continuous_integrable hα hT k hk u
  refine ⟨hc, hi, ?_⟩
  let K : C(volterraTriangle 0 T, 𝕜) := ⟨fun p => k p, hk.domRestrict⟩
  let k' : ℝ × ℝ → 𝕜 := fun p => K (volterraTriangleClamp hT p)
  have hkc : Continuous k' := K.continuous.comp (continuous_volterraTriangleClamp hT)
  have hkB : ∀ p, ‖k' p‖ ≤ ‖K‖ := fun p => K.norm_coe_le_norm _
  have he : EqOn k' k (volterraTriangle 0 T) := by
    intro p hp
    change K (volterraTriangleClamp hT (⟨p,hp⟩ : volterraTriangle 0 T)) = _
    rw [volterraTriangleClamp_coe]
    rfl
  have ha : EqOn (amplitudeValue α k' (continuousExtension hT u))
      (amplitudeValue α k (continuousExtension hT u)) (Icc 0 T) := by
    intro t ht
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only
    rw [he (show (t,s) ∈ volterraTriangle 0 T from ⟨hs.1.le, hs.2, ht.2⟩)]
  have hae : amplitudeValue α k' (continuousExtension hT u)
      =ᵐ[intervalMeasure T] amplitudeValue α k (continuousExtension hT u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ha ⟨ht.1.le, ht.2⟩
  intro t ht
  rw [← (FractionalIntegrals.representative_independence (1-α) T _ _ hae t ht).2,
    composition_bounded hα hα1 ht.1 hkc (FractionalIntegrals.continuous_extension hT u)
      hkB (FractionalIntegrals.extension_norm_le hT u)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  exact congrArg (fun a : 𝕜 => a * continuousExtension hT u s)
    (transformedKernel_congr he (show (t,s) ∈ volterraTriangle 0 T from ⟨hs.1.le, hs.2, ht.2⟩))

/-- For compatible C¹ data the complementary integral is C¹, with the
continuous derivative in the source's second-kind equation. -/
lemma fractional_datum_c1 {𝕜 : Type} [RCLike 𝕜] {β T : ℝ}
    (hβ : 0 < β) (hT : 0 < T) {g g' : ℝ → 𝕜}
    (hg : AbelInversion.Spec.C1On T g g') (h0 : g 0 = 0) :
    AbelInversion.Spec.C1On T (fractionalValue β g) (fractionalValue β g') := by
  have hq := AbelInversion.continuousOn_fractional hβ hT.le hg.2.1
  have he : EqOn g (fractionalValue 1 g') (Icc 0 T) := by
    intro t ht
    rw [AbelInversion.c1_integral_identity hg ht, h0, sub_zero]
  have hae : g =ᵐ[intervalMeasure T] fractionalValue 1 g' := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact he ⟨ht.1.le, ht.2⟩
  have hprim : EqOn (fractionalValue β g)
      (fractionalValue 1 (fractionalValue β g')) (Icc 0 T) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with hz | hp
    · subst t
      simp [FractionalIntegrals.fractional_zero_time]
    · rw [(FractionalIntegrals.representative_independence β T g _ hae t ht).2,
        AbelInversion.continuous_semigroup_value hβ zero_lt_one hT hg.2.1 ⟨hp, ht.2⟩,
        AbelInversion.continuous_semigroup_value zero_lt_one hβ hT hg.2.1 ⟨hp, ht.2⟩,
        add_comm β 1]
  let q : C(Icc (0 : ℝ) T, 𝕜) := ⟨fun t => fractionalValue β g' t, hq.domRestrict⟩
  have hc : Continuous (continuousExtension hT.le q) := q.continuous.comp continuous_projIcc
  refine ⟨AbelInversion.continuousOn_fractional hβ hT.le hg.1, hq, ?_⟩
  intro t ht
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hdt : continuousExtension hT.le q t = fractionalValue β g' t := by
    simp [continuousExtension, projIcc_of_mem hT.le ht, q]
  rw [hdt] at hd
  apply hd.hasDerivWithinAt.congr_of_mem _ ht
  intro r hr
  rw [hprim hr, AbelInversion.fractional_one, ← intervalIntegral.integral_of_le hr.1]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hr.1] at hs
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans hr.2⟩
  simp [continuousExtension, projIcc_of_mem hT.le hsT, q]

/-- Back-substitution uses fractional injectivity on the original continuous
functions. The only hypothesis here to be supplied by the analytic bridge is
`CompositionIdentity`; the final solvability Spec does not assume it. -/
lemma equation_iff_transformed (hcomp : Spec.CompositionIdentity)
    {𝕜 : Type} [RCLike 𝕜] {α T : ℝ} (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T)
    (k : ℝ × ℝ → 𝕜) (hk : ContinuousOn k (volterraTriangle 0 T))
    (g u : C(Icc (0 : ℝ) T, 𝕜)) :
    AmplitudeEquation hT.le α k g u ↔
      ∀ t : Icc (0 : ℝ) T,
        (∫ s in Ioc 0 (t : ℝ), transformedKernel α k (t,s) * continuousExtension hT.le u s) =
          fractionalValue (1-α) (continuousExtension hT.le g) t := by
  have hb := hcomp 𝕜 α T hα hα1 hT.le k hk u
  have hgc : ContinuousOn (continuousExtension hT.le g) (Icc 0 T) :=
    (g.continuous.comp continuous_projIcc).continuousOn
  have hgc_eq (t : Icc (0 : ℝ) T) : continuousExtension hT.le g t = g t := by
    simp [continuousExtension, projIcc_of_mem hT.le t.property]
  constructor
  · intro hu t
    rw [← hb.2.2 t t.property]
    apply (FractionalIntegrals.representative_independence (1-α) T _ _ ?_ t t.property).2
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (hu ⟨s, hs.1.le, hs.2⟩).trans (hgc_eq ⟨s, hs.1.le, hs.2⟩).symm
  · intro hu
    have he : fractionalValue (1-α) (amplitudeValue α k (continuousExtension hT.le u))
        =ᵐ[intervalMeasure T] fractionalValue (1-α) (continuousExtension hT.le g) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact (hb.2.2 s ⟨hs.1.le, hs.2⟩).trans (hu ⟨s, hs.1.le, hs.2⟩)
    have hi := AbelInversion.fractional_injective (sub_pos.mpr hα1)
      (by linarith : 1-α < 1) hT
      (AbelInversion.continuousOn_integrable hb.1)
      (AbelInversion.continuousOn_integrable hgc) he
    have hpoint := Measure.eqOn_Ioc_of_ae_eq volume hi
      (hb.1.mono Ioc_subset_Icc_self) (hgc.mono Ioc_subset_Icc_self)
    have hclosed := hpoint.of_subset_closure hb.1 hgc Ioc_subset_Icc_self
      (by rw [closure_Ioc hT.ne])
    intro t
    exact (hclosed t.property).trans (hgc_eq t)

/-- Complete assembly from the explicitly isolated analytic composition lemma.
It is a reduction theorem, not a replacement statement of C1Solvability. -/
theorem c1_solvability_of_composition (hcomp : Spec.CompositionIdentity) :
    Spec.C1Solvability := by
  intro 𝕜 _ α T hα hα1 hT U hU hsub k hk hne g hg hg0
  have hg' : AbelInversion.Spec.C1On T (continuousExtension hT.le g)
      (derivWithin (continuousExtension hT.le g) (Icc 0 T)) :=
    (AbelInversion.c1_identification T hT _ _).mpr ⟨hg, fun _ _ => rfl⟩
  have hgzero : continuousExtension hT.le g 0 = 0 := by
    simpa [continuousExtension] using hg0
  have hJ := fractional_datum_c1 (sub_pos.mpr hα1) hT hg' hgzero
  let G := transformedKernel α k
  let H : C(Icc (0 : ℝ) T, 𝕜) :=
    ⟨fun t => fractionalValue (1-α) (continuousExtension hT.le g) t, hJ.1.domRestrict⟩
  have hH : ContDiffOn ℝ 1 (volterraIntervalExtension hT.le H) (Icc 0 T) := by
    have hj := ((AbelInversion.c1_identification T hT _ _).mp hJ).1
    apply hj.congr
    intro t ht
    simp [volterraIntervalExtension, projIcc_of_mem hT.le ht, H]
  obtain ⟨⟨W, hW, hWsub, hG⟩, hdiag⟩ := kernel_regularity 𝕜 α T hα hα1 hT.le U hU hsub k hk
  have hGne : ∀ t : Icc (0 : ℝ) T, G (t,t) ≠ 0 := by
    intro t
    change transformedKernel α k (t,t) ≠ 0
    rw [hdiag t]
    exact smul_ne_zero (Real.Gamma_pos_of_pos hα).ne' (hne t)
  obtain ⟨hex, huniq⟩ := FirstKindSmooth.c1_solvability 𝕜 0 T hT.le W hW hWsub G hG hGne H hH
  have hH0 : H ⟨0, le_rfl, hT.le⟩ = 0 := FractionalIntegrals.fractional_zero_time _ _
  obtain ⟨u, hu⟩ := hex.mpr hH0
  have hiff (v : C(Icc (0 : ℝ) T, 𝕜)) :
      AmplitudeEquation hT.le α k g v ↔ firstKindVolterraEquation hT.le G H v := by
    rw [equation_iff_transformed hcomp hα hα1 hT k (hk.continuousOn.mono hsub)]
    apply forall_congr'
    intro t
    rw [intervalIntegral.integral_of_le t.property.1]
    rfl
  exact ⟨u, (hiff u).mpr hu, fun v hv => huniq hT v u ((hiff v).mp hv) hu⟩

/-- The general-amplitude first-kind Abel equation has a unique continuous
solution on every positive-length interval under the source's C¹ hypotheses. -/
theorem c1_solvability : Spec.C1Solvability :=
  c1_solvability_of_composition composition_identity

end ExpandedFA.PartV.AbelAmplitude
