import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.AbelInversion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.BetaSemigroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.TangentCone.Real

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace ExpandedFA.PartV.AbelInversion
open ExpandedFA.PartV.FractionalIntegrals.Spec
open ExpandedFA.PartV.FractionalIntegrals
open ExpandedFA.PartV.BetaSemigroup
open Spec

/-- The independent datum interface is precisely C¹ on the closed interval;
its derivative is the unique real within derivative, for both scalar fields. -/
theorem c1_identification : C1Identification := by
  intro 𝕜 _ T hT g g'
  have hs := uniqueDiffOn_Icc hT
  constructor
  · intro hg
    have he : EqOn g' (derivWithin g (Icc 0 T)) (Icc 0 T) := by
      intro t ht
      exact ((hg.2.2 t ht).derivWithin (hs t ht)).symm
    exact ⟨(contDiffOn_one_iff_derivWithin hs).mpr
      ⟨fun t ht => (hg.2.2 t ht).differentiableWithinAt,
        hg.2.1.congr he.symm⟩, he⟩
  · rintro ⟨hg, he⟩
    obtain ⟨hd, hc⟩ := (contDiffOn_one_iff_derivWithin hs).mp hg
    refine ⟨hg.continuousOn, hc.congr he, ?_⟩
    intro t ht
    rw [he ht]
    exact (hd t ht).hasDerivWithinAt

lemma continuousOn_fractional {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) {f : ℝ → 𝕜} (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (fractionalValue α f) (Icc 0 T) := by
  let fC : C(Icc (0 : ℝ) T, 𝕜) := ⟨fun t => f t, hf.domRestrict⟩
  have he : f =ᵐ[intervalMeasure T] continuousExtension hT fC := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [continuousExtension, projIcc_of_mem hT ⟨ht.1.le, ht.2⟩]
    rfl
  apply ((continuousOn_const : ContinuousOn (fun _ : ℝ => (Real.Gamma α)⁻¹) (Icc 0 T)).smul (continuous_powerValue hα hT fC)).congr
  intro t ht
  exact (representative_independence α T f _ he t ht).2

lemma continuousOn_integrable {𝕜 : Type} [RCLike 𝕜] {T : ℝ}
    {f : ℝ → 𝕜} (hf : ContinuousOn f (Icc 0 T)) :
    Integrable f (intervalMeasure T) :=
  (hf.integrableOn_Icc).mono_set Ioc_subset_Icc_self

lemma continuousOn_weighted_integrable {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) {f : ℝ → 𝕜} (hf : ContinuousOn f (Icc 0 T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntegrableOn (fun s => (t-s) ^ (α-1) • f s) (Ioc 0 t) := by
  let fC : C(Icc (0 : ℝ) T, 𝕜) := ⟨fun s => f s, hf.domRestrict⟩
  apply (continuous_input_integrable hα hT fC t).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simp only [continuousExtension, projIcc_of_mem hT ⟨hs.1.le, hs.2.trans ht.2⟩]
  rfl

lemma fractional_one {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (t : ℝ) :
    fractionalValue 1 f t = ∫ s in Ioc 0 t, f s := by
  simp [fractionalValue, powerValue, Real.Gamma_one]

lemma continuous_semigroup_value {𝕜 : Type} [RCLike 𝕜] {α β T : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hT : 0 < T) {f : ℝ → 𝕜}
    (hf : ContinuousOn f (Icc 0 T)) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) :
    fractionalValue α (fractionalValue β f) t = fractionalValue (α+β) f t := by
  exact Measure.eqOn_Ioc_of_ae_eq volume
    (representative_semigroup α β T hα hβ hT.le 1 le_rfl f
      (memLp_one_iff_integrable.mpr (continuousOn_integrable hf)))
    ((continuousOn_fractional hα hT.le (continuousOn_fractional hβ hT.le hf)).mono Ioc_subset_Icc_self)
    ((continuousOn_fractional (add_pos hα hβ) hT.le hf).mono Ioc_subset_Icc_self) ht

lemma c1_integral_identity {𝕜 : Type} [RCLike 𝕜] {T : ℝ} {g g' : ℝ → 𝕜}
    (hg : C1On T g g') {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    fractionalValue 1 g' t = g t - g 0 := by
  rw [fractional_one, ← intervalIntegral.integral_of_le ht.1]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hg.1.mono (Icc_subset_Icc le_rfl ht.2))
  · intro x hx
    exact (hg.2.2 x ⟨hx.1.le, hx.2.le.trans ht.2⟩).hasDerivAt
      (Icc_mem_nhds hx.1 (hx.2.trans_le ht.2))
  · exact (hg.2.1.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1

/-- Injectivity of ordinary integration on L¹. Equality a.e. of the
continuous primitives is first promoted to equality on the interval. -/
lemma primitive_injective {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 < T)
    {u v : ℝ → 𝕜} (hu : Integrable u (intervalMeasure T))
    (hv : Integrable v (intervalMeasure T))
    (he : fractionalValue 1 u =ᵐ[intervalMeasure T] fractionalValue 1 v) :
    u =ᵐ[intervalMeasure T] v := by
  have hui : IntervalIntegrable u volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr hu
  have hvi : IntervalIntegrable v volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr hv
  have he' : (fun t => ∫ s in (0 : ℝ)..t, u s) =ᵐ[intervalMeasure T]
      (fun t => ∫ s in (0 : ℝ)..t, v s) := by
    filter_upwards [he, ae_restrict_mem measurableSet_Ioc] with t ht hmem
    simpa only [fractional_one, intervalIntegral.integral_of_le hmem.1.le] using ht
  have hcU := intervalIntegral.continuousOn_primitive_interval' hui left_mem_uIcc
  have hcV := intervalIntegral.continuousOn_primitive_interval' hvi left_mem_uIcc
  rw [uIcc_of_le hT.le] at hcU hcV
  have heq := Measure.eqOn_Ioc_of_ae_eq volume he'
    (hcU.mono Ioc_subset_Icc_self) (hcV.mono Ioc_subset_Icc_self)
  filter_upwards [ae_restrict_of_ae hui.ae_hasDerivAt_integral,
    ae_restrict_of_ae hvi.ae_hasDerivAt_integral,
    ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne T)] with t hut hvt ht hne
  have hti : t ∈ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hT.le]
    exact ⟨ht.1.le, ht.2⟩
  have hn : Ioc (0 : ℝ) T ∈ 𝓝 t :=
    mem_of_superset (Ioo_mem_nhds ht.1 (lt_of_le_of_ne ht.2 hne)) Ioo_subset_Ioc_self
  exact (hut hti 0 left_mem_uIcc).unique
    ((hvt hti 0 left_mem_uIcc).congr_of_eventuallyEq (heq.eventuallyEq_of_mem hn))

/-- Abel injectivity follows by composing with the complementary order and
then using the Lebesgue differentiation theorem. -/
lemma fractional_injective {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) {u v : ℝ → 𝕜}
    (hu : Integrable u (intervalMeasure T)) (hv : Integrable v (intervalMeasure T))
    (he : fractionalValue α u =ᵐ[intervalMeasure T] fractionalValue α v) :
    u =ᵐ[intervalMeasure T] v := by
  have hsU := representative_semigroup (1-α) α T (sub_pos.mpr hα1) hα hT.le
    1 le_rfl u (memLp_one_iff_integrable.mpr hu)
  have hsV := representative_semigroup (1-α) α T (sub_pos.mpr hα1) hα hT.le
    1 le_rfl v (memLp_one_iff_integrable.mpr hv)
  have h := hsU.symm.trans ((fractionalValue_congr_ae (1-α) T he).trans hsV)
  rw [sub_add_cancel] at h
  exact primitive_injective hT hu hv h

lemma singular_integrable {𝕜 : Type} [RCLike 𝕜] {α T : ℝ} (hα1 : α < 1) (c : 𝕜) :
    Integrable (fun s : ℝ => (s ^ (-α) / Real.Gamma (1-α)) • c) (intervalMeasure T) := by
  have h := ((power_integrable (T := T) (sub_pos.mpr hα1)).div_const
    (Real.Gamma (1-α))).smul_const c
  simpa only [intervalMeasure, sub_sub_cancel_left] using h

/-- The Beta identity reconstructs the endpoint constant for every t>0,
with absolute integrability even though the inverse has a singularity at zero. -/
lemma singular_inversion {𝕜 : Type} [RCLike 𝕜] {α t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (ht : 0 < t) (c : 𝕜) :
    IntegrableOn (fun s : ℝ => (t-s) ^ (α-1) •
      ((s ^ (-α) / Real.Gamma (1-α)) • c)) (Ioc 0 t) ∧
    fractionalValue α (fun s => (s ^ (-α) / Real.Gamma (1-α)) • c) t = c := by
  have hb := beta_convolution α (1-α) 0 t hα (sub_pos.mpr hα1) ht
  have hs : α+(1-α) = 1 := by ring
  simp only [sub_zero, sub_sub_cancel_left, hs, sub_self, Real.rpow_zero,
    Real.Gamma_one, div_one, mul_one] at hb
  have hi := (hb.1.div_const (Real.Gamma (1-α))).smul_const c
  have he : (fun s : ℝ => (t-s) ^ (α-1) •
      ((s ^ (-α) / Real.Gamma (1-α)) • c)) =
      (fun s => ((t-s) ^ (α-1) * s ^ (-α) / Real.Gamma (1-α)) • c) := by
    funext s
    rw [smul_smul, mul_div_assoc]
  refine ⟨by rwa [he], ?_⟩
  simp only [fractionalValue, powerValue]
  rw [he, integral_smul_const, integral_div, hb.2,
    mul_div_cancel_right₀ _ (Real.Gamma_pos_of_pos (sub_pos.mpr hα1)).ne', smul_smul,
    inv_mul_cancel₀ (Real.Gamma_pos_of_pos hα).ne', one_smul]

lemma representative_integrable {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα1 : α < 1) (hT : 0 ≤ T) {g g' : ℝ → 𝕜} (hg : C1On T g g') :
    Integrable (abelRepresentative α g g') (intervalMeasure T) :=
  (singular_integrable hα1 (g 0)).add
    (continuousOn_integrable (continuousOn_fractional (sub_pos.mpr hα1) hT hg.2.1))

lemma representative_solves {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) {g g' : ℝ → 𝕜}
    (hg : C1On T g g') {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) :
    IntegrableOn (fun s => (t-s) ^ (α-1) • abelRepresentative α g g' s) (Ioc 0 t) ∧
    fractionalValue α (abelRepresentative α g g') t = g t := by
  have hi := singular_inversion hα hα1 ht.1 (g 0)
  have hj := continuousOn_weighted_integrable hα hT.le
    (continuousOn_fractional (sub_pos.mpr hα1) hT.le hg.2.1) ⟨ht.1.le, ht.2⟩
  refine ⟨?_, ?_⟩
  · convert hi.1.add hj using 1
    ext s
    exact smul_add _ _ _
  · change fractionalValue α
      ((fun s => (s ^ (-α) / Real.Gamma (1-α)) • g 0) + fractionalValue (1-α) g') t = _
    rw [fractionalValue_add hi.1 hj, hi.2,
      continuous_semigroup_value hα (sub_pos.mpr hα1) hT hg.2.1 ht,
      show α+(1-α) = 1 by ring, c1_integral_identity hg ⟨ht.1.le, ht.2⟩]
    exact add_sub_cancel _ _

/-- The full scalar inversion and classification of all representatives. -/
theorem scalar_inversion : ScalarInversion := by
  intro 𝕜 _ α T hα hα1 hT g g' hg
  have hi := representative_integrable hα1 hT.le hg
  have hs := fun t ht => representative_solves hα hα1 hT hg (t := t) ht
  have hae : fractionalValue α (abelRepresentative α g g') =ᵐ[intervalMeasure T] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hs t ht).2
  refine ⟨hi, hs, ?_⟩
  intro u hu
  constructor
  · intro he
    exact fractional_injective hα hα1 hT hu hi (he.trans hae.symm)
  · intro he
    exact (fractionalValue_congr_ae α T he).trans hae

theorem unique_l1_class : UniqueL1Class := by
  intro 𝕜 _ α T hα hα1 hT g g' hg
  obtain ⟨hi, _, hclass⟩ := scalar_inversion α T hα hα1 hT g g' hg
  let hm := memLp_one_iff_integrable.mpr hi
  refine ⟨hm.toLp (abelRepresentative α g g'), ?_, ?_⟩
  · exact (hclass _ (memLp_one_iff_integrable.mp (Lp.memLp _))).mpr hm.coeFn_toLp
  · intro u hu
    apply Lp.ext
    exact ((hclass _ (memLp_one_iff_integrable.mp (Lp.memLp u))).mp hu).trans hm.coeFn_toLp.symm

theorem equation_equivalence : EquationEquivalence := by
  intro 𝕜 _ α T hα hα1 hT g g' hg u hu
  constructor
  · intro he t ht
    have hc := ((scalar_inversion α T hα hα1 hT g g' hg).2.2 u hu).mp he
    exact ((representative_independence α T u _ hc t ⟨ht.1.le, ht.2⟩).2).trans
      (representative_solves hα hα1 hT hg ht).2
  · intro he
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact he t ht

/-- Multiplication by t^α removes the explicit singularity. If the
representative had a continuous extension, evaluate this identity at zero
by continuity and density to force the endpoint datum to vanish. -/
lemma continuous_extension_forces_zero {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) {g g' v : ℝ → 𝕜}
    (hg : C1On T g g') (hv : ContinuousOn v (Icc 0 T))
    (he : EqOn v (abelRepresentative α g g') (Ioc 0 T)) : g 0 = 0 := by
  have hβ : 0 < 1-α := sub_pos.mpr hα1
  have hc : ContinuousOn (fun t => t ^ α • (v t - fractionalValue (1-α) g' t))
      (Icc 0 T) :=
    (Real.continuous_rpow_const hα.le).continuousOn.smul
      (hv.sub (continuousOn_fractional hβ hT.le hg.2.1))
  have heq : EqOn (fun t => t ^ α • (v t - fractionalValue (1-α) g' t))
      (fun _ => (Real.Gamma (1-α))⁻¹ • g 0) (Ioc 0 T) := by
    intro t ht
    change t ^ α • (v t - fractionalValue (1-α) g' t) = (Real.Gamma (1-α))⁻¹ • g 0
    rw [he ht, abelRepresentative, add_sub_cancel_right, smul_smul]
    congr 1
    rw [div_eq_mul_inv, ← mul_assoc, ← Real.rpow_add ht.1, add_neg_cancel,
      Real.rpow_zero, one_mul]
  have h0 := heq.of_subset_closure hc continuousOn_const Ioc_subset_Icc_self
    (by rw [closure_Ioc hT.ne]) (left_mem_Icc.mpr hT.le)
  simp only [Real.zero_rpow hα.ne', zero_smul] at h0
  exact (smul_eq_zero.mp h0.symm).resolve_left (inv_ne_zero (Real.Gamma_pos_of_pos hβ).ne')

lemma representative_continuous_of_zero {𝕜 : Type} [RCLike 𝕜] {α T : ℝ}
    (hα1 : α < 1) (hT : 0 ≤ T) {g g' : ℝ → 𝕜}
    (hg : C1On T g g') (h0 : g 0 = 0) :
    ContinuousOn (abelRepresentative α g g') (Icc 0 T) := by
  have he : abelRepresentative α g g' = fractionalValue (1-α) g' := by
    ext t
    simp [abelRepresentative, h0]
  rw [he]
  exact continuousOn_fractional (sub_pos.mpr hα1) hT hg.2.1

theorem endpoint_extension : EndpointExtension := by
  intro 𝕜 _ α T hα hα1 hT g g' hg
  have hzero : abelRepresentative α g g' 0 = 0 := by
    simp [abelRepresentative, Real.zero_rpow (neg_ne_zero.mpr hα.ne'), fractional_zero_time]
  have hc := representative_continuous_of_zero hα1 hT.le hg
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro ⟨v, hv, he⟩
    exact continuous_extension_forces_zero hα hα1 hT hg hv he
  · intro h0
    exact ⟨abelRepresentative α g g', hc h0, fun _ _ => rfl⟩
  · intro v hv he
    have hg0 := continuous_extension_forces_zero hα hα1 hT hg hv he
    have he0 := he.of_subset_closure hv (hc hg0) Ioc_subset_Icc_self
      (by rw [closure_Ioc hT.ne]) (left_mem_Icc.mpr hT.le)
    exact he0.trans hzero
  · intro hg0
    exact ⟨hc hg0, hzero, by rw [fractional_zero_time, hg0]⟩
  · intro _
    exact fractional_zero_time α _

theorem zero_interval : ZeroInterval := by
  intro 𝕜 _ α g
  have hz : intervalMeasure 0 = 0 := by simp [intervalMeasure]
  have hsingle : ∀ u : C(Icc (0 : ℝ) 0, 𝕜),
      (∀ t : Icc (0 : ℝ) 0,
        fractionalValue α (continuousExtension (le_refl 0) u) t = g t) ↔ g 0 = 0 := by
    intro u
    constructor
    · intro h
      exact (h ⟨0, by simp⟩).symm.trans (fractional_zero_time α _)
    · intro h t
      have ht : (t : ℝ) = 0 := le_antisymm t.property.2 t.property.1
      rw [ht, fractional_zero_time, h]
  refine ⟨?_, ?_, hsingle, ?_⟩
  · intro u
    apply Lp.ext
    simp [Filter.EventuallyEq, hz]
  · intro u t ht
    exact (not_lt_of_ge ht.2 ht.1).elim
  · constructor
    · rintro ⟨u, hu⟩
      exact (hsingle u).mp hu
    · intro h
      exact ⟨0, (hsingle 0).mpr h⟩

end ExpandedFA.PartV.AbelInversion
