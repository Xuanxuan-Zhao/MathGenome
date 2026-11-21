import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.PolarMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueCompletion
import MathGenome.Internal.RealAnalysis.D11.Ch08.CompletedProduct

/-! Polar measure with Euclidean norm and completed Lebesgue normalization.
The library Haar decomposition is specialized to the shared Euclidean space,
then its two factors are exchanged. Completion is handled by null measurable
functions and the previously proved completed-product theorems. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal Pointwise
set_option maxHeartbeats 400000

namespace D11.Ch09.PolarMeasure
open D11.Ch03 D11.Ch03.LebesgueMeasures
open Specs.D11.Ch09.PolarMeasure
open Specs.D11.Ch08.CompletedProduct
open Specs.D11.Ch02.Completion (completedSpace_value completedMeasure_value)
open D11.Ch06.ScalarIntegral

noncomputable def angularMeasure : angularMeasure_type := angularMeasure_value
noncomputable def radialMeasure : radialMeasure_type := radialMeasure_value
noncomputable def polarEquiv : polarEquiv_type := polarEquiv_value
noncomputable def fromPolar : fromPolar_type := fromPolar_value

theorem polar_coordinates : Specs.D11.Ch09.PolarMeasure.polar_coordinates := by
  intro n x
  constructor <;> simp [polarEquiv_value, homeomorphUnitSphereProd_apply_snd_coe,
    homeomorphUnitSphereProd_apply_fst_coe]

theorem inverse_coordinates : Specs.D11.Ch09.PolarMeasure.inverse_coordinates := by
  intro n p
  simp [polarEquiv_value, fromPolar_value, homeomorphUnitSphereProd_symm_apply_coe]

instance angularMeasure_isFinite (n : ℕ) [NeZero n] : IsFiniteMeasure (angularMeasure n) :=
  inferInstanceAs (IsFiniteMeasure (volume : Measure (Point n)).toSphere)
instance radialMeasure_sigmaFinite (n : ℕ) : SigmaFinite (radialMeasure n) :=
  inferInstanceAs (SigmaFinite (Measure.volumeIoiPow (n - 1)))

theorem angular_finite : Specs.D11.Ch09.PolarMeasure.angular_finite := by
  intro n _
  exact angularMeasure_isFinite n

lemma finrank_point (n : ℕ) : Module.finrank ℝ (Point n) = n := by simp [Point]

theorem radial_direction_transport : Specs.D11.Ch09.PolarMeasure.radial_direction_transport := by
  intro n _
  have h : MeasurePreserving (homeomorphUnitSphereProd (Point n))
      ((volume : Measure (Point n)).comap Subtype.val)
      ((angularMeasure n).prod (radialMeasure n)) := by
    simpa only [angularMeasure, angularMeasure_value, radialMeasure, radialMeasure_value,
      finrank_point] using (volume : Measure (Point n)).measurePreserving_homeomorphUnitSphereProd
  change MeasurePreserving (Prod.swap ∘ homeomorphUnitSphereProd (Point n))
    ((volume : Measure (Point n)).comap Subtype.val)
    ((radialMeasure n).prod (angularMeasure n))
  exact Measure.measurePreserving_swap.comp h

lemma fromPolar_eq (n : ℕ) :
    fromPolar n = Subtype.val ∘ (polarEquiv n).symm := by
  funext p
  exact (inverse_coordinates n p).symm

lemma fromPolar_measurableEmbedding (n : ℕ) : MeasurableEmbedding (fromPolar n) := by
  have h := (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : Point n)).compl).comp
    (polarEquiv n).symm.measurableEmbedding
  rw [fromPolar_eq]
  exact h

lemma closedCone_eq_image (n : ℕ) (A : Set (Sphere n)) :
    closedCone A = fromPolar n '' (Iic (⟨1, by norm_num [Radius]⟩ : Radius) ×ˢ A) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨θ, hθ, rfl⟩, rfl⟩
    refine ⟨(⟨r, hr.1⟩, θ), ⟨hr.2, hθ⟩, rfl⟩
  · rintro ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩
    exact ⟨r, ⟨r.2, hr⟩, θ, ⟨θ, hθ, rfl⟩, rfl⟩

theorem closedCone_borel : Specs.D11.Ch09.PolarMeasure.closedCone_borel := by
  intro n A hA
  rw [closedCone_eq_image]
  exact (fromPolar_measurableEmbedding n).measurableSet_image.mpr (measurableSet_Iic.prod hA)

lemma fromPolar_measurePreserving (n : ℕ) [NeZero n] :
    MeasurePreserving (fromPolar n) ((radialMeasure n).prod (angularMeasure n)) volume := by
  have hi := MeasurePreserving.symm (polarEquiv n).toMeasurableEquiv
    (radial_direction_transport n)
  have hc := measurePreserving_subtype_coe (μa := (volume : Measure (Point n)))
    (measurableSet_singleton (0 : Point n)).compl
  rw [restrict_compl_singleton] at hc
  have h := hc.comp hi
  rw [fromPolar_eq]
  exact h

lemma lebesgue_eq_volume (n : ℕ) [NeZero n] (E : Set (Point n)) :
    lebesgue n E = volume E := by
  have heq := D11.Ch03.LebesgueCompletion.completion_value n
  have hE : MeasurableSet[lebesgueSpace n] (toMeasurable volume E) :=
    native_borel_le n _ (measurableSet_toMeasurable volume E)
  apply le_antisymm
  · calc
      lebesgue n E ≤ lebesgue n (toMeasurable volume E) := measure_mono (subset_toMeasurable _ _)
      _ = volume (toMeasurable volume E) := heq _ hE
      _ = volume E := measure_toMeasurable E
  · rw [native_outer_agreement]
    exact @le_toMeasure_apply (Point n) (lebesgueSpace n) (OuterVolume.outerVolume n) le_rfl E

theorem origin_null : Specs.D11.Ch09.PolarMeasure.origin_null := by
  intro n _
  change lebesgue n {0} = 0
  rw [lebesgue_eq_volume]
  exact measure_singleton _

theorem total_mass : Specs.D11.Ch09.PolarMeasure.total_mass := by
  intro n _
  change angularMeasure n univ = (n : ℝ≥0∞) * lebesgue n (ball 0 1)
  rw [lebesgue_eq_volume]
  simpa [angularMeasure, angularMeasure_value, finrank_point] using
    (volume : Measure (Point n)).toSphere_apply_univ

lemma closedCone_ae_openCone (n : ℕ) [NeZero n] (A : Set (Sphere n)) :
    closedCone A =ᵐ[(volume : Measure (Point n))] Ioo (0 : ℝ) 1 • (Subtype.val '' A) := by
  have hs : ∀ᵐ x ∂(volume : Measure (Point n)), x ∉ sphere (0 : Point n) 1 := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using (volume : Measure (Point n)).addHaar_sphere 0 1
  filter_upwards [hs] with x hx
  apply propext
  change x ∈ Ioc (0 : ℝ) 1 • (Subtype.val '' A) ↔ _
  constructor
  · rintro ⟨r, hr, y, ⟨θ, hθ, rfl⟩, rfl⟩
    refine ⟨r, ⟨hr.1, lt_of_le_of_ne hr.2 ?_⟩, θ, ⟨θ, hθ, rfl⟩, rfl⟩
    intro hr1
    apply hx
    simpa [hr1] using θ.property
  · rintro ⟨r, hr, y, hy, rfl⟩
    exact ⟨r, ⟨hr.1, hr.2.le⟩, y, hy, rfl⟩

theorem angular_cone : Specs.D11.Ch09.PolarMeasure.angular_cone := by
  intro n _ A hA
  change angularMeasure n A = (n : ℝ≥0∞) * lebesgue n (closedCone A)
  rw [lebesgue_eq_volume, measure_congr (closedCone_ae_openCone n A)]
  simpa [angularMeasure, angularMeasure_value, finrank_point] using
    (volume : Measure (Point n)).toSphere_apply' hA

lemma radial_unit_mass (n : ℕ) [NeZero n] :
    radialMeasure n (Iio (⟨1, by norm_num [Radius]⟩ : Radius)) = ENNReal.ofReal (1 / (n : ℝ)) := by
  simp [radialMeasure, radialMeasure_value, Measure.volumeIoiPow_apply_Iio,
    Nat.cast_pred (Nat.pos_of_ne_zero (NeZero.ne n))]

theorem angular_unique : Specs.D11.Ch09.PolarMeasure.angular_unique := by
  intro n _ σ hσ hmap
  let := hσ
  have hp : (radialMeasure n).prod σ = (radialMeasure n).prod (angularMeasure n) :=
    hmap.symm.trans (radial_direction_transport n).map_eq
  apply Measure.ext
  intro A hA
  have h := congrArg (fun μ : Measure (Radius × Sphere n) =>
    μ (Iio (⟨1, by norm_num [Radius]⟩ : Radius) ×ˢ A)) hp
  simp only [Measure.prod_prod, radial_unit_mass] at h
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  apply (ENNReal.mul_left_inj
    (ne_of_gt (ENNReal.ofReal_pos.mpr (one_div_pos.mpr hn))) ENNReal.ofReal_ne_top).mp
  simpa only [mul_comm, angularMeasure] using h


lemma native_aemeasurable {n : ℕ} [NeZero n] {F : Type*} [MeasurableSpace F]
    [MeasurableSpace.CountablyGenerated F] {h : Point n → F} (hh : @Measurable _ _ (lebesgueSpace n) _ h) :
    AEMeasurable h (volume : Measure (Point n)) := by
  have heq : lebesgueSpace n = eventuallyMeasurableSpace
      (inferInstance : MeasurableSpace (Point n)) (ae (volume : Measure (Point n))) :=
    D11.Ch03.LebesgueCompletion.completion_space n
  have hc := heq ▸ hh
  exact (show NullMeasurable h volume from hc).aemeasurable

lemma source_trim (n : ℕ) [NeZero n] :
    (lebesgue n).trim (native_borel_le n) = (volume : Measure (Point n)) :=
  borel_restriction n (native_borel_le n)

lemma source_lintegral {n : ℕ} [NeZero n] (h : Point n → ℝ≥0∞)
    (hh : AEMeasurable h volume) :
    @lintegral _ (lebesgueSpace n) (lebesgue n) h = ∫⁻ x, h x := by
  have ht := @lintegral_trim_ae (Point n) inferInstance (lebesgueSpace n)
    (lebesgue n) (native_borel_le n) h
  rw [source_trim] at ht
  exact (ht hh).symm

lemma source_nnIntegral {n : ℕ} [NeZero n] (h : Point n → ℝ≥0∞)
    (hh : AEMeasurable h volume) :
    @D11.Ch05.NonnegativeIntegral.nonnegativeIntegral _ (lebesgueSpace n) (lebesgue n) h =
      ∫⁻ x, h x :=
  (@D11.Ch05.NonnegativeIntegral.integral_eq_lintegral _ (lebesgueSpace n)
    (lebesgue n) h).trans (source_lintegral h hh)

lemma source_integral {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (h : Point n → 𝕜)
    (hh : AEMeasurable h volume) :
    @integral _ 𝕜 _ _ (lebesgueSpace n) (lebesgue n) h = ∫ x, h x := by
  have ht := @integral_trim_ae 𝕜 _ _ (Point n) inferInstance (lebesgueSpace n)
    (lebesgue n) (native_borel_le n) h
  rw [source_trim] at ht
  exact ht hh.aestronglyMeasurable

lemma source_integrable {n : ℕ} [NeZero n] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {h : Point n → 𝕜}
    (hh : @scalarIntegrable _ _ (lebesgueSpace n) _ _ _ (lebesgue n) h) :
    Integrable h (volume : Measure (Point n)) := by
  have ha := native_aemeasurable hh.1
  have hi := (@scalarIntegrable_iff _ _ (lebesgueSpace n) _ _ _ (lebesgue n) h).mp hh
  refine ⟨ha.aestronglyMeasurable, ?_⟩
  change ∫⁻ x, ‖h x‖ₑ < ∞
  rw [← source_lintegral _ ha.enorm]
  exact hi.2.2

theorem nonnegative_formula : Specs.D11.Ch09.PolarMeasure.nonnegative_formula := by
  intro n _ h hh
  have hp := fromPolar_measurePreserving n
  calc
    _ = ∫⁻ x, h x := source_nnIntegral h hh.aemeasurable
    _ = ∫⁻ p, h (fromPolar n p) ∂(radialMeasure n).prod (angularMeasure n) :=
      (hp.lintegral_comp_emb (fromPolar_measurableEmbedding n) h).symm
    _ = _ := lintegral_prod _ (hh.comp (fromPolar_measurableEmbedding n).measurable).aemeasurable

theorem scalar_formula : Specs.D11.Ch09.PolarMeasure.scalar_formula := by
  intro n _ 𝕜 _ _ _ h hh
  have hi := source_integrable hh
  have hp := fromPolar_measurePreserving n
  have hc := hp.integrable_comp_of_integrable hi
  refine ⟨hc, hc.prod_right_ae, hc.integral_prod_left, ?_⟩
  change @integral _ 𝕜 _ _ (lebesgueSpace n) (lebesgue n) h = _
  rw [source_integral h (native_aemeasurable hh.1)]
  exact (hp.integral_comp (fromPolar_measurableEmbedding n) h).symm.trans
    (integral_prod _ hc)

theorem completed_nonnegative_formula : Specs.D11.Ch09.PolarMeasure.completed_nonnegative_formula := by
  intro n _ h hh
  have ha := native_aemeasurable hh
  have hp := fromPolar_measurePreserving n
  have hc := ha.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  have hm : completedMeasurable ((radialMeasure n).prod (angularMeasure n))
      (h ∘ fromPolar n) := hc.nullMeasurable
  have ht := D11.Ch08.CompletedProduct.tonelli (radialMeasure n) (angularMeasure n)
    inferInstance inferInstance (h ∘ fromPolar n) hm
  refine ⟨hm, ?_, ht.2.2.1, ?_⟩
  · exact (@D11.Ch04.AeCommonException.almostEverywhere_iff_native Radius
      (completedSpace_value (radialMeasure n)) (completedMeasure_value (radialMeasure n)) _).mp ht.1
  · calc
      _ = ∫⁻ x, h x := source_nnIntegral h ha
      _ = ∫⁻ p, h (fromPolar n p) ∂(radialMeasure n).prod (angularMeasure n) :=
        (hp.lintegral_comp_emb (fromPolar_measurableEmbedding n) h).symm
      _ = completedNNIntegral ((radialMeasure n).prod (angularMeasure n))
          (h ∘ fromPolar n) :=
        (D11.Ch08.CompletedProduct.completedNNIntegral_eq _ _ hm).symm
      _ = _ := ht.2.2.2.2.1

theorem completed_scalar_formula : Specs.D11.Ch09.PolarMeasure.completed_scalar_formula := by
  intro n _ 𝕜 _ _ _ h hh
  have hi := source_integrable hh
  have hp := fromPolar_measurePreserving n
  have hc := hp.integrable_comp_of_integrable hi
  have hm : completedIntegrable ((radialMeasure n).prod (angularMeasure n))
      (h ∘ fromPolar n) :=
    (D11.Ch08.CompletedProduct.completedIntegrable_iff _ _).mpr
      ⟨hc.aemeasurable.nullMeasurable, hc⟩
  have ht := D11.Ch08.CompletedProduct.fubini (radialMeasure n) (angularMeasure n)
    inferInstance inferInstance (h ∘ fromPolar n) hm
  obtain ⟨hl, hr, heq, heqr⟩ := ht.2.2.2.2
  refine ⟨hm, ?_, hl, ?_⟩
  · exact (@D11.Ch04.AeCommonException.almostEverywhere_iff_native Radius
      (completedSpace_value (radialMeasure n)) (completedMeasure_value (radialMeasure n)) _).mp ht.1
  · change @integral _ 𝕜 _ _ (lebesgueSpace n) (lebesgue n) h = _
    rw [source_integral h (native_aemeasurable hh.1)]
    exact (hp.integral_comp (fromPolar_measurableEmbedding n) h).symm.trans
      ((D11.Ch08.CompletedProduct.completedIntegral_eq _ _ hm).symm.trans heq)


lemma offZeroMeasure_eq_native (n : ℕ) [NeZero n] (A : Set (Punctured n)) :
    offZeroMeasure n A = (volume : Measure (Point n)).comap Subtype.val A := by
  have hB : MeasurableSet (Punctured n) := (measurableSet_singleton (0 : Point n)).compl
  have hL : MeasurableSet[lebesgueSpace n] (Punctured n) := native_borel_le n _ hB
  change @Measure.comap _ _ (offZeroSpace n) (lebesgueSpace n) Subtype.val (lebesgue n) A = _
  exact (@comap_subtype_coe_apply (Point n) (lebesgueSpace n) (Punctured n) hL
    (lebesgue n) A).trans ((lebesgue_eq_volume n _).trans
      (comap_subtype_coe_apply hB (volume : Measure (Point n)) A).symm)

lemma polar_null_preimage_measurable (n : ℕ) [NeZero n] (A : Set (Radius × Sphere n))
    (hA : NullMeasurableSet A ((radialMeasure n).prod (angularMeasure n))) :
    MeasurableSet[offZeroSpace n] ((polarEquiv n) ⁻¹' A) := by
  have hp := hA.preimage (radial_direction_transport n).quasiMeasurePreserving
  have hB : MeasurableSet (Punctured n) := (measurableSet_singleton (0 : Point n)).compl
  have himg := Measure.NullMeasurableSet.subtype_coe hB.nullMeasurableSet hp
  have heq : lebesgueSpace n = eventuallyMeasurableSpace
      (inferInstance : MeasurableSpace (Point n)) (ae (volume : Measure (Point n))) :=
    D11.Ch03.LebesgueCompletion.completion_space n
  have himgL : MeasurableSet[lebesgueSpace n]
      (Subtype.val '' ((polarEquiv n) ⁻¹' A)) := by
    rw [heq]
    exact himg
  exact ⟨_, himgL, Set.preimage_image_eq _ Subtype.coe_injective⟩

theorem completed_source_transport : Specs.D11.Ch09.PolarMeasure.completed_source_transport := by
  intro n _
  have hm : @Measurable _ _ (offZeroSpace n) inferInstance (polarEquiv n) :=
    fun A hA => polar_null_preimage_measurable n A hA.nullMeasurableSet
  refine @MeasurePreserving.mk _ _ (offZeroSpace n) _ (polarEquiv n) (offZeroMeasure n) _ hm ?_
  apply Measure.ext
  intro A hA
  exact (Measure.map_apply (mα := offZeroSpace n) (μ := offZeroMeasure n) hm hA).trans
    ((offZeroMeasure_eq_native n _).trans
      ((radial_direction_transport n).measure_preimage hA.nullMeasurableSet))

theorem completed_transport : Specs.D11.Ch09.PolarMeasure.completed_transport := by
  intro n _
  have hm : @Measurable _ _ (offZeroSpace n)
      (completedSpace_value ((radialMeasure n).prod (angularMeasure n))) (polarEquiv n) :=
    fun A hA => polar_null_preimage_measurable n A hA
  refine @MeasurePreserving.mk _ _ (offZeroSpace n)
    (completedSpace_value ((radialMeasure n).prod (angularMeasure n)))
    (polarEquiv n) (offZeroMeasure n) ((radialMeasure n).prod (angularMeasure n)).completion hm ?_
  apply @Measure.ext (Radius × Sphere n)
    (completedSpace_value ((radialMeasure n).prod (angularMeasure n)))
  intro A hA
  exact (Measure.map_apply (mα := offZeroSpace n)
    (mβ := completedSpace_value ((radialMeasure n).prod (angularMeasure n)))
    (μ := offZeroMeasure n) hm hA).trans
    ((offZeroMeasure_eq_native n _).trans
      ((radial_direction_transport n).measure_preimage hA))

theorem polar_measure : Specs.D11.Ch09.PolarMeasure.polar_measure := by
  intro n _
  have hmp : @MeasurePreserving _ _ (offZeroSpace n) inferInstance (polarEquiv n)
      (offZeroMeasure n) ((radialMeasure n).prod (angularMeasure n)) := completed_source_transport n
  have hmap := @MeasurePreserving.map_eq _ _ (offZeroSpace n) inferInstance
    (polarEquiv n) (offZeroMeasure n) ((radialMeasure n).prod (angularMeasure n)) hmp
  refine ⟨angularMeasure n, ⟨inferInstance, hmap⟩, ?_⟩
  rintro σ ⟨hσ, hσmap⟩
  apply angular_unique n σ hσ
  apply Measure.ext
  intro A hA
  have hm : @Measurable _ _ (offZeroSpace n) inferInstance (polarEquiv n) :=
    @MeasurePreserving.measurable _ _ (offZeroSpace n) inferInstance
      (polarEquiv n) (offZeroMeasure n) ((radialMeasure n).prod (angularMeasure n)) hmp
  have hh := congrArg (fun μ : Measure (Radius × Sphere n) => μ A) hσmap
  have hmapeval := Measure.map_apply (mα := offZeroSpace n) (μ := offZeroMeasure n) hm hA
  have hv := (offZeroMeasure_eq_native n ((polarEquiv n) ⁻¹' A))
  have hh' : ((volume : Measure (Point n)).comap Subtype.val) ((polarEquiv n) ⁻¹' A) =
      ((radialMeasure n).prod σ) A := (hmapeval.trans hv).symm.trans hh
  exact (Measure.map_apply (polarEquiv n).measurable hA).trans hh' 

end D11.Ch09.PolarMeasure
