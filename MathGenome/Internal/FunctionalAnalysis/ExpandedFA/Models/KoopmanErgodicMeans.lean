import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.KoopmanErgodicMeans
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.KoopmanGroups
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Ergodic.ContinuousMeanErgodic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace NNReal
namespace ExpandedFA.Models.KoopmanErgodicMeans
open KoopmanGroups
universe u
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

lemma fixed_iff_ae (Φ : MeasurePreservingFlow X μ) (f : Lp ℂ 2 μ) (t : ℝ) :
    pullback Φ t f = f ↔ (fun x => f (Φ.maps t x)) =ᵐ[μ] f := by
  constructor
  · intro h
    exact (Lp.coeFn_compMeasurePreserving f (Φ.measure_preserving t)).symm.trans
      (Filter.Eventually.of_forall (fun x => congrArg (fun g : Lp ℂ 2 μ => g x) h))
  · intro h
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving f (Φ.measure_preserving t)).trans h

variable [IsProbabilityMeasure μ]

lemma const_fixed (Φ : MeasurePreservingFlow X μ) (c : ℂ) (t : ℝ) :
    pullback Φ t (Lp.const 2 μ c) = Lp.const 2 μ c := by
  apply (fixed_iff_ae Φ _ t).mpr
  exact ((Φ.measure_preserving t).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_const 2 μ c)).trans (Lp.coeFn_const 2 μ c).symm

omit [IsProbabilityMeasure μ] in
lemma ae_const_of_fixed (Φ : MeasurePreservingFlow X μ) (hΦ : Ergodic Φ)
    (f : Lp ℂ 2 μ) (hf : ∀ t : ℝ, pullback Φ t f = f) :
    ∃ c : ℂ, f =ᵐ[μ] Function.const X c := by
  apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
  intro V hV
  have hm : NullMeasurableSet (f ⁻¹' V) μ :=
    (Lp.aestronglyMeasurable f).aemeasurable.nullMeasurable hV
  have hi (t : ℝ) : Φ.maps t ⁻¹' (f ⁻¹' V) =ᵐ[μ] f ⁻¹' V := by
    filter_upwards [(fixed_iff_ae Φ f t).mp (hf t)] with x hx
    simp only [Set.mem_preimage, hx]
  rcases hΦ _ hm hi with hz | hz
  · exact Or.inr (by simpa using (measure_eq_zero_iff_ae_notMem.mp hz))
  · exact Or.inl (by simpa using (measure_eq_zero_iff_ae_notMem.mp hz))

lemma constants_of_ergodic (Φ : MeasurePreservingFlow X μ) (hΦ : Ergodic Φ) :
    FixedVectorsAreConstants Φ := by
  intro f
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := ae_const_of_fixed Φ hΦ f hf
    exact ⟨c, Lp.ext (hc.trans (Lp.coeFn_const 2 μ c).symm)⟩
  · rintro ⟨c, rfl⟩
    exact const_fixed Φ c

lemma ergodic_of_constants (Φ : MeasurePreservingFlow X μ)
    (hΦ : FixedVectorsAreConstants Φ) : Ergodic Φ := by
  intro s hs hi
  let g : X → ℂ := s.indicator (fun _ => 1)
  have hg : MemLp g 2 μ := MemLp.indicator hs (memLp_const (1 : ℂ))
  let f : Lp ℂ 2 μ := hg.toLp g
  have hf : ∀ t : ℝ, pullback Φ t f = f := by
    intro t
    apply (fixed_iff_ae Φ f t).mpr
    have hcomp := (Φ.measure_preserving t).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp
    filter_upwards [hcomp, hg.coeFn_toLp, hi t] with x hx hy hz
    change f (Φ.maps t x) = g (Φ.maps t x) at hx
    change f x = g x at hy
    rw [hx, hy]
    change (s.indicator (fun _ => (1 : ℂ))) (Φ.maps t x) = s.indicator (fun _ => 1) x
    have hmem : Φ.maps t x ∈ s ↔ x ∈ s := Iff.of_eq hz
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem (hmem.mpr hxs), Set.indicator_of_mem hxs]
    · rw [Set.indicator_of_notMem (mt hmem.mp hxs), Set.indicator_of_notMem hxs]
  obtain ⟨c, hc⟩ := (hΦ f).mp hf
  have hfc : f =ᵐ[μ] Function.const X c := by
    rw [hc]
    exact Lp.coeFn_const 2 μ c
  have hgc : g =ᵐ[μ] Function.const X c := hg.coeFn_toLp.symm.trans hfc
  by_cases hc0 : c = 0
  · left
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hgc] with x hx
    intro hxs
    simp [g, hxs, hc0] at hx
  · right
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hgc] with x hx
    intro hxs
    have hxs' : x ∉ s := hxs
    exact hc0 (by simpa [g, hxs'] using hx.symm)

/-- The fixed-space criterion needs no continuity assumption. -/
theorem fixed_space_characterization : Spec.FixedSpaceCharacterization.{u} := by
  intro X _ μ _ Φ
  exact ⟨ergodic_of_constants Φ, constants_of_ergodic Φ⟩

open ExpandedFA.Ergodic

/-- Restrict the unitary real flow to the nonnegative-time contraction semigroup. -/
def contractionSemigroup (Φ : MeasurePreservingFlow X μ) (hΦ : StronglyContinuous Φ) :
    ContinuousMeanErgodic.Spec.ContractionSemigroup ℂ (Lp ℂ 2 μ) where
  op s := (pullback Φ (s : ℝ)).toContinuousLinearMap
  zero := by
    apply ContinuousLinearMap.ext
    intro f
    exact pullback_zero Φ f
  add s t := by
    apply ContinuousLinearMap.ext
    intro f
    exact pullback_add Φ s t f
  continuous f := (hΦ f).comp NNReal.continuous_coe
  norm_le s := (pullback Φ (s : ℝ)).norm_toContinuousLinearMap_le

omit [IsProbabilityMeasure μ] in
/-- Inverse time shows that fixing every nonnegative time fixes every real time. -/
lemma fixed_of_nonnegative (Φ : MeasurePreservingFlow X μ) (f : Lp ℂ 2 μ)
    (hf : ∀ s : ℝ≥0, pullback Φ (s : ℝ) f = f) :
    ∀ t : ℝ, pullback Φ t f = f := by
  intro t
  by_cases ht : 0 ≤ t
  · exact hf ⟨t, ht⟩
  · have hn : 0 ≤ -t := by linarith
    have h := hf ⟨-t, hn⟩
    calc
      pullback Φ t f = pullback Φ t (pullback Φ (-t) f) := congrArg (pullback Φ t) h.symm
      _ = f := by rw [← pullback_add, add_neg_cancel, pullback_zero]

omit [IsProbabilityMeasure μ] in
lemma mem_semigroup_fixedSpace (Φ : MeasurePreservingFlow X μ) (hΦ : StronglyContinuous Φ)
    (f : Lp ℂ 2 μ) :
    f ∈ ContinuousMeanErgodic.Spec.fixedSpace (contractionSemigroup Φ hΦ) ↔
      ∀ t : ℝ, pullback Φ t f = f := by
  rw [ContinuousMeanErgodic.mem_fixedSpace]
  exact ⟨fixed_of_nonnegative Φ f, fun h s => h s⟩

lemma inner_const_one (f : Lp ℂ 2 μ) :
    ⟪Lp.const 2 μ (1 : ℂ), f⟫_ℂ = ∫ x, f x ∂μ := by
  simpa using L2.inner_indicatorConstLp_one (μ := μ) MeasurableSet.univ
    (measure_ne_top μ Set.univ) f

lemma integral_constLp (c : ℂ) : ∫ x, (Lp.const 2 μ c) x ∂μ = c := by
  rw [integral_congr_ae (Lp.coeFn_const 2 μ c)]
  change (∫ _ : X, c ∂μ) = c
  simp

/-- For probability measure the orthogonal projection onto constants is integration. -/
lemma fixedSpace_projection (Φ : MeasurePreservingFlow X μ) (hΦ : StronglyContinuous Φ)
    (he : Ergodic Φ) (f : Lp ℂ 2 μ) :
    (ContinuousMeanErgodic.Spec.fixedSpace (contractionSemigroup Φ hΦ)).toSubmodule.starProjection f =
      Lp.const 2 μ (∫ x, f x ∂μ) := by
  let F := (ContinuousMeanErgodic.Spec.fixedSpace (contractionSemigroup Φ hΦ)).toSubmodule
  have hp : ∀ t : ℝ, pullback Φ t (F.starProjection f) = F.starProjection f :=
    (mem_semigroup_fixedSpace Φ hΦ _).mp (F.starProjection_apply_mem f)
  obtain ⟨c, hc⟩ := (constants_of_ergodic Φ he (F.starProjection f)).mp hp
  have hone : Lp.const 2 μ (1 : ℂ) ∈ F :=
    (mem_semigroup_fixedSpace Φ hΦ _).mpr (const_fixed Φ 1)
  have hi : ⟪Lp.const 2 μ (1 : ℂ), F.starProjection f⟫_ℂ =
      ⟪Lp.const 2 μ (1 : ℂ), f⟫_ℂ := by
    rw [← F.inner_starProjection_left_eq_right,
      F.starProjection_eq_self_iff.mpr hone]
  rw [hc, inner_const_one, inner_const_one, integral_constLp] at hi
  change F.starProjection f = _
  rw [hc, hi]

omit [IsProbabilityMeasure μ] in
lemma semigroup_average_eq_timeAverage (Φ : MeasurePreservingFlow X μ)
    (hΦ : StronglyContinuous Φ) (t : ℝ≥0) (f : Lp ℂ 2 μ) :
    ContinuousMeanErgodic.Spec.average (contractionSemigroup Φ hΦ) t f = timeAverage Φ t f := by
  unfold ContinuousMeanErgodic.Spec.average timeAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le t.coe_nonneg] at hs
  simp only [ContinuousMeanErgodic.Spec.orbit, contractionSemigroup,
    LinearIsometry.coe_toContinuousLinearMap, Real.coe_toNNReal _ hs.1]

/-- The continuous mean ergodic limit, identified as the integral of the initial vector. -/
theorem ergodic_time_means : Spec.ErgodicTimeMeans.{u} := by
  intro X _ μ _ Φ hΦ he f
  have h := ContinuousMeanErgodic.strong_convergence ℂ (Lp ℂ 2 μ) (contractionSemigroup Φ hΦ) f
  simpa only [semigroup_average_eq_timeAverage, fixedSpace_projection Φ hΦ he f] using h

/-! The real-valued argument is carried out on `Lp ℝ 2 μ` itself.
Every almost-everywhere composition equality below is taken separately at
each time, just as in the complex argument. -/
namespace RealL2

omit [IsProbabilityMeasure μ] in
lemma fixed_iff_ae (Φ : MeasurePreservingFlow X μ) (f : Lp ℝ 2 μ) (t : ℝ) :
    realPullback Φ t f = f ↔ (fun x => f (Φ.maps t x)) =ᵐ[μ] f := by
  constructor
  · intro h
    exact (Lp.coeFn_compMeasurePreserving f (Φ.measure_preserving t)).symm.trans
      (Filter.Eventually.of_forall (fun x => congrArg (fun g : Lp ℝ 2 μ => g x) h))
  · intro h
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving f (Φ.measure_preserving t)).trans h

lemma const_fixed (Φ : MeasurePreservingFlow X μ) (c : ℝ) (t : ℝ) :
    realPullback Φ t (Lp.const 2 μ c) = Lp.const 2 μ c := by
  apply (fixed_iff_ae Φ _ t).mpr
  exact ((Φ.measure_preserving t).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_const 2 μ c)).trans (Lp.coeFn_const 2 μ c).symm

omit [IsProbabilityMeasure μ] in
lemma ae_const_of_fixed (Φ : MeasurePreservingFlow X μ) (hΦ : Ergodic Φ)
    (f : Lp ℝ 2 μ) (hf : ∀ t : ℝ, realPullback Φ t f = f) :
    ∃ c : ℝ, f =ᵐ[μ] Function.const X c := by
  apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
  intro V hV
  have hm : NullMeasurableSet (f ⁻¹' V) μ :=
    (Lp.aestronglyMeasurable f).aemeasurable.nullMeasurable hV
  have hi (t : ℝ) : Φ.maps t ⁻¹' (f ⁻¹' V) =ᵐ[μ] f ⁻¹' V := by
    filter_upwards [(fixed_iff_ae Φ f t).mp (hf t)] with x hx
    simp only [Set.mem_preimage, hx]
  rcases hΦ _ hm hi with hz | hz
  · exact Or.inr (by simpa using (measure_eq_zero_iff_ae_notMem.mp hz))
  · exact Or.inl (by simpa using (measure_eq_zero_iff_ae_notMem.mp hz))

lemma constants_of_ergodic (Φ : MeasurePreservingFlow X μ) (hΦ : Ergodic Φ) :
    RealFixedVectorsAreConstants Φ := by
  intro f
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := ae_const_of_fixed Φ hΦ f hf
    exact ⟨c, Lp.ext (hc.trans (Lp.coeFn_const 2 μ c).symm)⟩
  · rintro ⟨c, rfl⟩
    exact const_fixed Φ c

lemma ergodic_of_constants (Φ : MeasurePreservingFlow X μ)
    (hΦ : RealFixedVectorsAreConstants Φ) : Ergodic Φ := by
  intro s hs hi
  let g : X → ℝ := s.indicator (fun _ => 1)
  have hg : MemLp g 2 μ := MemLp.indicator hs (memLp_const (1 : ℝ))
  let f : Lp ℝ 2 μ := hg.toLp g
  have hf : ∀ t : ℝ, realPullback Φ t f = f := by
    intro t
    apply (fixed_iff_ae Φ f t).mpr
    have hcomp := (Φ.measure_preserving t).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp
    filter_upwards [hcomp, hg.coeFn_toLp, hi t] with x hx hy hz
    change f (Φ.maps t x) = g (Φ.maps t x) at hx
    change f x = g x at hy
    rw [hx, hy]
    change (s.indicator (fun _ => (1 : ℝ))) (Φ.maps t x) = s.indicator (fun _ => 1) x
    have hmem : Φ.maps t x ∈ s ↔ x ∈ s := Iff.of_eq hz
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem (hmem.mpr hxs), Set.indicator_of_mem hxs]
    · rw [Set.indicator_of_notMem (mt hmem.mp hxs), Set.indicator_of_notMem hxs]
  obtain ⟨c, hc⟩ := (hΦ f).mp hf
  have hfc : f =ᵐ[μ] Function.const X c := by
    rw [hc]
    exact Lp.coeFn_const 2 μ c
  have hgc : g =ᵐ[μ] Function.const X c := hg.coeFn_toLp.symm.trans hfc
  by_cases hc0 : c = 0
  · left
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hgc] with x hx
    intro hxs
    simp [g, hxs, hc0] at hx
  · right
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hgc] with x hx
    intro hxs
    have hxs' : x ∉ s := hxs
    exact hc0 (by simpa [g, hxs'] using hx.symm)

/-- The fixed-space criterion needs no continuity assumption. -/
theorem fixed_space_characterization : Spec.RealFixedSpaceCharacterization.{u} := by
  intro X _ μ _ Φ
  exact ⟨ergodic_of_constants Φ, constants_of_ergodic Φ⟩

open ExpandedFA.Ergodic

/-- Restrict the orthogonal real flow to the nonnegative-time contraction semigroup. -/
def contractionSemigroup (Φ : MeasurePreservingFlow X μ) (hΦ : RealStronglyContinuous Φ) :
    ContinuousMeanErgodic.Spec.ContractionSemigroup ℝ (Lp ℝ 2 μ) where
  op s := (realPullback Φ (s : ℝ)).toContinuousLinearMap
  zero := by
    apply ContinuousLinearMap.ext
    intro f
    exact realPullback_zero Φ f
  add s t := by
    apply ContinuousLinearMap.ext
    intro f
    exact realPullback_add Φ s t f
  continuous f := (hΦ f).comp NNReal.continuous_coe
  norm_le s := (realPullback Φ (s : ℝ)).norm_toContinuousLinearMap_le

omit [IsProbabilityMeasure μ] in
/-- Inverse time shows that fixing every nonnegative time fixes every real time. -/
lemma fixed_of_nonnegative (Φ : MeasurePreservingFlow X μ) (f : Lp ℝ 2 μ)
    (hf : ∀ s : ℝ≥0, realPullback Φ (s : ℝ) f = f) :
    ∀ t : ℝ, realPullback Φ t f = f := by
  intro t
  by_cases ht : 0 ≤ t
  · exact hf ⟨t, ht⟩
  · have hn : 0 ≤ -t := by linarith
    have h := hf ⟨-t, hn⟩
    calc
      realPullback Φ t f = realPullback Φ t (realPullback Φ (-t) f) := congrArg (realPullback Φ t) h.symm
      _ = f := by rw [← realPullback_add, add_neg_cancel, realPullback_zero]

omit [IsProbabilityMeasure μ] in
lemma mem_semigroup_fixedSpace (Φ : MeasurePreservingFlow X μ) (hΦ : RealStronglyContinuous Φ)
    (f : Lp ℝ 2 μ) :
    f ∈ ContinuousMeanErgodic.Spec.fixedSpace (contractionSemigroup Φ hΦ) ↔
      ∀ t : ℝ, realPullback Φ t f = f := by
  rw [ContinuousMeanErgodic.mem_fixedSpace]
  exact ⟨fixed_of_nonnegative Φ f, fun h s => h s⟩

lemma inner_const_one (f : Lp ℝ 2 μ) :
    ⟪Lp.const 2 μ (1 : ℝ), f⟫_ℝ = ∫ x, f x ∂μ := by
  simpa using L2.inner_indicatorConstLp_one (μ := μ) MeasurableSet.univ
    (measure_ne_top μ Set.univ) f

lemma integral_constLp (c : ℝ) : ∫ x, (Lp.const 2 μ c) x ∂μ = c := by
  rw [integral_congr_ae (Lp.coeFn_const 2 μ c)]
  change (∫ _ : X, c ∂μ) = c
  simp

/-- For probability measure the orthogonal projection onto constants is integration. -/
lemma fixedSpace_projection (Φ : MeasurePreservingFlow X μ) (hΦ : RealStronglyContinuous Φ)
    (he : Ergodic Φ) (f : Lp ℝ 2 μ) :
    (ContinuousMeanErgodic.Spec.fixedSpace (contractionSemigroup Φ hΦ)).toSubmodule.starProjection f =
      Lp.const 2 μ (∫ x, f x ∂μ) := by
  let F := (ContinuousMeanErgodic.Spec.fixedSpace (contractionSemigroup Φ hΦ)).toSubmodule
  have hp : ∀ t : ℝ, realPullback Φ t (F.starProjection f) = F.starProjection f :=
    (mem_semigroup_fixedSpace Φ hΦ _).mp (F.starProjection_apply_mem f)
  obtain ⟨c, hc⟩ := (constants_of_ergodic Φ he (F.starProjection f)).mp hp
  have hone : Lp.const 2 μ (1 : ℝ) ∈ F :=
    (mem_semigroup_fixedSpace Φ hΦ _).mpr (const_fixed Φ 1)
  have hi : ⟪Lp.const 2 μ (1 : ℝ), F.starProjection f⟫_ℝ =
      ⟪Lp.const 2 μ (1 : ℝ), f⟫_ℝ := by
    rw [← F.inner_starProjection_left_eq_right,
      F.starProjection_eq_self_iff.mpr hone]
  rw [hc, inner_const_one, inner_const_one, integral_constLp] at hi
  change F.starProjection f = _
  rw [hc, hi]

omit [IsProbabilityMeasure μ] in
lemma semigroup_average_eq_realTimeAverage (Φ : MeasurePreservingFlow X μ)
    (hΦ : RealStronglyContinuous Φ) (t : ℝ≥0) (f : Lp ℝ 2 μ) :
    ContinuousMeanErgodic.Spec.average (contractionSemigroup Φ hΦ) t f = realTimeAverage Φ t f := by
  unfold ContinuousMeanErgodic.Spec.average realTimeAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le t.coe_nonneg] at hs
  simp only [ContinuousMeanErgodic.Spec.orbit, contractionSemigroup,
    LinearIsometry.coe_toContinuousLinearMap, Real.coe_toNNReal _ hs.1]

/-- The continuous mean ergodic limit, identified as the integral of the initial vector. -/
theorem ergodic_time_means : Spec.RealErgodicTimeMeans.{u} := by
  intro X _ μ _ Φ hΦ he f
  have h := ContinuousMeanErgodic.strong_convergence ℝ (Lp ℝ 2 μ) (contractionSemigroup Φ hΦ) f
  simpa only [semigroup_average_eq_realTimeAverage, fixedSpace_projection Φ hΦ he f] using h

end RealL2

/-- Real-valued fixed vectors are constants exactly for ergodic flows. -/
theorem real_fixed_space_characterization : Spec.RealFixedSpaceCharacterization.{u} :=
  RealL2.fixed_space_characterization

/-- The genuine real Bochner averages converge in real-valued L². -/
theorem real_ergodic_time_means : Spec.RealErgodicTimeMeans.{u} :=
  RealL2.ergodic_time_means

end ExpandedFA.Models.KoopmanErgodicMeans
