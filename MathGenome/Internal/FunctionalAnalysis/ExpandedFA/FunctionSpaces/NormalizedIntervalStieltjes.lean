import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.NormalizedIntervalStieltjes
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BVMeasureBridge
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov

namespace ExpandedFA.FunctionSpaces.NormalizedIntervalStieltjes
open Set MeasureTheory Filter
open scoped Topology ENNReal ZeroAtInfty
open NormalizedIntervalStieltjesSpec BVMeasureBridgeSpec ScalarRieszMarkovSpec
variable {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}

lemma normalized_eq_cumulative (ν : VectorMeasure (Icc a b) 𝕜)
    {t : ℝ} (ht : a < t) : normalizedIntegrator ν t = cumulative (extendByZero ν) t := by
  simp only [normalizedIntegrator, ite_eq_right (not_le.mpr ht), cumulative,
    extendByZero, VectorMeasure.map_apply _ measurable_subtype_coe measurableSet_Iic]
  rfl

lemma cumulative_zero (ν : VectorMeasure (Icc a b) 𝕜) {t : ℝ} (ht : t < a) :
    cumulative (extendByZero ν) t = 0 := by
  rw [cumulative, extendByZero,
    VectorMeasure.map_apply _ measurable_subtype_coe measurableSet_Iic]
  have h : (Subtype.val : Icc a b → ℝ) ⁻¹' Iic t = ∅ := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
    exact not_le.mpr (ht.trans_le x.property.1)
  rw [h, VectorMeasure.empty]

lemma cumulative_constant (ν : VectorMeasure (Icc a b) 𝕜) {t : ℝ} (ht : b ≤ t) :
    cumulative (extendByZero ν) t = ν univ := by
  rw [cumulative, extendByZero,
    VectorMeasure.map_apply _ measurable_subtype_coe measurableSet_Iic]
  congr 1
  ext x
  simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
  exact x.property.2.trans ht

/-- Replacing the value at a by zero amounts to a monotone change of parameter
in the global cumulative function. -/
lemma normalized_variation_le (ν : VectorMeasure (Icc a b) 𝕜)
    [IsFiniteMeasure ν.variation] :
    eVariationOn (normalizedIntegrator ν) univ ≤ ν.variation univ := by
  have : IsFiniteMeasure (extendByZero ν).variation := by unfold extendByZero; infer_instance
  let φ : ℝ → ℝ := fun t => if t ≤ a then a-1 else t
  have hφ : Monotone φ := by
    intro x y hxy
    by_cases hx : x ≤ a <;> by_cases hy : y ≤ a <;> simp only [φ, hx, hy, ite_true, ite_false]
    · exact le_rfl
    · linarith
    · exact (hx (hxy.trans hy)).elim
    · exact hxy
  have heq : normalizedIntegrator ν = cumulative (extendByZero ν) ∘ φ := by
    funext t
    by_cases ht : t ≤ a
    · simp only [normalizedIntegrator, ht, ite_true, Function.comp_apply, φ]
      exact (cumulative_zero ν (by linarith : a-1 < a)).symm
    · simp only [Function.comp_apply, φ, ht, ite_false]
      exact normalized_eq_cumulative ν (lt_of_not_ge ht)
  rw [heq]
  have hval : MeasurableEmbedding (Subtype.val : Icc a b → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  calc
    _ ≤ eVariationOn (cumulative (extendByZero ν)) univ :=
      eVariationOn.comp_le_of_monotoneOn _ φ (hφ.monotoneOn univ) (mapsTo_univ _ _)
    _ = (extendByZero ν).variation univ := BVMeasureBridge.cumulative_variation _
    _ = ν.variation univ := by
      rw [extendByZero, hval.variation_map, Measure.map_apply hval.measurable MeasurableSet.univ,
        preimage_univ]

lemma normalized_tendsto_right (ν : VectorMeasure (Icc a b) 𝕜)
    [IsFiniteMeasure ν.variation] {t : ℝ} (ht : a ≤ t) :
    Tendsto (normalizedIntegrator ν) (𝓝[>] t)
      (𝓝 (cumulative (extendByZero ν) t)) := by
  have : IsFiniteMeasure (extendByZero ν).variation := by unfold extendByZero; infer_instance
  apply ((BVMeasureBridge.cumulative_rightContinuous (extendByZero ν) t).mono
    Ioi_subset_Ici_self).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (normalized_eq_cumulative ν (ht.trans_lt hx)).symm

lemma normalized_rightLim (ν : VectorMeasure (Icc a b) 𝕜)
    [IsFiniteMeasure ν.variation] :
    (normalizedIntegrator ν).rightLim = cumulative (extendByZero ν) := by
  funext t
  apply rightLim_eq_of_tendsto
  by_cases ht : a ≤ t
  · exact normalized_tendsto_right ν ht
  · have hta : t < a := lt_of_not_ge ht
    rw [cumulative_zero ν hta]
    apply tendsto_const_nhds.congr'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hta)] with x hx
    simp [normalizedIntegrator, (show x < a from hx).le]

lemma normalized_global_variation (ν : VectorMeasure (Icc a b) 𝕜)
    [IsFiniteMeasure ν.variation] :
    eVariationOn (normalizedIntegrator ν) univ = ν.variation univ := by
  apply le_antisymm (normalized_variation_le ν)
  have : IsFiniteMeasure (extendByZero ν).variation := by unfold extendByZero; infer_instance
  have h := eVariationOn.eVariationOn_rightLim_le (f := normalizedIntegrator ν) isOpen_univ
  rw [normalized_rightLim, BVMeasureBridge.cumulative_variation] at h
  have hval : MeasurableEmbedding (Subtype.val : Icc a b → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  simpa only [extendByZero, hval.variation_map,
    Measure.map_apply hval.measurable MeasurableSet.univ, preimage_univ] using h

lemma normalized_interval_variation (hab : a < b) (ν : VectorMeasure (Icc a b) 𝕜)
    [IsFiniteMeasure ν.variation] :
    eVariationOn (normalizedIntegrator ν) (Icc a b) = ν.variation univ := by
  apply le_antisymm ((eVariationOn.mono _ (subset_univ _)).trans (normalized_variation_le ν))
  rw [← normalized_global_variation ν]
  let φ : ℝ → ℝ := fun t => max a (min t b)
  have hφ : Monotone φ := monotone_const.max (monotone_id.min monotone_const)
  have hmap : MapsTo φ univ (Icc a b) := by
    intro t _
    exact ⟨le_max_left _ _, max_le hab.le (min_le_right _ _)⟩
  have heq : normalizedIntegrator ν = normalizedIntegrator ν ∘ φ := by
    funext t
    dsimp [Function.comp_def, φ]
    rcases le_or_gt t a with ht | ht
    · rw [max_eq_left (min_le_left _ _ |>.trans ht)]
      simp [normalizedIntegrator, ht]
    · rcases le_or_gt t b with hb | hb
      · rw [min_eq_left hb, max_eq_right ht.le]
      · rw [min_eq_right hb.le, max_eq_right hab.le]
        rw [normalized_eq_cumulative ν ht, normalized_eq_cumulative ν hab,
          cumulative_constant ν hb.le, cumulative_constant ν le_rfl]
  calc
    _ = eVariationOn (normalizedIntegrator ν ∘ φ) univ := congrArg (fun f => eVariationOn f univ) heq
    _ ≤ _ := eVariationOn.comp_le_of_monotoneOn _ φ (hφ.monotoneOn univ) hmap


lemma cumulative_at_left (ν : VectorMeasure (Icc a b) 𝕜) :
    cumulative (extendByZero ν) a = ν {x | (x : ℝ) = a} := by
  rw [cumulative, extendByZero,
    VectorMeasure.map_apply _ measurable_subtype_coe measurableSet_Iic]
  congr 1
  ext x
  simp only [mem_preimage, mem_Iic, mem_ofPred_eq]
  exact ⟨fun h => le_antisymm h x.property.1, fun h => h.le⟩

/-- Normalization, exact interval variation, interior right continuity, and
both formulations of the left endpoint jump. -/
theorem measure_properties : MeasureProperties := by
  intro 𝕜 _ a b hab ν hν
  have : IsFiniteMeasure ν.variation := hν
  have : IsFiniteMeasure (extendByZero ν).variation := by unfold extendByZero; infer_instance
  have hzero : normalizedIntegrator ν a = 0 := by simp [normalizedIntegrator]
  have hvar := normalized_interval_variation hab ν
  have htend : Tendsto (normalizedIntegrator ν) (𝓝[>] a)
      (𝓝 (ν {x | (x : ℝ) = a})) := by
    rw [← cumulative_at_left]
    exact normalized_tendsto_right ν le_rfl
  refine ⟨hzero, (fun t ht => by simp [normalizedIntegrator, not_le.mpr ht.1]),
    (by rw [BoundedVariationOn, hvar]; exact measure_ne_top _ _), hvar, ?_, htend, ?_⟩
  · intro t ht
    apply (BVMeasureBridge.cumulative_rightContinuous (extendByZero ν) t).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact normalized_eq_cumulative ν (ht.1.trans_le hx)
    · exact normalized_eq_cumulative ν ht.1
  · rw [rightLim_eq_of_tendsto htend, hzero, sub_zero]

namespace IntervalPartition
variable (p : IntervalPartition a b)

lemma cells_pos (i : ℕ) (hi : i < p.n) : p.point i < p.point (i+1) :=
  p.strict (by exact hi.le) (by exact hi) (Nat.lt_succ_self _)

lemma point_gt_left (i : ℕ) (hi : i ≤ p.n) (hi0 : 0 < i) : a < p.point i := by
  simpa only [p.first] using p.strict (Nat.zero_le _) hi hi0

lemma n_pos (hab : a < b) : 0 < p.n := by
  by_contra hn
  have hn0 : p.n = 0 := by omega
  have : a = b := p.first.symm.trans (hn0 ▸ p.last)
  exact hab.ne this

end IntervalPartition

/-- The exact difference between ordinary interval sums and the upstream
atom-separated sums. Only the tag of the first cell changes the atom term. -/
lemma standardSum_eq (hab : a < b) (ν : VectorMeasure (Icc a b) 𝕜)
    (p : IntervalPartition a b) (f : ℝ → 𝕜) :
    standardSum p (normalizedIntegrator ν) f =
      stieltjesSum p.toTaggedPartition (fun t => ν {x | (x : ℝ) ≤ t}) f +
      (f (p.tag 0) - f a) * ν {x | (x : ℝ) ≤ a} := by
  classical
  let F : ℝ → 𝕜 := fun t => ν {x | (x : ℝ) ≤ t}
  have hterm (i : ℕ) (hi : i ∈ Finset.range p.n) :
      f (p.tag i) * (normalizedIntegrator ν (p.point (i+1)) - normalizedIntegrator ν (p.point i)) =
        f (p.tag i) * (F (p.point (i+1)) - F (p.point i)) +
          if i = 0 then f (p.tag 0) * F a else 0 := by
    have hi' : i < p.n := Finset.mem_range.mp hi
    have hn : a < p.point (i+1) := IntervalPartition.point_gt_left p _ hi' (Nat.zero_lt_succ _)
    simp only [normalizedIntegrator, not_le.mpr hn, ite_false]
    by_cases hi0 : i = 0
    · subst i
      simp only [p.first, le_refl, ite_true]
      dsimp [F]
      ring
    · have hleft : a < p.point i := IntervalPartition.point_gt_left p i hi'.le (Nat.pos_of_ne_zero hi0)
      simp only [not_le.mpr hleft, ite_false, hi0, add_zero]
      rfl
  unfold standardSum
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hn : 0 ∈ Finset.range p.n := Finset.mem_range.mpr (IntervalPartition.n_pos p hab)
  simp only [Finset.sum_ite_eq', hn, ite_true]
  unfold stieltjesSum
  dsimp [F]
  ring


/-- Ordinary tagged sums converge, retaining the atom at a in the first cell. -/
theorem tagged_convergence : TaggedConvergence := by
  intro 𝕜 _ a b hab ν hν f
  have : IsFiniteMeasure ν.variation := hν
  obtain ⟨hfint, hconv⟩ := BVMeasureBridge.subtype_stieltjes_functional 𝕜 a b ν hν f
  refine ⟨hfint, ?_⟩
  intro ε hε
  obtain ⟨δ₁, hδ₁, hsum⟩ := hconv (ε/2) (by linarith)
  let f' := intervalIntegrand f
  let c := ν {x | (x : ℝ) ≤ a}
  let η := (ε/2) / (‖c‖+1)
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  obtain ⟨δ₂, hδ₂, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (BVMeasureBridge.intervalIntegrand_continuousOn f)) η hη
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro p hp
  have hn : 0 < p.n := IntervalPartition.n_pos p hab
  have htag := p.tag_mem 0 hn
  have htagmem := BVMeasureBridge.TaggedPartition.tag_mem_interval p.toTaggedPartition 0 hn
  have hd : dist (p.tag 0) a < δ₂ := by
    rw [Real.dist_eq]
    have hmesh := (hp 0 hn).trans_le (min_le_right _ _)
    simp only [p.first] at htag hmesh
    rw [abs_of_nonneg (sub_nonneg.mpr htag.1)]
    linarith [htag.2]
  have hsmall : ‖f' (p.tag 0) - f' a‖ < η := by
    rw [← dist_eq_norm]
    exact hmod _ htagmem _ ⟨le_rfl, hab.le⟩ hd
  have hcorrection : ‖(f' (p.tag 0) - f' a) * c‖ < ε/2 := by
    rw [norm_mul]
    calc
      _ ≤ η * ‖c‖ := mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg _)
      _ < η * (‖c‖+1) := mul_lt_mul_of_pos_left (by linarith) hη
      _ = ε/2 := div_mul_cancel₀ _ (by positivity : ‖c‖+1 ≠ 0)
  have hs := hsum p.toTaggedPartition (fun i hi => (hp i hi).trans_le (min_le_left _ _))
  rw [standardSum_eq hab]
  change ‖(stieltjesSum p.toTaggedPartition (fun t => ν {x | (x : ℝ) ≤ t}) f' +
    (f' (p.tag 0) - f' a) * c) - scalarIntegral ν f‖ < ε
  calc
    _ = ‖(stieltjesSum p.toTaggedPartition (fun t => ν {x | (x : ℝ) ≤ t}) f' - scalarIntegral ν f) +
        (f' (p.tag 0) - f' a) * c‖ := by congr 1; ring
    _ ≤ ‖stieltjesSum p.toTaggedPartition (fun t => ν {x | (x : ℝ) ≤ t}) f' - scalarIntegral ν f‖ +
        ‖(f' (p.tag 0) - f' a) * c‖ := norm_add_le _ _
    _ < ε/2 + ε/2 := add_lt_add hs hcorrection
    _ = ε := by ring


lemma functional_representation_of_scalarRepresentation {𝕜 : Type} [RCLike 𝕜]
    (hR : ScalarRepresentation.{0} 𝕜) : FunctionalRepresentation 𝕜 := by
  intro a b hab L
  obtain ⟨e, he, _⟩ := ScalarRieszMarkov.compact_identification (Icc a b) 𝕜
  let M : C₀(Icc a b, 𝕜) →L[𝕜] 𝕜 := L.comp e.symm.toLinearIsometry.toContinuousLinearMap
  have hMnorm : ‖M‖ = ‖L‖ := by
    apply le_antisymm
    · apply M.opNorm_le_bound (norm_nonneg L)
      intro f
      simpa only [M, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
        LinearIsometryEquiv.norm_map] using L.le_opNorm (e.symm f)
    · apply L.opNorm_le_bound (norm_nonneg M)
      intro f
      simpa only [M, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
        e.symm_apply_apply, e.norm_map] using M.le_opNorm (e f)
  obtain ⟨ν, hν, hrep, hnorm, _⟩ := hR (Icc a b) M
  have : IsFiniteMeasure ν.variation := ⟨hν.1⟩
  have hcoe (f : C(Icc a b, 𝕜)) : ⇑(e f) = ⇑f := funext (he f)
  have hrep' (f : C(Icc a b, 𝕜)) : Integrable f ν.variation ∧ L f = scalarIntegral ν f := by
    have h := hrep (e f)
    simpa only [M, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      e.symm_apply_apply, hcoe f] using h
  obtain ⟨hz, _, hbv, hvar, hrc, _, hjump⟩ := measure_properties 𝕜 a b hab ν inferInstance
  refine ⟨ν, hν, hz, hbv, ?_, hrep', ?_, hrc, hjump⟩
  · rw [hvar]
    exact hnorm.symm.trans hMnorm
  · intro f ε hε
    simpa only [(hrep' f).2] using (tagged_convergence 𝕜 a b hab ν inferInstance f).2 ε hε

/-- The real continuous-dual normalized Riemann–Stieltjes representation. -/
theorem real_functional_representation : FunctionalRepresentation ℝ :=
  functional_representation_of_scalarRepresentation ScalarRieszMarkov.real_representation

/-- The complex scalar-linear version, with no conjugation in the sums or integral. -/
theorem complex_functional_representation : FunctionalRepresentation ℂ :=
  functional_representation_of_scalarRepresentation ScalarRieszMarkov.complex_representation

end ExpandedFA.FunctionSpaces.NormalizedIntervalStieltjes
