import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BVMeasureBridge
import Mathlib.Order.Interval.Set.Union
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

namespace ExpandedFA.FunctionSpaces.BVMeasureBridge
open Set MeasureTheory Filter
open scoped Topology ENNReal
open BVMeasureBridgeSpec ScalarRieszMarkovSpec
variable {𝕜 : Type*} [RCLike 𝕜]

lemma cumulative_increment (ν : VectorMeasure ℝ 𝕜) {s t : ℝ} (h : s ≤ t) :
    ν (Ioc s t) = cumulative ν t - cumulative ν s := by
  rw [cumulative, cumulative, ← VectorMeasure.of_sdiff (v := ν) measurableSet_Iic
    measurableSet_Iic (Iic_subset_Iic.mpr h), Iic_sdiff_Iic]

lemma cumulative_variation_le (ν : VectorMeasure ℝ 𝕜) :
    eVariationOn (cumulative ν) univ ≤ ν.variation univ := by
  simp only [eVariationOn, iSup_le_iff, Prod.forall, Subtype.forall, and_imp,
    edist_eq_enorm_sub]
  intro n u hu _
  calc
    (∑ i ∈ Finset.range n, ‖cumulative ν (u (i+1)) - cumulative ν (u i)‖ₑ) ≤
        ∑ i ∈ Finset.range n, ν.variation (Ioc (u i) (u (i+1))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← cumulative_increment ν (hu (Nat.le_succ i))]
      exact VectorMeasure.enorm_measure_le_variation ν _
    _ = ν.variation (⋃ i ∈ Finset.range n, Ioc (u i) (u (i+1))) := by
      rw [measure_biUnion_finset ?_ (fun _ _ => measurableSet_Ioc)]
      rintro i _ j _ hij
      simp only [Function.onFun]
      rcases lt_or_gt_of_ne hij with h | h
      · exact disjoint_left.mpr (by intro x hx hy; have := hu (Nat.succ_le_of_lt h); grind)
      · exact disjoint_left.mpr (by intro x hx hy; have := hu (Nat.succ_le_of_lt h); grind)
    _ ≤ ν.variation univ := measure_mono (subset_univ _)

lemma cumulative_bv (ν : VectorMeasure ℝ 𝕜) [IsFiniteMeasure ν.variation] :
    BoundedVariationOn (cumulative ν) univ :=
  ne_top_of_le_ne_top (measure_ne_top _ _) (cumulative_variation_le ν)

lemma scalarIntegral_indicator (ν : VectorMeasure ℝ 𝕜) [IsFiniteMeasure ν.variation]
    (s : Set ℝ) (hs : MeasurableSet s) (c : 𝕜) :
    scalarIntegral ν (s.indicator (fun _ => c)) = c * ν s := by
  exact VectorMeasure.integral_indicator_const c hs

lemma cumulative_rightContinuous (ν : VectorMeasure ℝ 𝕜) [IsFiniteMeasure ν.variation]
    (t : ℝ) : ContinuousWithinAt (cumulative ν) (Ici t) t := by
  have heq : cumulative ν = fun t => scalarIntegral ν ((Iic t).indicator (fun _ => (1 : 𝕜))) := by
    funext t
    simp [scalarIntegral_indicator, cumulative]
  rw [heq]
  apply VectorMeasure.continuousWithinAt_of_dominated (bound := fun _ => (1 : ℝ))
  · exact Eventually.of_forall fun x => (stronglyMeasurable_const.indicator measurableSet_Iic).aestronglyMeasurable
  · exact Eventually.of_forall fun x => Eventually.of_forall fun y => by
      by_cases hy : y ≤ x <;> simp [hy]
  · exact integrable_const _
  · apply Eventually.of_forall
    intro y
    by_cases h : y ≤ t
    · apply (continuousWithinAt_const (b := (1 : 𝕜))).congr_of_eventuallyEq _ (by simp [h])
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp [h.trans hx]
    · have hy : t < y := lt_of_not_ge h
      apply (continuousWithinAt_const (b := (0 : 𝕜))).congr_of_eventuallyEq _ (by simp [h])
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hy)] with x hx
      simp [not_le.mpr (show x < y from hx)]

/-- Equality on half-open intervals determines a scalar measure on the line. -/
lemma ext_of_Ioc (μ ν : VectorMeasure ℝ 𝕜)
    (h : ∀ s t, s ≤ t → μ (Ioc s t) = ν (Ioc s t)) : μ = ν := by
  have hcover : (⋃ n : ℕ, Ioc (-(n : ℝ)) (n : ℝ)) = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    simp only [mem_iUnion, mem_Ioc]
    exact ⟨n, by have := neg_abs_le x; linarith, (le_abs_self x).trans hn.le⟩
  have hmono : Monotone (fun n : ℕ => Ioc (-(n : ℝ)) (n : ℝ)) := by
    intro m n hmn
    exact Ioc_subset_Ioc (neg_le_neg (Nat.cast_le.mpr hmn)) (Nat.cast_le.mpr hmn)
  apply VectorMeasure.ext_of_generateFrom
    {S : Set ℝ | ∃ s t, s < t ∧ Ioc s t = S}
    (by rintro S ⟨s, t, hst, rfl⟩; exact h s t hst.le)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc ℝ))
    (isPiSystem_Ioc id id)
  have hμ := μ.tendsto_vectorMeasure_iUnion_atTop_nat hmono (fun _ => measurableSet_Ioc)
  have hν := ν.tendsto_vectorMeasure_iUnion_atTop_nat hmono (fun _ => measurableSet_Ioc)
  rw [hcover] at hμ hν
  apply tendsto_nhds_unique hμ
  convert hν using 1
  funext n
  exact h _ _ (neg_nonpos.mpr (Nat.cast_nonneg n) |>.trans (Nat.cast_nonneg n))

lemma cumulative_injective (μ ν : VectorMeasure ℝ 𝕜)
    (h : ∀ t, cumulative μ t = cumulative ν t) : μ = ν := by
  apply ext_of_Ioc
  intro s t hst
  rw [cumulative_increment μ hst, cumulative_increment ν hst, h, h]

lemma cumulative_vectorMeasure (ν : VectorMeasure ℝ 𝕜) [IsFiniteMeasure ν.variation] :
    (cumulative_bv ν).vectorMeasure = ν := by
  apply ext_of_Ioc
  intro s t hst
  rw [(cumulative_bv ν).vectorMeasure_Ioc hst,
    (cumulative_rightContinuous ν t).rightLim_eq,
    (cumulative_rightContinuous ν s).rightLim_eq, cumulative_increment ν hst]

lemma cumulative_variation (ν : VectorMeasure ℝ 𝕜) [IsFiniteMeasure ν.variation] :
    eVariationOn (cumulative ν) univ = ν.variation univ := by
  apply le_antisymm (cumulative_variation_le ν)
  have h := (cumulative_bv ν).variation_vectorMeasure_univ_le
  rwa [cumulative_vectorMeasure ν] at h

lemma intervalCumulative_zero (a b : ℝ) (ν : VectorMeasure ℝ 𝕜)
    {t : ℝ} (ht : t < a) : intervalCumulative a b ν t = 0 := by
  unfold intervalCumulative cumulative
  rw [VectorMeasure.restrict_apply _ measurableSet_Icc measurableSet_Iic]
  have : Iic t ∩ Icc a b = ∅ := by ext x; simp; grind
  simp [this]

lemma intervalCumulative_constant (a b : ℝ) (ν : VectorMeasure ℝ 𝕜)
    {t : ℝ} (ht : b ≤ t) : intervalCumulative a b ν t = ν (Icc a b) := by
  unfold intervalCumulative cumulative
  rw [VectorMeasure.restrict_apply _ measurableSet_Icc measurableSet_Iic,
    inter_eq_right.mpr (fun x hx => hx.2.trans ht)]

/-- The entire forward bridge, including the exact total variation identity. -/
theorem forward_bridge : ForwardBridge := by
  intro 𝕜 _ a b ν hν
  have : IsFiniteMeasure ν.variation := hν
  refine ⟨cumulative_rightContinuous _, cumulative_bv _, (fun t ht => intervalCumulative_zero a b ν ht),
    (fun t ht => intervalCumulative_constant a b ν ht), (fun s t hst => cumulative_increment _ hst), ?_⟩
  unfold intervalCumulative
  rw [cumulative_variation, VectorMeasure.variation_restrict measurableSet_Icc,
    Measure.restrict_apply_univ]

lemma normalized_cumulative {a b : ℝ} {F : ℝ → 𝕜} (hF : NormalizedBV a b F) :
    ∀ t, cumulative hF.2.1.vectorMeasure t = F t := by
  have hbot : Tendsto F atBot (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot a] with t ht
    exact (hF.2.2.1 t ht).symm
  have hlim : limUnder atBot F = 0 := tendsto_nhds_unique hF.2.1.tendsto_atBot_limUnder hbot
  intro t
  simp only [cumulative, hF.2.1.vectorMeasure_Iic, (hF.1 t).rightLim_eq, hlim, sub_zero]

lemma normalized_support {a b : ℝ} {F : ℝ → 𝕜} (hF : NormalizedBV a b F) :
    hF.2.1.vectorMeasure.restrict (Icc a b) = hF.2.1.vectorMeasure := by
  have hleft : eVariationOn F (Iio a) = 0 := by
    apply eVariationOn.constant_on
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hF.2.2.1 x hx, hF.2.2.1 y hy]
  have hright : eVariationOn F (Ioi b) = 0 := by
    apply eVariationOn.constant_on
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hF.2.2.2 x hx.le, hF.2.2.2 y hy.le]
  have hzero : hF.2.1.vectorMeasure.variation (Icc a b)ᶜ = 0 := by
    have hc : (Icc a b)ᶜ = Iio a ∪ Ioi b := by ext x; simp only [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi]; push Not; grind
    apply le_antisymm _ bot_le
    rw [hc]
    exact (measure_union_le _ _).trans (by
      have hl := hF.2.1.variation_vectorMeasure_Iio_le (a := a)
      have hr := hF.2.1.variation_vectorMeasure_Ioi_le (a := b)
      rw [hleft] at hl
      rw [hright] at hr
      simpa using add_le_add hl hr)
  have hrestrict : hF.2.1.vectorMeasure.restrict (Icc a b)ᶜ = 0 := by
    apply VectorMeasure.ext
    intro s hs
    rw [VectorMeasure.restrict_apply _ measurableSet_Icc.compl hs,
      zero_apply]
    apply enorm_eq_zero.mp
    apply le_antisymm _ bot_le
    exact (VectorMeasure.enorm_measure_le_variation _ _).trans
      ((measure_mono inter_subset_right).trans hzero.le)
  have := VectorMeasure.restrict_add_restrict_compl (v := hF.2.1.vectorMeasure)
    (i := Icc a b) measurableSet_Icc
  simpa [hrestrict] using this

/-- Construction, support, exact variation, interval increments and uniqueness
for every normalized right-continuous scalar BV function. -/
theorem converse_bridge : ConverseBridge := by
  intro 𝕜 _ a b F hF
  refine ⟨hF.2.1.vectorMeasure, inferInstance, normalized_support hF,
    normalized_cumulative hF, ?_, ?_, ?_⟩
  · have heq : cumulative hF.2.1.vectorMeasure = F := funext (normalized_cumulative hF)
    exact (congrArg (fun G => eVariationOn G univ) heq).symm.trans (cumulative_variation _)
  · intro s t hst
    rw [hF.2.1.vectorMeasure_Ioc hst, (hF.1 s).rightLim_eq, (hF.1 t).rightLim_eq]
  · intro η _ hη
    apply cumulative_injective
    intro t
    exact (hη t).trans (normalized_cumulative hF t).symm

/-- Transport from measures on the actual closed-interval subtype to their
zero extensions; both variation and scalar integration are preserved. -/
theorem subtype_bridge : SubtypeBridge := by
  intro 𝕜 _ a b ν hν
  have : IsFiniteMeasure ν.variation := hν
  have hval : MeasurableEmbedding (Subtype.val : Icc a b → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hsupport : (extendByZero ν).restrict (Icc a b) = extendByZero ν := by
    apply VectorMeasure.ext
    intro s hs
    rw [VectorMeasure.restrict_apply _ measurableSet_Icc hs]
    simp only [extendByZero, VectorMeasure.map_apply _ hval.measurable (hs.inter measurableSet_Icc),
      VectorMeasure.map_apply _ hval.measurable hs]
    congr 1
    ext x
    exact and_iff_left x.property
  refine ⟨(by dsimp [extendByZero]; infer_instance), hsupport, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact VectorMeasure.map_apply ν hval.measurable hs
  · intro t
    unfold intervalCumulative cumulative
    rw [hsupport]
    exact VectorMeasure.map_apply ν hval.measurable measurableSet_Iic
  · rw [extendByZero, hval.variation_map, Measure.map_apply hval.measurable measurableSet_Icc]
    have hpre : (Subtype.val : Icc a b → ℝ) ⁻¹' Icc a b = univ := by
      ext x; simp
    rw [hpre]
  · intro f
    exact hval.integral_map_vectorMeasure

/-- The paper's cumulative function for the original interval measure. -/
theorem subtype_forward_bridge : SubtypeForwardBridge := by
  intro 𝕜 _ a b ν hν
  have hsub := subtype_bridge 𝕜 a b ν hν
  have heq : intervalCumulative a b (extendByZero ν) =
      fun t => ν {x | (x : ℝ) ≤ t} := funext hsub.2.2.2.1
  have hmass : extendByZero ν (Icc a b) = ν univ := by
    simpa using hsub.2.2.1 (Icc a b) measurableSet_Icc
  simpa only [heq, hmass, hsub.2.1, hsub.2.2.2.2.1] using
    (forward_bridge 𝕜 a b (extendByZero ν) hsub.1)

lemma extendByZero_injective {a b : ℝ} (ν η : VectorMeasure (Icc a b) 𝕜)
    (h : extendByZero ν = extendByZero η) : ν = η := by
  have hval : MeasurableEmbedding (Subtype.val : Icc a b → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  apply VectorMeasure.ext
  intro s hs
  have heq := congrArg (fun μ : VectorMeasure ℝ 𝕜 => μ (Subtype.val '' s)) h
  simpa only [extendByZero, VectorMeasure.map_apply _ hval.measurable
    (hval.measurableSet_image.mpr hs), preimage_image_eq _ hval.injective] using heq

/-- Every supported ambient measure is a zero extension of an interval measure.
Projection onto the interval gives its inverse, when the interval is nonempty. -/
lemma exists_intervalMeasure (a b : ℝ) (μ : VectorMeasure ℝ 𝕜)
    [IsFiniteMeasure μ.variation] (hsupport : μ.restrict (Icc a b) = μ) :
    ∃ ν : VectorMeasure (Icc a b) 𝕜,
      IsFiniteMeasure ν.variation ∧ extendByZero ν = μ := by
  by_cases hab : a ≤ b
  · have hproj : Measurable (projIcc a b hab) := continuous_projIcc.measurable
    have hval : MeasurableEmbedding (Subtype.val : Icc a b → ℝ) :=
      MeasurableEmbedding.subtype_coe measurableSet_Icc
    have heval (s : Set ℝ) (hs : MeasurableSet s) : μ s = μ (s ∩ Icc a b) := by
      have := congrArg (fun ν : VectorMeasure ℝ 𝕜 => ν s) hsupport.symm
      simpa only [VectorMeasure.restrict_apply _ measurableSet_Icc hs] using this
    refine ⟨μ.map (projIcc a b hab), inferInstance, ?_⟩
    apply VectorMeasure.ext
    intro s hs
    rw [extendByZero, VectorMeasure.map_apply _ hval.measurable hs,
      VectorMeasure.map_apply _ hproj (hval.measurable hs),
      heval _ (hproj (hval.measurable hs)), heval s hs]
    congr 1
    ext x
    by_cases hx : x ∈ Icc a b
    · simp [hx, projIcc_of_mem hab hx]
    · simp [hx]
  · have hemp : Icc a b = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hab)
    have hμ : μ = 0 := by simpa only [hemp, VectorMeasure.restrict_empty] using hsupport.symm
    refine ⟨0, by simp only [VectorMeasure.variation_zero]; infer_instance, ?_⟩
    simp [extendByZero, hμ]

/-- Existence and uniqueness on the original interval subtype. -/
theorem subtype_converse_bridge : SubtypeConverseBridge := by
  intro 𝕜 _ a b F hF
  obtain ⟨μ, hμ, hsupp, hc, hv, hinc, huniq⟩ := converse_bridge 𝕜 a b F hF
  have : IsFiniteMeasure μ.variation := hμ
  obtain ⟨ν, hν, hext⟩ := exists_intervalMeasure a b μ hsupp
  have hsub := subtype_bridge 𝕜 a b ν hν
  have hCDF (t : ℝ) : ν {x | (x : ℝ) ≤ t} = F t := by
    rw [← hsub.2.2.2.1, intervalCumulative, hsub.2.1, hext]
    exact hc t
  refine ⟨ν, hν, hCDF, ?_, ?_, ?_⟩
  · have hval : MeasurableEmbedding (Subtype.val : Icc a b → ℝ) :=
      MeasurableEmbedding.subtype_coe measurableSet_Icc
    calc
      eVariationOn F univ = μ.variation univ := hv
      _ = (extendByZero ν).variation univ := by rw [hext]
      _ = ν.variation univ := by
        rw [extendByZero, hval.variation_map, Measure.map_apply hval.measurable MeasurableSet.univ,
          preimage_univ]
  · intro s t hst
    rw [hext]
    exact hinc s t hst
  · intro η hη hηCDF
    apply extendByZero_injective
    apply cumulative_injective
    intro t
    have hextCDF (ζ : VectorMeasure (Icc a b) 𝕜) :
        cumulative (extendByZero ζ) t = ζ {x | (x : ℝ) ≤ t} := by
      exact VectorMeasure.map_apply ζ measurable_subtype_coe measurableSet_Iic
    rw [hextCDF, hextCDF, hηCDF, hCDF]

namespace TaggedPartition
variable {a b : ℝ} (p : BVMeasureBridgeSpec.TaggedPartition a b)

lemma point_mem (i : ℕ) (hi : i ≤ p.n) : p.point i ∈ Icc a b := by
  constructor
  · simpa only [p.first] using p.mono (Nat.zero_le i)
  · simpa only [p.last] using p.mono hi

lemma tag_mem_interval (i : ℕ) (hi : i < p.n) : p.tag i ∈ Icc a b :=
  ⟨(point_mem p i hi.le).1.trans (p.tag_mem i hi).1,
    (p.tag_mem i hi).2.trans (point_mem p (i+1) hi).2⟩

lemma cells_disjoint (i j : ℕ) (hij : i ≠ j) :
    Disjoint (Ioc (p.point i) (p.point (i+1))) (Ioc (p.point j) (p.point (j+1))) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact disjoint_left.mpr (by intro x hx hy; have := p.mono (Nat.succ_le_of_lt h); grind)
  · exact disjoint_left.mpr (by intro x hx hy; have := p.mono (Nat.succ_le_of_lt h); grind)

lemma exists_cell {x : ℝ} (hx : x ∈ Ioc a b) :
    ∃ i < p.n, x ∈ Ioc (p.point i) (p.point (i+1)) := by
  have h := Ioc_subset_biUnion_Ioc p.n p.point
  rw [p.first, p.last] at h
  simpa [and_assoc, and_left_comm, and_comm] using h hx

end TaggedPartition

/-- The step function whose integral is the tagged sum, including the atom at a. -/
noncomputable def partitionStep {a b : ℝ} (p : BVMeasureBridgeSpec.TaggedPartition a b)
    (f : ℝ → 𝕜) : ℝ → 𝕜 :=
  ({a} : Set ℝ).indicator (fun _ => f a) + fun x =>
    ∑ i ∈ Finset.range p.n, (Ioc (p.point i) (p.point (i+1))).indicator (fun _ => f (p.tag i)) x

lemma partitionStep_at_left {a b : ℝ} (p : BVMeasureBridgeSpec.TaggedPartition a b)
    (f : ℝ → 𝕜) : partitionStep p f a = f a := by
  have h (i : ℕ) : a ≤ p.point i := by simpa only [p.first] using p.mono (Nat.zero_le i)
  simp [partitionStep, not_lt.mpr (h _)]

lemma partitionStep_on_cell {a b : ℝ} (p : BVMeasureBridgeSpec.TaggedPartition a b)
    (f : ℝ → 𝕜) {x : ℝ} {i : ℕ} (hi : i < p.n)
    (hx : x ∈ Ioc (p.point i) (p.point (i+1))) : partitionStep p f x = f (p.tag i) := by
  have hxa : x ≠ a := by
    have := (TaggedPartition.point_mem p i hi.le).1
    exact ne_of_gt (this.trans_lt hx.1)
  simp only [partitionStep, Pi.add_apply]
  rw [Set.indicator_of_notMem (show x ∉ ({a} : Set ℝ) from hxa), zero_add]
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hx _
  · intro j hj hji
    exact Set.indicator_of_notMem (fun hxj =>
      Set.disjoint_left.mp (TaggedPartition.cells_disjoint p j i hji) hxj hx) _
  · intro h
    exact (h (Finset.mem_range.mpr hi)).elim

lemma partitionStep_integrable {a b : ℝ} (p : BVMeasureBridgeSpec.TaggedPartition a b)
    (f : ℝ → 𝕜) (μ : Measure ℝ) [IsFiniteMeasure μ] : Integrable (partitionStep p f) μ :=
  ((integrable_const _).indicator (measurableSet_singleton _)).add
    (integrable_finsetSum _ (fun _ _ => (integrable_const _).indicator measurableSet_Ioc))

lemma partitionStep_integral {a b : ℝ} (p : BVMeasureBridgeSpec.TaggedPartition a b)
    (f : ℝ → 𝕜) (ν : VectorMeasure ℝ 𝕜) [IsFiniteMeasure ν.variation] :
    scalarIntegral (ν.restrict (Icc a b)) (partitionStep p f) =
      stieltjesSum p (intervalCumulative a b ν) f := by
  have hab : a ≤ b := by simpa only [p.first, p.last] using p.mono (Nat.zero_le p.n)
  have hatom : (ν.restrict (Icc a b)) {a} = intervalCumulative a b ν a := by
    unfold intervalCumulative cumulative
    rw [VectorMeasure.restrict_apply _ measurableSet_Icc (measurableSet_singleton _),
      VectorMeasure.restrict_apply _ measurableSet_Icc measurableSet_Iic]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_singleton_iff, mem_Icc, mem_Iic]
    grind
  unfold partitionStep
  rw [scalarIntegral, VectorMeasure.integral_add
    ((integrable_const _).indicator (measurableSet_singleton _))
    (integrable_finsetSum _ (fun _ _ => (integrable_const _).indicator measurableSet_Ioc)),
    VectorMeasure.integral_finsetSum _ (fun _ _ => (integrable_const _).indicator measurableSet_Ioc)]
  simp only [VectorMeasure.integral_indicator_const _ (measurableSet_singleton a),
    VectorMeasure.integral_indicator_const _ measurableSet_Ioc,
    ContinuousLinearMap.mul_apply', hatom, cumulative_increment _ (p.mono (Nat.le_succ _))]
  rfl

/-- Explicit convergence of tagged sums, with the lower atom retained. -/
theorem stieltjes_functional : StieltjesFunctional := by
  intro 𝕜 _ a b ν hν f hf
  have : IsFiniteMeasure ν.variation := hν
  have hfint : Integrable f (ν.restrict (Icc a b)).variation := by
    rw [VectorMeasure.variation_restrict measurableSet_Icc]
    exact hf.integrableOn_Icc
  refine ⟨hf.integrableOn_Icc, ?_⟩
  intro ε hε
  let μ := ν.restrict (Icc a b)
  let m := μ.variation.real univ
  have hm : 0 ≤ m := measureReal_nonneg
  let η := ε / (m+1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
  refine ⟨δ, hδ, ?_⟩
  intro p hp
  have hbound : ∀ᵐ x ∂μ.variation, ‖partitionStep p f x - f x‖ ≤ η := by
    have ha : ∀ᵐ x ∂μ.variation, x ∈ Icc a b := by
      dsimp [μ]
      rw [VectorMeasure.variation_restrict measurableSet_Icc]
      exact ae_restrict_mem measurableSet_Icc
    filter_upwards [ha] with x hx
    rcases eq_or_lt_of_le hx.1 with hxa | hxa
    · rw [← hxa, partitionStep_at_left, sub_self, norm_zero]
      exact hη.le
    · obtain ⟨i, hi, hxi⟩ := TaggedPartition.exists_cell p ⟨hxa, hx.2⟩
      rw [partitionStep_on_cell p f hi hxi]
      rw [← dist_eq_norm]
      apply le_of_lt
      apply hmod (p.tag i) (TaggedPartition.tag_mem_interval p i hi) x hx
      rw [Real.dist_eq]
      have ht := p.tag_mem i hi
      exact (abs_le.mpr ⟨by linarith [hxi.2, ht.1], by linarith [hxi.1, ht.2]⟩).trans_lt (hp i hi)
  have hnorm : ‖scalarIntegral μ (fun x => partitionStep p f x - f x)‖ ≤ η * m := by
    have h := VectorMeasure.norm_integral_le_of_norm_le_const
      (μ := μ) (B := ContinuousLinearMap.mul ℝ 𝕜) hbound
    calc
      _ ≤ η * ‖ContinuousLinearMap.mul ℝ 𝕜‖ * m := h
      _ ≤ η * 1 * m := by
        gcongr
        exact ContinuousLinearMap.opNorm_mul_le ℝ 𝕜
      _ = η * m := by ring
  have heq : scalarIntegral μ (fun x => partitionStep p f x - f x) =
      stieltjesSum p (intervalCumulative a b ν) f - scalarIntegral μ f := by
    rw [scalarIntegral, VectorMeasure.integral_fun_sub
      (partitionStep_integrable p f μ.variation) hfint]
    rw [← scalarIntegral, partitionStep_integral]
    rfl
  rw [heq] at hnorm
  apply hnorm.trans_lt
  calc
    η * m < η * (m+1) := mul_lt_mul_of_pos_left (by linarith) hη
    _ = ε := div_mul_cancel₀ _ (by linarith : m+1 ≠ 0)

lemma intervalIntegrand_comp {a b : ℝ} (f : C(Icc a b, 𝕜)) :
    intervalIntegrand f ∘ Subtype.val = f := by
  funext x
  simp [intervalIntegrand, x.property]

lemma intervalIntegrand_continuousOn {a b : ℝ} (f : C(Icc a b, 𝕜)) :
    ContinuousOn (intervalIntegrand f) (Icc a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (Icc a b).domRestrict (intervalIntegrand f) = f := intervalIntegrand_comp f
  rw [heq]
  exact f.continuous

/-- Tagged sums and integration for the original measures and test functions
on the closed interval, including singleton and empty intervals. -/
theorem subtype_stieltjes_functional : SubtypeStieltjesFunctional := by
  intro 𝕜 _ a b ν hν f
  have : IsFiniteMeasure ν.variation := hν
  have hsub := subtype_bridge 𝕜 a b ν hν
  have hst := stieltjes_functional 𝕜 a b (extendByZero ν) hsub.1
    (intervalIntegrand f) (intervalIntegrand_continuousOn f)
  have heq : intervalCumulative a b (extendByZero ν) =
      fun t => ν {x | (x : ℝ) ≤ t} := funext hsub.2.2.2.1
  have hsupport := hsub.2.1
  have hint : scalarIntegral ((extendByZero ν).restrict (Icc a b)) (intervalIntegrand f) =
      scalarIntegral ν f := by
    rw [hsupport, hsub.2.2.2.2.2, intervalIntegrand_comp]
  refine ⟨f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_⟩
  simpa only [heq, hint] using hst.2

end ExpandedFA.FunctionSpaces.BVMeasureBridge
