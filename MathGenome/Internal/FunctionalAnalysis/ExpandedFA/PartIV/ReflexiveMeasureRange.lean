import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.ReflexiveMeasureRange
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.VectorMeasureVariation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarL1DunfordPettis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.DunfordPettisL1
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.CompleteContinuity
import Mathlib.MeasureTheory.Integral.SetToL1.L1
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
universe u v
namespace ExpandedFA.PartIV
open ReflexiveMeasureRangeSpec

section IntegralOperator
variable (𝕜 : Type) [RCLike 𝕜] {X : Type u} {Y : Type v}
  [MeasurableSpace X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  [CompleteSpace Y]

private def integralSetMap (m : VectorMeasure X Y) (A : Set X) : 𝕜 →L[𝕜] Y :=
  (ContinuousLinearMap.id 𝕜 𝕜).smulRight (m A)

private theorem integralSetMap_dominated (m : VectorMeasure X Y) :
    letI : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ 𝕜 Y
    DominatedFinMeasAdditive m.variation
      (fun A => (integralSetMap 𝕜 m A).restrictScalars ℝ) 1 := by
  letI : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ 𝕜 Y
  constructor
  · intro A B hA hB _ _ hd
    ext a
    simp [integralSetMap, m.of_union hd hA hB, smul_add]
  · intro A hA hf
    calc
      ‖(integralSetMap 𝕜 m A).restrictScalars ℝ‖ = ‖m A‖ := by
        simp [integralSetMap]
      _ ≤ 1 * m.variation.real A := by
        simpa using VectorMeasure.norm_measure_le_variation (μ := m) hf.ne

/-- Integration of scalar L¹ functions against m, constructed by extending
the dominated finitely additive map on indicators. -/
def vectorIntegralOperator (m : VectorMeasure X Y) : Lp 𝕜 1 m.variation →L[𝕜] Y := by
  letI : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ 𝕜 Y
  exact L1.setToL1' 𝕜 (integralSetMap_dominated 𝕜 m)
    (fun c A a => by simp [integralSetMap, mul_smul])

theorem vectorIntegralOperator_indicator (m : VectorMeasure X Y)
    [IsFiniteMeasure m.variation] (A : Set X) (hA : MeasurableSet A) :
    vectorIntegralOperator 𝕜 m (indicatorConstLp 1 hA (measure_ne_top _ _) 1) = m A := by
  letI : NormedSpace ℝ Y := NormedSpace.restrictScalars ℝ 𝕜 Y
  unfold vectorIntegralOperator
  erw [← L1.setToL1_eq_setToL1']
  simpa [integralSetMap] using
    L1.setToL1_indicatorConstLp (integralSetMap_dominated 𝕜 m) hA
      (measure_ne_top m.variation A) (1 : 𝕜)

end IntegralOperator

section UnitFamily
variable {𝕜 : Type} [RCLike 𝕜] {X : Type u} [MeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- A convenient superset of the measurable indicator classes. -/
def unitDominatedFamily : Set (Lp 𝕜 1 μ) := {f | ∀ᵐ x ∂μ, ‖f x‖ ≤ 1}

private theorem unitFamily_setIntegral_le (f : Lp 𝕜 1 μ)
    (hf : f ∈ unitDominatedFamily μ) (A : Set X) :
    (∫ x in A, ‖f x‖ ∂μ) ≤ μ.real A := by
  calc
    (∫ x in A, ‖f x‖ ∂μ) ≤ ∫ _x in A, (1 : ℝ) ∂μ :=
      integral_mono_ae (L1.integrable_coeFn f).norm.restrict (integrable_const 1)
        (ae_restrict_of_ae hf)
    _ = μ.real A := by simp

theorem unitFamily_bounded_uniformlyIntegrable :
    FunctionSpaces.ScalarL1DunfordPettisSpec.BoundedAndUniformlyIntegrable μ
      (unitDominatedFamily (𝕜 := 𝕜) μ) := by
  refine ⟨isBounded_iff_forall_norm_le.mpr ⟨μ.real univ, ?_⟩, ?_, ?_⟩
  · intro f hf
    rw [L1.norm_eq_integral_norm]
    simpa using unitFamily_setIntegral_le μ f hf univ
  · intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro A hA hμA f
    exact (unitFamily_setIntegral_le μ f.val f.property A).trans_lt
      ((ENNReal.toReal_lt_toReal (measure_ne_top μ A)
        (ENNReal.ofReal_ne_top)).mpr hμA |>.trans_eq (ENNReal.toReal_ofReal hε.le))
  · intro ε hε
    refine ⟨univ, MeasurableSet.univ, measure_lt_top μ univ, ?_⟩
    intro f
    simpa using hε

theorem unitFamily_weaklyCompact :
    FunctionSpaces.ScalarL1DunfordPettisSpec.RelativelyWeaklyCompact μ
      (unitDominatedFamily (𝕜 := 𝕜) μ) :=
  (FunctionSpaces.scalar_l1_dunford_pettis μ _).mpr
    (unitFamily_bounded_uniformlyIntegrable μ)

end UnitFamily
section ReflexiveOperators
variable {𝕜 : Type} [RCLike 𝕜] {E : Type u} {Y : Type v}
  [NormedAddCommGroup E] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 Y]

/-- A bounded operator with reflexive target is weakly compact. -/
theorem weaklyCompact_of_reflexive_target
    (hY : P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 Y) (T : E →L[𝕜] Y) :
    Compactness.DefinitionsSpec.IsWeaklyCompactOperatorValue T := by
  have hb := Compactness.CompleteContinuity.reflexive_closedBall_weaklyCompact 𝕜 Y hY
  have hb' : IsCompact ((toWeakSpace 𝕜 Y) '' Metric.closedBall (0 : Y) 1) := by
    change @IsCompact (WeakSpace 𝕜 Y) (TopologicalSpace.induced id
      (instTopologicalSpaceWeakSpace 𝕜 Y)) _ at hb
    let B : Set Y := Metric.closedBall (0 : Y) 1
    change @IsCompact (WeakSpace 𝕜 Y) _ (id '' B)
    erw [image_id]
    erw [induced_id] at hb
    exact hb
  let a : 𝕜 := algebraMap ℝ 𝕜 (‖T‖ + 1)
  have ha : ‖a‖ = ‖T‖ + 1 := by
    change ‖((‖T‖ + 1 : ℝ) : 𝕜)‖ = ‖T‖ + 1
    rw [RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    have := norm_nonneg T
    linarith
  let K : Set (WeakSpace 𝕜 Y) := (fun y => a • y) ''
    ((toWeakSpace 𝕜 Y) '' Metric.closedBall (0 : Y) 1)
  have hK : IsCompact K := hb'.image (continuous_const_smul a)
  apply (Compactness.weaklyCompact_iff_weakSpace T).mpr
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨toWeakSpace 𝕜 Y (a⁻¹ • T x), ?_, ?_⟩
  · apply mem_image_of_mem
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, ha]
    have hTx : ‖T x‖ ≤ ‖T‖ := by
      exact (T.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg T)
        (by simpa [Metric.mem_closedBall, dist_zero_right] using hx))
    exact (inv_mul_le_one₀ (by positivity : 0 < ‖T‖ + 1)).mpr (hTx.trans (by linarith))
  · change a • (a⁻¹ • T x) = T x
    rw [smul_smul, mul_inv_cancel₀ ha0, one_smul]

end ReflexiveOperators


/-- Compact range is proved before introducing any Bochner density. -/
theorem reflexive_measure_compactRange : CompactRange.{u,v} := by
  intro 𝕜 _ X Y _ _ _ _ hY m hm
  letI : IsFiniteMeasure m.variation := ⟨hm⟩
  let T := vectorIntegralOperator 𝕜 m
  have hTweak := weaklyCompact_of_reflexive_target hY T
  have hTcc := (Compactness.DunfordPettisL1.l1_theorem 𝕜 X m.variation).2 Y T hTweak
  let K := @closure (Lp 𝕜 1 m.variation)
    (FunctionSpaces.ScalarL1DunfordPettisSpec.weakTopology m.variation)
    (unitDominatedFamily (𝕜 := 𝕜) m.variation)
  have hK : @IsCompact (Lp 𝕜 1 m.variation)
      (P1.EberleinSmulian.Spec.weakTopology 𝕜 (Lp 𝕜 1 m.variation)) K :=
    unitFamily_weaklyCompact m.variation
  have hTK := Compactness.CompleteContinuity.image_isCompact_of_completelyContinuous T hTcc K hK
  have hsub : range m ⊆ T '' K := by
    rintro _ ⟨A, rfl⟩
    by_cases hA : MeasurableSet A
    · let f : Lp 𝕜 1 m.variation := indicatorConstLp 1 hA (measure_ne_top _ _) 1
      refine ⟨f, ?_, vectorIntegralOperator_indicator 𝕜 m A hA⟩
      apply @subset_closure _ (FunctionSpaces.ScalarL1DunfordPettisSpec.weakTopology m.variation)
      change ∀ᵐ x ∂m.variation, ‖f x‖ ≤ 1
      filter_upwards [indicatorConstLp_coeFn (p := 1) (hs := hA)
        (hμs := measure_ne_top m.variation A) (c := (1 : 𝕜))] with x hx
      change ‖indicatorConstLp 1 hA (measure_ne_top m.variation A) (1 : 𝕜) x‖ ≤ 1
      rw [hx]
      by_cases h : x ∈ A <;> simp [h]
    · refine ⟨0, ?_, ?_⟩
      · apply @subset_closure _ (FunctionSpaces.ScalarL1DunfordPettisSpec.weakTopology m.variation)
        change ∀ᵐ x ∂m.variation, ‖(0 : Lp 𝕜 1 m.variation) x‖ ≤ 1
        filter_upwards [Lp.coeFn_zero (E := 𝕜) (p := 1) (μ := m.variation)] with x hx
        have he : (0 : Lp 𝕜 1 m.variation) x = 0 := hx
        rw [he]
        norm_num
      · simp [VectorMeasure.not_measurable m hA]
  exact hTK.closure.of_isClosed_subset isClosed_closure (closure_mono hsub)

/-- Closed subspaces inherit surjectivity of the canonical bidual map. -/
theorem closed_subspace_reflexive {𝕜 Y : Type*} [RCLike 𝕜] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (hY : P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 Y)
    (V : Submodule 𝕜 Y) (hV : IsClosed (V : Set Y)) :
    P1.C04CanonicalMap.Spec.IsReflexiveValue 𝕜 V := by
  letI : IsClosed (V : Set Y) := hV
  let R : (Y →L[𝕜] 𝕜) →L[𝕜] (V →L[𝕜] 𝕜) :=
    (ContinuousLinearMap.compL 𝕜 V Y 𝕜).flip V.subtypeL
  intro φ
  obtain ⟨y, hy⟩ := hY (φ.comp R)
  have hyV : y ∈ V := by
    by_contra hn
    have hq : V.mkQ y ≠ 0 := fun h => hn ((Submodule.Quotient.mk_eq_zero V).mp h)
    obtain ⟨g, _, hg⟩ := exists_dual_vector 𝕜 (V.mkQ y) (norm_ne_zero_iff.mpr hq)
    let f : Y →L[𝕜] 𝕜 := g.comp V.mkQL
    have hRf : R f = 0 := by
      ext z
      change g (V.mkQ z.val) = 0
      rw [show V.mkQ z.val = 0 from (Submodule.Quotient.mk_eq_zero V).mpr z.property, map_zero]
    have hfy := congrArg (fun ψ => ψ f) hy
    change f y = φ (R f) at hfy
    rw [hRf, map_zero] at hfy
    have hz : ‖V.mkQ y‖ = 0 := by simpa only [RCLike.ofReal_eq_zero] using hg.symm.trans hfy
    exact hq (norm_eq_zero.mp hz)
  refine ⟨⟨y, hyV⟩, ?_⟩
  ext f
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq V f
  have hRg : R g = f := by ext z; exact hg z
  have hgy := congrArg (fun ψ => ψ g) hy
  change g y = φ (R g) at hgy
  change f ⟨y, hyV⟩ = φ f
  rw [← hg ⟨y, hyV⟩, hgy, hRg]

/-- The closed span is formed only after compactness has been established. -/
theorem reflexive_measure_separableSpan : SeparableReflexiveSpan.{u,v} := by
  intro 𝕜 _ X Y _ _ _ _ hY m hm
  let V := rangeSpan 𝕜 m
  have hV : IsClosed (V : Set Y) := (Submodule.span 𝕜 (range m)).isClosed_topologicalClosure
  letI : IsClosed (V : Set Y) := hV
  have hs : TopologicalSpace.IsSeparable (V : Set Y) := by
    change TopologicalSpace.IsSeparable (closure (Submodule.span 𝕜 (range m) : Set Y))
    exact ((reflexive_measure_compactRange 𝕜 hY m hm).isSeparable.mono subset_closure).span.closure
  exact ⟨hs.separableSpace, inferInstance, closed_subspace_reflexive hY V hV⟩

end ExpandedFA.PartIV
