import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.MultiplicityCommutant
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.MultiplicityExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.MultiplicityUniqueness
import Mathlib.Analysis.CStarAlgebra.Unitary.Span

noncomputable section
set_option synthInstance.maxHeartbeats 100000
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace ExpandedFA.VonNeumann.MultiplicityCommutant
universe u
open MultiplicityModel.Spec

/-- Fiber operators commute with scalar multiplication, including on L² classes. -/
theorem field_scalar_commutation : Spec.FieldScalarCommutation := by
  intro μ m B φ hφ hb f g hfg
  filter_upwards [applyLpValue_ae B g.val, applyLpValue_ae B f.val, hfg]
    with z hg hf hfgz
  change applyLpValue B g.val z = φ z • applyLpValue B f.val z
  rw [hg, hf, hfgz, map_smul]

/-- No finiteness is needed for the inclusion of fields in the commutant. -/
theorem field_coordinate_commutation : Spec.FieldCoordinateCommutation := by
  intro μ m h B
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [applyLpValue_ae B (coordinateOperatorValue μ m h f).val,
    coordinateLpValue_ae h f.val,
    coordinateLpValue_ae h (fieldActionValue B f).val,
    applyLpValue_ae B f.val] with z h1 h2 h3 h4
  change applyLpValue B (coordinateOperatorValue μ m h f).val z =
    coordinateLpValue h (fieldActionValue B f).val z
  rw [h1, h3]
  change B z (coordinateLpValue h f.val z) = z • applyLpValue B f.val z
  rw [h2, h4, map_smul]

/-- Equality on the countable coordinate basis determines any bounded operator on ℓ². -/
lemma sequence_operator_ext {A D : SequenceSpace →L[ℂ] SequenceSpace}
    (h : ∀ k : ℕ, A (lp.single 2 k (1 : ℂ)) = D (lp.single 2 k (1 : ℂ))) : A = D := by
  apply ContinuousLinearMap.ext
  intro x
  have hsum := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x
  apply HasSum.unique (A.hasSum hsum)
  convert D.hasSum hsum using 1
  funext k
  have hs : (lp.single 2 k (x k) : SequenceSpace) = x k • lp.single 2 k (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : ℕ => ℂ) 2 k (x k) (1 : ℂ))
  rw [hs, map_smul, map_smul, h k]

/-- The finite measure makes all active coordinate constants available as test sections. -/
theorem field_action_faithful : Spec.FieldActionFaithful := by
  intro μ _ m B C
  constructor
  · intro h
    have hc (k : ℕ) : ∀ᵐ z ∂μ,
        B z ((MultiplicityUniqueness.Localization.coordinateSection m k).val z) =
        C z ((MultiplicityUniqueness.Localization.coordinateSection m k).val z) := by
      let f := MultiplicityUniqueness.Localization.coordinateSection m k
      have hh : fieldActionValue B f = fieldActionValue C f := congrArg (fun T => T f) h
      have heq : (fieldActionValue B f).val =ᵐ[μ] (fieldActionValue C f).val := by rw [hh]
      exact (applyLpValue_ae B f.val).symm.trans (heq.trans (applyLpValue_ae C f.val))
    filter_upwards [ae_all_iff.mpr hc,
      ae_all_iff.mpr (MultiplicityUniqueness.Localization.coordinateSection_ae m),
      B.fiberwise, C.fiberwise] with z hz hs hB hC
    apply sequence_operator_ext
    intro k
    by_cases hk : (k : ℕ∞) < m z
    · simpa only [hs k, if_pos hk] using hz k
    · rw [hB.2 _ (MultiplicityUniqueness.FiberBasis.single_orthogonal hk),
        hC.2 _ (MultiplicityUniqueness.FiberBasis.single_orthogonal hk)]
  · exact fieldActionValue_congr

open scoped InnerProductSpace

/-- Coefficient localization promotes continuous scalar commutation to every
bounded Borel scalar graph, for arbitrary bounded operators. -/
lemma scalar_commutation_of_coefficient {μ : Measure ℂ} {m : Multiplicity μ}
    (T : DirectIntegral μ m →L[ℂ] DirectIntegral μ m)
    (hc : ∀ x f : DirectIntegral μ m,
      (fun z => ⟪(T.adjoint x).val z, f.val z⟫_ℂ) =ᵐ[μ]
        fun z => ⟪x.val z, (T f).val z⟫_ℂ) :
    MultiplicityUniqueness.Spec.IntertwinesScalars T := by
  intro φ hφ hb f g hfg
  obtain ⟨C, hC⟩ := hb
  have hm : MemLp (fun z => φ z • (T f).val z) 2 μ :=
    (Lp.memLp (T f).val).of_le_mul
      (hφ.aestronglyMeasurable.smul (Lp.aestronglyMeasurable (T f).val))
      (c := C) (by
        filter_upwards [] with z
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _))
  let a : DirectIntegral μ m := ⟨hm.toLp _, by
    change ∀ᵐ z ∂μ, _ ∈ fiber (m z)
    filter_upwards [MemLp.coeFn_toLp hm, (T f).property] with z hz hf
    rw [hz]
    exact (fiber (m z)).smul_mem (φ z) hf⟩
  have ha : a.val =ᵐ[μ] fun z => φ z • (T f).val z := MemLp.coeFn_toLp hm
  have heq : T g = a := by
    apply ext_inner_left ℂ
    intro x
    calc
      ⟪x, T g⟫_ℂ = ⟪T.adjoint x, g⟫_ℂ := (T.adjoint_inner_left g x).symm
      _ = ∫ z, φ z * ⟪(T.adjoint x).val z, f.val z⟫_ℂ ∂μ := by
        change ⟪(T.adjoint x).val, g.val⟫_ℂ = _
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hfg] with z hz
        rw [hz, inner_smul_right]
      _ = ∫ z, φ z * ⟪x.val z, (T f).val z⟫_ℂ ∂μ := by
        apply integral_congr_ae
        filter_upwards [hc x f] with z hz
        rw [hz]
      _ = ⟪x, a⟫_ℂ := by
        change _ = ⟪x.val, a.val⟫_ℂ
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [ha] with z hz
        rw [hz, inner_smul_right]
  change (T g).val =ᵐ[μ] fun z => φ z • (T f).val z
  rw [heq]
  exact ha

/-- Fuglede is used in the upstream continuous intertwiner theorem. Weighted
coefficient uniqueness then supplies all bounded Borel scalar multiplications. -/
theorem coordinate_scalar_commutation : Spec.CoordinateScalarCommutation := by
  intro μ _ m h T hT
  classical
  let s : Set ℂ := Metric.closedBall 0 (h.choose : ℝ)
  have hs : MeasurableSet s := Metric.isClosed_closedBall.measurableSet
  letI : CompactSpace s := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) _)
  have h0 : (0 : ℂ) ∈ s := by
    change dist (0 : ℂ) 0 ≤ (h.choose : ℝ)
    simpa using h.choose.coe_nonneg
  have hconull : ∀ᵐ z ∂μ, z ∈ s := by
    simpa only [s, Metric.mem_closedBall, dist_zero_right] using h.choose_spec
  let q := MultiplicityUniqueness.NativeScalar.retract s h0
  have hq : Measurable q := MultiplicityUniqueness.NativeScalar.retract_measurable hs h0
  let π := MultiplicityUniqueness.NativeScalar.representation m q hq
  have hcoord : π ((ContinuousMap.id ℂ).restrict s) = coordinateOperatorValue μ m h :=
    MultiplicityUniqueness.NativeScalar.representation_coordinate m h hs h0 hconull
  have hcomm : ∀ a : C(s, ℂ), (π a).comp T = T.comp (π a) := by
    intro a
    apply MultiplicityUniqueness.NativeScalar.continuous_intertwining π π
      (MultiplicityUniqueness.NativeScalar.representation_continuous m q hq)
      (MultiplicityUniqueness.NativeScalar.representation_continuous m q hq) T
    rw [hcoord]
    exact hT.symm
  have hcoef (x f : DirectIntegral μ m) :
      (fun z => ⟪(T.adjoint x).val z, f.val z⟫_ℂ) =ᵐ[μ]
        fun z => ⟪x.val z, (T f).val z⟫_ℂ := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
      (L2.integrable_inner (T.adjoint x).val f.val) (L2.integrable_inner x.val (T f).val)
    have hsets := MultiplicityUniqueness.continuous_tests_setIntegral μ μ _ _
      (L2.integrable_inner (T.adjoint x).val f.val) (L2.integrable_inner x.val (T f).val) ?_
    · intro a ha _
      exact hsets a ha
    intro a
    let b := a.toContinuousMap.restrict s
    have hgraph (v : DirectIntegral μ m) :
        (π b v).val =ᵐ[μ] fun z => a z • v.val z := by
      filter_upwards [MultiplicityUniqueness.NativeScalar.mulOperator_ae m q hq b v,
        hconull] with z hz hzs
      change (MultiplicityUniqueness.NativeScalar.mulOperator m q hq b v).val z = _
      rw [hz]
      simp [b, q, MultiplicityUniqueness.NativeScalar.retract, hzs]
    calc
      (∫ z, a z * ⟪(T.adjoint x).val z, f.val z⟫_ℂ ∂μ) =
          ⟪T.adjoint x, π b f⟫_ℂ := by
        change _ = ⟪(T.adjoint x).val, (π b f).val⟫_ℂ
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hgraph f] with z hz
        rw [hz, inner_smul_right]
      _ = ⟪x, T (π b f)⟫_ℂ := T.adjoint_inner_left _ _
      _ = ⟪x, π b (T f)⟫_ℂ := by
        exact congrArg (fun v => ⟪x, v⟫_ℂ)
          ((congrArg (fun A : DirectIntegral μ m →L[ℂ] DirectIntegral μ m => A f) (hcomm b)).symm)
      _ = ∫ z, a z * ⟪x.val z, (T f).val z⟫_ℂ ∂μ := by
        change ⟪x.val, (π b (T f)).val⟫_ℂ = _
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hgraph (T f)] with z hz
        rw [hz, inner_smul_right]
  exact scalar_commutation_of_coefficient T hcoef

/-- Scalar-module maps are exactly the commutant of measurable indicator
projections. This avoids any assumption about a coordinate bound. -/
lemma scalar_commutation_of_projections {μ : Measure ℂ} {m : Multiplicity μ}
    (T : DirectIntegral μ m →L[ℂ] DirectIntegral μ m)
    (hT : ∀ (s : Set ℂ) (hs : MeasurableSet s) (f : DirectIntegral μ m),
      T (MultiplicityUniqueness.Localization.restrictSection hs f) =
        MultiplicityUniqueness.Localization.restrictSection hs (T f)) :
    MultiplicityUniqueness.Spec.IntertwinesScalars T := by
  apply scalar_commutation_of_coefficient
  intro x f
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (L2.integrable_inner (T.adjoint x).val f.val) (L2.integrable_inner x.val (T f).val)
  intro s hs _
  rw [← MultiplicityUniqueness.Localization.inner_section hs,
    ← MultiplicityUniqueness.Localization.inner_section hs,
    T.adjoint_inner_left, hT]

lemma indicator_projection_selfAdjoint {μ : Measure ℂ} {m : Multiplicity μ}
    {s : Set ℂ} (hs : MeasurableSet s) :
    IsSelfAdjoint (MultiplicityUniqueness.Localization.projection (m := m) hs) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change ⟪(MultiplicityUniqueness.Localization.restrictSection hs f).val, g.val⟫_ℂ =
    ⟪f.val, (MultiplicityUniqueness.Localization.restrictSection hs g).val⟫_ℂ
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MultiplicityUniqueness.Localization.section_ae hs f,
    MultiplicityUniqueness.Localization.section_ae hs g] with z hf hg
  rw [hf, hg]
  by_cases hz : z ∈ s <;> simp [hz]

/-- A closed C⋆-algebra, formed without a finite-measure or coordinate-bound
hypothesis. Its unitary elements are scalar-module unitaries. -/
def scalarCentralizer (μ : Measure ℂ) (m : Multiplicity μ) :
    StarSubalgebra ℂ (DirectIntegral μ m →L[ℂ] DirectIntegral μ m) :=
  StarSubalgebra.centralizer ℂ
    {P | ∃ (s : Set ℂ) (hs : MeasurableSet s),
      P = MultiplicityUniqueness.Localization.projection (m := m) hs}

instance scalarCentralizer_closed (μ : Measure ℂ) (m : Multiplicity μ) :
    IsClosed (scalarCentralizer μ m : Set (DirectIntegral μ m →L[ℂ] DirectIntegral μ m)) := by
  letI : ContinuousMul (DirectIntegral μ m →L[ℂ] DirectIntegral μ m) :=
    ⟨continuous_fst.clm_comp continuous_snd⟩
  exact Set.isClosed_centralizer _

lemma mem_scalarCentralizer_iff {μ : Measure ℂ} {m : Multiplicity μ}
    (T : DirectIntegral μ m →L[ℂ] DirectIntegral μ m) :
    T ∈ scalarCentralizer μ m ↔ MultiplicityUniqueness.Spec.IntertwinesScalars T := by
  constructor
  · intro hT
    apply scalar_commutation_of_projections
    intro s hs f
    have hh := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT)
      _ ⟨s, hs, rfl⟩ |>.1
    exact (congrArg (fun A : DirectIntegral μ m →L[ℂ] DirectIntegral μ m => A f) hh).symm
  · intro hT
    rw [scalarCentralizer, StarSubalgebra.mem_centralizer_iff]
    rintro P ⟨s, hs, rfl⟩
    have hcomm : (MultiplicityUniqueness.Localization.projection (m := m) hs) * T =
        T * MultiplicityUniqueness.Localization.projection (m := m) hs := by
      apply ContinuousLinearMap.ext
      intro f
      exact (MultiplicityUniqueness.Localization.intertwines_section T hT hs f).symm
    exact ⟨hcomm, by rw [(indicator_projection_selfAdjoint hs).star_eq]; exact hcomm⟩

/-- Finite linear combinations of actual measurable, bounded fields. -/
def combinationField {μ : Measure ℂ} {m : Multiplicity μ} {n : ℕ}
    (c : Fin n → ℂ) (B : Fin n → OperatorField μ m) : OperatorField μ m where
  toFun z := ∑ i, c i • B i z
  fiberwise := by
    filter_upwards [ae_all_iff.mpr (fun i => (B i).fiberwise)] with z hz
    constructor
    · intro x
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      exact (fiber (m z)).sum_mem fun i _ => (fiber (m z)).smul_mem _ ((hz i).1 x)
    · intro x hx
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      exact Finset.sum_eq_zero fun i _ => by rw [(hz i).2 x hx, smul_zero]
  measurable_orbit x := by
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    convert (Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => ((B i).measurable_orbit x).const_smul (c i))) using 1
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply]
  bounded := by
    refine ⟨∑ i, ‖c i‖₊ * (B i).bounded.choose, ?_⟩
    filter_upwards [ae_all_iff.mpr (fun i => (B i).bounded.choose_spec)] with z hz
    calc
      ‖∑ i, c i • B i z‖ ≤ ∑ i, ‖c i • B i z‖ := norm_sum_le _ _
      _ = ∑ i, ‖c i‖ * ‖B i z‖ := by simp only [norm_smul]
      _ ≤ ∑ i, ‖c i‖ * ((B i).bounded.choose : ℝ) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _)
      _ = ((∑ i, ‖c i‖₊ * (B i).bounded.choose : ℝ≥0) : ℝ) := by simp

lemma combinationField_action {μ : Measure ℂ} {m : Multiplicity μ} {n : ℕ}
    (c : Fin n → ℂ) (B : Fin n → OperatorField μ m) :
    fieldActionValue (combinationField c B) = ∑ i, c i • fieldActionValue (B i) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [sum_apply, smul_apply]
  apply Subtype.ext
  simp only [AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul]
  apply Lp.ext
  have hsum := Lp.coeFn_finsetSum Finset.univ
    (fun i => c i • (fieldActionValue (B i) f).val)
  filter_upwards [applyLpValue_ae (combinationField c B) f.val, hsum,
    ae_all_iff.mpr (fun i => applyLpValue_ae (B i) f.val),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) (fieldActionValue (B i) f).val)]
    with z hB hs hz hc
  change applyLpValue (combinationField c B) f.val z =
    (∑ i, c i • (fieldActionValue (B i) f).val : Lp SequenceSpace 2 μ) z
  rw [hB, hs]
  simp only [combinationField, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc i]
  change c i • B i z (f.val z) = c i • applyLpValue (B i) f.val z
  rw [hz i]

/-- The accepted unitary decomposition suffices for all bounded module maps:
apply the four-unitary theorem inside the closed scalar commutant. -/
theorem scalar_decomposition : Spec.ScalarDecomposition := by
  intro μ _ m T hT
  let A := scalarCentralizer μ m
  let t : A := ⟨T, (mem_scalarCentralizer_iff T).mpr hT⟩
  obtain ⟨u, c, heq, _⟩ := CStarAlgebra.exists_sum_four_unitary t
  let inclusion : A →⋆* (DirectIntegral μ m →L[ℂ] DirectIntegral μ m) :=
    { toFun := Subtype.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_star' := fun _ => rfl }
  let v (i : Fin 4) : unitary (DirectIntegral μ m →L[ℂ] DirectIntegral μ m) :=
    Unitary.map inclusion (u i)
  let U (i : Fin 4) := Unitary.linearIsometryEquiv (v i)
  have hU (i : Fin 4) : MultiplicityUniqueness.Spec.IntertwinesScalars
      (U i).toLinearIsometry.toContinuousLinearMap := by
    apply (mem_scalarCentralizer_iff _).mp
    change (u i).val.val ∈ scalarCentralizer μ m
    exact (u i).val.property
  choose B hB using fun i => MultiplicityUniqueness.unitary_decomposition μ m m (U i) (hU i)
  let D (i : Fin 4) : OperatorField μ m :=
    { toFun := B i
      fiberwise := ((B i).unitary).mono fun _ h => ⟨h.1, h.2.1⟩
      measurable_orbit := (B i).measurable_orbit
      bounded := ⟨1, ((B i).unitary).mono fun _ h =>
        MultiplicityUniqueness.fiberUnitary_norm_le_one _ h⟩ }
  have hD (i : Fin 4) : fieldActionValue (D i) = (U i).toLinearIsometry.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    apply Lp.ext
    exact (applyLpValue_ae (D i) f.val).trans ((hB i f).symm)
  refine ⟨combinationField c D, ?_⟩
  rw [combinationField_action]
  simp_rw [hD]
  have hUcoe (i : Fin 4) : (U i).toLinearIsometry.toContinuousLinearMap = A.subtype (u i).val := rfl
  simp_rw [hUcoe]
  have hv := congrArg (fun a : A => a.val) heq
  simp only [AddSubmonoidClass.coe_finsetSum] at hv
  change T = ∑ i, c i • A.subtype (u i).val at hv
  exact hv.symm

lemma section_norm_sq {μ : Measure ℂ} {m : Multiplicity μ} (f : DirectIntegral μ m) :
    ‖f‖ ^ 2 = ∫ z, ‖f.val z‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (⟪f.val, f.val⟫_ℂ).re = _
  rw [L2.inner_def]
  change RCLike.re (∫ z, ⟪f.val z, f.val z⟫_ℂ ∂μ) = _
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) f.val f.val)]
  congr 1
  funext z
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (f.val z)

lemma section_integrable_norm_sq {μ : Measure ℂ} {m : Multiplicity μ}
    (f : DirectIntegral μ m) : Integrable (fun z => ‖f.val z‖ ^ 2) μ := by
  simpa only [inner_self_eq_norm_sq (𝕜 := ℂ)] using (L2.integrable_inner (𝕜 := ℂ) f.val f.val).re

lemma localized_norm_sq {μ : Measure ℂ} {m : Multiplicity μ} {s : Set ℂ}
    (hs : MeasurableSet s) (f : DirectIntegral μ m) :
    ‖MultiplicityUniqueness.Localization.restrictSection hs f‖ ^ 2 =
      ∫ z in s, ‖f.val z‖ ^ 2 ∂μ := by
  rw [section_norm_sq, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [MultiplicityUniqueness.Localization.section_ae hs f] with z hz
  rw [hz]
  by_cases hzs : z ∈ s <;> simp [hzs]

/-- Localizing the operator inequality on every measurable set yields a
pointwise bound for each section. -/
lemma scalar_module_pointwise_bound {μ : Measure ℂ} {m : Multiplicity μ}
    (T : DirectIntegral μ m →L[ℂ] DirectIntegral μ m)
    (hT : MultiplicityUniqueness.Spec.IntertwinesScalars T) (f : DirectIntegral μ m) :
    ∀ᵐ z ∂μ, ‖(T f).val z‖ ≤ ‖T‖ * ‖f.val z‖ := by
  have hh : ∀ᵐ z ∂μ, ‖(T f).val z‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖f.val z‖ ^ 2 := by
    apply ae_le_of_forall_setIntegral_le (section_integrable_norm_sq (T f))
      ((section_integrable_norm_sq f).const_mul (‖T‖ ^ 2))
    intro s hs _
    rw [integral_const_mul, ← localized_norm_sq hs (T f), ← localized_norm_sq hs f,
      ← MultiplicityUniqueness.Localization.intertwines_section T hT hs f]
    exact (pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2).trans_eq (mul_pow _ _ _)
  filter_upwards [hh] with z hz
  rw [← mul_pow] at hz
  exact (sq_le_sq₀ (norm_nonneg ((T f).val z))
    (mul_nonneg (norm_nonneg T) (norm_nonneg (f.val z)))).mp hz

lemma fiber_projection_single (d : ℕ∞) (k : ℕ) :
    (fiber d).starProjection (lp.single 2 k (1 : ℂ)) =
      if (k : ℕ∞) < d then lp.single 2 k (1 : ℂ) else 0 := by
  classical
  by_cases hk : (k : ℕ∞) < d
  · rw [if_pos hk]
    exact Submodule.starProjection_eq_self_iff.mpr
      (MultiplicityUniqueness.FiberBasis.vector d ⟨k, hk⟩).property
  · rw [if_neg hk]
    exact ((fiber d).starProjection_apply_eq_zero_iff).mpr
      (MultiplicityUniqueness.FiberBasis.single_orthogonal hk)

/-- Strong measurability of the varying coordinate projection follows from
its finite coordinate sums. It needs no operator-norm measurability. -/
lemma fiber_projection_measurable {μ : Measure ℂ} (m : Multiplicity μ) (x : SequenceSpace) :
    AEStronglyMeasurable (fun z => (fiber (m z)).starProjection x) μ := by
  classical
  let a (k : ℕ) : ℂ → SequenceSpace :=
    {z | (k : ℕ∞) < m z}.indicator (fun _ => x k • (lp.single 2 k (1 : ℂ) : SequenceSpace))
  have ha (k : ℕ) : AEStronglyMeasurable (a k) μ :=
    (stronglyMeasurable_const.indicator (MultiplicityModel.coordinate_support_measurable m k)).aestronglyMeasurable
  have hs (N : ℕ) : AEStronglyMeasurable (fun z => ∑ k ∈ Finset.range N, a k z) μ := by
    convert Finset.aestronglyMeasurable_sum (Finset.range N) (fun k _ => ha k) using 1
    funext z
    simp only [Finset.sum_apply]
  apply aestronglyMeasurable_of_tendsto_ae atTop hs
  filter_upwards [] with z
  have hl := ((fiber (m z)).starProjection.hasSum
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)).tendsto_sum_nat
  have hterm (k : ℕ) : (fiber (m z)).starProjection (lp.single 2 k (x k)) = a k z := by
    have he : (lp.single 2 k (x k) : SequenceSpace) = x k • lp.single 2 k (1 : ℂ) := by
      simpa only [smul_eq_mul, mul_one] using
        (lp.single_smul (E := fun _ : ℕ => ℂ) 2 k (x k) (1 : ℂ))
    rw [he, map_smul, fiber_projection_single]
    by_cases hk : (k : ℕ∞) < m z <;> simp [a, hk]
  simpa only [hterm] using hl

lemma projected_constant_memLp {μ : Measure ℂ} [IsFiniteMeasure μ]
    (m : Multiplicity μ) (x : SequenceSpace) :
    MemLp (fun z => (fiber (m z)).starProjection x) 2 μ :=
  MemLp.of_bound (fiber_projection_measurable m x) ‖x‖
    (ae_of_all _ fun z => (fiber (m z)).norm_starProjection_apply_le x)

def projectedConstant {μ : Measure ℂ} [IsFiniteMeasure μ]
    (m : Multiplicity μ) (x : SequenceSpace) : DirectIntegral μ m :=
  ⟨(projected_constant_memLp m x).toLp _, by
    change ∀ᵐ z ∂μ, _ ∈ fiber (m z)
    filter_upwards [MemLp.coeFn_toLp (projected_constant_memLp m x)] with z hz
    rw [hz]
    exact (fiber (m z)).starProjection_apply_mem x⟩

lemma projectedConstant_ae {μ : Measure ℂ} [IsFiniteMeasure μ]
    (m : Multiplicity μ) (x : SequenceSpace) :
    (projectedConstant m x).val =ᵐ[μ] fun z => (fiber (m z)).starProjection x :=
  MemLp.coeFn_toLp (projected_constant_memLp m x)

/-- The native countable-coordinate ℓ² is separable. -/
theorem sequenceSpace_separable : TopologicalSpace.SeparableSpace SequenceSpace := by
  let e : ℕ → SequenceSpace := fun k => lp.single 2 k (1 : ℂ)
  let V := Submodule.span ℂ (Set.range e)
  have hsep : TopologicalSpace.IsSeparable (V : Set SequenceSpace) :=
    (Set.countable_range e).isSeparable.span
  apply TopologicalSpace.isSeparable_univ_iff.mp
  apply hsep.closure.mono
  intro x _
  apply isClosed_closure.mem_of_tendsto
    (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x).tendsto_sum_nat
  apply Eventually.of_forall
  intro N
  apply subset_closure
  apply V.sum_mem
  intro k _
  have he : (lp.single 2 k (x k) : SequenceSpace) = x k • e k := by
    simpa only [e, smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : ℕ => ℂ) 2 k (x k) (1 : ℂ))
  rw [he]
  exact V.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)

/-- Countably many dense-vector tests provide one common conull set for
all fiber operator norm bounds. -/
lemma ae_fiber_norm_le_action_norm {μ : Measure ℂ} [IsFiniteMeasure μ]
    {m : Multiplicity μ} (B : OperatorField μ m) :
    ∀ᵐ z ∂μ, ‖B z‖ ≤ ‖fieldActionValue B‖ := by
  let T := fieldActionValue B
  have htest (x : SequenceSpace) : ∀ᵐ z ∂μ, ‖B z x‖ ≤ ‖T‖ * ‖x‖ := by
    filter_upwards [scalar_module_pointwise_bound T (field_scalar_commutation B) (projectedConstant m x),
      projectedConstant_ae m x, applyLpValue_ae B (projectedConstant m x).val, B.fiberwise]
      with z hbound hp ha hB
    have hproj : B z ((fiber (m z)).starProjection x) = B z x := by
      have hz := hB.2 (x - (fiber (m z)).starProjection x)
        ((fiber (m z)).sub_starProjection_mem_orthogonal x)
      rw [map_sub] at hz
      exact (sub_eq_zero.mp hz).symm
    change ‖applyLpValue B (projectedConstant m x).val z‖ ≤
      ‖T‖ * ‖(projectedConstant m x).val z‖ at hbound
    rw [ha, hp, hproj] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_left
      ((fiber (m z)).norm_starProjection_apply_le x) (norm_nonneg T))
  letI := sequenceSpace_separable
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq SequenceSpace
  filter_upwards [ae_all_iff.mpr (fun n => htest (d n))] with z hz
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  exact isClosed_property hd (isClosed_le (B z).continuous.norm
    (continuous_const.mul continuous_norm)) hz

/-- The global norm is exactly the essential supremum of the fiber norms. -/
theorem field_norm_identity : Spec.FieldNormIdentity := by
  intro μ _ m B
  apply le_antisymm (MultiplicityModel.field_action_bound B)
  change (fieldENorm B).toReal ≤ ‖fieldActionValue B‖
  apply ENNReal.toReal_le_of_le_ofReal (norm_nonneg (fieldActionValue B)) 
  change essSup (fun z => (‖B z‖₊ : ℝ≥0∞)) μ ≤ ENNReal.ofReal ‖fieldActionValue B‖
  apply essSup_le_of_ae_le (ENNReal.ofReal ‖fieldActionValue B‖)
  filter_upwards [ae_fiber_norm_le_action_norm B] with z hz
  calc
    (‖B z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖B z‖ := ENNReal.coe_nnreal_eq _
    _ ≤ ENNReal.ofReal ‖fieldActionValue B‖ := ENNReal.ofReal_le_ofReal hz

/-- Assembly of the decomposition, scalar-calculus and norm theorems. -/
theorem commutant_from_bridges
    (hd : Spec.ScalarDecomposition) (hs : Spec.CoordinateScalarCommutation)
    (hn : Spec.FieldNormIdentity) : Spec.Commutant := by
  intro μ _ m h T
  constructor
  · intro hT
    obtain ⟨B, hB⟩ := hd μ m T (hs μ m h T hT)
    exact ⟨B, hB, hB ▸ hn μ m B⟩
  · rintro ⟨B, rfl, _⟩
    exact field_coordinate_commutation h B

/-- A.e. quotient fields give an injective and surjective commutant description. -/
theorem essential_commutant_from_bridges
    (hc : Spec.Commutant) (hn : Spec.FieldNormIdentity) : Spec.EssentialCommutant := by
  intro μ _ m h
  refine ⟨?_, ?_, ?_⟩
  · intro B C heq
    induction B using Quotient.inductionOn with
    | h B =>
      induction C using Quotient.inductionOn with
      | h C =>
        exact Quotient.sound ((field_action_faithful B C).mp heq)
  · intro T
    constructor
    · intro hT
      obtain ⟨B, hB, _⟩ := (hc μ m h T).mp hT
      exact ⟨Quotient.mk _ B, hB⟩
    · rintro ⟨B, rfl⟩
      induction B using Quotient.inductionOn with
      | h B => exact field_coordinate_commutation h B
  · intro B
    induction B using Quotient.inductionOn with
    | h B => exact hn μ m B

/-- Transport preserves the operator norm and the full commutant, on the
original Hilbert space rather than only on coordinate models. -/
theorem original_commutant_from_commutant (hc : Spec.Commutant) : Spec.OriginalCommutant.{u} := by
  intro H _ _ _ N μ _ m h U hU T
  let S : DirectIntegral μ m →L[ℂ] DirectIntegral μ m :=
    U.symm.toLinearIsometry.toContinuousLinearMap.comp
      (T.comp U.toLinearIsometry.toContinuousLinearMap)
  have hS (f : DirectIntegral μ m) : S f = U.symm (T (U f)) := rfl
  have hnorm : ‖S‖ = ‖T‖ := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
      intro f
      simpa only [hS, U.symm.norm_map, U.norm_map] using T.le_opNorm (U f)
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S)
      intro x
      simpa only [hS, U.symm.norm_map, U.apply_symm_apply] using S.le_opNorm (U.symm x)
  constructor
  · intro hT
    have hs : Spec.CommutesCoordinate h S := by
      apply ContinuousLinearMap.ext
      intro f
      apply U.injective
      change U (S (coordinateOperatorValue μ m h f)) =
        U (coordinateOperatorValue μ m h (S f))
      rw [hS, U.apply_symm_apply, hU f, hU (S f), hS, U.apply_symm_apply]
      exact congrArg (fun A : H →L[ℂ] H => A (U f)) hT
    obtain ⟨B, hB, hn⟩ := (hc μ m h S).mp hs
    refine ⟨B, ?_, hnorm ▸ hn⟩
    intro f
    rw [hB, hS, U.apply_symm_apply]
  · rintro ⟨B, hB, _⟩
    apply ContinuousLinearMap.ext
    intro x
    have hb := congrArg (fun A => A (U.symm x)) (field_coordinate_commutation h B)
    change fieldActionValue B (coordinateOperatorValue μ m h (U.symm x)) =
      coordinateOperatorValue μ m h (fieldActionValue B (U.symm x)) at hb
    change T (N x) = N (T x)
    calc
      T (N x) = T (U (coordinateOperatorValue μ m h (U.symm x))) := by
        rw [hU, U.apply_symm_apply]
      _ = U (fieldActionValue B (coordinateOperatorValue μ m h (U.symm x))) := hB _
      _ = U (coordinateOperatorValue μ m h (fieldActionValue B (U.symm x))) := congrArg U hb
      _ = N (T x) := by rw [hU, ← hB, U.apply_symm_apply]

/-- Assembly with the accepted existence and classification theorems. -/
theorem spectral_multiplicity_from_bridges
    (hd : Spec.ScalarDecomposition) (hs : Spec.CoordinateScalarCommutation)
    (hn : Spec.FieldNormIdentity) : Spec.SpectralMultiplicity.{u} := by
  have hc := commutant_from_bridges hd hs hn
  exact ⟨MultiplicityExistence.multiplicity_existence, MultiplicityUniqueness.classification,
    hc, essential_commutant_from_bridges hc hn, original_commutant_from_commutant hc⟩

/-- The full coordinate-model commutant, with the sharp norm identity. -/
theorem commutant : Spec.Commutant :=
  commutant_from_bridges scalar_decomposition coordinate_scalar_commutation field_norm_identity

/-- An exact bijective description by fields modulo a.e. equality. -/
theorem essential_commutant : Spec.EssentialCommutant :=
  essential_commutant_from_bridges commutant field_norm_identity

/-- The original operator's commutant, under any of its coordinate-model unitaries. -/
theorem original_commutant : Spec.OriginalCommutant.{u} :=
  original_commutant_from_commutant commutant

/-- Full separable spectral multiplicity, classification and commutant theorem. -/
theorem spectral_multiplicity : Spec.SpectralMultiplicity.{u} :=
  spectral_multiplicity_from_bridges scalar_decomposition coordinate_scalar_commutation field_norm_identity

end ExpandedFA.VonNeumann.MultiplicityCommutant
