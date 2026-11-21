import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Integration.Densities
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.MetricVolume
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.FormPullback
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Tensors
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.DensityIntegral

/-! Density calculus for M10.05. Canonical objects live in the independent Specs.
The shared unsigned integration results supply the global integral, localization,
diffeomorphism invariance and zero-dimensional sum. The remaining results prove
the fiber algebra, pullback regularity, metric case and regularity counterexamples. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Topology BigOperators
open Module

namespace SmoothManifolds.DensityIntegrationResults
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  OrientationData MetricVolumeData ExteriorData DensityIntegrationData
  MetricVolumeResults FrameData FiniteRegularityData Set MeasureTheory Filter
universe u

section Algebra
variable {n : ℕ} {V W Z : Type u} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [AddCommGroup Z] [Module ℝ Z]

@[simp] theorem density_zero (ρ : densitySubmodule V) : ρ.val 0 = 0 := by
  simpa only [zero_smul, abs_zero, zero_mul] using ρ.property 0 (0 : V)

theorem tuple_dependent (ρ : densitySubmodule (⋀[ℝ]^n V))
    (v : Fin n → V) (hv : ¬ LinearIndependent ℝ v) : tupleEvaluation ρ v = 0 := by
  unfold tupleEvaluation
  rw [(exteriorPower.ιMulti ℝ n).map_linearDependent v hv, density_zero]

theorem tuple_basis (ρ : densitySubmodule (⋀[ℝ]^n V))
    (b : Basis (Fin n) ℝ V) (v : Fin n → V) :
    tupleEvaluation ρ v = |b.det v| * tupleEvaluation ρ b := by
  unfold tupleEvaluation
  rw [wedge_basis_expansion b v, ρ.property]

theorem tuple_law : Specs.SmoothManifolds.Integration.Densities.tuple_lawType.{u} := by
  intro n V _ _ ρ
  exact ⟨tuple_dependent ρ, tuple_basis ρ⟩

theorem fiber_pullback : Specs.SmoothManifolds.Integration.Densities.fiber_pullbackType.{u} := by
  intro n V W _ _ _ _ L ρ v
  change ρ.val (exteriorPower.map n L (exteriorPower.ιMulti ℝ n v)) = _
  rw [exteriorPower.map_apply_ιMulti]
  rfl

@[simp] theorem fiberPullback_id (ρ : densitySubmodule (⋀[ℝ]^n V)) :
    DensityIntegrationData.fiberPullback (LinearMap.id : V →ₗ[ℝ] V) ρ = ρ := by
  apply Subtype.ext
  funext v
  change ρ.val (exteriorPower.map n LinearMap.id v) = ρ.val v
  rw [exteriorPower.map_id, LinearMap.id_apply]

theorem fiberPullback_comp (L : V →ₗ[ℝ] W) (H : W →ₗ[ℝ] Z)
    (ρ : densitySubmodule (⋀[ℝ]^n Z)) :
    DensityIntegrationData.fiberPullback (H.comp L) ρ =
      DensityIntegrationData.fiberPullback L (DensityIntegrationData.fiberPullback H ρ) := by
  apply Subtype.ext
  funext v
  change ρ.val (exteriorPower.map n (H.comp L) v) =
    ρ.val (exteriorPower.map n H (exteriorPower.map n L v))
  rw [exteriorPower.map_comp, LinearMap.comp_apply]

/-- The determinant formula for an arbitrary linear map, without a rank
hypothesis or a choice of rays. -/
theorem fiberPullback_basis (L : V →ₗ[ℝ] W)
    (b : Basis (Fin n) ℝ V) (c : Basis (Fin n) ℝ W)
    (ρ : densitySubmodule (⋀[ℝ]^n W)) :
    tupleEvaluation (DensityIntegrationData.fiberPullback L ρ) b =
      |c.det (L ∘ b)| * tupleEvaluation ρ c := by
  rw [fiber_pullback, tuple_basis ρ c]

end Algebra

section Coordinates
variable {n : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold n b N}

theorem pullback_coefficient :
    Specs.SmoothManifolds.Integration.Densities.pullback_coefficientType.{u} := by
  intro n a b M N _ _ S T f L K J c hc d hd p hp hq ρ
  let bs := coordinateBasis K c hc ⟨p, hp⟩
  let bt := coordinateBasis J d hd ⟨f p, hq⟩
  have he := fiberPullback_basis (V := TangentSpace S p) (W := TangentSpace T (f p)) (L p) bs bt (ρ (f p))
  have hdet : bt.det (L p ∘ bs) =
      (Matrix.of (fun i j => J.equiv d hd (f p) hq
        (L p ((K.equiv c hc p hp).symm ((Pi.basisFun ℝ (Fin n)) j))) i)).det := by
    rw [Basis.det_apply]
    congr 1
  rw [hdet, mul_comm] at he
  simpa only [bs, bt, coordinateBasis, tupleEvaluation, Basis.coe_map,
    Function.comp_def, densityCoefficient, OrientationData.coordinateVector,
    DensityIntegrationData.pullbackField, LinearMap.coe_mk, AddHom.coe_mk] using he

/-- Absolute value does not change any coordinate convention or ordered wedge. -/
theorem absolute_coefficient :
    Specs.SmoothManifolds.Integration.Densities.absolute_coefficientType.{u} := by
  intro n a M _ S ω K c hc p
  change |pairing p.val (ω p.val) (OrientationData.coordinateVector K c hc p)| = _
  rw [FormPullbackData.topCoefficient, FormPullbackResults.evaluate_eq_pairing]
  unfold _root_.SmoothManifolds.CovectorData.coordinateVector
  simp only [pairing, OrientationData.coordinateVector, Pi.basisFun_apply]

theorem absolute_continuous :
    Specs.SmoothManifolds.Integration.Densities.absolute_continuousType.{u} := by
  intro n a M _ S ω hω K c hc
  have he : (fun p : c.source => densityCoefficient K c hc p (absoluteTopForm ω p.val)) =
      (fun p : c.source => |FormPullbackData.topCoefficient K c hc p.val p.property ω|) := by
    funext p
    exact absolute_coefficient S ω K c hc p
  rw [he]
  exact (hω K c hc).abs

theorem smooth_density_continuous (ρ : DensityField S) (hρ : IsSmoothDensity ρ) :
    IsContinuousDensity ρ := by
  intro K c hc
  exact continuous_iff_continuousAt.mpr (fun p => (hρ K c hc p).1)

theorem metric : Specs.SmoothManifolds.Integration.Densities.metricType.{u} := by
  intro n a M _ S C g
  obtain ⟨ρ, hρ, huniq⟩ := MetricVolumeResults.density_exists_unique S C g
  refine ⟨ρ, ⟨hρ.1, hρ.2.1, smooth_density_continuous ρ hρ.2.1,
    hρ.2.2.1, hρ.2.2.2.2⟩, ?_⟩
  intro σ hσ
  exact (metricDensity_unique g σ hσ.1).trans (metricDensity_unique g ρ hρ.1).symm

end Coordinates

section Regularity
variable {n : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold n b N}

/-- Determinant of the full coordinate differential, including normal directions
at a true boundary point. -/
def chartJacobianDet (c : ModelChart n a M) (d : ModelChart n b N)
    (f : M → N) (p : M) : ℝ :=
  (Matrix.of (fun i j => chartDerivative c d f p (Pi.single j 1) i)).det

theorem chartJacobianDet_smoothAt (f : M → N) (hf : IsSmoothMap S T f)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hfp : f p ∈ d.source) :
    VectorSmoothAt S.smoothStructure.val (chartJacobianDet c d f) p := by
  have heval : ContDiff ℝ (⊤ : ℕ∞)
      (fun D : Euclidean n →L[ℝ] Euclidean n => fun i j => D (Pi.single j 1) i) := by
    fun_prop
  exact ((Tensors.chartDerivative_smoothAt S T f hf c d hc hd p hp hfp).postcomp
    heval).postcomp (matrix_det_smooth n)

theorem pullback_chart_coefficient (f : M → N) (hf : IsSmoothMap S T f)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p)) (K : FiberCoordinates S)
    (J : FiberCoordinates T) (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hfp : f p ∈ d.source) (ρ : DensityField T) :
    densityCoefficient K c hc ⟨p, hp⟩ (DensityIntegrationData.pullbackField S T f L ρ p) =
      densityCoefficient J d hd ⟨f p, hfp⟩ (ρ (f p)) * |chartJacobianDet c d f p| := by
  rw [pullback_coefficient S T f L K J c hc d hd p hp hfp ρ]
  congr 2
  congr 1
  ext i j
  have hj := FiniteRegularity.smooth_jacobian_coordinateDerivative S T f hf p (L p)
    (hL p) c d hc hd hp hfp (K.equiv c hc p hp) (J.equiv d hd (f p) hfp)
    (K.isCoordinates c hc p hp) (J.isCoordinates d hd (f p) hfp)
    ((K.equiv c hc p hp).symm ((Pi.basisFun ℝ (Fin n)) j))
  simpa only [Matrix.of_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
    using congrFun hj i

theorem totalize_continuousAt {X : Type u} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) (f : U → ℝ) (hf : Continuous f) (p : U) :
    ContinuousAt (FrameData.totalize f) p.val := by
  apply hU.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
  simpa only [Function.comp_def, FrameData.totalize_of_mem f _ (Subtype.property _)]
    using hf.continuousAt (x := p)

theorem pullback_continuous :
    Specs.SmoothManifolds.Integration.Densities.pullback_continuousType.{u} := by
  intro n a b M N _ _ S T f hf L hL ρ hρ K c hc
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p.val)
  obtain ⟨J⟩ := TangentBundle.fiberCoordinates_exists T
  let q : d.source := ⟨f p.val, hfp⟩
  let bc : d.source → ℝ := fun q => densityCoefficient J d hd q (ρ q.val)
  have hb := totalize_continuousAt d.open_source bc (hρ J d hd) q
  have hj := chartJacobianDet_smoothAt f hf c d hc hd p.val p.property hfp
  have hh : ContinuousAt (fun y : M => FrameData.totalize bc (f y) *
      |chartJacobianDet c d f y|) p.val := (hb.comp (f := f) (x := p.val) (hf p.val).1).mul hj.1.abs
  have he : (fun y : c.source => FrameData.totalize bc (f y.val) *
      |chartJacobianDet c d f y.val|) =ᶠ[𝓝 p]
      (fun y : c.source => densityCoefficient K c hc y
        (DensityIntegrationData.pullbackField S T f L ρ y.val)) := by
    filter_upwards [((hf p.val).1.comp continuousAt_subtype_val).preimage_mem_nhds
      (d.open_source.mem_nhds hfp)] with y hy
    change f y.val ∈ d.source at hy
    simp only [FrameData.totalize, dif_pos hy]
    exact (pullback_chart_coefficient f hf L hL K J c d hc hd y.val y.property hy ρ).symm
  exact (hh.comp continuousAt_subtype_val).congr he

theorem chartJacobianDet_ne_zero (f : M → N)
    (hf : TensorData.IsLocalDiffeomorphism S T f)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hfp : f p ∈ d.source) :
    chartJacobianDet c d f p ≠ 0 := by
  obtain ⟨e, he⟩ := Tensors.chartDerivative_isInvertible S T f hf c d hc hd p hp hfp
  have hm : Matrix.of (fun i j => chartDerivative c d f p (Pi.single j 1) i) =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n)) e.toLinearEquiv.toLinearMap := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply,
      Matrix.of_apply, ← he]
    rfl
  unfold chartJacobianDet
  rw [hm, LinearMap.det_toMatrix, ← LinearEquiv.coe_det]
  exact Units.ne_zero _

theorem pullback_smooth :
    Specs.SmoothManifolds.Integration.Densities.pullback_smoothType.{u} := by
  intro n a b M N _ _ S T f hf L hL ρ hρ K c hc
  let g : M → ℝ := FrameData.totalize (fun p : c.source =>
    densityCoefficient K c hc p (DensityIntegrationData.pullbackField S T f L ρ p.val))
  have hg : BundleData.SmoothOnBase S g c.source := by
    intro p hp
    obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
    obtain ⟨J⟩ := TangentBundle.fiberCoordinates_exists T
    let bc : d.source → ℝ := fun q => densityCoefficient J d hd q (ρ q.val)
    have hb : VectorSmoothAt T.smoothStructure.val (FrameData.totalize bc) (f p) :=
      (hρ J d hd ⟨f p, hfp⟩).totalize d.open_source
    have hbf := hb.comp T.smoothStructure.property.1.1 (hf.1 p)
    have hj := chartJacobianDet_smoothAt f hf.1 c d hc hd p hp hfp
    have hja : VectorSmoothAt S.smoothStructure.val (fun y => |chartJacobianDet c d f y|) p :=
      hj.postcompOn isOpen_ne
        (chartJacobianDet_ne_zero f hf c d hc hd p hp hfp)
        (contDiffOn_abs (fun _ hx => hx))
    have hh := (hbf.prod hja).postcomp (contDiff_fst.mul contDiff_snd)
    apply hh.congr
    filter_upwards [c.open_source.mem_nhds hp,
      (hf.1 p).1.preimage_mem_nhds (d.open_source.mem_nhds hfp)] with y hy hfy
    change f y ∈ d.source at hfy
    dsimp only [g]
    rw [FrameData.totalize_of_mem _ _ hy, FrameData.totalize_of_mem bc _ hfy]
    exact (pullback_chart_coefficient f hf.1 L hL K J c d hc hd y hy hfy ρ).symm
  have hres := smoothOnBase_restrict c.source c.open_source g hg
  simpa only [g, FrameData.totalize_of_mem _ _ (Subtype.property _)] using hres

end Regularity

section Integration

/-- The unsigned local integrals glue uniquely on every manifold, including
manifolds with boundary and dimension zero. -/
theorem integral_exists_unique :
    Specs.SmoothManifolds.Integration.Densities.integral_exists_uniqueType.{u} :=
  DensityIntegralResults.integral_exists_unique

/-- Diffeomorphic pullback preserves compact support and the unsigned integral. -/
theorem diffeomorphism :
    Specs.SmoothManifolds.Integration.Densities.diffeomorphismType.{u} :=
  DensityIntegralResults.diffeomorphism

/-- Every finite chart decomposition computes the unique integral. -/
theorem finite_localization :
    Specs.SmoothManifolds.Integration.Densities.finite_localizationType.{u} :=
  DensityIntegralResults.finite_localization

/-- In dimension zero, compact support is finite and integration is its
unsigned coefficient sum. -/
theorem zero_finite_sum :
    Specs.SmoothManifolds.Integration.Densities.zero_finite_sumType.{u} :=
  DensityIntegralResults.zero_finite_sum

end Integration

section Counterexamples
theorem real_coordinate_bridge :
    Specs.SmoothManifolds.Integration.Densities.real_coordinate_bridgeType := by
  constructor
  · intro f b x
    rw [fiber_pullback]
    simp only [tupleEvaluation, realDensity, exteriorPower.oneEquiv_ιMulti,
      Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one,
      realPullbackCoefficient]
  · intro x
    simp [realTopForm, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_one]

/-- Analytic coefficient computation in the standard real coordinate. -/
theorem square_coefficient (x : ℝ) :
    realPullbackCoefficient (fun t => t ^ 2) (fun _ => 1) x = 2 * |x| := by
  have hd : deriv (fun t : ℝ => t ^ 2) x = 2 * x := by
    simpa using (hasDerivAt_pow 2 x).deriv
  simp only [realPullbackCoefficient, one_mul, hd, abs_mul]
  norm_num

theorem square_nondifferentiable : ¬ DifferentiableAt ℝ (fun x : ℝ => 2 * |x|) 0 := by
  intro h
  have he : (fun x : ℝ => (2 : ℝ)⁻¹ * (2 * |x|)) = abs := by
    funext x
    ring
  have hh := h.const_mul ((2 : ℝ)⁻¹)
  rw [he] at hh
  exact not_differentiableAt_abs_zero hh

theorem square_counterexample :
    Specs.SmoothManifolds.Integration.Densities.square_counterexampleType := by
  have he : realPullbackCoefficient (fun t => t ^ 2) (fun _ => 1) =
      (fun x : ℝ => 2 * |x|) := funext square_coefficient
  refine ⟨contDiff_id.pow 2, contDiff_const, square_coefficient, ?_, ?_, ?_⟩
  · rw [he]
    exact continuous_const.mul continuous_abs
  · rw [he]
    exact square_nondifferentiable
  · rw [he]
    intro h
    exact square_nondifferentiable (h.differentiableAt (by simp))

theorem absolute_counterexample :
    Specs.SmoothManifolds.Integration.Densities.absolute_counterexampleType := by
  refine ⟨contDiff_id, rfl, continuous_abs, not_differentiableAt_abs_zero, ?_⟩
  intro h
  exact not_differentiableAt_abs_zero (h.differentiableAt (by simp))

end Counterexamples
end SmoothManifolds.DensityIntegrationResults
