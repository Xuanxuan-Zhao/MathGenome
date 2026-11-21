import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SmoothMetrics

set_option autoImplicit false
namespace P202.Geometry.SmoothMetrics
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.DifferentialData
  SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  P202.MetricData
open Set Filter
open scoped Topology
universe u v w

theorem exists_metric : P202Specs.Geometry.SmoothMetrics.exists_metricType.{u} := by
  intro n a M _ S
  letI := (tangentRealization S).space.topology
  exact SmoothManifolds.BundleMetrics.exists_smoothFiberMetric
    (tangentRealization S).space.bundle

section Norm
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} (g : RiemannianMetric S) (p : M)

@[simp] theorem pairing_self_zero : pairing g p 0 0 = 0 := by
  simp [pairing]

theorem pairing_self_nonneg (v : TangentSpace S p) : 0 ≤ pairing g p v v := by
  by_cases hv : v = 0
  · subst v; simp
  · exact (g.positive p v hv).le

theorem tangentNorm_nonneg (v : TangentSpace S p) : 0 ≤ tangentNorm g p v :=
  Real.sqrt_nonneg _

@[simp] theorem tangentNorm_zero : tangentNorm g p 0 = 0 := by
  simp [tangentNorm]

theorem tangentNorm_sq (v : TangentSpace S p) :
    tangentNorm g p v ^ 2 = pairing g p v v :=
  Real.sq_sqrt (pairing_self_nonneg g p v)

@[simp] theorem tangentNorm_eq_zero_iff (v : TangentSpace S p) :
    tangentNorm g p v = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    have hp := g.positive p v hv
    have hs := tangentNorm_sq g p v
    rw [h, zero_pow (by decide)] at hs
    exact (ne_of_gt hp) hs.symm
  · rintro rfl
    exact tangentNorm_zero g p

@[simp] theorem tangentNorm_neg (v : TangentSpace S p) :
    tangentNorm g p (-v) = tangentNorm g p v := by
  simp only [tangentNorm, pairing, LinearMap.BilinForm.neg_left,
    LinearMap.BilinForm.neg_right, neg_neg]

@[simp] theorem tangentNorm_smul (c : ℝ) (v : TangentSpace S p) :
    tangentNorm g p (c • v) = |c| * tangentNorm g p v := by
  unfold tangentNorm pairing
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    ← mul_assoc, Real.sqrt_mul (mul_self_nonneg c), Real.sqrt_mul_self_eq_abs]

end Norm

/-- Bilinear evaluation in an actual linear frame, in every finite rank. -/
theorem bilinear_coordinates {V : Type v} [AddCommGroup V] [Module ℝ V]
    {r : ℕ} (e : V ≃ₗ[ℝ] Euclidean r) (B : LinearMap.BilinForm ℝ V) (v w : V) :
    B v w = ∑ j : Fin r, ∑ k : Fin r,
      (e v) j * ((e w) k * B (e.symm (Pi.single j 1)) (e.symm (Pi.single k 1))) := by
  have hex (v : V) : v = ∑ j : Fin r, (e v) j • e.symm (Pi.single j 1) := by
    simpa using (congrArg e.symm ((Pi.basisFun ℝ (Fin r)).sum_equivFun (e v))).symm
  conv_lhs => rw [hex v, hex w]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

/-- Smoothness of a metric pairing along two smooth sections over a smooth
base map. This is proved from the Gram coefficients, not assumed as a field. -/
theorem metric_pairing_smoothAt
    {n r d : ℕ} {a c : ModelKind} {M : Type u} {X : Type v}
    [TopologicalSpace M] [TopologicalSpace X]
    {S : SmoothManifold n a M} (R : SmoothManifold d c X)
    {ι : Type w} {E : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (g : SmoothFiberMetric B)
    (f : X → M) (v w : ∀ x, E (f x)) (x : X)
    (hf : ManifoldSmoothAt R.smoothStructure.val S.smoothStructure.val f x)
    (hv : ManifoldSmoothAt R.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun x => (⟨f x, v x⟩ : Bundle.TotalSpace (Euclidean r) E)) x)
    (hw : ManifoldSmoothAt R.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun x => (⟨f x, w x⟩ : Bundle.TotalSpace (Euclidean r) E)) x) :
    VectorSmoothAt R.smoothStructure.val (fun y => g.form (f y) (v y) (w y)) x := by
  obtain ⟨i, hi⟩ := B.covers (f x)
  let cv : X → Euclidean r := fun y => ((B.trivialization i) ⟨f y, v y⟩).2
  let cw : X → Euclidean r := fun y => ((B.trivialization i) ⟨f y, w y⟩).2
  have hcv : VectorSmoothAt R.smoothStructure.val cv x :=
    (SmoothManifolds.Frames.trivializationCoordinates_smoothAt B i ⟨f x, v x⟩ hi).comp
      (g := fun y => (⟨f y, v y⟩ : Bundle.TotalSpace (Euclidean r) E))
      B.totalManifold.smoothStructure.property.1.1 hv
  have hcw : VectorSmoothAt R.smoothStructure.val cw x :=
    (SmoothManifolds.Frames.trivializationCoordinates_smoothAt B i ⟨f x, w x⟩ hi).comp
      (g := fun y => (⟨f y, w y⟩ : Bundle.TotalSpace (Euclidean r) E))
      B.totalManifold.smoothStructure.property.1.1 hw
  let gram : Fin r → Fin r → M → ℝ := fun j k p =>
    g.form p ((B.trivialization i).symm p (Pi.single j 1))
      ((B.trivialization i).symm p (Pi.single k 1))
  have hgram (j k : Fin r) :
      VectorSmoothAt R.smoothStructure.val (fun y => gram j k (f y)) x :=
    (show VectorSmoothAt S.smoothStructure.val (gram j k) (f x) from
      g.smooth i j k (f x) hi).comp S.smoothStructure.property.1.1 hf
  have hsum : VectorSmoothAt R.smoothStructure.val
      (fun y => ∑ j : Fin r, ∑ k : Fin r, cv y j * (cw y k * gram j k (f y))) x := by
    apply SmoothManifolds.FrameData.VectorSmoothAt.sum
    intro j
    apply SmoothManifolds.FrameData.VectorSmoothAt.sum
    intro k
    have hj := hcv.postcomp (ContinuousLinearMap.proj (R := ℝ) j).contDiff
    have hk := hcw.postcomp (ContinuousLinearMap.proj (R := ℝ) k).contDiff
    exact (hj.prod ((hk.prod (hgram j k)).postcomp
      (contDiff_fst.mul contDiff_snd))).postcomp (contDiff_fst.mul contDiff_snd)
  apply hsum.congr
  have hO : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  filter_upwards [hf.1.preimage_mem_nhds (hO.mem_nhds hi)] with y hy
  exact (bilinear_coordinates (B.fiberCoordinates i (f y) hy)
    (g.form (f y)) (v y) (w y)).symm

section Pullback
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

/-- The differential acts smoothly on the fixed realizations of the original
intrinsic tangent bundles. The P104 realization maps supply both adapters. -/
theorem differential_totalMap_smooth (f : M → N) (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p)) :
    IsSmoothMap (tangentRealization S).space.bundle.totalManifold
      (tangentRealization T).space.bundle.totalManifold
      (fun q => (⟨f q.proj, L q.proj q.snd⟩ :
        Bundle.TotalSpace (Euclidean m) (TangentSpace T))) := by
  letI := (tangentStructure S).topology
  letI := (tangentStructure T).topology
  have hm := SmoothManifolds.TangentBundle.map_smooth S T
    (tangentStructure S) (tangentStructure T) f hf L hL
  have h1 := SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    (tangentStructure S).manifold.smoothStructure.property.1.1 _ _
    (tangentRealization S).smooth_to_original hm
  have h2 := SmoothManifolds.manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    (tangentStructure T).manifold.smoothStructure.property.1.1 _ _
    h1 (tangentRealization T).smooth_from_original
  exact h2

/-- Standard local tangent-frame sections are smooth at every point in their
chart domain; their globally defined values outside it impose no hypothesis. -/
theorem localFrame_smoothAt (i : TangentIndex S) (j : Fin n) (p : M)
    (hi : p ∈ (tangentRealization S).space.bundle.baseSet i) :
    ManifoldSmoothAt S.smoothStructure.val
      (tangentRealization S).space.bundle.totalManifold.smoothStructure.val
      (fun q => (⟨q, ((tangentRealization S).space.bundle.trivialization i).symm
        q (Pi.single j 1)⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) p := by
  let B := (tangentRealization S).space.bundle
  apply SmoothManifolds.Frames.smoothAt_from_trivialization B
    S.smoothStructure.property.1 i hi
    (SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 p)
    (SmoothManifolds.FrameData.VectorSmoothAt.const _ (Pi.single j 1) p) (fun _ => rfl)
  have hO : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  filter_upwards [hO.mem_nhds hi] with q hq
  exact (B.fiberCoordinates i q hq).apply_symm_apply (Pi.single j 1)

@[simp] theorem pullbackForm_apply (h : RiemannianMetric T) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (p : M) (v w : TangentSpace S p) :
    pullbackForm h f L p v w = pairing h (f p) (L p v) (L p w) := rfl

theorem pullbackForm_symmetric (h : RiemannianMetric T) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (p : M) (v w : TangentSpace S p) :
    pullbackForm h f L p v w = pullbackForm h f L p w v :=
  h.symmetric (f p) (L p v) (L p w)

theorem pullbackForm_positive (h : RiemannianMetric T) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, Function.Injective (L p)) (p : M)
    (v : TangentSpace S p) (hv : v ≠ 0) :
    0 < pullbackForm h f L p v v := by
  apply h.positive
  intro hz
  apply hv
  apply hL p
  simpa using hz

/-- Smoothness of the immersion pullback in every standard tangent chart. -/
theorem pullbackForm_smooth (h : RiemannianMetric T) (f : M → N)
    (i : SmoothImmersion S T f) :
    ∀ (c : TangentIndex S) (j k : Fin n), SmoothOnBase S
      (fun p => pullbackForm h f i.differential p
        (((tangentRealization S).space.bundle.trivialization c).symm p (Pi.single j 1))
        (((tangentRealization S).space.bundle.trivialization c).symm p (Pi.single k 1)))
      ((tangentRealization S).space.bundle.baseSet c) := by
  intro c j k p hp
  let B := (tangentRealization S).space.bundle
  let v : ∀ q, TangentSpace S q :=
    fun q => (B.trivialization c).symm q (Pi.single j 1)
  let w : ∀ q, TangentSpace S q :=
    fun q => (B.trivialization c).symm q (Pi.single k 1)
  have hm := differential_totalMap_smooth f i.smooth i.differential i.isDifferential
  have hv := SmoothManifolds.manifoldContDiffAt_comp
    B.totalManifold.smoothStructure.property.1.1
    (localFrame_smoothAt c j p hp) (hm ⟨p, v p⟩)
  have hw := SmoothManifolds.manifoldContDiffAt_comp
    B.totalManifold.smoothStructure.property.1.1
    (localFrame_smoothAt c k p hp) (hm ⟨p, w p⟩)
  exact metric_pairing_smoothAt S (tangentRealization T).space.bundle h f
    (fun q => i.differential q (v q)) (fun q => i.differential q (w q)) p
    (i.smooth p) hv hw

/-- Pullback by any smooth immersion, including in dimension zero and over
ordinary-boundary models. No compactness or connectedness is required. -/
noncomputable def pullbackMetric (h : RiemannianMetric T) (f : M → N)
    (i : SmoothImmersion S T f) : RiemannianMetric S where
  form := pullbackForm h f i.differential
  symmetric := pullbackForm_symmetric h f i.differential
  positive := pullbackForm_positive h f i.differential i.injective
  smooth := pullbackForm_smooth h f i

@[simp] theorem pullbackMetric_pairing (h : RiemannianMetric T) (f : M → N)
    (i : SmoothImmersion S T f) (p : M) (v w : TangentSpace S p) :
    pairing (pullbackMetric h f i) p v w =
      pairing h (f p) (i.differential p v) (i.differential p w) := rfl

theorem metricPreserving_norm (g : RiemannianMetric S) (h : RiemannianMetric T)
    (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (heq : IsMetricPreserving g h f L) (p : M) (v : TangentSpace S p) :
    tangentNorm h (f p) (L p v) = tangentNorm g p v := by
  unfold tangentNorm
  rw [heq]

theorem localIsometry_isIsometricImmersion (g : RiemannianMetric S)
    (h : RiemannianMetric T) (f : M → N) (hf : IsLocalIsometry g h f) :
    IsIsometricImmersion g h f := by
  obtain ⟨hlocal, L, hL, heq⟩ := hf
  obtain ⟨e, he⟩ := SmoothManifolds.Tensors.local_diffeomorphism_differential S T f hlocal
  have hinj (p : M) : Function.Injective (L p) := by
    have h := (SmoothManifolds.differential_exists S T f hlocal.1 p).unique (hL p) (he p)
    rw [h]
    exact (e p).injective
  exact ⟨⟨hlocal.1, L, hL, hinj⟩, heq⟩

end Pullback

theorem pullback_metric : P202Specs.Geometry.SmoothMetrics.pullback_metricType.{u} := by
  intro n m a b M N _ _ S T f i h
  exact ⟨pullbackMetric h f i, fun _ _ _ => rfl⟩

theorem smoothImmersion_iff :
    P202Specs.Geometry.SmoothMetrics.smoothImmersion_iffType.{u} := by
  intro n m a b M N _ _ S T f
  constructor
  · rintro ⟨i⟩
    refine ⟨i.smooth, fun p => ?_⟩
    exact (SmoothManifolds.MapClasses.smooth_tangent_invariants S T f i.smooth p
      (i.differential p) (i.isDifferential p)).2.1.mpr (i.injective p)
  · rintro ⟨hf, hi⟩
    let L := SmoothManifolds.differential S T f hf
    have hL := SmoothManifolds.differential_spec S T f hf
    exact ⟨⟨hf, L, hL, fun p =>
      (SmoothManifolds.MapClasses.smooth_tangent_invariants S T f hf p (L p)
        (hL p)).2.1.mp (hi p)⟩⟩

theorem pullback_metric_original :
    P202Specs.Geometry.SmoothMetrics.pullback_metric_originalType.{u} := by
  intro n m a b M N _ _ S T f hf hi h
  let L := SmoothManifolds.differential S T f hf
  have hL := SmoothManifolds.differential_spec S T f hf
  let i : SmoothImmersion S T f := ⟨hf, L, hL, fun p =>
    (SmoothManifolds.MapClasses.smooth_tangent_invariants S T f hf p (L p)
      (hL p)).2.1.mp (hi p)⟩
  exact ⟨pullbackMetric h f i, fun _ _ _ => rfl⟩

/-- Public names for the independent shared objects. -/
abbrev Metric := @P202.MetricData.RiemannianMetric
abbrev metricPairing := @P202.MetricData.pairing
noncomputable abbrev metricNorm := @P202.MetricData.tangentNorm
abbrev Immersion := @P202.MetricData.SmoothImmersion
abbrev metricPullbackForm := @P202.MetricData.pullbackForm
abbrev MetricPreserving := @P202.MetricData.IsMetricPreserving
abbrev IsometricImmersion := @P202.MetricData.IsIsometricImmersion
abbrev LocalIsometry := @P202.MetricData.IsLocalIsometry

end P202.Geometry.SmoothMetrics
