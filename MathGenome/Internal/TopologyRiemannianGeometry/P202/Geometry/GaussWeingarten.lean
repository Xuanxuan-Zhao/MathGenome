import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.GaussWeingarten
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothMetrics
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.MetricSplittings

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

namespace P202.Geometry.GaussWeingarten
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.DifferentialData SmoothManifolds.BundleData
  SmoothManifolds.FrameData SmoothManifolds.BundleOperationsData
  SmoothManifolds.BundleMetricData SmoothManifolds.MetricSplittingData
  SmoothManifolds.ConstantRankData SmoothManifolds.SectionExtensionData
  P202.ConnectionData P202.MetricData P202.LeviCivitaData P202.GaussWeingartenData
open Set Filter
open scoped Topology
universe u

section Setup
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M → N}

/-- Constant sections of a bundle chart, extended arbitrarily outside the
chart, are smooth at each point of that chart. -/
theorem frame_vector_smoothAt
    {r : ℕ} {ι : Type u} {E : M → Type u}
    [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (B : SmoothVectorBundle S r ι E) (c : ι) (v : Euclidean r)
    (p : M) (hp : p ∈ B.baseSet c) :
    ManifoldSmoothAt S.smoothStructure.val B.totalManifold.smoothStructure.val
      (fun q => (⟨q, (B.trivialization c).symm q v⟩ :
        Bundle.TotalSpace (Euclidean r) E)) p := by
  apply SmoothManifolds.Frames.smoothAt_from_trivialization B
    S.smoothStructure.property.1 c hp
    (SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 p)
    (VectorSmoothAt.const _ v p) (fun _ => rfl)
  have hO : IsOpen (B.baseSet c) :=
    B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  filter_upwards [hO.mem_nhds hp] with q hq
  exact (B.fiberCoordinates c q hq).apply_symm_apply v

/-- Pulling back the metric does not require any rank assumption on F. -/
noncomputable def pullbackMetric (h : RiemannianMetric T)
    (hf : IsSmoothMap S T F) (P : PullbackBundle (tangentBundle T) S F) :
    letI := P.space.topology; SmoothFiberMetric P.space.bundle := by
  letI := P.space.topology
  refine ⟨fun p => h.form (F p), fun p => h.symmetric (F p),
    fun p => h.positive (F p), ?_⟩
  intro c j k p hp
  have hv (l : Fin m) := SmoothManifolds.manifoldContDiffAt_comp
    P.space.bundle.totalManifold.smoothStructure.property.1.1
    (frame_vector_smoothAt P.space.bundle c (Pi.single l 1) p hp)
    (P.canonical_smooth _)
  exact SmoothMetrics.metric_pairing_smoothAt S (tangentBundle T) h F
    (fun q => (P.space.bundle.trivialization c).symm q (Pi.single j 1))
    (fun q => (P.space.bundle.trivialization c).symm q (Pi.single k 1))
    p (hf p) (hv j) (hv k)

@[simp] theorem pullbackMetric_form (h : RiemannianMetric T)
    (hf : IsSmoothMap S T F) (P : PullbackBundle (tangentBundle T) S F) (p : M) :
    letI := P.space.topology
    (pullbackMetric h hf P).form p = h.form (F p) := rfl

/-- dF is a genuine smooth morphism into F*TN, not merely a fiberwise family. -/
noncomputable def differentialMorphism (i : SmoothImmersion S T F)
    (P : PullbackBundle (tangentBundle T) S F) :
    letI := P.space.topology; SmoothBundleMorphism (tangentBundle S) P.space.bundle := by
  letI := P.space.topology
  refine ⟨i.differential, ?_⟩
  exact SmoothManifolds.BundleOperations.pullback_smooth_lift (tangentBundle T) P
    (tangentBundle S).totalManifold (fun q => q.proj)
    (fun q => i.differential q.proj q.snd)
    (tangentBundle S).projection_smooth
    (SmoothMetrics.differential_totalMap_smooth F i.smooth i.differential i.isDifferential)

theorem tangent_image_rank (i : SmoothImmersion S T F) (p : M) :
    Module.finrank ℝ (tangentImage i p) = n := by
  rw [tangentImage, LinearMap.finrank_range_of_inj (i.injective p)]
  exact SmoothManifolds.ConstantRankBundles.finrank_fiber (tangentBundle S) p

theorem tangent_image_smooth (i : SmoothImmersion S T F)
    (P : PullbackBundle (tangentBundle T) S F) :
    letI := P.space.topology
    IsSmoothSubbundle P.space.bundle n (tangentImage i) := by
  letI := P.space.topology
  exact (SmoothManifolds.ConstantRankBundles.kernel_image_subbundles
    (tangentBundle S) P.space.bundle (differentialMorphism i P) n
    (tangent_image_rank i)).2.1

theorem orthogonal_splitting_exists (i : SmoothImmersion S T F)
    (P : PullbackBundle (tangentBundle T) S F)
    (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle) :
    letI := P.space.topology
    Nonempty (OrthogonalSplitting P.space.bundle hP (tangentImage i) n) := by
  letI := P.space.topology
  exact SmoothManifolds.MetricSplittings.orthogonal_splitting
    P.space.bundle hP (tangentImage i) n (tangent_image_smooth i P)

/-- Replace the image summand by the original tangent fiber, using the
injective differential. This is an actual linear equivalence on each fiber. -/
noncomputable def adaptedFiberEquiv (i : SmoothImmersion S T F)
    (P : PullbackBundle (tangentBundle T) S F)
    (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
    (W : letI := P.space.topology;
      OrthogonalSplitting P.space.bundle hP (tangentImage i) n) (p : M) :
    letI := P.space.topology
    (TangentSpace S p × orthogonal P.space.bundle hP (tangentImage i) p) ≃ₗ[ℝ]
      TangentSpace T (F p) :=
  by
  letI := P.space.topology
  exact ((LinearEquiv.ofInjective (i.differential p) (i.injective p)).prodCongr
    (LinearEquiv.refl ℝ _)).trans (Submodule.prodEquivOfIsCompl (tangentImage i p)
      (orthogonal P.space.bundle hP (tangentImage i) p) (W.complementary p))

@[simp] theorem adaptedFiberEquiv_apply (i : SmoothImmersion S T F)
    (P : PullbackBundle (tangentBundle T) S F)
    (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
    (W : letI := P.space.topology;
      OrthogonalSplitting P.space.bundle hP (tangentImage i) n) (p : M)
    (v : letI := P.space.topology
      TangentSpace S p × (hP.form p).orthogonal (tangentImage i p)) :
    adaptedFiberEquiv i P hP W p v = i.differential p v.1 + v.2.val := rfl

noncomputable def adaptedSplitting (i : SmoothImmersion S T F)
    (P : PullbackBundle (tangentBundle T) S F)
    (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle) :
    AdaptedSplitting i P hP := by
  letI := P.space.topology
  let W := Classical.choice (orthogonal_splitting_exists i P hP)
  letI := W.right.topology
  let V := Classical.choice (SmoothManifolds.BundleOperations.exists_directSum
    (tangentBundle S) W.right.bundle)
  letI := V.space.topology
  let e := adaptedFiberEquiv i P hP W
  have he : IsSmoothMap V.space.bundle.totalManifold P.space.bundle.totalManifold
      (fun q => (⟨q.proj, e q.proj q.snd⟩ :
        Bundle.TotalSpace (Euclidean m) (fun p => TangentSpace T (F p)))) :=
    SmoothManifolds.MetricSplittings.coprod_smooth
      (tangentBundle S) P.space.bundle W.right.bundle
      (differentialMorphism i P) ⟨fun p => (orthogonal P.space.bundle hP
        (tangentImage i) p).subtype, W.right_inclusion⟩ V
  exact ⟨W, V, ⟨e, he, SmoothManifolds.MetricSplittings.inverse_smooth
    V.space.bundle P.space.bundle e he⟩, fun _ _ => rfl⟩

end Setup

theorem pullback_metric_exists :
    P202Specs.Geometry.GaussWeingarten.pullback_metric_existsType.{u} := by
  intro n m a b M N _ _ S T h F hf P
  exact ⟨pullbackMetric h hf P, fun _ => rfl⟩

theorem adapted_splitting_exists :
    P202Specs.Geometry.GaussWeingarten.adapted_splitting_existsType.{u} := by
  intro n m a b M N _ _ S T F i P hP
  exact ⟨adaptedSplitting i P hP⟩


section BundleMaps
variable {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι κ : Type u} {E G : M → Type u}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean s) G)]
  (B : SmoothVectorBundle S r ι E) (J : SmoothVectorBundle S s κ G)

/-- A smooth bundle morphism acts linearly on the actual smooth sections. -/
noncomputable def mapSections (L : SmoothBundleMorphism B J) :
    Section B →ₗ[ℝ] Section J :=
  InducedConnections.fiberLinearMapSection B J L.linearMap (fun s p =>
    SmoothManifolds.manifoldContDiffAt_comp B.totalManifold.smoothStructure.property.1.1
      (s.property p) (L.smooth _))

@[simp] theorem mapSections_apply (L : SmoothBundleMorphism B J) (s : Section B) (p : M) :
    (mapSections B J L s).val p = L.linearMap p (s.val p) := rfl

@[simp] theorem mapSections_mul (L : SmoothBundleMorphism B J)
    (f : SmoothManifolds.TangentData.GlobalSmooth S) (s : Section B) :
    mapSections B J L (mulSection f s) = mulSection f (mapSections B J L s) := by
  apply Subtype.ext
  funext p
  exact map_smul (L.linearMap p) (f.val p) (s.val p)

/-- The first projection is smooth for the specified canonical direct sum. -/
noncomputable def sumFirst (V : DirectSumBundle B J) :
    letI := V.space.topology; SmoothBundleMorphism V.space.bundle B := by
  letI := V.space.topology
  refine ⟨fun p => LinearMap.fst ℝ (E p) (G p), ?_⟩
  apply SmoothManifolds.MetricSplittings.smooth_of_columns V.space.bundle B
    (fun p => LinearMap.fst ℝ (E p) (G p))
  intro p
  obtain ⟨i, hi⟩ := B.covers p
  obtain ⟨j, hj⟩ := J.covers p
  refine ⟨(i,j), i, (V.baseSet (i,j)).symm ▸ ⟨hi,hj⟩, hi, fun l => ?_⟩
  apply (VectorSmoothAt.const S.smoothStructure.val
    ((SmoothManifolds.BundleOperations.sumCoordinates r s).symm (Pi.single l 1)).1 p).congr
  have hiO : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  have hjO : IsOpen (J.baseSet j) :=
    J.trivialization_baseSet j ▸ (J.trivialization j).open_baseSet
  filter_upwards [(hiO.inter hjO).mem_nhds ⟨hi,hj⟩] with q hq
  have he := SmoothManifolds.MetricSplittings.sum_fiberCoordinates B J V i j q hq.1 hq.2
  change _ = (B.fiberCoordinates i q hq.1)
    ((V.space.bundle.fiberCoordinates (i,j) q ((V.baseSet (i,j)).symm ▸ hq)).symm
      (Pi.single l 1)).1
  rw [he]
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply]
  exact ((B.fiberCoordinates i q hq.1).apply_symm_apply _).symm

/-- The second projection is smooth, including in codimension zero. -/
noncomputable def sumSecond (V : DirectSumBundle B J) :
    letI := V.space.topology; SmoothBundleMorphism V.space.bundle J := by
  letI := V.space.topology
  refine ⟨fun p => LinearMap.snd ℝ (E p) (G p), ?_⟩
  apply SmoothManifolds.MetricSplittings.smooth_of_columns V.space.bundle J
    (fun p => LinearMap.snd ℝ (E p) (G p))
  intro p
  obtain ⟨i, hi⟩ := B.covers p
  obtain ⟨j, hj⟩ := J.covers p
  refine ⟨(i,j), j, (V.baseSet (i,j)).symm ▸ ⟨hi,hj⟩, hj, fun l => ?_⟩
  apply (VectorSmoothAt.const S.smoothStructure.val
    ((SmoothManifolds.BundleOperations.sumCoordinates r s).symm (Pi.single l 1)).2 p).congr
  have hiO : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  have hjO : IsOpen (J.baseSet j) :=
    J.trivialization_baseSet j ▸ (J.trivialization j).open_baseSet
  filter_upwards [(hiO.inter hjO).mem_nhds ⟨hi,hj⟩] with q hq
  have he := SmoothManifolds.MetricSplittings.sum_fiberCoordinates B J V i j q hq.1 hq.2
  change _ = (J.fiberCoordinates j q hq.2)
    ((V.space.bundle.fiberCoordinates (i,j) q ((V.baseSet (i,j)).symm ▸ hq)).symm
      (Pi.single l 1)).2
  rw [he]
  simp only [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_symm, LinearEquiv.prodCongr_apply]
  exact ((J.fiberCoordinates j q hq.2).apply_symm_apply _).symm

end BundleMaps


section ProjectedConnection
variable {n r s : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι κ : Type u} {E G : M → Type u}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean s) G)]
  (B : SmoothVectorBundle S r ι E) (J : SmoothVectorBundle S s κ G)

/-- Pull back a fiber metric by a smooth injective bundle morphism. -/
noncomputable def inducedMetric (L : SmoothBundleMorphism B J)
    (hL : ∀ p, Function.Injective (L.linearMap p)) (g : SmoothFiberMetric J) :
    SmoothFiberMetric B where
  form p := (g.form p).compl₁₂ (L.linearMap p) (L.linearMap p)
  symmetric p v w := g.symmetric p _ _
  positive p v hv := g.positive p _ (fun hz =>
    hv (hL p (by simpa only [map_zero] using hz)))
  smooth c j k p hp := by
    have hv (l : Fin r) := SmoothManifolds.manifoldContDiffAt_comp
      B.totalManifold.smoothStructure.property.1.1
      (frame_vector_smoothAt B c (Pi.single l 1) p hp) (L.smooth _)
    exact SmoothMetrics.metric_pairing_smoothAt S J g id
      (fun q => L.linearMap q ((B.trivialization c).symm q (Pi.single j 1)))
      (fun q => L.linearMap q ((B.trivialization c).symm q (Pi.single k 1))) p
      (SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1 p)
      (hv j) (hv k)

/-- Projection of an ambient connection to a smooth direct summand. The
left-inverse identity is only the ordinary algebraic identity on fibers. -/
noncomputable def projectedConnection (I : SmoothBundleMorphism B J)
    (R : SmoothBundleMorphism J B)
    (hRI : ∀ p v, R.linearMap p (I.linearMap p v) = v)
    (D : Connection J) : Connection B where
  cov := {
    toFun X := (mapSections J B R).comp ((D.cov X).comp (mapSections B J I))
    map_add' X Y := by
      ext s p
      change R.linearMap p ((D.cov (X + Y) (mapSections B J I s)).val p) = _
      rw [map_add]
      change R.linearMap p
        ((D.cov X (mapSections B J I s)).val p +
          (D.cov Y (mapSections B J I s)).val p) = _
      exact map_add (R.linearMap p) _ _
    map_smul' c X := by
      ext s p
      change R.linearMap p ((D.cov (c • X) (mapSections B J I s)).val p) = _
      rw [map_smul]
      change R.linearMap p (c • (D.cov X (mapSections B J I s)).val p) = _
      exact map_smul (R.linearMap p) c _ }
  linear_field f X s := by
    change mapSections J B R (D.cov (mulSection f X) (mapSections B J I s)) = _
    rw [D.linear_field, mapSections_mul]
    rfl
  leibniz X f s := by
    change mapSections J B R (D.cov X (mapSections B J I (mulSection f s))) = _
    rw [mapSections_mul, D.leibniz, map_add, mapSections_mul, mapSections_mul]
    have h : mapSections J B R (mapSections B J I s) = s := by
      apply Subtype.ext
      funext p
      exact hRI p (s.val p)
    rw [h]
    rfl

end ProjectedConnection


section GeometricProjections
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M → N} (i : SmoothImmersion S T F)
  (P : PullbackBundle (tangentBundle T) S F)

  (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
  (W : AdaptedSplitting i P hP)

noncomputable def tangentProjectionMorphism :
    letI := P.space.topology
    SmoothBundleMorphism P.space.bundle (tangentBundle S) := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  refine ⟨fun p => (LinearMap.fst ℝ _ _).comp (W.iso.equiv p).symm.toLinearMap, ?_⟩
  intro q
  exact SmoothManifolds.manifoldContDiffAt_comp
    W.sum.space.bundle.totalManifold.smoothStructure.property.1.1
    (W.iso.inverse_smooth q)
    ((sumFirst (tangentBundle S) W.orthogonal.right.bundle W.sum).smooth _)

noncomputable def normalProjectionMorphism :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    SmoothBundleMorphism P.space.bundle W.orthogonal.right.bundle := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  refine ⟨fun p => (LinearMap.snd ℝ _ _).comp (W.iso.equiv p).symm.toLinearMap, ?_⟩
  intro q
  exact SmoothManifolds.manifoldContDiffAt_comp
    W.sum.space.bundle.totalManifold.smoothStructure.property.1.1
    (W.iso.inverse_smooth q)
    ((sumSecond (tangentBundle S) W.orthogonal.right.bundle W.sum).smooth _)

noncomputable def normalInclusionMorphism :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    SmoothBundleMorphism W.orthogonal.right.bundle P.space.bundle := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  exact ⟨fun p => (orthogonal P.space.bundle hP (tangentImage i) p).subtype,
    W.orthogonal.right_inclusion⟩

theorem inverse_on_sum (p : M) (v : TangentSpace S p)
    (z : letI := P.space.topology; (hP.form p).orthogonal (tangentImage i p)) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    letI := W.sum.space.topology
    (W.iso.equiv p).symm (i.differential p v + z.val) = (v,z) := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  rw [← W.canonical p (v,z), LinearEquiv.symm_apply_apply]

@[simp] theorem tangentProjection_image (p : M) (v : TangentSpace S p) :
    letI := P.space.topology
    (tangentProjectionMorphism i P hP W).linearMap p (i.differential p v) = v := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  have h := inverse_on_sum i P hP W p v 0
  simpa only [tangentProjectionMorphism, LinearMap.comp_apply, LinearMap.fst_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_coe,
    Submodule.coe_zero, add_zero] using congrArg Prod.fst h

@[simp] theorem normalProjection_normal (p : M)
    (z : letI := P.space.topology; (hP.form p).orthogonal (tangentImage i p)) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    (normalProjectionMorphism i P hP W).linearMap p z.val = z := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  have h := inverse_on_sum i P hP W p 0 z
  simpa only [normalProjectionMorphism, LinearMap.comp_apply, LinearMap.snd_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_coe,
    map_zero, zero_add] using congrArg Prod.snd h

/-- The tangent projection of a normal vector vanishes. -/
@[simp] theorem tangentProjection_normal (p : M)
    (z : letI := P.space.topology; (hP.form p).orthogonal (tangentImage i p)) :
    letI := P.space.topology
    (tangentProjectionMorphism i P hP W).linearMap p z.val = 0 := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  have h := inverse_on_sum i P hP W p 0 z
  simpa only [tangentProjectionMorphism, LinearMap.comp_apply, LinearMap.fst_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_coe,
    map_zero, zero_add] using congrArg Prod.fst h

/-- The normal projection of a tangent vector vanishes. -/
@[simp] theorem normalProjection_image (p : M) (v : TangentSpace S p) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    (normalProjectionMorphism i P hP W).linearMap p (i.differential p v) = 0 := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  have h := inverse_on_sum i P hP W p v 0
  simpa only [normalProjectionMorphism, LinearMap.comp_apply, LinearMap.snd_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_coe,
    Submodule.coe_zero, add_zero] using congrArg Prod.snd h

/-- The induced metric is the restriction of the ambient pullback metric. -/
noncomputable def normalMetric :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    SmoothFiberMetric W.orthogonal.right.bundle := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  exact inducedMetric W.orthogonal.right.bundle P.space.bundle
    (normalInclusionMorphism i P hP W) (fun _ => Subtype.val_injective) hP

noncomputable def tangentConnection
    (D : letI := P.space.topology; Connection P.space.bundle) :
    Connection (tangentBundle S) := by
  letI := P.space.topology
  exact projectedConnection (tangentBundle S) P.space.bundle
    (differentialMorphism i P) (tangentProjectionMorphism i P hP W)
    (tangentProjection_image i P hP W) D

noncomputable def normalConnection
    (D : letI := P.space.topology; Connection P.space.bundle) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    Connection W.orthogonal.right.bundle := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  exact projectedConnection W.orthogonal.right.bundle P.space.bundle
    (normalInclusionMorphism i P hP W) (normalProjectionMorphism i P hP W)
    (normalProjection_normal i P hP W) D


@[simp] theorem normalMetric_apply (p : M)
    (v w : letI := P.space.topology; (hP.form p).orthogonal (tangentImage i p)) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    (normalMetric i P hP W).form p v w = hP.form p v.val w.val := rfl

@[simp] theorem tangentConnection_apply
    (D : letI := P.space.topology; Connection P.space.bundle)
    (X Y : Field S) (p : M) :
    letI := P.space.topology
    ((tangentConnection i P hP W D).cov X Y).val p =
      (tangentProjectionMorphism i P hP W).linearMap p
        ((D.cov X (mapSections (tangentBundle S) P.space.bundle
          (differentialMorphism i P) Y)).val p) := rfl

@[simp] theorem normalConnection_apply
    (D : letI := P.space.topology; Connection P.space.bundle)
    (X : Field S)
    (s : letI := P.space.topology; letI := W.orthogonal.right.topology
      Section W.orthogonal.right.bundle) (p : M) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    ((normalConnection i P hP W D).cov X s).val p =
      (normalProjectionMorphism i P hP W).linearMap p
        ((D.cov X (mapSections W.orthogonal.right.bundle P.space.bundle
          (normalInclusionMorphism i P hP W) s)).val p) := rfl

/-- The two projections reconstruct every vector of the ambient pullback fiber. -/
theorem projection_decomposition (p : M) (x : TangentSpace T (F p)) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    i.differential p ((tangentProjectionMorphism i P hP W).linearMap p x) +
      ((normalProjectionMorphism i P hP W).linearMap p x).val = x := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  change i.differential p ((W.iso.equiv p).symm x).1 +
    (((W.iso.equiv p).symm x).2).val = x
  rw [← W.canonical p ((W.iso.equiv p).symm x), LinearEquiv.apply_symm_apply]

theorem tangent_normal_orthogonal (p : M) (v : TangentSpace S p)
    (z : letI := P.space.topology; (hP.form p).orthogonal (tangentImage i p)) :
    letI := P.space.topology
    hP.form p (i.differential p v) z.val = 0 := by
  letI := P.space.topology
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp z.property)
    (i.differential p v) ⟨v, rfl⟩

/-- Pairing with tangent vectors discards exactly the normal projection. -/
theorem pairing_tangentProjection (g : RiemannianMetric S)
    (hi : letI := P.space.topology
      ∀ p v w, hP.form p (i.differential p v) (i.differential p w) = pairing g p v w)
    (p : M) (x : TangentSpace T (F p)) (v : TangentSpace S p) :
    letI := P.space.topology
    hP.form p x (i.differential p v) =
      pairing g p ((tangentProjectionMorphism i P hP W).linearMap p x) v := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  have he := projection_decomposition i P hP W p x
  have h := congrArg (fun y => hP.form p y (i.differential p v)) he
  rw [map_add, LinearMap.add_apply, hi, hP.symmetric p
    (((normalProjectionMorphism i P hP W).linearMap p x).val) (i.differential p v),
    tangent_normal_orthogonal i P hP, add_zero] at h
  exact h.symm

/-- Pairing with a normal vector discards exactly the tangent projection. -/
theorem pairing_normalProjection (p : M) (x : TangentSpace T (F p))
    (z : letI := P.space.topology; (hP.form p).orthogonal (tangentImage i p)) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    hP.form p x z.val =
      (normalMetric i P hP W).form p ((normalProjectionMorphism i P hP W).linearMap p x) z := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  have he := projection_decomposition i P hP W p x
  have h := congrArg (fun y => hP.form p y z.val) he
  rw [map_add, LinearMap.add_apply, tangent_normal_orthogonal i P hP, zero_add] at h
  exact h.symm

/-- Projection of a metric connection onto the normal bundle is metric. -/
theorem normalConnection_metric
    (D : letI := P.space.topology; Connection P.space.bundle)
    (hD : letI := P.space.topology;
      P202.TorsionMetricData.MetricCompatible P.space.bundle D hP) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    P202.TorsionMetricData.MetricCompatible W.orthogonal.right.bundle
      (normalConnection i P hP W D) (normalMetric i P hP W) := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  intro X s t p
  simp only [normalConnection_apply, normalMetric_apply]
  let sp := mapSections W.orthogonal.right.bundle P.space.bundle
    (normalInclusionMorphism i P hP W) s
  let tp := mapSections W.orthogonal.right.bundle P.space.bundle
    (normalInclusionMorphism i P hP W) t
  have hh := hD X sp tp p
  change scalarDerivative S
    (fun q => hP.form q (s.val q).val (t.val q).val) p (X.val p) = _
  calc
    _ = hP.form p ((D.cov X sp).val p) (t.val p).val +
        hP.form p (s.val p).val ((D.cov X tp).val p) := hh
    _ = _ := by
      have h1 := pairing_normalProjection i P hP W p ((D.cov X sp).val p) (t.val p)
      have h2 := pairing_normalProjection i P hP W p ((D.cov X tp).val p) (s.val p)
      simp only [normalMetric_apply] at h1 h2
      rw [h1, hP.symmetric p (s.val p).val ((D.cov X tp).val p), h2,
        hP.symmetric p (((normalProjectionMorphism i P hP W).linearMap p
          ((D.cov X tp).val p)).val) (s.val p).val]

/-- Projection onto the tangent bundle is compatible with the induced metric. -/
theorem tangentConnection_metric (g : RiemannianMetric S)
    (hi : letI := P.space.topology
      ∀ p v w, hP.form p (i.differential p v) (i.differential p w) = pairing g p v w)
    (D : letI := P.space.topology; Connection P.space.bundle)
    (hD : letI := P.space.topology;
      P202.TorsionMetricData.MetricCompatible P.space.bundle D hP) :
    IsMetricCompatible g (tangentConnection i P hP W D) := by
  letI := P.space.topology
  intro X Y Z p
  simp only [tangentConnection_apply]
  let Yp := mapSections (tangentBundle S) P.space.bundle (differentialMorphism i P) Y
  let Zp := mapSections (tangentBundle S) P.space.bundle (differentialMorphism i P) Z
  have hh := hD X Yp Zp p
  have he : (fun q => hP.form q (Yp.val q) (Zp.val q)) =
      (fun q => pairing g q (Y.val q) (Z.val q)) := funext (fun q => hi q _ _)
  rw [he] at hh
  calc
    _ = hP.form p ((D.cov X Yp).val p) (i.differential p (Z.val p)) +
        hP.form p (i.differential p (Y.val p)) ((D.cov X Zp).val p) := hh
    _ = _ := by
      rw [pairing_tangentProjection i P hP W g hi,
        hP.symmetric p (i.differential p (Y.val p)) ((D.cov X Zp).val p),
        pairing_tangentProjection i P hP W g hi]
      rw [show pairing g p
        ((tangentProjectionMorphism i P hP W).linearMap p ((D.cov X Zp).val p))
        (Y.val p) = pairing g p (Y.val p)
        ((tangentProjectionMorphism i P hP W).linearMap p ((D.cov X Zp).val p))
        from g.symmetric p _ _]


/-- The immersion's stored differential is the canonical intrinsic one. -/
theorem immersion_differential_eq (p : M) :
    i.differential p = SmoothManifolds.differential S T F i.smooth p :=
  (SmoothManifolds.differential_exists S T F i.smooth p).unique
    (i.isDifferential p) (SmoothManifolds.differential_spec S T F i.smooth p)

/-- Tangent projection of the torsion identity for the pullback connection. -/
theorem tangentConnection_torsionFree
    (K : Connection (tangentBundle T)) (hK : IsTorsionFree K)
    (D : letI := P.space.topology; Connection P.space.bundle)
    (hDP : letI := P.space.topology;
      P202.PullbackData.IsPullback (tangentBundle T) K F i.smooth P D) :
    IsTorsionFree (tangentConnection i P hP W D) := by
  letI := P.space.topology
  intro X Y
  apply Subtype.ext
  funext p
  let push := mapSections (tangentBundle S) P.space.bundle (differentialMorphism i P)
  have hz := (TorsionAndMetric.torsion_free_tensor K (TorsionAndMetric.torsionTensor K)
    (TorsionAndMetric.torsionFiber_apply K)).mp hK
  have h := TorsionAndMetric.differential_naturality K (TorsionAndMetric.torsionTensor K)
    (TorsionAndMetric.torsionFiber_apply K) F i.smooth P D hDP X Y (push X) (push Y)
    (fun q => by exact congrFun (congrArg DFunLike.coe (immersion_differential_eq i q)) (X.val q))
    (fun q => by exact congrFun (congrArg DFunLike.coe (immersion_differential_eq i q)) (Y.val q)) p
  rw [hz, ← immersion_differential_eq i p] at h
  have hh := congrArg ((tangentProjectionMorphism i P hP W).linearMap p) h
  simp only [LeviCivita.tangent_sub_as_add, map_add, map_smul, map_zero,
    tangentProjection_image, neg_one_smul] at hh
  rw [TorsionAndMetric.torsion_apply]
  change (tangentProjectionMorphism i P hP W).linearMap p ((D.cov X (push Y)).val p) -
    (tangentProjectionMorphism i P hP W).linearMap p ((D.cov Y (push X)).val p) -
    (P202.TorsionMetricData.bracket X Y).val p = 0
  simpa only [LeviCivita.tangent_sub_as_add, neg_one_smul] using hh

/-- The projected tangent connection is the intrinsic Levi–Civita connection. -/
theorem tangentConnection_eq_intrinsic (g : RiemannianMetric S)
    (hi : letI := P.space.topology
      ∀ p v w, hP.form p (i.differential p v) (i.differential p w) = pairing g p v w)
    (K : Connection (tangentBundle T)) (hK : IsTorsionFree K)
    (D : letI := P.space.topology; Connection P.space.bundle)
    (hDP : letI := P.space.topology;
      P202.PullbackData.IsPullback (tangentBundle T) K F i.smooth P D)
    (hD : letI := P.space.topology;
      P202.TorsionMetricData.MetricCompatible P.space.bundle D hP)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C) :
    tangentConnection i P hP W D = C :=
  LeviCivita.uniqueness g _ C
    ⟨tangentConnection_torsionFree i P hP W K hK D hDP,
      tangentConnection_metric i P hP W g hi D hD⟩ hC

end GeometricProjections


/-- All bundle and projected-connection constructions, for every isometric
immersion, without any assumption of global injectivity or a normal frame. -/
theorem projected_connections_exists :
    P202Specs.Geometry.GaussWeingarten.projected_connections_existsType.{u} := by
  intro n m a b M N _ _ S T g h F i hi C K hC hK P
  letI := P.space.topology
  let hP := pullbackMetric h i.smooth P
  let W := adaptedSplitting i P hP
  let D := PullbackConnections.pullback (tangentBundle T) F i.smooth P K
  have hDP := PullbackConnections.pullback_isPullback (tangentBundle T) F i.smooth P K
  have hD : P202.TorsionMetricData.MetricCompatible P.space.bundle D hP :=
    TorsionAndMetric.metric_map_product (tangentBundle T) h K hK.2 F i.smooth P D hDP
  have hiP : ∀ p v w,
      hP.form p (i.differential p v) (i.differential p w) = pairing g p v w := hi
  have hCT := tangentConnection_eq_intrinsic i P hP W g hiP K hK.1 D hDP hD C hC
  refine ⟨hP, D, W, fun _ => rfl, hDP, ?_⟩
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  refine ⟨normalConnection i P hP W D, normalMetric i P hP W,
    fun _ _ _ => rfl, normalConnection_metric i P hP W D hD, ?_, ?_⟩
  · intro X Y
    refine ⟨mapSections (tangentBundle S) P.space.bundle (differentialMorphism i P) Y,
      fun _ => rfl, ?_⟩
    intro p
    rw [← hCT]
    exact tangentConnection_apply i P hP W D X Y p
  · intro X xi
    refine ⟨mapSections W.orthogonal.right.bundle P.space.bundle
      (normalInclusionMorphism i P hP W) xi, fun _ => rfl, ?_⟩
    intro p
    exact normalConnection_apply i P hP W D X xi p


open SmoothManifolds.SectionExtensionData
section TensorDescent
variable {n r s t : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι κ ν : Type u} {E G H : M → Type u}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [∀ p, AddCommGroup (G p)] [∀ p, Module ℝ (G p)]
  [∀ p, AddCommGroup (H p)] [∀ p, Module ℝ (H p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean s) G)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean t) H)]
  (B : SmoothVectorBundle S r ι E) (J : SmoothVectorBundle S s κ G)
  (K : SmoothVectorBundle S t ν H)

/-- A smooth-function-linear section operator depends only on section germs. -/
theorem sectionLinear_locality (L : Section B →ₗ[ℝ] Section J)
    (hL : ∀ (f : GlobalSmooth S) (s : Section B),
      L (mulSection f s) = mulSection f (L s))
    (s t : Section B) (p : M) (h : ∀ᶠ q in 𝓝 p, s.val q = t.val q) :
    (L s).val p = (L t).val p := by
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp h
  obtain ⟨f, hfone, hfsupp⟩ := ConnectionForms.exists_cutoff_near (S := S) p U hUo hpU
  have hfp : f.val p = 1 := hfone.eq_of_nhds
  have hst : mulSection f s = mulSection f t := by
    apply Subtype.ext
    funext q
    change f.val q • s.val q = f.val q • t.val q
    by_cases hq : q ∈ U
    · rw [hU q hq]
    · have hfq : f.val q = 0 := Function.notMem_support.mp
        (fun hz => hq (hfsupp (subset_closure hz)))
      simp only [hfq, zero_smul]
  have he := congrArg (fun z : Section B => (L z).val p) hst
  simpa only [hL, ConnectionForms.mulSection_apply, hfp, one_smul] using he

/-- A smooth-function-linear section operator vanishes where its input does. -/
theorem sectionLinear_zero (L : Section B →ₗ[ℝ] Section J)
    (hL : ∀ (f : GlobalSmooth S) (s : Section B),
      L (mulSection f s) = mulSection f (L s))
    (s : Section B) (p : M) (hs : s.val p = 0) : (L s).val p = 0 := by
  obtain ⟨f, e, heq, hf⟩ := ConnectionForms.section_zero_decomposition B s p hs
  rw [sectionLinear_locality B J L hL s (∑ j, mulSection (f j) (e j)) p heq]
  simp only [map_sum, hL, Submodule.coe_sum, Finset.sum_apply,
    ConnectionForms.mulSection_apply, hf, zero_smul, Finset.sum_const_zero]

/-- Smooth-function linearity makes a section operator pointwise. -/
theorem sectionLinear_pointwise (L : Section B →ₗ[ℝ] Section J)
    (hL : ∀ (f : GlobalSmooth S) (s : Section B),
      L (mulSection f s) = mulSection f (L s))
    (s t : Section B) (p : M) (hst : s.val p = t.val p) :
    (L s).val p = (L t).val p := by
  have hz := sectionLinear_zero B J L hL (s + (-1 : ℝ) • t) p (by
    simp only [ConnectionForms.section_add_apply, ConnectionForms.section_smul_apply,
      neg_one_smul, hst, add_neg_cancel])
  simpa only [map_add, map_smul, ConnectionForms.section_add_apply,
    ConnectionForms.section_smul_apply, neg_one_smul, add_neg_eq_zero] using hz

/-- A bilinear section operator linear over smooth functions in both variables
is induced by actual bilinear maps on the individual fibers. -/
theorem sectionBilinear_descent
    (D : Section B →ₗ[ℝ] Section J →ₗ[ℝ] Section K)
    (h₁ : ∀ (f : GlobalSmooth S) (s : Section B) (t : Section J),
      D (mulSection f s) t = mulSection f (D s t))
    (h₂ : ∀ (f : GlobalSmooth S) (s : Section B) (t : Section J),
      D s (mulSection f t) = mulSection f (D s t)) :
    ∃ d : (p : M) → E p →ₗ[ℝ] G p →ₗ[ℝ] H p,
      (∀ (s : Section B) (t : Section J) p,
        d p (s.val p) (t.val p) = (D s t).val p) ∧
      (∀ (s : Section B) (t : Section J),
        SmoothSection K (fun p => d p (s.val p) (t.val p))) := by
  classical
  have hleft (s s' : Section B) (t : Section J) (p : M)
      (hs : s.val p = s'.val p) : (D s t).val p = (D s' t).val p :=
    sectionLinear_pointwise B K (D.flip t) (fun f s => h₁ f s t) s s' p hs
  have hright (s : Section B) (t t' : Section J) (p : M)
      (ht : t.val p = t'.val p) : (D s t).val p = (D s t').val p :=
    sectionLinear_pointwise J K (D s) (fun f t => h₂ f s t) t t' p ht
  choose liftB hB using ConnectionForms.section_evaluation_surjective B
  choose liftJ hJ using ConnectionForms.section_evaluation_surjective J
  let d (p : M) : E p →ₗ[ℝ] G p →ₗ[ℝ] H p := {
    toFun := fun v => {
      toFun := fun w => (D (liftB p v) (liftJ p w)).val p
      map_add' := by
        intro w z
        have hh := hright (liftB p v) (liftJ p (w + z))
          (liftJ p w + liftJ p z) p (by
            simp only [hJ, ConnectionForms.section_add_apply])
        simpa only [map_add, ConnectionForms.section_add_apply] using hh
      map_smul' := by
        intro c w
        have hh := hright (liftB p v) (liftJ p (c • w))
          (c • liftJ p w) p (by
            simp only [hJ, ConnectionForms.section_smul_apply])
        simpa only [map_smul, ConnectionForms.section_smul_apply, RingHom.id_apply] using hh }
    map_add' := by
      intro v w
      ext z
      change (D (liftB p (v + w)) (liftJ p z)).val p =
        (D (liftB p v) (liftJ p z)).val p + (D (liftB p w) (liftJ p z)).val p
      have hh := hleft (liftB p (v + w)) (liftB p v + liftB p w) (liftJ p z) p (by
        simp only [hB, ConnectionForms.section_add_apply])
      simpa only [map_add, LinearMap.add_apply, ConnectionForms.section_add_apply] using hh
    map_smul' := by
      intro c v
      ext z
      change (D (liftB p (c • v)) (liftJ p z)).val p =
        c • (D (liftB p v) (liftJ p z)).val p
      have hh := hleft (liftB p (c • v)) (c • liftB p v) (liftJ p z) p (by
        simp only [hB, ConnectionForms.section_smul_apply])
      simpa only [map_smul, LinearMap.smul_apply, ConnectionForms.section_smul_apply,
        RingHom.id_apply] using hh }
  have hd (s : Section B) (t : Section J) (p : M) :
      d p (s.val p) (t.val p) = (D s t).val p :=
    (hleft _ s _ p (hB p _)).trans (hright s _ t p (hJ p _))
  exact ⟨d, hd, fun s t p => by simpa only [hd] using (D s t).property p⟩

end TensorDescent


section SecondFundamental
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M → N} (i : SmoothImmersion S T F)
  (P : PullbackBundle (tangentBundle T) S F)
  (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
  (W : AdaptedSplitting i P hP)
  (D : letI := P.space.topology; Connection P.space.bundle)

/-- The normal part of the derivative of a tangent section. -/
noncomputable def secondFundamentalOperation :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    Field S →ₗ[ℝ] Field S →ₗ[ℝ] Section W.orthogonal.right.bundle := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  let L := mapSections (tangentBundle S) P.space.bundle (differentialMorphism i P)
  let R := mapSections P.space.bundle W.orthogonal.right.bundle
    (normalProjectionMorphism i P hP W)
  exact {
    toFun := fun X => R.comp ((D.cov X).comp L)
    map_add' := fun X Y => by
      apply LinearMap.ext
      intro Z
      apply Subtype.ext
      funext p
      change (normalProjectionMorphism i P hP W).linearMap p
        ((D.cov (X + Y) (L Z)).val p) = _
      rw [map_add]
      change (normalProjectionMorphism i P hP W).linearMap p
        ((D.cov X (L Z)).val p + (D.cov Y (L Z)).val p) = _
      exact map_add _ _ _
    map_smul' := fun c X => by
      apply LinearMap.ext
      intro Z
      apply Subtype.ext
      funext p
      change (normalProjectionMorphism i P hP W).linearMap p
        ((D.cov (c • X) (L Z)).val p) = _
      rw [map_smul]
      change (normalProjectionMorphism i P hP W).linearMap p
        (c • (D.cov X (L Z)).val p) = _
      exact map_smul _ _ _ }

@[simp] theorem secondFundamentalOperation_apply (X Y : Field S) (p : M) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    (secondFundamentalOperation i P hP W D X Y).val p =
      (normalProjectionMorphism i P hP W).linearMap p
        ((D.cov X (mapSections (tangentBundle S) P.space.bundle
          (differentialMorphism i P) Y)).val p) := rfl

theorem secondFundamentalOperation_mul_left (f : GlobalSmooth S) (X Y : Field S) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    secondFundamentalOperation i P hP W D (mulSection f X) Y =
      mulSection f (secondFundamentalOperation i P hP W D X Y) := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  apply Subtype.ext
  funext p
  simp only [secondFundamentalOperation_apply, D.linear_field]
  change (normalProjectionMorphism i P hP W).linearMap p
    (f.val p • _) = f.val p • _
  exact map_smul _ _ _

theorem secondFundamentalOperation_mul_right (f : GlobalSmooth S) (X Y : Field S) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    secondFundamentalOperation i P hP W D X (mulSection f Y) =
      mulSection f (secondFundamentalOperation i P hP W D X Y) := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  apply Subtype.ext
  funext p
  simp only [secondFundamentalOperation_apply, mapSections_mul, D.leibniz]
  change (normalProjectionMorphism i P hP W).linearMap p
    ((act S X f).val p • i.differential p (Y.val p) +
      f.val p • _) = f.val p • _
  rw [map_add, map_smul, map_smul, normalProjection_image, smul_zero, zero_add]
  rfl

theorem secondFundamentalOperation_symmetric
    (K : Connection (tangentBundle T)) (hK : IsTorsionFree K)
    (hDP : letI := P.space.topology;
      P202.PullbackData.IsPullback (tangentBundle T) K F i.smooth P D)
    (X Y : Field S) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    secondFundamentalOperation i P hP W D X Y =
      secondFundamentalOperation i P hP W D Y X := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  apply Subtype.ext
  funext p
  let push := mapSections (tangentBundle S) P.space.bundle (differentialMorphism i P)
  have hz := (TorsionAndMetric.torsion_free_tensor K (TorsionAndMetric.torsionTensor K)
    (TorsionAndMetric.torsionFiber_apply K)).mp hK
  have h := TorsionAndMetric.differential_naturality K (TorsionAndMetric.torsionTensor K)
    (TorsionAndMetric.torsionFiber_apply K) F i.smooth P D hDP X Y (push X) (push Y)
    (fun q => by exact congrFun (congrArg DFunLike.coe (immersion_differential_eq i q)) (X.val q))
    (fun q => by exact congrFun (congrArg DFunLike.coe (immersion_differential_eq i q)) (Y.val q)) p
  rw [hz, ← immersion_differential_eq i p] at h
  have hh := congrArg ((normalProjectionMorphism i P hP W).linearMap p) h
  simp only [LeviCivita.tangent_sub_as_add, map_add, map_smul, map_zero,
    normalProjection_image, smul_zero, add_zero, neg_one_smul] at hh
  change (normalProjectionMorphism i P hP W).linearMap p ((D.cov X (push Y)).val p) =
    (normalProjectionMorphism i P hP W).linearMap p ((D.cov Y (push X)).val p)
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hh)
end SecondFundamental


section ShapeOperation
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M → N} (i : SmoothImmersion S T F)
  (P : PullbackBundle (tangentBundle T) S F)
  (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
  (W : AdaptedSplitting i P hP)

/-- Negation agrees with multiplication by minus one in the fixed derivation model. -/
theorem tangent_neg_as_smul (p : M) (v : TangentSpace S p) :
    -v = (-1 : ℝ) • v := by
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  change -(v.val f) = (-1 : ℝ) * v.val f
  ring

/-- Minus the tangential derivative of a normal section. -/
noncomputable def shapeOperation
    (D : letI := P.space.topology; Connection P.space.bundle) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    Section W.orthogonal.right.bundle →ₗ[ℝ] Field S →ₗ[ℝ] Field S := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  let inc := mapSections W.orthogonal.right.bundle P.space.bundle
    (normalInclusionMorphism i P hP W)
  let pr := mapSections P.space.bundle (tangentBundle S)
    (tangentProjectionMorphism i P hP W)
  exact LinearMap.flip {
    toFun X := (-1 : ℝ) • (pr.comp ((D.cov X).comp inc))
    map_add' X Y := by
      apply LinearMap.ext
      intro s
      apply Subtype.ext
      funext p
      change (-1 : ℝ) • ((pr (D.cov (X + Y) (inc s))).val p) = _
      rw [map_add]
      change (-1 : ℝ) • ((pr (D.cov X (inc s) + D.cov Y (inc s))).val p) = _
      rw [map_add]
      simpa only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        ConnectionForms.section_add_apply, ConnectionForms.section_smul_apply]
        using smul_add (-1 : ℝ) ((pr (D.cov X (inc s))).val p)
          ((pr (D.cov Y (inc s))).val p)
    map_smul' c X := by
      apply LinearMap.ext
      intro s
      apply Subtype.ext
      funext p
      change (-1 : ℝ) • ((pr (D.cov (c • X) (inc s))).val p) = _
      rw [map_smul]
      change (-1 : ℝ) • ((pr (c • D.cov X (inc s))).val p) = _
      rw [map_smul]
      simpa only [LinearMap.smul_apply, LinearMap.comp_apply, RingHom.id_apply,
        ConnectionForms.section_smul_apply]
        using smul_comm (-1 : ℝ) c ((pr (D.cov X (inc s))).val p) }

@[simp] theorem shapeOperation_apply
    (D : letI := P.space.topology; Connection P.space.bundle)
    (xi : letI := P.space.topology; letI := W.orthogonal.right.topology
      Section W.orthogonal.right.bundle) (X : Field S) (p : M) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    (shapeOperation i P hP W D xi X).val p =
      -(tangentProjectionMorphism i P hP W).linearMap p
        ((D.cov X (mapSections W.orthogonal.right.bundle P.space.bundle
          (normalInclusionMorphism i P hP W) xi)).val p) := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  change (-1 : ℝ) • ((tangentProjectionMorphism i P hP W).linearMap p
    ((D.cov X (mapSections W.orthogonal.right.bundle P.space.bundle
      (normalInclusionMorphism i P hP W) xi)).val p)) = _
  exact (tangent_neg_as_smul p _).symm

/-- The Leibniz correction is normal, so its tangent projection vanishes. -/
theorem shapeOperation_linear_normal
    (D : letI := P.space.topology; Connection P.space.bundle)
    (f : GlobalSmooth S)
    (xi : letI := P.space.topology; letI := W.orthogonal.right.topology
      Section W.orthogonal.right.bundle) (X : Field S) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    shapeOperation i P hP W D (mulSection f xi) X =
      mulSection f (shapeOperation i P hP W D xi X) := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  apply Subtype.ext
  funext p
  simp only [shapeOperation_apply, mapSections_mul, D.leibniz,
    ConnectionForms.section_add_apply, ConnectionForms.mulSection_apply,
    map_add, map_smul, mapSections_apply]
  have hp0 : (tangentProjectionMorphism i P hP W).linearMap p
      ((normalInclusionMorphism i P hP W).linearMap p (xi.val p)) = 0 :=
    tangentProjection_normal i P hP W p (xi.val p)
  rw [hp0, smul_zero, zero_add, tangent_neg_as_smul, tangent_neg_as_smul]
  exact smul_comm (-1 : ℝ) (f.val p) _

/-- Linearity over smooth functions in the differentiation direction. -/
theorem shapeOperation_linear_field
    (D : letI := P.space.topology; Connection P.space.bundle)
    (f : GlobalSmooth S)
    (xi : letI := P.space.topology; letI := W.orthogonal.right.topology
      Section W.orthogonal.right.bundle) (X : Field S) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    shapeOperation i P hP W D xi (mulSection f X) =
      mulSection f (shapeOperation i P hP W D xi X) := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  apply Subtype.ext
  funext p
  simp only [shapeOperation_apply, D.linear_field,
    ConnectionForms.mulSection_apply, map_smul]
  rw [tangent_neg_as_smul, tangent_neg_as_smul]
  exact smul_comm (-1 : ℝ) (f.val p) _

/-- Differentiating the vanishing tangent-normal pairing gives the adjoint
identity with the sign fixed by the definition of the shape operation. -/
theorem shapeOperation_pairing (g : RiemannianMetric S)
    (hi : letI := P.space.topology
      ∀ p v w, hP.form p (i.differential p v) (i.differential p w) = pairing g p v w)
    (D : letI := P.space.topology; Connection P.space.bundle)
    (hD : letI := P.space.topology;
      P202.TorsionMetricData.MetricCompatible P.space.bundle D hP)
    (xi : letI := P.space.topology; letI := W.orthogonal.right.topology
      Section W.orthogonal.right.bundle) (X Y : Field S) (p : M) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    pairing g p ((shapeOperation i P hP W D xi X).val p) (Y.val p) =
      hP.form p (((normalProjectionMorphism i P hP W).linearMap p
        ((D.cov X (mapSections (tangentBundle S) P.space.bundle
          (differentialMorphism i P) Y)).val p)).val) (xi.val p).val := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  let U := mapSections W.orthogonal.right.bundle P.space.bundle
    (normalInclusionMorphism i P hP W) xi
  let V := mapSections (tangentBundle S) P.space.bundle
    (differentialMorphism i P) Y
  have hh := hD X U V p
  have hfun : (fun q => hP.form q (U.val q) (V.val q)) =
      (fun _ : M => (0 : ℝ)) := by
    funext q
    change hP.form q (xi.val q).val (i.differential q (Y.val q)) = 0
    rw [hP.symmetric]
    exact tangent_normal_orthogonal i P hP q (Y.val q) (xi.val q)
  have hz : scalarDerivative S (fun _ : M => (0 : ℝ)) p (X.val p) = 0 := by
    have he : (fun _ : M => (0 : ℝ)) = (0 : GlobalSmooth S).val := by
      funext q
      rfl
    rw [he, ConnectionForms.scalarDerivative_global]
    exact congrArg (fun f : GlobalSmooth S => f.val p) (act S X).map_zero
  rw [hfun, hz] at hh
  change 0 = hP.form p ((D.cov X U).val p) (i.differential p (Y.val p)) +
    hP.form p (xi.val p).val ((D.cov X V).val p) at hh
  rw [hP.symmetric p (xi.val p).val ((D.cov X V).val p)] at hh
  have ht := pairing_tangentProjection i P hP W g hi p ((D.cov X U).val p) (Y.val p)
  have hn := pairing_normalProjection i P hP W p ((D.cov X V).val p) (xi.val p)
  simp only [normalMetric_apply] at hn
  rw [shapeOperation_apply, tangent_neg_as_smul, map_smul, LinearMap.smul_apply]
  change (-1 : ℝ) * pairing g p
    ((tangentProjectionMorphism i P hP W).linearMap p ((D.cov X U).val p))
    (Y.val p) = _
  rw [← ht, ← hn]
  linarith

/-- The normal derivative splits with the minus sign in Weingarten's formula. -/
theorem shapeOperation_weingarten
    (D : letI := P.space.topology; Connection P.space.bundle)
    (xi : letI := P.space.topology; letI := W.orthogonal.right.topology
      Section W.orthogonal.right.bundle) (X : Field S) (p : M) :
    letI := P.space.topology; letI := W.orthogonal.right.topology
    (D.cov X (mapSections W.orthogonal.right.bundle P.space.bundle
      (normalInclusionMorphism i P hP W) xi)).val p =
      -i.differential p ((shapeOperation i P hP W D xi X).val p) +
        (((normalConnection i P hP W D).cov X xi).val p).val := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  simpa only [shapeOperation_apply, normalConnection_apply, tangent_neg_as_smul,
    map_smul, smul_smul, neg_mul_neg, one_mul, one_smul]
    using (projection_decomposition i P hP W p
      ((D.cov X (mapSections W.orthogonal.right.bundle P.space.bundle
        (normalInclusionMorphism i P hP W) xi)).val p)).symm

end ShapeOperation


section FinalAssembly
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {F : M → N} (i : SmoothImmersion S T F)
  (P : PullbackBundle (tangentBundle T) S F)
  (hP : letI := P.space.topology; SmoothFiberMetric P.space.bundle)
  (W : AdaptedSplitting i P hP)

set_option maxHeartbeats 1600000 in
theorem gaussWeingartenConclusion (g : RiemannianMetric S)
    (hiP : letI := P.space.topology
      ∀ p v w, hP.form p (i.differential p v) (i.differential p w) = pairing g p v w)
    (K : Connection (tangentBundle T)) (hK : IsTorsionFree K)
    (D : letI := P.space.topology; Connection P.space.bundle)
    (hDP : letI := P.space.topology;
      P202.PullbackData.IsPullback (tangentBundle T) K F i.smooth P D)
    (hD : letI := P.space.topology;
      P202.TorsionMetricData.MetricCompatible P.space.bundle D hP)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C) :
    GaussWeingartenConclusion i P hP g C D W := by
  letI := P.space.topology
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  have hCT := tangentConnection_eq_intrinsic i P hP W g hiP K hK D hDP hD C hC
  obtain ⟨B, hB, hBsmooth⟩ := sectionBilinear_descent
    (tangentBundle S) (tangentBundle S) W.orthogonal.right.bundle
    (secondFundamentalOperation i P hP W D)
    (secondFundamentalOperation_mul_left i P hP W D)
    (secondFundamentalOperation_mul_right i P hP W D)
  obtain ⟨A, hA, hAsmooth⟩ := sectionBilinear_descent
    W.orthogonal.right.bundle (tangentBundle S) (tangentBundle S)
    (shapeOperation i P hP W D)
    (shapeOperation_linear_normal i P hP W D)
    (shapeOperation_linear_field i P hP W D)
  have hBsymm : ∀ p v w, B p v w = B p w v := by
    intro p v w
    obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p v
    obtain ⟨Y, hY⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p w
    rw [← hX, ← hY, hB, hB]
    exact congrArg (fun z : Section W.orthogonal.right.bundle => z.val p)
      (secondFundamentalOperation_symmetric i P hP W D K hK hDP X Y)
  have hAdj : ∀ p xi v w, pairing g p (A p xi v) w =
      hP.form p (B p v w).val xi.val := by
    intro p xi v w
    obtain ⟨eta, heta⟩ := ConnectionForms.section_evaluation_surjective
      W.orthogonal.right.bundle p xi
    obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p v
    obtain ⟨Y, hY⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p w
    rw [← heta, ← hX, ← hY, hA, hB, secondFundamentalOperation_apply]
    exact shapeOperation_pairing i P hP W g hiP D hD eta X Y p
  refine ⟨tangentConnection i P hP W D, normalConnection i P hP W D,
    normalMetric i P hP W, B, A, hCT, fun _ _ _ => rfl,
    normalConnection_metric i P hP W D hD, ?_, ?_, hBsmooth, hAsmooth,
    hBsymm, hAdj, ?_⟩
  · intro X Y
    refine ⟨mapSections (tangentBundle S) P.space.bundle (differentialMorphism i P) Y,
      fun _ => rfl, ?_, ?_, ?_⟩
    · intro p
      exact tangentConnection_apply i P hP W D X Y p
    · intro p
      exact hB X Y p
    · intro p
      rw [hB, secondFundamentalOperation_apply, ← hCT, tangentConnection_apply]
      exact (projection_decomposition i P hP W p
        ((D.cov X (mapSections (tangentBundle S) P.space.bundle
          (differentialMorphism i P) Y)).val p)).symm
  · intro X xi
    refine ⟨mapSections W.orthogonal.right.bundle P.space.bundle
      (normalInclusionMorphism i P hP W) xi, fun _ => rfl, ?_, ?_, ?_⟩
    · intro p
      exact normalConnection_apply i P hP W D X xi p
    · intro p
      refine (hA xi X p).trans ?_
      rw [shapeOperation_apply]
      apply Subtype.ext
      apply LinearMap.ext
      intro f
      rfl
    · intro p
      simpa only [hA xi X p] using shapeOperation_weingarten i P hP W D xi X p
  · intro p xi v w
    calc
      pairing g p (A p xi v) w = hP.form p (B p v w).val xi.val := hAdj p xi v w
      _ = hP.form p (B p w v).val xi.val := congrArg
        (fun z : (hP.form p).orthogonal (tangentImage i p) => hP.form p z.val xi.val)
        (hBsymm p v w)
      _ = pairing g p (A p xi w) v := (hAdj p xi w v).symm
      _ = pairing g p v (A p xi w) := g.symmetric p _ _

end FinalAssembly

theorem exists_geometry :
    P202Specs.Geometry.GaussWeingarten.exists_geometryType.{u} := by
  intro n m a b M N _ _ S T g h F i hi C K hC hK P
  letI := P.space.topology
  let hP := pullbackMetric h i.smooth P
  let W := adaptedSplitting i P hP
  let D := PullbackConnections.pullback (tangentBundle T) F i.smooth P K
  have hDP := PullbackConnections.pullback_isPullback (tangentBundle T) F i.smooth P K
  have hD : P202.TorsionMetricData.MetricCompatible P.space.bundle D hP :=
    TorsionAndMetric.metric_map_product (tangentBundle T) h K hK.2 F i.smooth P D hDP
  have hiP : ∀ p v w,
      hP.form p (i.differential p v) (i.differential p w) = pairing g p v w := hi
  exact ⟨hP, D, W, fun _ => rfl, hDP,
    gaussWeingartenConclusion i P hP W g hiP K hK.1 D hDP hD C hC⟩

/-- Export the canonical tangent image used throughout the immersion
constructions, with its independent expected value. -/
def tangentImage : P202Specs.Geometry.GaussWeingarten.tangentImageType.{u} :=
  @P202.GaussWeingartenData.tangentImage

end P202.Geometry.GaussWeingarten
