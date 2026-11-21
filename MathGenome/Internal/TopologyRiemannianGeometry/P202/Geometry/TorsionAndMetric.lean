import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.TorsionAndMetric
import Mathlib.Tactic.Module
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConnectionCalculus
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.InducedConnections
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothMetrics

/-! Torsion, metric compatibility, and differentiation along maps and curves.
Implements the unnumbered conclusions of paper.tex 3065–3084 on the original
intrinsic tangent fibers and arbitrary smooth vector bundles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace P202.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.SectionExtensionData SmoothManifolds.VectorFieldData
  SmoothManifolds.LieBracketData P202.ConnectionData P202.TorsionMetricData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

noncomputable abbrev torsion := @P202.TorsionMetricData.torsion

theorem originalBracket_rule : BracketOperation (originalBracket (S := S)) :=
  (Classical.choose_spec (SmoothManifolds.LieBrackets.bracket_exists S
    (P202.MetricData.tangentStructure S))).1

private def bracket_algebra :=
  (SmoothManifolds.LieBrackets.bracket_algebra S
    (P202.MetricData.tangentStructure S)).2.2 _ (originalBracket_rule (S := S))

@[simp] theorem bracket_skew (X Y : Field S) : bracket X Y = (-1 : ℝ) • bracket Y X := by
  apply Subtype.ext
  funext p
  simp only [ConnectionForms.section_smul_apply, neg_one_smul]
  exact (bracket_algebra (S := S)).1 (originalField S X) (originalField S Y) p

@[simp] theorem bracket_add_left (X Y Z : Field S) :
    bracket (X + Y) Z = bracket X Z + bracket Y Z := by
  apply Subtype.ext
  funext p
  exact (bracket_algebra (S := S)).2.2.1 (originalField S X) (originalField S Y)
    (originalField S Z) (originalField S (X + Y)) (fun _ => rfl) p

@[simp] theorem bracket_add_right (X Y Z : Field S) :
    bracket X (Y + Z) = bracket X Y + bracket X Z := by
  apply Subtype.ext
  funext p
  exact (bracket_algebra (S := S)).2.2.2.1 (originalField S X) (originalField S Y)
    (originalField S Z) (originalField S (Y + Z)) (fun _ => rfl) p

@[simp] theorem bracket_smul_left (c : ℝ) (X Y : Field S) :
    bracket (c • X) Y = c • bracket X Y := by
  apply Subtype.ext
  funext p
  exact (bracket_algebra (S := S)).2.2.2.2.1 c (originalField S X)
    (originalField S Y) (originalField S (c • X)) (fun _ => rfl) p

@[simp] theorem bracket_smul_right (c : ℝ) (X Y : Field S) :
    bracket X (c • Y) = c • bracket X Y := by
  apply Subtype.ext
  funext p
  exact (bracket_algebra (S := S)).2.2.2.2.2.1 c (originalField S X)
    (originalField S Y) (originalField S (c • Y)) (fun _ => rfl) p

/-- The derivative term in the bracket Leibniz rule is the same intrinsic
scalar action used in the defining connection axiom. -/
theorem bracket_mul_right (f : GlobalSmooth S) (X Y : Field S) :
    bracket X (mulSection f Y) =
      mulSection f (bracket X Y) + mulSection (act S X f) Y := by
  apply Subtype.ext
  funext p
  exact (bracket_algebra (S := S)).2.2.2.2.2.2 f (originalField S X)
    (originalField S Y) (originalField S (mulSection f Y)) (act S X)
    (SmoothManifolds.VectorFields.derivationOfField_represents S
      (P202.MetricData.tangentStructure S) (originalField S X)) (fun _ => rfl) p

variable (C : Connection (tangentBundle S))

theorem torsion_apply (X Y : Field S) (p : M) :
    (torsion C X Y).val p =
      (C.cov X Y).val p - (C.cov Y X).val p - (bracket X Y).val p := by
  simp only [torsion, P202.TorsionMetricData.torsion, ConnectionForms.section_add_apply,
    ConnectionForms.section_smul_apply, neg_one_smul]
  abel

theorem torsion_skew (X Y : Field S) :
    torsion C X Y = (-1 : ℝ) • torsion C Y X := by
  apply Subtype.ext
  funext p
  simp only [torsion_apply, ConnectionForms.section_smul_apply, neg_one_smul]
  rw [bracket_skew X Y, ConnectionForms.section_smul_apply, neg_one_smul]
  abel

theorem torsion_add_left (X Y Z : Field S) :
    torsion C (X + Y) Z = torsion C X Z + torsion C Y Z := by
  apply Subtype.ext
  funext p
  simp only [torsion_apply, map_add, LinearMap.add_apply, bracket_add_left,
    ConnectionForms.section_add_apply]
  abel

theorem torsion_add_right (X Y Z : Field S) :
    torsion C X (Y + Z) = torsion C X Y + torsion C X Z := by
  apply Subtype.ext
  funext p
  simp only [torsion_apply, map_add, LinearMap.add_apply, bracket_add_right,
    ConnectionForms.section_add_apply]
  abel

theorem torsion_smul_left (c : ℝ) (X Y : Field S) :
    torsion C (c • X) Y = c • torsion C X Y := by
  apply Subtype.ext
  funext p
  simp only [torsion_apply, map_smul, LinearMap.smul_apply, bracket_smul_left,
    ConnectionForms.section_smul_apply]
  module

theorem torsion_smul_right (c : ℝ) (X Y : Field S) :
    torsion C X (c • Y) = c • torsion C X Y := by
  apply Subtype.ext
  funext p
  simp only [torsion_apply, map_smul, LinearMap.smul_apply, bracket_smul_right,
    ConnectionForms.section_smul_apply]
  module

theorem torsion_mul_right (f : GlobalSmooth S) (X Y : Field S) :
    torsion C X (mulSection f Y) = mulSection f (torsion C X Y) := by
  apply Subtype.ext
  funext p
  simp only [torsion_apply, C.leibniz, C.linear_field, bracket_mul_right,
    ConnectionForms.section_add_apply, ConnectionForms.mulSection_apply]
  module

theorem torsion_mul_left (f : GlobalSmooth S) (X Y : Field S) :
    torsion C (mulSection f X) Y = mulSection f (torsion C X Y) := by
  rw [torsion_skew, torsion_mul_right]
  apply Subtype.ext
  funext p
  simp only [ConnectionForms.section_smul_apply, ConnectionForms.mulSection_apply]
  rw [torsion_skew C X Y, ConnectionForms.section_smul_apply]
  exact smul_comm _ _ _

theorem torsion_tensorial : P202Specs.Geometry.TorsionAndMetric.torsion_tensorialType.{u} := by
  intro n a M _ S C
  exact ⟨torsion_add_left C, torsion_add_right C, torsion_mul_left C, torsion_mul_right C⟩

/-- Real-bilinear torsion on smooth sections, before fiber descent. -/
noncomputable def torsionBilinear : Field S →ₗ[ℝ] Field S →ₗ[ℝ] Field S where
  toFun X := {
    toFun := torsion C X
    map_add' := torsion_add_right C X
    map_smul' := fun c Y => torsion_smul_right C c X Y }
  map_add' X Y := by
    apply LinearMap.ext
    intro Z
    exact torsion_add_left C X Y Z
  map_smul' c X := by
    apply LinearMap.ext
    intro Y
    exact torsion_smul_left C c X Y

/-- A fiber-valued C∞-linear operator is germ-local. -/
theorem tensorOperator_local {G : Type*} [AddCommGroup G] [Module ℝ G]
    (p : M) (H : Field S →ₗ[ℝ] G)
    (hH : ∀ (f : GlobalSmooth S) (X : Field S),
      H (mulSection f X) = f.val p • H X)
    (X Y : Field S) (hXY : ∀ᶠ q in 𝓝 p, X.val q = Y.val q) : H X = H Y := by
  obtain ⟨U, hU, hUo, hpU⟩ := eventually_nhds_iff.mp hXY
  obtain ⟨f, hf, hsupp⟩ := ConnectionForms.exists_cutoff_near (S := S) p U hUo hpU
  have heq : mulSection f X = mulSection f Y := by
    apply Subtype.ext
    funext q
    by_cases hq : q ∈ U
    · change f.val q • X.val q = f.val q • Y.val q
      rw [hU q hq]
    · have hz : f.val q = 0 := Function.notMem_support.mp
        (fun hz => hq (hsupp (subset_closure hz)))
      change f.val q • X.val q = f.val q • Y.val q
      rw [hz, zero_smul, zero_smul]
  have h := congrArg H heq
  simpa only [hH, hf.eq_of_nhds, one_smul] using h

/-- A fiber-valued C∞-linear operator depends only on the tangent value.
The finite local-frame decomposition works also in dimension zero. -/
theorem tensorOperator_zero {G : Type*} [AddCommGroup G] [Module ℝ G]
    (p : M) (H : Field S →ₗ[ℝ] G)
    (hH : ∀ (f : GlobalSmooth S) (X : Field S),
      H (mulSection f X) = f.val p • H X)
    (X : Field S) (hX : X.val p = 0) : H X = 0 := by
  obtain ⟨f, e, heq, hf⟩ :=
    ConnectionForms.section_zero_decomposition (tangentBundle S) X p hX
  rw [tensorOperator_local p H hH X _ heq, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [hH, hf, zero_smul]

theorem torsion_zero_right (X Y : Field S) (p : M) (hY : Y.val p = 0) :
    (torsion C X Y).val p = 0 := by
  let H := (InducedConnections.sectionEvaluation (tangentBundle S) p).comp
    (torsionBilinear C X)
  exact tensorOperator_zero p H (fun f Z => by
    change (torsion C X (mulSection f Z)).val p = f.val p • (torsion C X Z).val p
    rw [torsion_mul_right C]
    rfl) Y hY

theorem torsion_pointwise_right (X Y Z : Field S) (p : M)
    (hYZ : Y.val p = Z.val p) : (torsion C X Y).val p = (torsion C X Z).val p := by
  have h := torsion_zero_right C X (Y + (-1 : ℝ) • Z) p (by
    simp only [ConnectionForms.section_add_apply, ConnectionForms.section_smul_apply,
      neg_one_smul, hYZ, add_neg_cancel])
  rw [torsion_add_right, torsion_smul_right, ConnectionForms.section_add_apply,
    ConnectionForms.section_smul_apply, neg_one_smul] at h
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)

theorem torsion_pointwise_left (X Y Z : Field S) (p : M)
    (hXY : X.val p = Y.val p) : (torsion C X Z).val p = (torsion C Y Z).val p := by
  rw [torsion_skew C X Z, torsion_skew C Y Z]
  simp only [ConnectionForms.section_smul_apply]
  exact congrArg (fun v => (-1 : ℝ) • v) (torsion_pointwise_right C Z X Y p hXY)

/-- A chosen global extension of an individual tangent vector, supplied by
upstream section extension, without imposing a global frame. -/
noncomputable def liftField (p : M) (v : TangentSpace S p) : Field S :=
  Classical.choose (ConnectionForms.section_evaluation_surjective (tangentBundle S) p v)

@[simp] theorem liftField_value (p : M) (v : TangentSpace S p) :
    (liftField p v).val p = v :=
  Classical.choose_spec (ConnectionForms.section_evaluation_surjective (tangentBundle S) p v)

/-- Torsion as an actual bilinear map on each original tangent fiber. -/
noncomputable def torsionFiber (p : M) :
    TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace S p where
  toFun v := {
    toFun := fun w => (torsion C (liftField p v) (liftField p w)).val p
    map_add' := by
      intro w z
      have h := torsion_pointwise_right C (liftField p v)
        (liftField p (w + z)) (liftField p w + liftField p z) p (by
          change _ = (liftField p w).val p + (liftField p z).val p
          simp only [liftField_value])
      simpa only [torsion_add_right, ConnectionForms.section_add_apply] using h
    map_smul' := by
      intro c w
      have h := torsion_pointwise_right C (liftField p v)
        (liftField p (c • w)) (c • liftField p w) p (by
          change _ = c • (liftField p w).val p
          simp only [liftField_value])
      simpa only [torsion_smul_right, ConnectionForms.section_smul_apply, RingHom.id_apply] using h }
  map_add' v w := by
    apply LinearMap.ext
    intro z
    have h := torsion_pointwise_left C (liftField p (v + w))
      (liftField p v + liftField p w) (liftField p z) p (by
        change _ = (liftField p v).val p + (liftField p w).val p
        simp only [liftField_value])
    change (torsion C (liftField p (v + w)) (liftField p z)).val p =
      (torsion C (liftField p v) (liftField p z)).val p +
        (torsion C (liftField p w) (liftField p z)).val p
    simpa only [torsion_add_left, ConnectionForms.section_add_apply] using h
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    have h := torsion_pointwise_left C (liftField p (c • v))
      (c • liftField p v) (liftField p w) p (by
        change _ = c • (liftField p v).val p
        simp only [liftField_value])
    change (torsion C (liftField p (c • v)) (liftField p w)).val p =
      c • (torsion C (liftField p v) (liftField p w)).val p
    simpa only [torsion_smul_left, ConnectionForms.section_smul_apply] using h

@[simp] theorem torsionFiber_apply (X Y : Field S) (p : M) :
    torsionFiber C p (X.val p) (Y.val p) = (torsion C X Y).val p := by
  change (torsion C (liftField p (X.val p)) (liftField p (Y.val p))).val p = _
  rw [torsion_pointwise_left C _ X _ p (liftField_value p _),
    torsion_pointwise_right C X _ Y p (liftField_value p _)]

noncomputable def torsionTensor : TangentTwoTensor S where
  val := torsionFiber C
  smooth X Y := by
    have h : (fun p => torsionFiber C p (X.val p) (Y.val p)) = (torsion C X Y).val :=
      funext (torsionFiber_apply C X Y)
    rw [h]
    exact (torsion C X Y).property

theorem tangentTwoTensor_ext {T U : TangentTwoTensor S} (h : T.val = U.val) : T = U := by
  cases T
  cases U
  cases h
  rfl

theorem torsion_tensor_exists_unique :
    P202Specs.Geometry.TorsionAndMetric.torsion_tensor_exists_uniqueType.{u} := by
  intro n a M _ S C
  refine ⟨torsionTensor C, torsionFiber_apply C, ?_⟩
  intro T hT
  have heq : T.val = (torsionTensor C).val := by
    funext p
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p v
    obtain ⟨Y, hY⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p w
    change T.val p v w = torsionFiber C p v w
    rw [← hX, ← hY, hT, torsionFiber_apply]
  exact tangentTwoTensor_ext heq

/-- Smoothness in the original linear tangent coordinates follows from local
frame representatives, with no triviality assumption on the tangent bundle. -/
theorem tangent_tensor_coordinates_smooth :
    P202Specs.Geometry.TorsionAndMetric.tangent_tensor_coordinates_smoothType.{u} := by
  intro n a M _ S T i j k p hp
  let B := tangentBundle S
  have ho : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B i
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b ⟨p, hp⟩
  have h := SmoothManifolds.SectionExtension.coordinates_smoothAt B i hp
    (T.smooth (e j) (e k) p)
  apply h.congr
  filter_upwards [ho.mem_nhds hp, he j, he k] with q hq hj hk
  rw [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq] at hj hk
  have hb (l : Fin n) : b.section_ l ⟨q, hq⟩ =
      (B.trivialization i).symm q (Pi.single l 1) := by
    change (B.fiberCoordinates i q hq).symm ((Pi.basisFun ℝ (Fin n)) l) = _
    rw [Pi.basisFun_apply, SmoothVectorBundle.fiberCoordinates_symm_apply]
  rw [hj, hk, hb, hb]

end P202.Geometry.TorsionAndMetric

namespace P202.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
  P202.TorsionMetricData
open Set Filter
open scoped Topology
universe u v w
section Metric
variable {n r : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

@[simp] theorem metricFunctional_tmul (h : SmoothFiberMetric B) (p : M) (v w : E p) :
    metricFunctional B h p (TensorProduct.tmul ℝ v w) = h.form p v w := rfl

/-- The coordinate definition of a metric makes its pairing of smooth sections
smooth. All base and fiber universes remain arbitrary. -/
theorem metricPairing_smooth (h : SmoothFiberMetric B) (s t : Section B) (p : M) :
    VectorSmoothAt S.smoothStructure.val (fun q => h.form q (s.val q) (t.val q)) p := by
  obtain ⟨i, hi⟩ := B.covers p
  let cs : M → Euclidean r := fun q => ((B.trivialization i) ⟨q, s.val q⟩).2
  let ct : M → Euclidean r := fun q => ((B.trivialization i) ⟨q, t.val q⟩).2
  have hs := SmoothManifolds.SectionExtension.coordinates_smoothAt B i hi (s.property p)
  have ht := SmoothManifolds.SectionExtension.coordinates_smoothAt B i hi (t.property p)
  let gram : Fin r → Fin r → M → ℝ := fun j k q =>
    h.form q ((B.trivialization i).symm q (Pi.single j 1))
      ((B.trivialization i).symm q (Pi.single k 1))
  have hsum : VectorSmoothAt S.smoothStructure.val
      (fun q => ∑ j : Fin r, ∑ k : Fin r, cs q j * (ct q k * gram j k q)) p := by
    apply VectorSmoothAt.sum
    intro j
    apply VectorSmoothAt.sum
    intro k
    exact ((hs.postcomp (ContinuousLinearMap.proj j).contDiff).prod
      (((ht.postcomp (ContinuousLinearMap.proj k).contDiff).prod
        (h.smooth i j k p hi)).postcomp (contDiff_fst.mul contDiff_snd))).postcomp
          (contDiff_fst.mul contDiff_snd)
  apply hsum.congr
  have ho : IsOpen (B.baseSet i) := B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  filter_upwards [ho.mem_nhds hi] with q hq
  exact (SmoothMetrics.bilinear_coordinates (B.fiberCoordinates i q hq)
    (h.form q) (s.val q) (t.val q)).symm

/-- Smoothness of the metric as an actual section of (E ⊗ E)*. -/
theorem metricFunctional_smooth (h : SmoothFiberMetric B) (T : TensorBundle B B) :
    letI := T.space.topology
    ∀ (D : DualBundle T.space.bundle),
    letI := D.space.topology
    SmoothSection D.space.bundle (metricFunctional B h) := by
  letI := T.space.topology
  intro D
  letI := D.space.topology
  apply InducedConnections.dual_smooth_of_evaluations T.space.bundle D
  intro s p
  obtain ⟨x, hx⟩ := InducedConnections.exists_tensorPresentation B B T s p
  have hp : ∀ x : InducedConnections.TensorPresentation B B,
      VectorSmoothAt S.smoothStructure.val
        (fun q => metricFunctional B h q
          ((InducedConnections.tensorPresentationValue B B T x).val q)) p := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simpa using (SmoothManifolds.FrameData.VectorSmoothAt.const
        S.smoothStructure.val (0 : ℝ) p)
    | tmul v w => exact metricPairing_smooth B h v w p
    | add x y hx hy =>
      simpa only [map_add, ConnectionForms.section_add_apply] using
        (hx.prod hy).postcomp (contDiff_fst.add contDiff_snd)
  apply (hp x).congr
  filter_upwards [hx] with q hq
  rw [hq]

noncomputable def metricSection (h : SmoothFiberMetric B) (T : TensorBundle B B) :
    letI := T.space.topology
    (D : DualBundle T.space.bundle) →
    letI := D.space.topology; Section D.space.bundle := by
  letI := T.space.topology
  intro D
  letI := D.space.topology
  exact ⟨metricFunctional B h, metricFunctional_smooth B h T D⟩

/-- The dual and tensor connections give the full derivative of the metric,
without a compatibility or torsion assumption. -/
theorem metric_derivative_formula (h : SmoothFiberMetric B) (C : Connection B)
    (T : TensorBundle B B) :
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C C T N →
    ∀ (D : DualBundle T.space.bundle),
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule N D K →
    ∀ (X : Field S) (s t : Section B) (p : M),
      (K.cov X (metricSection B h T D)).val p
        (TensorProduct.tmul ℝ (s.val p) (t.val p)) =
      scalarDerivative S (fun q => h.form q (s.val q) (t.val q)) p (X.val p) -
        h.form p ((C.cov X s).val p) (t.val p) -
        h.form p (s.val p) ((C.cov X t).val p) := by
  letI := T.space.topology
  intro N hN D
  letI := D.space.topology
  intro K hK X s t p
  have hd := hK X (metricSection B h T D) (InducedConnections.tensorSection B B T s t) p
  rw [hN X s t (InducedConnections.tensorSection B B T s t) (fun _ => rfl) p] at hd
  simpa only [metricSection, InducedConnections.tensorSection_apply, metricFunctional_tmul,
    map_add, sub_add_eq_sub_sub] using hd

/-- Metric compatibility is exactly parallelness of the actual metric tensor
under the induced connection. -/
theorem metric_compatible_iff_parallel (h : SmoothFiberMetric B) (C : Connection B)
    (T : TensorBundle B B) :
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C C T N →
    ∀ (D : DualBundle T.space.bundle),
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule N D K →
    (MetricCompatible B C h ↔ ∀ X : Field S, K.cov X (metricSection B h T D) = 0) := by
  letI := T.space.topology
  intro N hN D
  letI := D.space.topology
  intro K hK
  constructor
  · intro hc X
    apply Subtype.ext
    funext p
    apply LinearMap.ext
    intro v
    change (K.cov X (metricSection B h T D)).val p v = 0
    induction v using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul v w =>
      obtain ⟨s, hs⟩ := ConnectionForms.section_evaluation_surjective B p v
      obtain ⟨t, ht⟩ := ConnectionForms.section_evaluation_surjective B p w
      rw [← hs, ← ht, metric_derivative_formula B h C T N hN D K hK, hc]
      ring
    | add v w hv hw => rw [map_add, hv, hw, add_zero]
  · intro hp X s t p
    have hd := metric_derivative_formula B h C T N hN D K hK X s t p
    rw [hp X] at hd
    change 0 = _ at hd
    linarith only [hd]

/-- A smooth metric has an actual covariant two-tensor realization, with the
product-rule formula and the parallelness equivalence. -/
theorem metric_tensor_calculus (h : SmoothFiberMetric B) (C : Connection B)
    (T : TensorBundle B B) :
    letI := T.space.topology
    ∀ (N : Connection T.space.bundle), TensorRule C C T N →
    ∀ (D : DualBundle T.space.bundle),
    letI := D.space.topology
    ∀ (K : Connection D.space.bundle), DualRule N D K →
    ∃ H : Section D.space.bundle,
      (∀ p, H.val p = metricFunctional B h p) ∧
      (∀ (X : Field S) (s t : Section B) (p : M),
        (K.cov X H).val p (TensorProduct.tmul ℝ (s.val p) (t.val p)) =
          scalarDerivative S (fun q => h.form q (s.val q) (t.val q)) p (X.val p) -
            h.form p ((C.cov X s).val p) (t.val p) -
            h.form p (s.val p) ((C.cov X t).val p)) ∧
      (MetricCompatible B C h ↔ ∀ X : Field S, K.cov X H = 0) := by
  letI := T.space.topology
  intro N hN D
  letI := D.space.topology
  intro K hK
  exact ⟨metricSection B h T D, fun _ => rfl,
    metric_derivative_formula B h C T N hN D K hK,
    metric_compatible_iff_parallel B h C T N hN D K hK⟩

open P202.CurveConnectionData
/-- The metric differentiation rule for arbitrary differentiable fields along
a curve, including one-sided parameter germs. -/
theorem metric_curve_product (h : SmoothFiberMetric B) (C : Connection B)
    (hc : MetricCompatible B C h)
    {c : ℝ → M} {f g : (s : ℝ) → E (c s)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) {DF DG : E (c t)}
    (hF : HasCovariantDerivativeWithinAt C c f J t DF)
    (hG : HasCovariantDerivativeWithinAt C c g J t DG) :
    HasDerivWithinAt (fun s => h.form (c s) (f s) (g s))
      (h.form (c t) DF (g t) + h.form (c t) (f t) DG) J t := by
  let T := Classical.choice (SmoothManifolds.BundleOperations.exists_tensor B B)
  letI := T.space.topology
  let D := Classical.choice (SmoothManifolds.BundleOperations.exists_dual T.space.bundle)
  letI := D.space.topology
  let N := InducedConnections.tensorConnection B B T C C
  let K := InducedConnections.dualConnection T.space.bundle D N
  have hN := InducedConnections.tensorConnection_rule B B T C C
  have hK := InducedConnections.dualConnection_rule T.space.bundle D N
  have hpar := (metric_compatible_iff_parallel B h C T N hN D K hK).mp hc
  have hFcopy := hF
  obtain ⟨V, hV, _⟩ := hFcopy
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (c t) V
  have hVX : HasVelocityWithinAt S c J t (X.val (c t)) := by rwa [hX]
  have hH := CurveCovariantDerivative.derivative_section_field K (metricSection B h T D) X ht hVX
  rw [hpar X] at hH
  have hfg := InducedConnections.curve_tensor_product B B C C T N hN ht hJ hF hG
  have hd := InducedConnections.curve_dual_contraction T.space.bundle N D K hK ht hJ hH hfg
  simpa only [metricSection, ConnectionForms.section_zero_apply, LinearMap.zero_apply,
    zero_add, map_add, metricFunctional_tmul] using hd

/-- C¹ data give the formula for the actual chosen covariant derivatives. -/
theorem metric_curve_product_c1 (h : SmoothFiberMetric B) (C : Connection B)
    (hc : MetricCompatible B C h)
    {c : ℝ → M} {f g : (s : ℝ) → E (c s)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (hc1 : P202.CurveData.CoordinateC1On S c J) (hc' : ContinuousOn c J)
    (hf : C1FieldOn (B := B) c f J) (hg : C1FieldOn (B := B) c g J) :
    HasDerivWithinAt (fun s => h.form (c s) (f s) (g s))
      (h.form (c t) (covariantDerivativeWithin C c f J t) (g t) +
        h.form (c t) (f t) (covariantDerivativeWithin C c g J t)) J t := by
  exact metric_curve_product B h C hc ht hJ
    (CurveCovariantDerivative.covariantDerivativeWithin_spec C
      (CurveCovariantDerivative.exists_covariantDerivative C ht hc1 hc' hf))
    (CurveCovariantDerivative.covariantDerivativeWithin_spec C
      (CurveCovariantDerivative.exists_covariantDerivative C ht hc1 hc' hg))
end Metric
end P202.Geometry.TorsionAndMetric

namespace P202.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  SmoothManifolds.SectionExtensionData P202.ConnectionData P202.InducedConnectionData
  P202.TorsionMetricData
open Set Filter
open scoped Topology
universe u v w
section MetricMap
variable {n m r : ℕ} {a b : ModelKind} {M L : Type u}
  [TopologicalSpace M] [TopologicalSpace L]
  {S : SmoothManifold n a M} {R : SmoothManifold m b L}
  {ι : Type v} {E : M → Type w}
  [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
  [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
  (B : SmoothVectorBundle S r ι E)

/-- Metric compatibility differentiates arbitrary sections along every smooth
map. There is no assumption on the rank of its differential. -/
theorem metric_map_product (h : SmoothFiberMetric B) (C : Connection B)
    (hc : MetricCompatible B C h) (F : L → M) (hF : IsSmoothMap R S F)
    (P : PullbackBundle B R F) :
    letI := P.space.topology
    ∀ (CP : Connection P.space.bundle), P202.PullbackData.IsPullback B C F hF P CP →
    ∀ (X : Field R) (s t : Section P.space.bundle) (q : L),
      scalarDerivative R (fun z => h.form (F z) (s.val z) (t.val z)) q (X.val q) =
        h.form (F q) ((CP.cov X s).val q) (t.val q) +
          h.form (F q) (s.val q) ((CP.cov X t).val q) := by
  letI := P.space.topology
  intro CP hCP
  have heq : CP = PullbackConnections.pullback B F hF P C :=
    PullbackConnections.uniqueness B F hF P C _ _ hCP
      (PullbackConnections.pullback_isPullback B F hF P C)
  subst CP
  intro X s t q
  let U := Classical.choice (SmoothManifolds.BundleOperations.exists_tensor B B)
  letI := U.space.topology
  let D := Classical.choice (SmoothManifolds.BundleOperations.exists_dual U.space.bundle)
  letI := D.space.topology
  let Q := P202.PullbackData.bundle U.space.bundle R F hF
  letI := Q.space.topology
  let H := P202.PullbackData.bundle D.space.bundle R F hF
  letI := H.space.topology
  let UP := InducedConnections.pullbackTensorBundle B B F P P U Q
  let N := InducedConnections.tensorConnection B B U C C
  let K := InducedConnections.dualConnection U.space.bundle D N
  let CP := PullbackConnections.pullback B F hF P C
  let NP := PullbackConnections.pullback U.space.bundle F hF Q N
  let KP := PullbackConnections.pullback D.space.bundle F hF H K
  let g := metricSection B h U D
  let gp := PullbackConnections.pullSection D.space.bundle F hF H g
  let st : Section Q.space.bundle := InducedConnections.tensorSection P.space.bundle P.space.bundle UP s t
  have hN := InducedConnections.tensorConnection_rule B B U C C
  have hK := InducedConnections.dualConnection_rule U.space.bundle D N
  have hp := (metric_compatible_iff_parallel B h C U N hN D K hK).mp hc
  have hCPP := PullbackConnections.pullback_isPullback B F hF P C
  have hNPP := PullbackConnections.pullback_isPullback U.space.bundle F hF Q N
  have hKPP := PullbackConnections.pullback_isPullback D.space.bundle F hF H K
  have htensor := (InducedConnections.tensor_pullback_compatibility B B C C U F hF P P Q
    CP CP N NP hCPP hCPP hN hNPP).2
  have hdual := (InducedConnections.dual_pullback_compatibility U.space.bundle N D F hF Q H
    NP K KP hNPP hK hKPP).2
  have hpq : (KP.cov X gp).val q = 0 := by
    rw [hKPP X g gp (fun _ => rfl) q]
    obtain ⟨Y, hY⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (F q)
      (SmoothManifolds.differential R S F hF q (X.val q))
    rw [← hY, ConnectionForms.pointDerivative_global D.space.bundle K g (F q) Y]
    exact congrArg (fun z : Section D.space.bundle => z.val (F q)) (hp Y)
  have hd := hdual X gp st q
  rw [hpq, htensor X s t st (fun _ => rfl) q] at hd
  change (0 : Module.Dual ℝ (TensorProduct ℝ (E (F q)) (E (F q))))
      (TensorProduct.tmul ℝ (s.val q) (t.val q)) =
    scalarDerivative R (fun z => metricFunctional B h (F z)
      (TensorProduct.tmul ℝ (s.val z) (t.val z))) q (X.val q) -
      metricFunctional B h (F q)
        (TensorProduct.tmul ℝ ((CP.cov X s).val q) (t.val q) +
          TensorProduct.tmul ℝ (s.val q) ((CP.cov X t).val q)) at hd
  simp only [LinearMap.zero_apply, map_add, metricFunctional_tmul] at hd
  linarith only [hd]

end MetricMap
end P202.Geometry.TorsionAndMetric

namespace P202.Geometry.TorsionAndMetric

abbrev metricCompatible := @P202.TorsionMetricData.MetricCompatible

/-- The general bundle-metric theorem applied to the original tangent metric. -/
theorem tangent_metric_calculus :
    P202Specs.Geometry.TorsionAndMetric.tangent_metric_calculusType := by
  intro n a M _ S g C T
  exact metric_tensor_calculus (P202.ConnectionData.tangentBundle S) g C T

end P202.Geometry.TorsionAndMetric

namespace P202.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData P202.ConnectionData P202.TorsionMetricData

abbrev torsionFree := @P202.TorsionMetricData.TorsionFree

theorem torsion_free_tensor :
    P202Specs.Geometry.TorsionAndMetric.torsion_free_tensorType := by
  intro n a M _ S C T hT
  constructor
  · intro h p v w
    rw [← liftField_value p v, ← liftField_value p w, hT, h]
    rfl
  · intro h X Y
    apply Subtype.ext
    funext p
    rw [← hT, h]
    rfl

end P202.Geometry.TorsionAndMetric

namespace P202.TorsionMetricData
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.SectionExtensionData SmoothManifolds.VectorFieldData
  SmoothManifolds.LieBracketData SmoothManifolds.FiniteRegularityData
  P202.ConnectionData P202.TorsionMetricData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}
theorem fullChartConstantField_coefficients (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (hfull : e.source = univ) (v : Euclidean n) (p : M) :
    coefficients (P202.MetricData.tangentStructure S)
      (fullChartConstantField e he hfull v).val e he p = v := by
  exact (Classical.choose_spec
    (SmoothManifolds.LieBrackets.field_of_full_chart e he hfull (fun _ => v) contDiff_const)).1 p
end P202.TorsionMetricData
namespace P202.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.SectionExtensionData SmoothManifolds.VectorFieldData
  SmoothManifolds.LieBracketData SmoothManifolds.FiniteRegularityData
  P202.ConnectionData P202.TorsionMetricData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}
theorem bracket_fullChartConstantField (e : ModelChart n a M)
    (he : e ∈ S.smoothStructure.val) (hfull : e.source = univ) (v w : Euclidean n) :
    bracket (fullChartConstantField e he hfull v) (fullChartConstantField e he hfull w) = 0 := by
  let B := P202.MetricData.tangentStructure S
  let X := fullChartConstantField e he hfull v
  let Y := fullChartConstantField e he hfull w
  have hX (p : M) : HasCoordinateDerivative e (coefficients B X.val e he) p 0 := by
    refine ⟨fun _ => v, hasFDerivAt_const _ _, ?_⟩
    exact Eventually.of_forall (fun q => (fullChartConstantField_coefficients e he hfull v q).symm)
  have hY (p : M) : HasCoordinateDerivative e (coefficients B Y.val e he) p 0 := by
    refine ⟨fun _ => w, hasFDerivAt_const _ _, ?_⟩
    exact Eventually.of_forall (fun q => (fullChartConstantField_coefficients e he hfull w q).symm)
  apply Subtype.ext
  funext p
  have hp : p ∈ e.source := hfull.symm ▸ mem_univ p
  apply (B.fiberCoordinates.equiv e he p hp).injective
  change (B.fiberCoordinates.equiv e he p hp) ((bracket X Y).val p) =
    (B.fiberCoordinates.equiv e he p hp) 0
  rw [map_zero]
  rw [← SmoothManifolds.LieBrackets.coefficients_eq _ e he p hp]
  funext j
  have hb := (SmoothManifolds.LieBrackets.bracket_coordinates S B _
    (originalBracket_rule (S := S)) (originalField S X) (originalField S Y)).2
      e he p hp 0 0 (hX p) (hY p) j
  simpa only [ContinuousLinearMap.zero_apply, Pi.zero_apply, mul_zero,
    sub_zero, Finset.sum_const_zero, P202.TorsionMetricData.bracket,
    P202.TorsionMetricData.realizedField] using hb
end P202.Geometry.TorsionAndMetric
namespace P202.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.SectionExtensionData SmoothManifolds.VectorFieldData
  SmoothManifolds.LieBracketData SmoothManifolds.FiniteRegularityData
  P202.ConnectionData P202.TorsionMetricData
open Set Filter
open scoped Topology
@[simp] theorem parameterField_coordinates (j : Fin 2) (p : Euclidean 2) :
    coefficients (P202.MetricData.tangentStructure
      (SmoothManifolds.RegularLevels.standardEuclideanManifold 2))
      (parameterField j).val (SmoothManifolds.RegularLevels.standardEuclideanChart 2)
      (SmoothManifolds.RegularLevels.singleChartManifold_chart_mem _ rfl) p = Pi.single j 1 :=
  fullChartConstantField_coefficients _ _ _ _ _

@[simp] theorem parameterField_bracket (j k : Fin 2) :
    bracket (parameterField j) (parameterField k) = 0 :=
  bracket_fullChartConstantField _ _ _ _ _
end P202.Geometry.TorsionAndMetric

namespace P202.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData
  SmoothManifolds.VectorFieldData SmoothManifolds.LieBracketData
  P202.ConnectionData P202.TorsionMetricData P202.InducedConnectionData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

noncomputable def exactOneForm (f : GlobalSmooth S) : Section (cotangentBundle S) := by
  refine ⟨scalarDerivative S f.val, ?_⟩
  apply InducedConnections.dual_smooth_of_evaluations (tangentBundle S) (cotangentDual S)
  intro X p
  have hf : VectorSmoothAt S.smoothStructure.val (act S X f).val p :=
    (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
      ((SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp (act S X f).property p)
  apply hf.congr
  exact Eventually.of_forall (fun q => (ConnectionForms.scalarDerivative_global f X q).symm)

@[simp] theorem exactOneForm_apply (f : GlobalSmooth S) (X : Field S) (p : M) :
    (exactOneForm f).val p (X.val p) = (act S X f).val p :=
  ConnectionForms.scalarDerivative_global f X p

theorem bracket_act (X Y : Field S) (f : GlobalSmooth S) (p : M) :
    scalarDerivative S f.val p ((bracket X Y).val p) =
      (act S X (act S Y f)).val p - (act S Y (act S X f)).val p := by
  rw [ConnectionForms.scalarDerivative_global]
  have h := TorsionAndMetric.originalBracket_rule (S := S)
    (originalField S X) (originalField S Y) (act S X) (act S Y)
    (SmoothManifolds.VectorFields.derivationOfField_represents S
      (P202.MetricData.tangentStructure S) (originalField S X))
    (SmoothManifolds.VectorFields.derivationOfField_represents S
      (P202.MetricData.tangentStructure S) (originalField S Y))
  have hh := SmoothManifolds.LieBrackets.represents_eval h p f
  simpa only [ConnectionForms.act_apply, bracket, realizedField,
    Derivation.commutator_apply, Subalgebra.coe_sub, Pi.sub_apply] using hh

/-- The antisymmetric covariant Hessian of an exact covector is torsion. -/
theorem exact_hessian_antisymmetry_global
    (C : Connection (tangentBundle S))
    (K : Connection (cotangentBundle S)) (hK : DualRule C (cotangentDual S) K)
    (f : GlobalSmooth S) (lam : Section (cotangentBundle S))
    (hlam : ∀ (p : M) (v : TangentSpace S p),
      lam.val p v = scalarDerivative S f.val p v)
    (X Y : Field S) (p : M) :
    lam.val p (TorsionAndMetric.torsionFiber C p (X.val p) (Y.val p)) =
      (K.cov Y lam).val p (X.val p) - (K.cov X lam).val p (Y.val p) := by
  have hrep (Z : Field S) : (fun q => lam.val q (Z.val q)) = (act S Z f).val := by
    funext q
    rw [hlam, ConnectionForms.scalarDerivative_global]
  have hXY := hK X lam Y p
  have hYX := hK Y lam X p
  rw [hrep Y, ConnectionForms.scalarDerivative_global] at hXY
  rw [hrep X, ConnectionForms.scalarDerivative_global] at hYX
  have hb := bracket_act X Y f p
  rw [← hlam p ((bracket X Y).val p)] at hb
  rw [TorsionAndMetric.torsionFiber_apply, TorsionAndMetric.torsion_apply]
  change (lam.val p : Module.Dual ℝ (TangentSpace S p))
    ((C.cov X Y).val p - (C.cov Y X).val p - (bracket X Y).val p) = _
  have he := (lam.val p).map_sub
    ((C.cov X Y).val p - (C.cov Y X).val p) ((bracket X Y).val p)
  have he' := (lam.val p).map_sub ((C.cov X Y).val p) ((C.cov Y X).val p)
  rw [he, he']
  linarith only [hXY, hYX, hb]

/-- The exact-covector Hessian identity holds on arbitrary tangent vectors. -/
theorem exact_hessian_antisymmetry
    (C : Connection (tangentBundle S))
    (K : Connection (cotangentBundle S)) (hK : DualRule C (cotangentDual S) K)
    (f : GlobalSmooth S) (lam : Section (cotangentBundle S))
    (hlam : ∀ (p : M) (v : TangentSpace S p),
      lam.val p v = scalarDerivative S f.val p v)
    (p : M) (v w : TangentSpace S p) :
    lam.val p (TorsionAndMetric.torsionFiber C p v w) =
      (pointDerivative K lam.val p w) v - (pointDerivative K lam.val p v) w := by
  have hh := exact_hessian_antisymmetry_global C K hK f lam hlam
    (TorsionAndMetric.liftField p v) (TorsionAndMetric.liftField p w) p
  rw [← ConnectionForms.pointDerivative_global (cotangentBundle S) K lam p
    (TorsionAndMetric.liftField p w),
    ← ConnectionForms.pointDerivative_global (cotangentBundle S) K lam p
    (TorsionAndMetric.liftField p v)] at hh
  simpa only [TorsionAndMetric.liftField_value] using hh

section DifferentialAlong
variable {m : ℕ} {b : ModelKind} {N : Type u} [TopologicalSpace N]
  {R : SmoothManifold m b N} (F : N → M) (hF : IsSmoothMap R S F)
  (P : PullbackBundle (tangentBundle S) R F)

theorem differential_along_smooth (X : Field R) :
    letI := P.space.topology
    SmoothSection P.space.bundle
      (fun q => SmoothManifolds.differential R S F hF q (X.val q)) := by
  letI := P.space.topology
  have hOrig := PullbackConnections.differential_field_smooth F hF X
  have hd : IsSmoothMap R (tangentBundle S).totalManifold
      (fun q => (⟨F q, SmoothManifolds.differential R S F hF q (X.val q)⟩ :
        Bundle.TotalSpace (Euclidean n) (TangentSpace S))) := by
    letI := (P202.MetricData.tangentStructure S).topology
    intro q
    exact SmoothManifolds.manifoldContDiffAt_comp
      (P202.MetricData.tangentStructure S).manifold.smoothStructure.property.1.1
      (hOrig q) ((P202.MetricData.tangentRealization S).smooth_from_original _)
  exact SmoothManifolds.BundleOperations.pullback_smooth_lift
    (tangentBundle S) P R id
    (fun q => SmoothManifolds.differential R S F hF q (X.val q))
    (fun q => SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ R.smoothStructure.property.1 q) hd

noncomputable def differentialAlong (X : Field R) :
    letI := P.space.topology; Section P.space.bundle := by
  letI := P.space.topology
  exact ⟨_, differential_along_smooth F hF P X⟩

@[simp] theorem differentialAlong_apply (X : Field R) (q : N) :
    (differentialAlong F hF P X).val q =
      SmoothManifolds.differential R S F hF q (X.val q) := rfl

/-- Pair a differentiated differential field with an arbitrary exact covector.
The remaining term is the pullback of the target covariant Hessian. -/
theorem differential_along_dual_rule (C : Connection (tangentBundle S))
    (CP : letI := P.space.topology; Connection P.space.bundle)
    (hCP : P202.PullbackData.IsPullback (tangentBundle S) C F hF P CP)
    (X Y : Field R)
    (W : letI := P.space.topology; Section P.space.bundle)
    (hW : ∀ q, W.val q = SmoothManifolds.differential R S F hF q (Y.val q))
    (f : GlobalSmooth S) (q : N) :
    letI := P.space.topology
    scalarDerivative S f.val (F q) ((CP.cov X W).val q) =
      (act R X (act R Y (PullbackConnections.pullScalar F hF f))).val q -
        (pointDerivative (InducedConnections.dualConnection (tangentBundle S)
          (cotangentDual S) C) (exactOneForm f).val (F q)
          (SmoothManifolds.differential R S F hF q (X.val q)))
          (SmoothManifolds.differential R S F hF q (Y.val q)) := by
  let B := tangentBundle S
  let D := cotangentDual S
  letI := D.space.topology
  letI := P.space.topology
  let Q := P202.PullbackData.bundle D.space.bundle R F hF
  letI := Q.space.topology
  let K := InducedConnections.dualConnection B D C
  let CQ := PullbackConnections.pullback D.space.bundle F hF Q K
  let lam := exactOneForm f
  let lp := PullbackConnections.pullSection D.space.bundle F hF Q lam
  have hCQ := PullbackConnections.pullback_isPullback D.space.bundle F hF Q K
  have hdual := (InducedConnections.dual_pullback_compatibility B C D F hF P Q
    CP K CQ hCP (InducedConnections.dualConnection_rule B D C) hCQ).2
  have hh := hdual X lp W q
  have hpull := hCQ X lam lp (fun _ => rfl) q
  have heval : (fun z => lp.val z (W.val z)) =
      (act R Y (PullbackConnections.pullScalar F hF f)).val := by
    funext z
    change scalarDerivative S f.val (F z) (W.val z) = _
    rw [hW z]
    exact (PullbackConnections.scalar_chain F hF f Y z).symm
  rw [hpull, heval, ConnectionForms.scalarDerivative_global, hW q] at hh
  change
    (pointDerivative (InducedConnections.dualConnection (tangentBundle S)
      (cotangentDual S) C) (exactOneForm f).val (F q)
      (SmoothManifolds.differential R S F hF q (X.val q)))
      (SmoothManifolds.differential R S F hF q (Y.val q)) =
        (act R X (act R Y (PullbackConnections.pullScalar F hF f))).val q -
          scalarDerivative S f.val (F q) ((CP.cov X W).val q) at hh
  linarith

/-- Naturality of torsion under an arbitrary smooth map. No injectivity,
surjectivity, or constant-rank property of dF is needed. -/
theorem differential_naturality_fiber (C : Connection (tangentBundle S))
    (CP : letI := P.space.topology; Connection P.space.bundle)
    (hCP : P202.PullbackData.IsPullback (tangentBundle S) C F hF P CP)
    (X Y : Field R)
    (V W : letI := P.space.topology; Section P.space.bundle)
    (hV : ∀ q, V.val q = SmoothManifolds.differential R S F hF q (X.val q))
    (hW : ∀ q, W.val q = SmoothManifolds.differential R S F hF q (Y.val q))
    (q : N) :
    letI := P.space.topology
    (CP.cov X W).val q - (CP.cov Y V).val q -
      SmoothManifolds.differential R S F hF q ((bracket X Y).val q) =
        TorsionAndMetric.torsionFiber C (F q) (V.val q) (W.val q) := by
  letI := P.space.topology
  apply SmoothManifolds.LieBrackets.tangent_ext_global (F q)
  intro f
  have hev (v : TangentSpace S (F q)) :
      v.val (SmoothManifolds.globalToGerm S (F q) f) =
        scalarDerivative S f.val (F q) v :=
    (ConnectionForms.scalarDerivative_representative f.val f (F q) EventuallyEq.rfl v).symm
  rw [hev, hev]
  have hsub1 := (scalarDerivative S f.val (F q)).map_sub
    ((CP.cov X W).val q - (CP.cov Y V).val q)
    (SmoothManifolds.differential R S F hF q ((bracket X Y).val q))
  have hsub2 := (scalarDerivative S f.val (F q)).map_sub
    ((CP.cov X W).val q) ((CP.cov Y V).val q)
  rw [hsub1, hsub2]
  have hXY := differential_along_dual_rule F hF P C CP hCP X Y W hW f q
  have hYX := differential_along_dual_rule F hF P C CP hCP Y X V hV f q
  have htor := exact_hessian_antisymmetry C
    (InducedConnections.dualConnection (tangentBundle S) (cotangentDual S) C)
    (InducedConnections.dualConnection_rule (tangentBundle S) (cotangentDual S) C)
    f (exactOneForm f) (fun _ _ => rfl) (F q) (V.val q) (W.val q)
  change scalarDerivative S f.val (F q)
    (TorsionAndMetric.torsionFiber C (F q) (V.val q) (W.val q)) = _ at htor
  rw [hV q, hW q] at htor
  have hb := bracket_act X Y (PullbackConnections.pullScalar F hF f) q
  rw [ConnectionForms.scalarDerivative_global,
    PullbackConnections.scalar_chain F hF f (bracket X Y) q] at hb
  rw [hV q, hW q]
  linarith only [hXY, hYX, htor, hb]

end DifferentialAlong
end P202.Geometry.TorsionAndMetric

namespace P202.Geometry.TorsionAndMetric
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.BundleOperationsData SmoothManifolds.SectionExtensionData
  P202.ConnectionData P202.TorsionMetricData
open Set
universe u

/-- The uniquely descended torsion agrees with its intrinsic fiber evaluation. -/
theorem torsion_tensor_value {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : Connection (tangentBundle S)) (τ : TangentTwoTensor S)
    (hτ : ∀ (X Y : Field S) (p : M),
      τ.val p (X.val p) (Y.val p) = (torsion C X Y).val p)
    (p : M) (v w : TangentSpace S p) : τ.val p v w = torsionFiber C p v w := by
  rw [← liftField_value p v, ← liftField_value p w, hτ, torsionFiber_apply]

/-- The intrinsic torsion tensor obeys the naturality identity for arbitrary
smooth maps, including maps whose differential has nonconstant rank. -/
theorem differential_naturality :
    P202Specs.Geometry.TorsionAndMetric.differential_naturalityType := by
  intro n m a b M N _ _ S R C τ hτ F hF P
  letI := P.space.topology
  intro CP hCP X Y V W hV hW q
  rw [torsion_tensor_value C τ hτ]
  exact differential_naturality_fiber F hF P C CP hCP X Y V W hV hW q

/-- With V=dF(∂s), T=dF(∂t), the commuting coordinate directions give
D_s T - D_t V = torsion(V,T) on every parameter chart. -/
theorem two_parameter_identity :
    P202Specs.Geometry.TorsionAndMetric.two_parameter_identityType := by
  intro n a b M N _ _ S R e he hfull C τ hτ F hF P
  letI := P.space.topology
  intro CP hCP
  let ds := fullChartConstantField e he hfull (Pi.single (0 : Fin 2) 1)
  let dt := fullChartConstantField e he hfull (Pi.single (1 : Fin 2) 1)
  let V := differentialAlong F hF P ds
  let T := differentialAlong F hF P dt
  refine ⟨V, T, (fun _ => rfl), (fun _ => rfl), ?_⟩
  intro q
  have h := differential_naturality C τ hτ F hF P CP hCP ds dt V T
    (fun _ => rfl) (fun _ => rfl) q
  simp only [ds, dt, bracket_fullChartConstantField, ConnectionForms.section_zero_apply,
    map_zero] at h
  have hz (z : TangentSpace S (F q)) : z - (0 : TangentSpace S (F q)) = z := sub_zero z
  rw [hz] at h
  exact h

/-- In particular the two covariant derivatives agree for a torsion-free
connection, with no metric or rank hypothesis. -/
theorem two_parameter_torsion_free :
    P202Specs.Geometry.TorsionAndMetric.two_parameter_torsion_freeType := by
  intro n a b M N _ _ S R e he hfull C hC F hF P
  letI := P.space.topology
  intro CP hCP
  dsimp only
  intro V T hV hT q
  obtain ⟨τ, hτ, _⟩ := torsion_tensor_exists_unique C
  have hz := (torsion_free_tensor C τ hτ).mp hC
  have h := differential_naturality C τ hτ F hF P CP hCP
    (fullChartConstantField e he hfull (Pi.single (0 : Fin 2) 1))
    (fullChartConstantField e he hfull (Pi.single (1 : Fin 2) 1)) V T hV hT q
  simp only [bracket_fullChartConstantField, ConnectionForms.section_zero_apply,
    map_zero, hz] at h
  have hz0 (z : TangentSpace S (F q)) : z - (0 : TangentSpace S (F q)) = z := sub_zero z
  rw [hz0] at h
  exact sub_eq_zero.mp h

end P202.Geometry.TorsionAndMetric

namespace P202.Geometry.TorsionAndMetric
/-- Smoothness of the genuine differential fields in the statement's order. -/
theorem differential_fields_smooth :
    P202Specs.Geometry.TorsionAndMetric.differential_along_smoothType := by
  intro n m a b M N _ _ S R F hF P X
  exact differential_along_smooth F hF P X
end P202.Geometry.TorsionAndMetric
