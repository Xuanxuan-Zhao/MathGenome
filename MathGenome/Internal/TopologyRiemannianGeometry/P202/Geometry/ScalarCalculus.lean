import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ScalarCalculus
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConnectionForms
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothMetrics
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita

/-! Intrinsic scalar differential formulas for paper.tex 3246–3257 and
3272–3281. The coordinate formulas use the proved Levi–Civita Christoffel formula;
existence and uniqueness make the resulting scalar operators intrinsic. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000
noncomputable section

namespace P202.Geometry.ScalarCalculus
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.MapData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.ScalarData
universe u

namespace PointDerivationCalculus
open SmoothManifolds.TangentData
open scoped Classical
variable {A : Type*} [CommRing A] [Algebra ℝ A]
  (ε : A →ₐ[ℝ] ℝ) (d : pointDerivations ε)

theorem point_one : d.val 1 = 0 := by
  have h := d.property 1 1
  simp only [one_mul, map_one, one_mul] at h
  linarith

theorem point_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → A) :
    d.val (∏ i ∈ s, f i) = ∑ i ∈ s, d.val (f i) * ∏ j ∈ s.erase i, ε (f j) := by
  induction s using Finset.induction_on with
  | empty => simp [point_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, d.property, ih, map_prod, Finset.sum_insert ha,
      Finset.erase_insert ha]
    rw [Finset.mul_sum]
    conv_rhs => rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      have hia : i ≠ a := ne_of_mem_of_not_mem hi ha
      rw [Finset.erase_insert_of_ne hia.symm, Finset.prod_insert
        (fun h => ha (Finset.mem_of_mem_erase h))]
      ring
    · ring

theorem point_det {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι A) :
    d.val G.det = ∑ i : ι, ((G.map ε).updateCol i (fun j => d.val (G j i))).det := by
  simp only [Matrix.det_apply, map_sum, Units.smul_def, map_zsmul]
  simp_rw [point_prod]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [← Finset.sdiff_singleton_eq_erase]
  rw [← Finset.prod_update_of_mem (Finset.mem_univ i)]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp [Matrix.updateCol_apply]
  · simp [Matrix.updateCol_apply, Function.update_apply, hji]

theorem point_det_jacobi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι A) (hG : IsUnit (G.map ε).det) :
    d.val G.det = (G.map ε).det *
      (((G.map ε)⁻¹ * G.map d.val).trace) := by
  rw [point_det]
  have he : G.map d.val = G.map ε * ((G.map ε)⁻¹ * G.map d.val) := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
  have hc (i : ι) : (fun j => d.val (G j i)) =
      (fun j => ∑ k, ((G.map ε)⁻¹ * G.map d.val) k i • (G.map ε) j k) := by
    funext j
    have hij := congrFun (congrFun he j) i
    simpa only [Matrix.map_apply, Matrix.mul_apply, smul_eq_mul, mul_comm] using hij
  simp_rw [hc, Matrix.det_updateCol_sum, smul_eq_mul]
  simp only [Matrix.trace, Matrix.diag]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PointDerivationCalculus

section Intrinsic
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

@[simp] theorem musical_apply (g : RiemannianMetric S) (p : M)
    (v w : TangentSpace S p) : musical g p v w = pairing g p v w := rfl

theorem gradient_pairing (g : RiemannianMetric S) (u : GlobalSmooth S)
    (p : M) (v : TangentSpace S p) :
    pairing g p ((gradient g u).val p) v = scalarDerivative S u.val p v := by
  classical
  let hu := (SmoothManifolds.mem_globalSmoothAlgebra_iff S u.val).mp u.property
  have hg : scalarGerm S u.val p = SmoothManifolds.CovectorData.functionGerm S u.val hu p := by
    simp only [scalarGerm, dite_eq_left (hu p)]
    rfl
  change musical g p ((musical g p).symm
    (SmoothManifolds.CovectorData.dFunction S u.val hu p)) v = _
  rw [LinearEquiv.apply_symm_apply]
  unfold scalarDerivative
  rw [hg]
  rfl

theorem hessian_covariant_apply (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (u : GlobalSmooth S)
    (X Y : Field S) (p : M) :
    hessian g C u p (X.val p) (Y.val p) =
      pairing g p ((C.cov X (gradient g u)).val p) (Y.val p) := by
  change pairing g p (pointDerivative C (gradient g u).val p (X.val p)) (Y.val p) = _
  rw [ConnectionForms.pointDerivative_global (tangentBundle S) C]

theorem hessian_derivation_formula (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (u : GlobalSmooth S) (X Y : Field S) (p : M) :
    hessian g C u p (X.val p) (Y.val p) =
      (act S X (act S Y u)).val p - (act S (C.cov X Y) u).val p := by
  have he : (fun q => pairing g q ((gradient g u).val q) (Y.val q)) =
      (act S Y u).val := by
    funext q
    rw [gradient_pairing, ConnectionForms.scalarDerivative_global]
  have h := hC.2 X (gradient g u) Y p
  rw [he, ConnectionForms.scalarDerivative_global] at h
  rw [← hessian_covariant_apply] at h
  rw [gradient_pairing, ConnectionForms.scalarDerivative_global] at h
  exact (eq_sub_iff_add_eq).mpr h.symm

theorem laplacian_metric_trace (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (u : GlobalSmooth S) (p : M) :
    laplacian g C u p = metricTrace g p (hessian g C u p) := by
  unfold laplacian divergence metricTrace
  congr 1
  apply LinearMap.ext
  intro v
  change _ = (musical g p).symm (pairing g p (pointDerivative C (gradient g u).val p v))
  change _ = (musical g p).symm (musical g p (pointDerivative C (gradient g u).val p v))
  rw [LinearEquiv.symm_apply_apply]

theorem bracket_action (X Y : Field S) (u : GlobalSmooth S) (p : M) :
    (act S (P202.TorsionMetricData.bracket X Y) u).val p =
      (act S X (act S Y u)).val p - (act S Y (act S X u)).val p :=
  LeviCivita.bracket_action X Y u p

theorem hessian_symmetric (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (u : GlobalSmooth S) (p : M) (v w : TangentSpace S p) :
    hessian g C u p v w = hessian g C u p w v := by
  obtain ⟨X, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p v
  obtain ⟨Y, rfl⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p w
  rw [hessian_derivation_formula g C hC, hessian_derivation_formula g C hC]
  have ht := congrArg (fun Z : Field S => Z.val p) (hC.1 X Y)
  change (C.cov X Y).val p + (-1 : ℝ) • (C.cov Y X).val p +
    (-1 : ℝ) • (P202.TorsionMetricData.bracket X Y).val p = 0 at ht
  have hd := congrArg (scalarDerivative S u.val p) ht
  simp only [map_add, map_smul, map_zero, smul_eq_mul,
    ConnectionForms.scalarDerivative_global] at hd
  rw [bracket_action] at hd
  linarith

open SmoothManifolds.FrameData SmoothManifolds.PartitionData
open Filter
open scoped Topology

theorem scalarGerm_val {f : M → ℝ} {p : M}
    (hf : VectorSmoothAt S.smoothStructure.val f p) :
    (scalarGerm S f p).val = Germ.ofFun f := by
  simp only [scalarGerm, dite_eq_left ((SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr hf)]

theorem scalarDerivative_congr {f h : M → ℝ} {p : M}
    (hf : VectorSmoothAt S.smoothStructure.val f p)
    (he : f =ᶠ[𝓝 p] h) (v : TangentSpace S p) :
    scalarDerivative S f p v = scalarDerivative S h p v := by
  have hg : scalarGerm S f p = scalarGerm S h p := by
    apply Subtype.ext
    rw [scalarGerm_val hf, scalarGerm_val (hf.congr he)]
    exact Germ.coe_eq.mpr he
  change v.val (scalarGerm S f p) = v.val (scalarGerm S h p)
  rw [hg]

theorem vectorSmooth_mul {f h : M → ℝ} {p : M}
    (hf : VectorSmoothAt S.smoothStructure.val f p)
    (hh : VectorSmoothAt S.smoothStructure.val h p) :
    VectorSmoothAt S.smoothStructure.val (fun q => f q * h q) p :=
  (hf.prod hh).postcomp (contDiff_fst.mul contDiff_snd)

theorem scalarDerivative_mul {f h : M → ℝ} {p : M}
    (hf : VectorSmoothAt S.smoothStructure.val f p)
    (hh : VectorSmoothAt S.smoothStructure.val h p) (v : TangentSpace S p) :
    scalarDerivative S (fun q => f q * h q) p v =
      f p * scalarDerivative S h p v + h p * scalarDerivative S f p v := by
  have he : scalarGerm S (fun q => f q * h q) p = scalarGerm S f p * scalarGerm S h p := by
    apply Subtype.ext
    rw [scalarGerm_val (vectorSmooth_mul hf hh)]
    change _ = (scalarGerm S f p).val * (scalarGerm S h p).val
    rw [scalarGerm_val hf, scalarGerm_val hh]
    rfl
  change v.val (scalarGerm S (fun q => f q * h q) p) = _
  rw [he, v.property]
  change (scalarGerm S f p).val.value * _ + (scalarGerm S h p).val.value * _ = _
  rw [scalarGerm_val hf, scalarGerm_val hh]
  rfl

theorem scalarGerm_evaluation {f : M → ℝ} {p : M}
    (hf : VectorSmoothAt S.smoothStructure.val f p) :
    germEvaluation S p (scalarGerm S f p) = f p := by
  change (scalarGerm S f p).val.value = _
  rw [scalarGerm_val hf]
  rfl

theorem scalarDerivative_sum {κ : Type*} [Fintype κ]
    (f : κ → M → ℝ) {p : M}
    (hf : ∀ i, VectorSmoothAt S.smoothStructure.val (f i) p) (v : TangentSpace S p) :
    scalarDerivative S (fun q => ∑ i, f i q) p v = ∑ i, scalarDerivative S (f i) p v := by
  classical
  have he : scalarGerm S (fun q => ∑ i, f i q) p = ∑ i, scalarGerm S (f i) p := by
    apply Subtype.ext
    rw [scalarGerm_val (VectorSmoothAt.sum hf)]
    change _ = (smoothGermAlgebra S p).val (∑ i, scalarGerm S (f i) p)
    rw [map_sum]
    change Germ.ofFun (fun q => ∑ i, f i q) = ∑ i, (scalarGerm S (f i) p).val
    simp_rw [scalarGerm_val (hf _)]
    have hfun : (fun q => ∑ i, f i q) = ∑ i, f i := by
      funext q
      simp only [Finset.sum_apply]
    rw [hfun]
    exact map_sum (Germ.coeRingHom (𝓝 p)) f Finset.univ
  change v.val (scalarGerm S (fun q => ∑ i, f i q) p) = _
  rw [he, map_sum]
  rfl

@[simp] theorem matrix_of_self (A : Matrix (Fin n) (Fin n) ℝ) : Matrix.of A = A := rfl

theorem scalarGerm_det (F : M → Matrix (Fin n) (Fin n) ℝ) {p : M}
    (hF : ∀ i j, VectorSmoothAt S.smoothStructure.val (fun q => F q i j) p) :
    scalarGerm S (fun q => (F q).det) p =
      Matrix.det (fun i j => scalarGerm S (fun q => F q i j) p) := by
  apply Subtype.ext
  have hdF := (VectorSmoothAt.pi (fun i => VectorSmoothAt.pi (hF i))).postcomp
    (SmoothManifolds.MetricVolumeResults.matrix_det_smooth n)
  simp only [matrix_of_self] at hdF
  rw [scalarGerm_val hdF]
  change _ = (smoothGermAlgebra S p).val (Matrix.det (fun i j => scalarGerm S (fun q => F q i j) p))
  rw [AlgHom.map_det]
  have hmap : (smoothGermAlgebra S p).val.mapMatrix
      (fun i j => scalarGerm S (fun q => F q i j) p) =
      (Germ.coeRingHom (𝓝 p)).mapMatrix (fun i j q => F q i j) := by
    ext i j
    exact scalarGerm_val (hF i j)
  rw [hmap, ← RingHom.map_det]
  have hfun : Matrix.det (fun i j q => F q i j) = fun q => (F q).det := by
    funext q
    exact (Pi.evalRingHom (fun _ : M => ℝ) q).map_det (fun i j q => F q i j)
  rw [hfun]
  rfl

theorem metric_matrix_positive (g : RiemannianMetric S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) : (metricMatrix g c p.val).PosDef := by
  let e := (tangentBundle S).fiberCoordinates c p.val p.property
  let b := (Pi.basisFun ℝ (Fin n)).map e.symm
  have h := SmoothManifolds.MetricVolumeResults.bilinear_gram_posDef
    (pairing g p.val) (g.symmetric p.val) (g.positive p.val) b
  convert h using 1
  ext i j
  simp only [P202.LeviCivitaData.metricMatrix, P202.LeviCivitaData.coordinateVector,
    Matrix.of_apply, b, e, Module.Basis.map_apply, Pi.basisFun_apply,
    SmoothVectorBundle.fiberCoordinates_symm_apply]

theorem metric_entry_smooth (g : RiemannianMetric S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (i j : Fin n) :
    VectorSmoothAt S.smoothStructure.val (fun q => metricMatrix g c q i j) p.val :=
  g.smooth c i j p.val p.property

theorem rho_positive (g : RiemannianMetric S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) : 0 < rho g c p.val :=
  Real.sqrt_pos.mpr (metric_matrix_positive g c p).det_pos

theorem rho_smooth (g : RiemannianMetric S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) :
    VectorSmoothAt S.smoothStructure.val (rho g c) p.val := by
  have hdet := (VectorSmoothAt.pi (fun i => VectorSmoothAt.pi
    (metric_entry_smooth g c p i))).postcomp
    (SmoothManifolds.MetricVolumeResults.matrix_det_smooth n)
  simp only [matrix_of_self] at hdet
  apply hdet.postcompOn isOpen_Ioi (metric_matrix_positive g c p).det_pos
  intro x hx
  exact (Real.contDiffAt_sqrt (ne_of_gt hx)).contDiffWithinAt

theorem rho_derivative_jacobi (g : RiemannianMetric S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (v : TangentSpace S p.val) :
    scalarDerivative S (rho g c) p.val v = (rho g c p.val / 2) *
      ((metricMatrix g c p.val)⁻¹ *
        Matrix.of (fun i j => scalarDerivative S (fun q => metricMatrix g c q i j) p.val v)).trace := by
  let G : Matrix (Fin n) (Fin n) (SmoothGerm S p.val) :=
    fun i j => scalarGerm S (fun q => metricMatrix g c q i j) p.val
  let R := scalarGerm S (rho g c) p.val
  have heval : G.map (germEvaluation S p.val) = metricMatrix g c p.val := by
    ext i j
    exact scalarGerm_evaluation (metric_entry_smooth g c p i j)
  have hdet := scalarGerm_det (fun q => metricMatrix g c q) (metric_entry_smooth g c p)
  have hsq : R * R = G.det := by
    rw [← hdet]
    apply Subtype.ext
    change R.val * R.val = (scalarGerm S (fun q => (metricMatrix g c q).det) p.val).val
    have hdF := (VectorSmoothAt.pi (fun i => VectorSmoothAt.pi
      (metric_entry_smooth g c p i))).postcomp
      (SmoothManifolds.MetricVolumeResults.matrix_det_smooth n)
    simp only [matrix_of_self] at hdF
    rw [scalarGerm_val (rho_smooth g c p), scalarGerm_val hdF]
    apply Germ.coe_eq.mpr
    have hO : IsOpen ((tangentBundle S).baseSet c) :=
      (tangentBundle S).trivialization_baseSet c ▸ ((tangentBundle S).trivialization c).open_baseSet
    filter_upwards [hO.mem_nhds p.property] with q hq
    exact Real.mul_self_sqrt (metric_matrix_positive g c ⟨q, hq⟩).det_pos.le
  have hd := PointDerivationCalculus.point_det_jacobi (germEvaluation S p.val) v G
    (heval ▸ isUnit_iff_ne_zero.mpr (ne_of_gt (metric_matrix_positive g c p).det_pos))
  rw [heval, ← hsq, v.property] at hd
  have hR : germEvaluation S p.val R = rho g c p.val := scalarGerm_evaluation (rho_smooth g c p)
  rw [hR] at hd
  change rho g c p.val * scalarDerivative S (rho g c) p.val v +
    rho g c p.val * scalarDerivative S (rho g c) p.val v = _ at hd
  have hr2 : rho g c p.val * rho g c p.val = (metricMatrix g c p.val).det :=
    Real.mul_self_sqrt (metric_matrix_positive g c p).det_pos.le
  have hr := rho_positive g c p
  have hc : G.map v.val =
      (fun i j => scalarDerivative S (fun q => metricMatrix g c q i j) p.val v) := rfl
  rw [hc, ← hr2] at hd
  simp only [matrix_of_self]
  nlinarith

theorem gradient_coordinate_formula (g : RiemannianMetric S) (u : GlobalSmooth S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (i : Fin n) :
    component c (gradient g u) i p.val = ∑ j : Fin n,
      (metricMatrix g c p.val)⁻¹ i j * coordinateDerivative c j u.val p.val := by
  let e := (tangentBundle S).fiberCoordinates c p.val p.property
  let V := (gradient g u).val p.val
  have hex : V = ∑ j : Fin n, (e V) j • coordinateVector c j p.val := by
    have hx := congrArg e.symm ((Pi.basisFun ℝ (Fin n)).sum_equivFun (e V))
    simp only [map_sum, map_smul, LinearEquiv.symm_apply_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply] at hx
    simpa only [Pi.basisFun_apply, e, coordinateVector,
      SmoothVectorBundle.fiberCoordinates_symm_apply] using hx.symm
  have hd : (fun j => coordinateDerivative c j u.val p.val) =
      (metricMatrix g c p.val).mulVec (e V) := by
    funext j
    unfold coordinateDerivative
    rw [← gradient_pairing g u]
    change pairing g p.val V (coordinateVector c j p.val) = _
    conv_lhs => rw [hex]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct, metricMatrix]
    apply Finset.sum_congr rfl
    intro k _
    rw [show pairing g p.val (coordinateVector c k p.val) (coordinateVector c j p.val) =
      pairing g p.val (coordinateVector c j p.val) (coordinateVector c k p.val) from
      g.symmetric p.val _ _]
    ring
  have hu : IsUnit (metricMatrix g c p.val).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (metric_matrix_positive g c p).det_pos)
  have he := congrArg (fun v => (metricMatrix g c p.val)⁻¹.mulVec v) hd
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at he
  exact (congrFun he i).symm

theorem coordinate_frame_equiv
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) :
    ((SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c).basis p).equivFun =
      (tangentBundle S).fiberCoordinates c p.val p.property := by
  change ((Pi.basisFun ℝ (Fin n)).map
    ((tangentBundle S).fiberCoordinates c p.val p.property).symm).equivFun = _
  rw [Module.Basis.map_equivFun, Pi.basisFun_equivFun]
  rfl

theorem coordinate_frame_vector
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (i : Fin n) :
    (SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c).basis p i =
      coordinateVector c i p.val := by
  change ((Pi.basisFun ℝ (Fin n)).map
    ((tangentBundle S).fiberCoordinates c p.val p.property).symm) i = _
  simp only [Module.Basis.map_apply, Pi.basisFun_apply,
    SmoothVectorBundle.fiberCoordinates_symm_apply, coordinateVector]

theorem component_smooth (X : Field S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (i : Fin n) :
    VectorSmoothAt S.smoothStructure.val (component c X i) p.val :=
  (SmoothManifolds.SectionExtension.coordinates_smoothAt (tangentBundle S) c p.property
    (X.property p.val)).postcomp (ContinuousLinearMap.proj (R := ℝ) i).contDiff

theorem partial_function_smooth (u : GlobalSmooth S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (j : Fin n) :
    VectorSmoothAt S.smoothStructure.val (coordinateDerivative c j u.val) p.val := by
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hU : IsOpen (B.baseSet c) := B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b p
  have hsm : VectorSmoothAt S.smoothStructure.val (act S (e j) u).val p.val :=
    (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
    ((SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mp (act S (e j) u).property p.val)
  apply hsm.congr
  filter_upwards [he j, hU.mem_nhds p.property] with q heq hq
  rw [← ConnectionForms.scalarDerivative_global]
  unfold coordinateDerivative
  congr 1
  rw [heq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
  change b.basis ⟨q, hq⟩ j = _
  exact coordinate_frame_vector c ⟨q, hq⟩ j

theorem inverse_metric_smooth (g : RiemannianMetric S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (i j : Fin n) :
    VectorSmoothAt S.smoothStructure.val (fun q => (metricMatrix g c q)⁻¹ i j) p.val := by
  classical
  have hm := VectorSmoothAt.pi (fun i => VectorSmoothAt.pi (metric_entry_smooth g c p i))
  have hd := hm.postcomp (SmoothManifolds.MetricVolumeResults.matrix_det_smooth n)
  simp only [matrix_of_self] at hd
  have hi := (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
    (((SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr hd).inv
      (ne_of_gt (metric_matrix_positive g c p).det_pos))
  have ha : ContDiff ℝ (⊤ : ℕ∞)
      (fun A : Fin n → Fin n → ℝ => (Matrix.of A).adjugate i j) := by
    simp only [Matrix.adjugate_apply, Matrix.det_apply, Matrix.updateRow_apply,
      Matrix.of_apply]
    have hentry (σ : Equiv.Perm (Fin n)) (k : Fin n) :
        ContDiff ℝ (⊤ : ℕ∞) (fun A : Fin n → Fin n → ℝ =>
          if σ k = j then (if k = i then (1 : ℝ) else 0) else A (σ k) k) := by
      split_ifs <;> fun_prop
    apply ContDiff.sum
    intro σ _
    apply ContDiff.const_smul
    apply contDiff_prod
    intro k _
    by_cases hkj : σ k = j
    · simp only [hkj, ite_true]
      exact contDiff_const
    · simp only [hkj, ite_false]
      fun_prop
  have h := vectorSmooth_mul hi (hm.postcomp ha)
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
    smul_eq_mul, matrix_of_self] using h

theorem divergence_connection_coordinates (C : Connection (tangentBundle S)) (X : Field S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) :
    divergence C X p.val = ∑ i : Fin n,
      (coordinateDerivative c i (component c X i) p.val +
        ∑ j : Fin n, christoffel C c p i i j * component c X j p.val) := by
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  let hU : IsOpen (B.baseSet c) := B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  let s := restrictGlobalSection X (B.baseSet c) hU
  have hs : ∀ᶠ q in 𝓝 p.val,
      X.val q = SmoothManifolds.SectionExtension.totalSection s.val q := by
    filter_upwards [hU.mem_nhds p.property] with q hq
    exact (SmoothManifolds.SectionExtension.totalSection_of_mem s.val q hq).symm
  have hd := ConnectionForms.pointDerivative_congr B C X.val
    (SmoothManifolds.SectionExtension.totalSection s.val) p.val
    ⟨X, Filter.Eventually.of_forall (fun _ => rfl)⟩ hs
  change pointDerivative C X.val p.val =
    pointDerivative C (SmoothManifolds.SectionExtension.totalSection s.val) p.val at hd
  have hcoeff (q : B.baseSet c) (i : Fin n) : coefficients b s.val q i = component c X i q.val := by
    unfold coefficients
    rw [coordinate_frame_equiv]
    rfl
  unfold divergence
  rw [LinearMap.trace_eq_matrix_trace ℝ (b.basis p)]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply]
  change (b.basis p).equivFun (pointDerivative C X.val p.val ((b.basis p) i)) i = _
  rw [coordinate_frame_vector, hd]
  have hf := ConnectionForms.local_frame_formula B C b s p (coordinateVector c i p.val) i
  rw [hf]
  simp_rw [hcoeff]
  congr 1
  apply (scalarDerivative_congr (component_smooth X c p i) ?_ (coordinateVector c i p.val)).symm
  filter_upwards [hU.mem_nhds p.property] with q hq
  simp only [SmoothManifolds.FrameData.totalize_of_mem _ q hq, hcoeff]

theorem metric_matrix_symmetry (g : RiemannianMetric S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S) (p : M) :
    (metricMatrix g c p).IsSymm := by
  ext i j
  exact g.symmetric p _ _

theorem metric_derivative_symmetry (g : RiemannianMetric S)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : M) (v : TangentSpace S p) (i j : Fin n) :
    scalarDerivative S (fun q => metricMatrix g c q i j) p v =
      scalarDerivative S (fun q => metricMatrix g c q j i) p v := by
  have he : (fun q => metricMatrix g c q i j) = (fun q => metricMatrix g c q j i) := by
    funext q
    exact g.symmetric q _ _
  rw [he]

theorem contracted_christoffel
    (hchristoffel : P202Specs.Geometry.LeviCivita.christoffel_formulaType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (j : Fin n) :
    ∑ i : Fin n, christoffel C c p i i j =
      (1 / 2 : ℝ) * ∑ i : Fin n, ∑ l : Fin n,
        (metricMatrix g c p.val)⁻¹ i l *
          coordinateDerivative c j (fun q => metricMatrix g c q i l) p.val := by
  let A := (metricMatrix g c p.val)⁻¹
  let D (i j l : Fin n) := coordinateDerivative c i (fun q => metricMatrix g c q j l) p.val
  have hs (i l : Fin n) : A i l = A l i :=
    congrFun (congrFun (metric_matrix_symmetry g c p.val).inv l) i
  have hd (i k l : Fin n) : D i k l = D i l k :=
    metric_derivative_symmetry g c p.val (coordinateVector c i p.val) k l
  have hc : (∑ i : Fin n, ∑ l : Fin n, A i l * D i j l) =
      ∑ i : Fin n, ∑ l : Fin n, A i l * D l i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    rw [hs l i, hd l j i]
  have hf (i : Fin n) : christoffel C c p i i j =
      (1 / 2 : ℝ) * ∑ l : Fin n, A i l * (D i j l + D j i l - D l i j) :=
    hchristoffel g C hC c p i i j
  simp_rw [hf]
  rw [← Finset.mul_sum]
  change (1 / 2 : ℝ) * (∑ i : Fin n, ∑ l : Fin n, A i l * (D i j l + D j i l - D l i j)) = _
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hc]
  ring

theorem christoffel_rho
    (hchristoffel : P202Specs.Geometry.LeviCivita.christoffel_formulaType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) (j : Fin n) :
    ∑ i : Fin n, christoffel C c p i i j =
      (rho g c p.val)⁻¹ * coordinateDerivative c j (rho g c) p.val := by
  rw [contracted_christoffel hchristoffel g C hC]
  unfold coordinateDerivative
  rw [rho_derivative_jacobi]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  have he : (∑ i : Fin n, ∑ l : Fin n, (metricMatrix g c p.val)⁻¹ i l *
      scalarDerivative S (fun q => metricMatrix g c q l i) p.val (coordinateVector c j p.val)) =
      ∑ i : Fin n, ∑ l : Fin n, (metricMatrix g c p.val)⁻¹ i l *
        scalarDerivative S (fun q => metricMatrix g c q i l) p.val (coordinateVector c j p.val) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    rw [metric_derivative_symmetry g c p.val (coordinateVector c j p.val) l i]
  rw [he]
  have hr : rho g c p.val ≠ 0 := ne_of_gt (rho_positive g c p)
  field_simp

theorem divergence_density_formula
    (hchristoffel : P202Specs.Geometry.LeviCivita.christoffel_formulaType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (X : Field S) (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) :
    divergence C X p.val = (rho g c p.val)⁻¹ * ∑ i : Fin n,
      coordinateDerivative c i (fun q => rho g c q * component c X i q) p.val := by
  have hp (i : Fin n) : coordinateDerivative c i
      (fun q => rho g c q * component c X i q) p.val =
      rho g c p.val * coordinateDerivative c i (component c X i) p.val +
        component c X i p.val * coordinateDerivative c i (rho g c) p.val :=
    scalarDerivative_mul (rho_smooth g c p) (component_smooth X c p i) _
  rw [divergence_connection_coordinates C X c p]
  simp_rw [hp, Finset.sum_add_distrib]
  rw [mul_add, ← Finset.mul_sum,
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (rho_positive g c p)), one_mul]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, christoffel_rho hchristoffel g C hC]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem laplacian_density_formula
    (hchristoffel : P202Specs.Geometry.LeviCivita.christoffel_formulaType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (u : GlobalSmooth S) (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : (tangentBundle S).baseSet c) :
    laplacian g C u p.val = (rho g c p.val)⁻¹ * ∑ i : Fin n, ∑ j : Fin n,
      coordinateDerivative c i (fun q => rho g c q * (metricMatrix g c q)⁻¹ i j *
        coordinateDerivative c j u.val q) p.val := by
  change divergence C (P202.ScalarData.gradient g u) p.val = _
  rw [divergence_density_formula hchristoffel g C hC (P202.ScalarData.gradient g u) c p]
  apply congrArg (fun t : ℝ => (rho g c p.val)⁻¹ * t)
  apply Finset.sum_congr rfl
  intro i _
  let f (j : Fin n) (q : M) := rho g c q * (metricMatrix g c q)⁻¹ i j *
    coordinateDerivative c j u.val q
  have hf (j : Fin n) : VectorSmoothAt S.smoothStructure.val (f j) p.val :=
    vectorSmooth_mul (vectorSmooth_mul (rho_smooth g c p) (inverse_metric_smooth g c p i j))
      (partial_function_smooth u c p j)
  have hU : IsOpen ((tangentBundle S).baseSet c) :=
    (tangentBundle S).trivialization_baseSet c ▸ ((tangentBundle S).trivialization c).open_baseSet
  have he : (fun q => rho g c q * component c (P202.ScalarData.gradient g u) i q) =ᶠ[𝓝 p.val]
      (fun q => ∑ j : Fin n, f j q) := by
    filter_upwards [hU.mem_nhds p.property] with q hq
    rw [gradient_coordinate_formula g u c ⟨q, hq⟩ i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (mul_assoc _ _ _).symm
  exact (scalarDerivative_congr (vectorSmooth_mul (rho_smooth g c p)
    (component_smooth (P202.ScalarData.gradient g u) c p i)) he (coordinateVector c i p.val)).trans
      (scalarDerivative_sum f hf (coordinateVector c i p.val))

end Intrinsic

/-! The original targets have no additional premises. -/
theorem gradient_characterization :
    P202Specs.Geometry.ScalarCalculus.gradient_characterizationType.{u} :=
  gradient_pairing

theorem hessian_covariant :
    P202Specs.Geometry.ScalarCalculus.hessian_covariantType.{u} :=
  hessian_covariant_apply

theorem hessian_formula :
    P202Specs.Geometry.ScalarCalculus.hessian_formulaType.{u} :=
  hessian_derivation_formula

theorem hessian_symmetry :
    P202Specs.Geometry.ScalarCalculus.hessian_symmetryType.{u} :=
  hessian_symmetric

theorem laplacian_trace :
    P202Specs.Geometry.ScalarCalculus.laplacian_traceType.{u} :=
  laplacian_metric_trace

theorem gradient_coordinates :
    P202Specs.Geometry.ScalarCalculus.gradient_coordinatesType.{u} :=
  gradient_coordinate_formula

theorem divergence_coordinates :
    P202Specs.Geometry.ScalarCalculus.divergence_coordinatesType.{u} :=
  divergence_density_formula LeviCivita.christoffel_formula

theorem laplacian_coordinates :
    P202Specs.Geometry.ScalarCalculus.laplacian_coordinatesType.{u} :=
  laplacian_density_formula LeviCivita.christoffel_formula

theorem connection_independence :
    P202Specs.Geometry.ScalarCalculus.connection_independenceType.{u} := by
  intro n a M _ S g
  refine ⟨(LeviCivita.exists_unique g).exists, ?_⟩
  intro C D hC hD
  have he := LeviCivita.uniqueness g C D hC hD
  subst D
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end P202.Geometry.ScalarCalculus
