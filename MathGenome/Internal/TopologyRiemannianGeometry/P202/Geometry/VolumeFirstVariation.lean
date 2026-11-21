import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.VolumeFirstVariation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GaussWeingarten
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PiecewiseCurves
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RiemannianVolume
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.DivergenceGreen
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology CompactlySupported Classical

namespace P202.Geometry.VolumeFirstVariation
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData P202.MetricData P202.ConnectionData P202.ScalarData
  P202.VolumeVariationData
universe u v

section Trace
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem dual_metric_symmetry (g : RiemannianMetric S) (p : M)
    (α β : Module.Dual ℝ (TangentSpace S p)) :
    α ((musical g p).symm β) = β ((musical g p).symm α) := by
  have hα := congrArg (fun f => f ((musical g p).symm β))
    ((musical g p).apply_symm_apply α)
  have hβ := congrArg (fun f => f ((musical g p).symm α))
    ((musical g p).apply_symm_apply β)
  exact hα.symm.trans ((g.symmetric p _ _).trans hβ)

theorem trace_pairing_in_basis {E : Type v} [AddCommGroup E] [Module ℝ E]
    (g : RiemannianMetric S) (p : M)
    (B : TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] E)
    (φ : E →ₗ[ℝ] ℝ) {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (TangentSpace S p)) :
    φ (∑ j, B (e j) ((musical g p).symm (e.coord j))) =
      metricTrace g p (B.compr₂ φ) := by
  classical
  rw [map_sum, metricTrace, LinearMap.trace_eq_matrix_trace ℝ e]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.diag, LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change φ (B (e j) ((musical g p).symm (e.coord j))) =
    e.repr ((musical g p).symm ((B.compr₂ φ) (e j))) j
  exact (dual_metric_symmetry g p (e.coord j) ((B.compr₂ φ) (e j))).symm

theorem trace_pairing : P202Specs.Geometry.VolumeFirstVariation.trace_pairingType.{u,v} := by
  intro n a M _ S E _ _ g p B φ
  simp only [vectorMetricTrace, Module.Basis.coe_dualBasis]
  exact trace_pairing_in_basis g p B φ (fiberBasis S p)

theorem trace_basis_independent :
    P202Specs.Geometry.VolumeFirstVariation.trace_basis_independentType.{u,v} := by
  intro n a M _ S E _ _ g p B ι _ e
  simp only [Module.Basis.coe_dualBasis]
  apply Module.eval_apply_injective ℝ
  apply LinearMap.ext
  intro φ
  exact (trace_pairing g p B φ).trans (trace_pairing_in_basis g p B φ e).symm

def meanCurvature : P202Specs.Geometry.VolumeFirstVariation.meanCurvatureType.{u,v} :=
  @P202.VolumeVariationData.meanCurvature

theorem vectorMetricTrace_eq_orthonormal_sum {E : Type v} [AddCommGroup E] [Module ℝ E]
    (g : RiemannianMetric S) (p : M)
    (B : TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] E)
    {ι : Type*} [Fintype ι] (e : Module.Basis ι ℝ (TangentSpace S p))
    (he : ∀ i j, pairing g p (e i) (e j) = if j = i then 1 else 0) :
    vectorMetricTrace g p B = ∑ j, B (e j) (e j) := by
  rw [trace_basis_independent g p B e]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply (musical g p).injective
  rw [LinearEquiv.apply_symm_apply]
  apply e.ext
  intro k
  exact (e.dualBasis_apply_self j k).trans (he j k).symm


end Trace

section Determinant
theorem hasDerivAt_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ℝ → Matrix ι ι ℝ) (D : Matrix ι ι ℝ) (s : ℝ)
    (h : ∀ i j, HasDerivAt (fun t => G t i j) (D i j) s) :
    HasDerivAt (fun t => (G t).det)
      (∑ i : ι, ((G s).updateCol i (fun j => D j i)).det) s := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ =>
    (HasDerivAt.fun_finsetProd (u := Finset.univ)
      (fun j _ => h (σ j) j)).const_mul (↑(Equiv.Perm.sign σ) : ℝ))
  simp only [smul_eq_mul] at hd
  convert hd using 1
  · funext t
    simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  · simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [Matrix.updateCol_apply]
    rw [mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hji]

theorem hasDerivAt_det_jacobi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ℝ → Matrix ι ι ℝ) (D : Matrix ι ι ℝ) (s : ℝ)
    (h : ∀ i j, HasDerivAt (fun t => G t i j) (D i j) s)
    (hG : IsUnit (G s).det) :
    HasDerivAt (fun t => (G t).det) ((G s).det * ((G s)⁻¹ * D).trace) s := by
  convert hasDerivAt_det G D s h using 1
  have he : D = G s * ((G s)⁻¹ * D) := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
  have hc (i : ι) : (fun j => D j i) =
      (fun j => ∑ k, ((G s)⁻¹ * D) k i • G s j k) := by
    funext j
    have hij := congrFun (congrFun he j) i
    simpa only [Matrix.mul_apply, smul_eq_mul, mul_comm] using hij
  simp_rw [hc, Matrix.det_updateCol_sum, smul_eq_mul]
  simp only [Matrix.trace, Matrix.diag]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sqrt_det_derivative :
    P202Specs.Geometry.VolumeFirstVariation.sqrt_det_derivativeType := by
  intro ι _ _ G D s h hG
  have hne := ne_of_gt hG
  have hdet := hasDerivAt_det_jacobi G D s h (isUnit_iff_ne_zero.mpr hne)
  convert hdet.sqrt hne using 1
  have hs := Real.sq_sqrt (le_of_lt hG)
  have hsne := ne_of_gt (Real.sqrt_pos.mpr hG)
  field_simp
  rw [hs]
  ring

end Determinant

section Geometry
open SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
  SmoothManifolds.BundleMetricData P202.LeviCivitaData P202.GaussWeingartenData
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

theorem induced_metrics_exists :
    P202Specs.Geometry.VolumeFirstVariation.induced_metrics_existsType.{u} := by
  intro n m a b M N _ _ S T Q h
  classical
  let gg : Q.domain → RiemannianMetric S := fun s =>
    (SmoothMetrics.pullback_metric S T (Q.map s.val) (Q.immersion s.val s.property) h).choose
  let g : ℝ → RiemannianMetric S := fun s =>
    if hs : s ∈ Q.domain then gg ⟨s, hs⟩ else gg ⟨0, Q.zero_mem⟩
  refine ⟨g, ?_⟩
  intro s hs p v w
  dsimp only [g]
  rw [dite_eq_left hs]
  exact (SmoothMetrics.pullback_metric S T (Q.map s) (Q.immersion s hs) h).choose_spec p v w

theorem second_form_exists :
    P202Specs.Geometry.VolumeFirstVariation.second_form_existsType.{u} := by
  intro n m a b M N _ _ S T g h F i hi C K hC hK
  let P := Classical.choice
    (SmoothManifolds.BundleOperations.exists_pullback (tangentBundle T) S F i.smooth)
  letI := P.space.topology
  obtain ⟨hP, D, W, hform, hD, hgeo⟩ :=
    GaussWeingarten.exists_geometry g h F i hi C K hC hK P
  letI := W.orthogonal.right.topology
  letI := W.sum.space.topology
  obtain ⟨CT, CN, hN, B, A, hCT, hNform, hCN, hGauss, hWeingarten,
    hBsmooth, hAsmooth, hBsymm, hAdj, hAsymm⟩ := hgeo
  let BB : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (F p) :=
    fun p => (B p).compr₂ ((hP.form p).orthogonal (P202.GaussWeingartenData.tangentImage i p)).subtype
  refine ⟨BB, ?_, P, D, hD, ?_⟩
  · intro p v w z
    change pairing h (F p) (B p v w).val (i.differential p z) = 0
    change h.form (F p) _ _ = 0
    rw [← hform p, hP.symmetric p]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp (B p v w).property)
      (i.differential p z) ⟨z, rfl⟩
  · intro X Y
    obtain ⟨V, hV, ht, hn, hg⟩ := hGauss X Y
    exact ⟨V, hV, hg⟩

end Geometry

section VariationVelocity
open Set Filter
open SmoothManifolds.TangentBundleData
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

theorem variation_hasVelocityAt (Q : SmoothVariation S T) (p : M) :
    P202.CurveData.HasVelocityAt T (fun s => Q.map s p) 0 (variationVelocity Q p) := by
  obtain ⟨c, hc, d, hd, hp, hpd, U, f, hU, h0, hf, heq⟩ :=
    Q.joint_smooth 0 Q.zero_mem p
  have hpair : ContinuousAt (fun s : ℝ => (s, p)) 0 :=
    continuousAt_id.prodMk continuousAt_const
  have hcont : ContinuousAt (fun s => Q.map s p) 0 :=
    (Q.continuous.continuousAt ((Q.open_domain.prod isOpen_univ).mem_nhds
      ⟨Q.zero_mem, mem_univ p⟩)).comp hpair
  have hpairc : ContinuousAt (fun s : ℝ => (s, (c p).val)) 0 :=
    continuousAt_id.prodMk continuousAt_const
  have he : (fun s : ℝ => (d (Q.map s p)).val) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => f (s, (c p).val)) := by
    filter_upwards [Q.open_domain.mem_nhds Q.zero_mem,
      hpairc.preimage_mem_nhds (hU.mem_nhds h0)] with s hs hUs
    have he := (heq s hs (c p) hUs (c.map_source hp)).2
    simpa only [c.left_inv hp] using he.symm
  have hfd : ContDiffAt ℝ (⊤ : ℕ∞) (fun s => f (s, (c p).val)) 0 :=
    (hf.contDiffAt (hU.mem_nhds h0)).comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  let L := (tangentStructure T).fiberCoordinates.equiv d hd (Q.map 0 p) hpd
  let v := L.symm (deriv (fun s => f (s, (c p).val)) 0)
  have hv : P202.CurveData.HasVelocityAt T (fun s => Q.map s p) 0 v := by
    refine ⟨hcont, d, hd, hpd, ?_⟩
    change HasDerivAt _ (L (L.symm _)) 0
    rw [L.apply_symm_apply]
    exact (hfd.differentiableAt (by simp)).hasDerivAt.congr_of_eventuallyEq he
  change P202.CurveData.HasVelocityAt T _ 0 (P202.CurveData.velocity T _ 0)
  rw [PiecewiseCurves.velocity_eq hv]
  exact hv

theorem decomposition_compact_support (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
    (hQ : CompactlySupportedVariation Q)
    (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p))
    (hdec : VariationDecomposition Q h W ξ) :
    IsCompact (sectionSupport W.val) := by
  letI := S.topologicalManifold.hausdorff
  obtain ⟨L, hL, heq⟩ := hQ
  have hzero : ∀ p ∉ L, W.val p = 0 := by
    intro p hp
    have hc : (fun s => Q.map s p) =ᶠ[𝓝 (0 : ℝ)] (fun _ => Q.map 0 p) := by
      filter_upwards [heq] with s hs
      exact hs.2 p hp
    have hv : variationVelocity Q p = 0 := by
      have hh := PiecewiseCurves.velocity_congr (hdec.1 p) hc
      exact (eq_of_heq hh).trans (PiecewiseCurves.velocity_const (Q.map 0 p) 0)
    have hh := congrArg
      (fun v => pairing h (Q.map 0 p) v ((initialImmersion Q).differential p (W.val p)))
      (hdec.2.1 p)
    rw [hv] at hh
    simp only [map_zero, map_add, LinearMap.add_apply] at hh
    rw [hdec.2.2 p (W.val p), add_zero] at hh
    have he : pairing (g 0) p (W.val p) (W.val p) = 0 :=
      (hg 0 Q.zero_mem p (W.val p) (W.val p)).trans hh.symm
    by_contra hn
    exact (ne_of_gt ((g 0).positive p (W.val p) hn)) he
  apply hL.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hL.isClosed
  intro p hp
  by_contra hn
  exact hp (hzero p hn)


end VariationVelocity

section MeanCurvatureNormal
open SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
  P202.LeviCivitaData
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

theorem meanCurvature_normal (g : RiemannianMetric S) (h : RiemannianMetric T)
    (F : M → N) (i : SmoothImmersion S T F)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (F p))
    (hB : IsSecondFundamentalForm h F i C K B) (p : M) (z : TangentSpace S p) :
    pairing h (F p) (meanCurvature (E := fun p => TangentSpace T (F p)) g B p)
      (i.differential p z) = 0 := by
  change pairing h (F p) (∑ j : Fin n, B p (fiberBasis S p j)
    ((musical g p).symm ((fiberBasis S p).dualBasis j))) (i.differential p z) = 0
  simp only [map_sum, LinearMap.sum_apply]
  exact Finset.sum_eq_zero fun j _ => hB.1 p _ _ z

theorem normalIntegrand_eq_metricTrace (Q : SmoothVariation S T)
    (h : RiemannianMetric T) (g : RiemannianMetric S)
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p))
    (ξ : (p : M) → TangentSpace T (Q.map 0 p)) (p : M) :
    normalIntegrand Q h g B ξ p =
      metricTrace g p ((B p).compr₂ (pairing h (Q.map 0 p) (ξ p))) := by
  exact trace_pairing (E := TangentSpace T (Q.map 0 p)) g p (B p)
    (pairing h (Q.map 0 p) (ξ p))

theorem normalIntegrand_eq_velocity_pairing (Q : SmoothVariation S T)
    (h : RiemannianMetric T) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p))
    (hB : IsSecondFundamentalForm h (Q.map 0) (initialImmersion Q) C K B)
    (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p))
    (hdec : VariationDecomposition Q h W ξ) (p : M) :
    normalIntegrand Q h g B ξ p =
      pairing h (Q.map 0 p) (variationVelocity Q p)
        (meanCurvature (E := fun p => TangentSpace T (Q.map 0 p)) g B p) := by
  rw [hdec.2.1 p]
  simp only [map_add, LinearMap.add_apply]
  have ht : pairing h (Q.map 0 p) ((initialImmersion Q).differential p (W.val p))
      (meanCurvature (E := fun p => TangentSpace T (Q.map 0 p)) g B p) = 0 :=
    (h.symmetric (Q.map 0 p) _ _).trans
      (meanCurvature_normal g h (Q.map 0) (initialImmersion Q) C K B hB p (W.val p))
  rw [ht, zero_add]
  rfl

theorem shape_trace_pairing (g : RiemannianMetric S) (h : RiemannianMetric T)
    (F : M → N) (p : M)
    (B : TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (F p))
    (A : TangentSpace S p →ₗ[ℝ] TangentSpace S p)
    (ξ : TangentSpace T (F p))
    (hA : ∀ v w, pairing g p (A v) w = pairing h (F p) ξ (B v w)) :
    LinearMap.trace ℝ (TangentSpace S p) A =
      pairing h (F p) ξ (vectorMetricTrace g p B) := by
  rw [trace_pairing (E := TangentSpace T (F p)) g p B (pairing h (F p) ξ)]
  have he : B.compr₂ (pairing h (F p) ξ) = (musical g p).toLinearMap.comp A := by
    ext v w
    exact (hA v w).symm
  rw [metricTrace, he, ← LinearMap.comp_assoc]
  simp

end MeanCurvatureNormal

section NormalSupport
open Set Filter
open SmoothManifolds.TangentBundleData
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

theorem decomposition_zero_iff (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
    (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p))
    (hdec : VariationDecomposition Q h W ξ) (p : M) :
    variationVelocity Q p = 0 ↔ W.val p = 0 ∧ ξ p = 0 := by
  constructor
  · intro hv
    have hh := congrArg
      (fun v => pairing h (Q.map 0 p) v ((initialImmersion Q).differential p (W.val p)))
      (hdec.2.1 p)
    rw [hv] at hh
    simp only [map_zero, map_add, LinearMap.add_apply] at hh
    rw [hdec.2.2 p (W.val p), add_zero] at hh
    have he : pairing (g 0) p (W.val p) (W.val p) = 0 :=
      (hg 0 Q.zero_mem p (W.val p) (W.val p)).trans hh.symm
    have hw : W.val p = 0 := by
      by_contra hn
      exact (ne_of_gt ((g 0).positive p (W.val p) hn)) he
    refine ⟨hw, ?_⟩
    have hd := hdec.2.1 p
    simpa only [hv, hw, map_zero, zero_add] using hd.symm
  · rintro ⟨hw, hξ⟩
    simpa only [hw, hξ, map_zero, add_zero] using hdec.2.1 p

theorem variationVelocity_eq_zero_outside_support (Q : SmoothVariation S T)
    (L : Set M)
    (heq : ∀ᶠ s in nhds (0 : ℝ), s ∈ Q.domain ∧ ∀ p ∉ L, Q.map s p = Q.map 0 p)
    (p : M) (hp : p ∉ L) : variationVelocity Q p = 0 := by
  have hc : (fun s => Q.map s p) =ᶠ[𝓝 (0 : ℝ)] (fun _ => Q.map 0 p) := by
    filter_upwards [heq] with s hs
    exact hs.2 p hp
  have hh := PiecewiseCurves.velocity_congr (variation_hasVelocityAt Q p) hc
  exact (eq_of_heq hh).trans (PiecewiseCurves.velocity_const (Q.map 0 p) 0)

theorem normal_component_compact_support (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
    (hQ : CompactlySupportedVariation Q)
    (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p))
    (hdec : VariationDecomposition Q h W ξ) :
    IsCompact (sectionSupport ξ) := by
  letI := S.topologicalManifold.hausdorff
  obtain ⟨L, hL, heq⟩ := hQ
  have hzero : ∀ p ∉ L, ξ p = 0 := by
    intro p hp
    exact ((decomposition_zero_iff Q h g hg W ξ hdec p).mp
      (variationVelocity_eq_zero_outside_support Q L heq p hp)).2
  apply hL.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hL.isClosed
  intro p hp
  by_contra hn
  exact hp (hzero p hn)

theorem normalIntegrand_compact_support (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
    (hQ : CompactlySupportedVariation Q)
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p))
    (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p))
    (hdec : VariationDecomposition Q h W ξ) :
    HasCompactSupport (normalIntegrand Q h (g 0) B ξ) := by
  apply (normal_component_compact_support Q h g hg hQ W ξ hdec).of_isClosed_subset
    isClosed_closure
  apply closure_mono
  intro p hp
  change ξ p ≠ 0
  intro hz
  apply hp
  simp only [normalIntegrand, hz, map_zero, LinearMap.zero_apply]

end NormalSupport

section DensityCalculus
open Filter
open SmoothManifolds.MapData SmoothManifolds.DifferentialData
  SmoothManifolds.MetricVolumeData SmoothManifolds.DensityIntegrationData
variable {n m : ℕ} {a b : ModelKind} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
 {S : SmoothManifold n a M} {T : SmoothManifold m b N}

theorem isDifferential_congr {f g : M → N} {p : M}
 (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
 (hL : IsDifferential S T f p L) (heq : f =ᶠ[𝓝 p] g) :
 ∃ K : TangentSpace S p →ₗ[ℝ] TangentSpace T (g p), IsDifferential S T g p K ∧ HEq L K := by
 unfold IsDifferential at *
 have hp := heq.eq_of_nhds
 generalize hg : g p = q at *
 cases hp
 refine ⟨L, ?_, HEq.rfl⟩
 intro v h k r hr hk
 apply hL v h k r hr
 exact (Filter.Germ.coe_eq.mpr (heq.fun_comp r)).trans hk


theorem pullback_pairing_congr {f g : M → N} {p : M}
 (hg : IsSmoothMap S T g) (h : RiemannianMetric T)
 (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
 (K : TangentSpace S p →ₗ[ℝ] TangentSpace T (g p))
 (hL : IsDifferential S T f p L) (hK : IsDifferential S T g p K)
 (heq : f =ᶠ[𝓝 p] g) (v w : TangentSpace S p) :
 pairing h (f p) (L v) (L w) = pairing h (g p) (K v) (K w) := by
 obtain ⟨J, hJ, hLJ⟩ := isDifferential_congr L hL heq
 obtain ⟨A, hA, huniq⟩ := SmoothManifolds.differential_exists S T g hg p
 have hLK : HEq L K := hLJ.trans (heq_of_eq ((huniq J hJ).trans (huniq K hK).symm))
 clear hL hK hLJ hJ huniq hA J A hg
 have hp := heq.eq_of_nhds
 generalize hgp : g p = q at *
 cases hp
 have hK : L = K := eq_of_heq hLK
 rw [hK]

theorem density_eq_of_pairing_eq (g₁ g₂ : RiemannianMetric S) (p : M)
 (heq : ∀ v w, pairing g₁ p v w = pairing g₂ p v w) :
 P202.VolumeData.density g₁ p = P202.VolumeData.density g₂ p := by
 apply Subtype.ext
 funext v
 change Real.sqrt ((metricForm (P202.VolumeData.libraryMetric g₁) p).exteriorPower n v v) =
   Real.sqrt ((metricForm (P202.VolumeData.libraryMetric g₂) p).exteriorPower n v v)
 have hform : metricForm (P202.VolumeData.libraryMetric g₁) p =
   metricForm (P202.VolumeData.libraryMetric g₂) p :=
     LinearMap.ext (fun v => LinearMap.ext (heq v))
 rw [hform]


theorem density_difference_compact :
    P202Specs.Geometry.VolumeFirstVariation.density_difference_compactType.{u} := by
 intro n m a b M N _ _ S T Q h g hg hQ
 letI := S.topologicalManifold.hausdorff
 obtain ⟨L, hL, heq⟩ := hQ
 filter_upwards [heq] with s hs
 have hzero : ∀ p ∉ L, P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p = 0 := by
   intro p hp
   apply sub_eq_zero.mpr
   apply density_eq_of_pairing_eq
   intro v w
   rw [hg s hs.1 p v w, hg 0 Q.zero_mem p v w]
   apply pullback_pairing_congr (initialImmersion Q).smooth
     h _ _ ((Q.immersion s hs.1).isDifferential p) ((initialImmersion Q).isDifferential p)
   filter_upwards [hL.isClosed.isOpen_compl.mem_nhds hp] with q hq
   exact hs.2 q hq
 refine ⟨⟨(fun p => P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p), ?_, ?_⟩, rfl⟩
 · intro K c hc
   have h₁ := SmoothManifolds.DensityIntegrationResults.smooth_density_continuous
     (P202.VolumeData.density (g s))
     (SmoothManifolds.MetricVolumeResults.metricDensity_smooth (P202.VolumeData.libraryMetric (g s))) K c hc
   have h₀ := SmoothManifolds.DensityIntegrationResults.smooth_density_continuous
     (P202.VolumeData.density (g 0))
     (SmoothManifolds.MetricVolumeResults.metricDensity_smooth (P202.VolumeData.libraryMetric (g 0))) K c hc
   exact (h₁.sub h₀).congr (fun p => (map_sub (densityCoefficient K c hc p) _ _).symm)
 · apply hL.of_isClosed_subset isClosed_closure
   apply closure_minimal _ hL.isClosed
   intro p hp
   by_contra hn
   exact hp (hzero p hn)


def densityRatio (g : RiemannianMetric S) (ρ : DensityField S) (p : M) : ℝ :=
 let e : DensityLine S p ≃ₗ[ℝ] ℝ := SmoothManifolds.MetricVolumeResults.densityEvaluationEquiv (fiberBasis S p)
 e (ρ p) / e (P202.VolumeData.density g p)

theorem densityRatio_smul (g : RiemannianMetric S) (ρ : DensityField S) (p : M) :
 densityRatio g ρ p • P202.VolumeData.density g p = ρ p := by
 let e : DensityLine S p ≃ₗ[ℝ] ℝ := SmoothManifolds.MetricVolumeResults.densityEvaluationEquiv (fiberBasis S p)
 have he : e (P202.VolumeData.density g p) ≠ 0 := by
   intro hz
   apply SmoothManifolds.MetricVolumeResults.metricDensity_nonzero
      (P202.VolumeData.libraryMetric g) p
   exact e.injective (hz.trans (map_zero e).symm)
 apply e.injective
 rw [map_smul]
 exact div_mul_cancel₀ _ he

theorem densityRatio_coefficient (g : RiemannianMetric S) (ρ : DensityField S)
 (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
 (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
 densityRatio g ρ p.val = densityCoefficient K c hc p (ρ p.val) /
   densityCoefficient K c hc p (P202.VolumeData.density g p.val) := by
 have h₀ : densityCoefficient K c hc p (P202.VolumeData.density g p.val) ≠ 0 := by
   rw [P202.VolumeData.density, SmoothManifolds.MetricVolumeResults.metricDensity_coefficient]
   exact ne_of_gt (Real.sqrt_pos.mpr
     (SmoothManifolds.MetricVolumeResults.metricMatrix_det_pos _ K c hc p))
 apply (eq_div_iff h₀).mpr
 have he := congrArg (densityCoefficient K c hc p) (densityRatio_smul g ρ p.val)
 simpa only [map_smul, smul_eq_mul] using he

theorem densityRatio_continuous (g : RiemannianMetric S) (ρ : DensityField S)
 (hρ : IsContinuousDensity ρ) : Continuous (densityRatio g ρ) := by
 apply continuous_iff_continuousAt.mpr
 intro p
 obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
 let K := (P202.MetricData.tangentStructure S).fiberCoordinates
 have hd := SmoothManifolds.DensityIntegrationResults.smooth_density_continuous
   (P202.VolumeData.density g)
   (SmoothManifolds.MetricVolumeResults.metricDensity_smooth (P202.VolumeData.libraryMetric g))
 have hn : ∀ q : c.source,
     densityCoefficient K c hc q (P202.VolumeData.density g q.val) ≠ 0 := by
   intro q
   rw [P202.VolumeData.density, SmoothManifolds.MetricVolumeResults.metricDensity_coefficient]
   exact ne_of_gt (Real.sqrt_pos.mpr
     (SmoothManifolds.MetricVolumeResults.metricMatrix_det_pos _ K c hc q))
 have hh : Continuous (fun q : c.source => densityRatio g ρ q.val) :=
   ((hρ K c hc).div (hd K c hc) hn).congr
     (fun q => (densityRatio_coefficient g ρ K c hc q).symm)
 exact ((continuousOn_iff_continuous_domRestrict.mpr hh).continuousAt
   (c.open_source.mem_nhds hp))

def scalarRepresentative (g : RiemannianMetric S) (ρ : CompactDensity S) : C_c(M, ℝ) :=
 ⟨⟨densityRatio g ρ.field, densityRatio_continuous g ρ.field ρ.continuous⟩, by
   apply ρ.compact_support.of_isClosed_subset isClosed_closure
   apply closure_mono
   intro p hp
   change densityRatio g ρ.field p ≠ 0 at hp
   change ρ.field p ≠ 0
   intro hz
   exact hp (by simp [densityRatio, hz])⟩

theorem compactMetricDensity_scalarRepresentative (g : RiemannianMetric S) (ρ : CompactDensity S) :
 P202.VolumeData.compactMetricDensity g (scalarRepresentative g ρ) = ρ := by
 apply SmoothManifolds.DensityIntegralResults.compactDensity_ext
 funext p
 exact densityRatio_smul g ρ.field p

theorem densityIntegral_scalarRepresentative (g : RiemannianMetric S) (ρ : CompactDensity S) :
 P202.VolumeData.densityIntegral S ρ = P202.VolumeData.integral g (scalarRepresentative g ρ) := by
 unfold P202.VolumeData.integral
 rw [compactMetricDensity_scalarRepresentative]


theorem densityRatio_sub (g : RiemannianMetric S) (ρ σ : DensityField S) (p : M) :
 densityRatio g (ρ - σ) p = densityRatio g ρ p - densityRatio g σ p := by
 simp only [densityRatio, Pi.sub_apply, map_sub, sub_div]

theorem densityRatio_hasDerivAt (g : RiemannianMetric S) (ρ : ℝ → DensityField S)
 (d : M → ℝ) (t : ℝ)
 (hρ : ∀ (K : SmoothManifolds.TangentBundleData.FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source),
    HasDerivAt (fun s => densityCoefficient K c hc p (ρ s p.val))
      (d p.val * densityCoefficient K c hc p (P202.VolumeData.density g p.val)) t)
 (p : M) : HasDerivAt (fun s => densityRatio g (ρ s) p) (d p) t := by
 obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
 let K := (P202.MetricData.tangentStructure S).fiberCoordinates
 have hn : densityCoefficient K c hc ⟨p,hp⟩ (P202.VolumeData.density g p) ≠ 0 := by
   rw [P202.VolumeData.density, SmoothManifolds.MetricVolumeResults.metricDensity_coefficient]
   exact ne_of_gt (Real.sqrt_pos.mpr
     (SmoothManifolds.MetricVolumeResults.metricMatrix_det_pos _ K c hc ⟨p,hp⟩))
 convert (hρ K c hc ⟨p,hp⟩).div_const
    (densityCoefficient K c hc ⟨p,hp⟩ (P202.VolumeData.density g p)) using 1
 · funext s
   exact densityRatio_coefficient g (ρ s) K c hc ⟨p,hp⟩
 · exact (mul_div_cancel_right₀ (d p) hn).symm

theorem densityRatio_variation_hasDerivAt (Q : SmoothVariation S T) (h : RiemannianMetric T)
 (g : ℝ → RiemannianMetric S) (C : P202.ConnectionData.Connection (P202.ConnectionData.tangentBundle S))
 (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p))
 (W : P202.ConnectionData.Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p))
 (hloc : LocalDensityVariation Q h g C B W ξ) (p : M) :
 HasDerivAt (fun s => densityRatio (g 0) (P202.VolumeData.density (g s) - P202.VolumeData.density (g 0)) p)
    (P202.ScalarData.divergence C W p - normalIntegrand Q h (g 0) B ξ p) 0 := by
 have hh := densityRatio_hasDerivAt (g 0) (fun s => P202.VolumeData.density (g s))
   (fun p => P202.ScalarData.divergence C W p - normalIntegrand Q h (g 0) B ξ p) 0 hloc p
 simpa only [densityRatio_sub, sub_zero, Pi.sub_apply] using
   hh.fun_sub (hasDerivAt_const (0 : ℝ) (densityRatio (g 0) (P202.VolumeData.density (g 0)) p))

theorem localVolumeChange_eq_densityIntegral (g : ℝ → RiemannianMetric S) (s : ℝ)
 (ρ : CompactDensity S)
 (hρ : ρ.field = fun p => P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p) :
 localVolumeChange g s = P202.VolumeData.densityIntegral S ρ := by
 unfold localVolumeChange
 have hh : ∃ σ : CompactDensity S,
    σ.field = fun p => P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p := ⟨ρ,hρ⟩
 rw [dite_eq_left hh]
 congr 1
 exact SmoothManifolds.DensityIntegralResults.compactDensity_ext (hh.choose_spec.trans hρ.symm)

end DensityCalculus

section SmoothVariationSplitting
open SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
  SmoothManifolds.BundleMetricData P202.GaussWeingartenData
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

open Set Filter SmoothManifolds.TangentBundleData SmoothManifolds.FrameData

/-- A joint smooth coordinate extension differentiates to the actual velocity. -/
theorem variationVelocity_in_coordinates
    (Q : SmoothVariation S T) (c : ModelChart n a M)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (U : Set (ℝ × Euclidean n)) (f : ℝ × Euclidean n → Euclidean m)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (heq : ∀ t ∈ Q.domain, ∀ x : ModelSpace n a,
      (t, x.val) ∈ U → x ∈ c.target →
      Q.map t (c.symm x) ∈ d.source ∧
      f (t, x.val) = (d (Q.map t (c.symm x))).val)
    (q : M) (hqc : q ∈ c.source) (hqu : (0, (c q).val) ∈ U) :
    ∃ hqd : Q.map 0 q ∈ d.source,
      (tangentStructure T).fiberCoordinates.equiv d hd (Q.map 0 q) hqd
        (variationVelocity Q q) = fderiv ℝ f (0, (c q).val) (1, 0) := by
  have hqd : Q.map 0 q ∈ d.source := by
    simpa only [c.left_inv hqc] using
      (heq 0 Q.zero_mem (c q) hqu (c.map_source hqc)).1
  refine ⟨hqd, ?_⟩
  have hl : HasDerivAt (fun s : ℝ => (s, (c q).val)) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 _)
  have hdif : DifferentiableAt ℝ f (0, (c q).val) :=
    (hf.contDiffAt (hU.mem_nhds hqu)).differentiableAt (by simp)
  have hdf := hdif.hasFDerivAt.comp_hasDerivAt 0 hl
  have he : (fun s : ℝ => (d (Q.map s q)).val) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => f (s, (c q).val)) := by
    filter_upwards [Q.open_domain.mem_nhds Q.zero_mem,
      hl.continuousAt.preimage_mem_nhds (hU.mem_nhds hqu)] with s hs hUs
    simpa only [c.left_inv hqc] using
      (heq s hs (c q) hUs (c.map_source hqc)).2.symm
  exact (P202.Geometry.PiecewiseCurves.hasVelocityAt_coordinates
    (P202.Geometry.VolumeFirstVariation.variation_hasVelocityAt Q q) d hd hqd).unique
      (hdf.congr_of_eventuallyEq he)

/-- Joint smoothness of the variation makes its velocity smooth as an ambient
pullback tangent vector, including in source boundary charts. -/
theorem variationVelocity_ambient_smooth (Q : SmoothVariation S T) :
    IsSmoothMap S (tangentBundle T).totalManifold
      (fun p => (⟨Q.map 0 p, variationVelocity Q p⟩ :
        Bundle.TotalSpace (Euclidean m) (TangentSpace T))) := by
  intro p
  obtain ⟨c, hc, d, hd, hp, hpd, U, f, hU, h0, hf, heq⟩ :=
    Q.joint_smooth 0 Q.zero_mem p
  let w : M → Euclidean m := fun q => fderiv ℝ f (0, (c q).val) (1, 0)
  let V : Set (Euclidean n) := (fun z => ((0 : ℝ), z)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
  have hdf : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU (by simp)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Euclidean n => fderiv ℝ f (0, z) (1, 0)) V :=
    (hdf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => hz)).clm_apply
      contDiffOn_const
  have hw : SmoothManifolds.MapData.ManifoldContDiffToEuclideanAt
      (⊤ : ℕ∞) S.smoothStructure.val w p := by
    apply SmoothManifolds.TangentBundle.euclidean_smoothAt_of_chart S w p c hc hp
    exact ⟨V, hV, h0, (fun z => fderiv ℝ f (0, z) (1, 0)), hF,
      Filter.EventuallyEq.rfl⟩
  have hcontc : ContinuousAt (fun q : M => (c q).val) p :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  have hcoord : ∀ᶠ q in 𝓝 p, ∃ hq : Q.map 0 q ∈ d.source,
      w q = (tangentStructure T).fiberCoordinates.equiv d hd (Q.map 0 q) hq
        (variationVelocity Q q) := by
    filter_upwards [c.open_source.mem_nhds hp,
      hcontc.preimage_mem_nhds (hV.mem_nhds h0)] with q hqc hqV
    obtain ⟨hqd, hqdv⟩ := variationVelocity_in_coordinates Q c d hd U f hU hf heq q hqc hqV
    exact ⟨hqd, hqdv.symm⟩
  letI := (tangentStructure T).topology
  have hlift := SmoothManifolds.TangentBundle.lift_smoothAt_of_coeff
    T (tangentStructure T) S
    (fun q => (⟨Q.map 0 q, variationVelocity Q q⟩ : TotalSpace T)) p
    d hd hpd w ((initialImmersion Q).smooth p) hw hcoord
  exact SmoothManifolds.manifoldContDiffAt_comp
    (tangentStructure T).manifold.smoothStructure.property.1.1 hlift
    ((tangentRealization T).smooth_from_original _)

/-- The actual velocity is a smooth section of every canonical pullback realization. -/
theorem variationVelocity_smooth (Q : SmoothVariation S T)
    (P : PullbackBundle (tangentBundle T) S (Q.map 0)) :
    letI := P.space.topology
    SmoothManifolds.SectionExtensionData.SmoothSection P.space.bundle (variationVelocity Q) := by
  letI := P.space.topology
  exact SmoothManifolds.BundleOperations.pullback_smooth_lift (tangentBundle T) P S
    id (variationVelocity Q)
    (SmoothManifolds.manifoldContDiff_id (⊤ : ℕ∞) _ S.smoothStructure.property.1)
    (variationVelocity_ambient_smooth Q)

theorem variation_decomposition_of_smooth_velocity
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (P : PullbackBundle (tangentBundle T) S (Q.map 0))
    (hV : letI := P.space.topology
      SmoothManifolds.SectionExtensionData.SmoothSection P.space.bundle (variationVelocity Q)) :
    ∃ (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p)),
      VariationDecomposition Q h W ξ := by
  letI := P.space.topology
  let hP := P202.Geometry.GaussWeingarten.pullbackMetric h (initialImmersion Q).smooth P
  let A := Classical.choice
    (P202.Geometry.GaussWeingarten.adapted_splitting_exists (initialImmersion Q) P hP)
  letI := A.orthogonal.right.topology
  let V : Section P.space.bundle := ⟨variationVelocity Q, hV⟩
  let W : Field S := P202.Geometry.GaussWeingarten.mapSections P.space.bundle
    (tangentBundle S) (P202.Geometry.GaussWeingarten.tangentProjectionMorphism
      (initialImmersion Q) P hP A) V
  let ξ : (p : M) → TangentSpace T (Q.map 0 p) := fun p =>
    ((P202.Geometry.GaussWeingarten.normalProjectionMorphism
      (initialImmersion Q) P hP A).linearMap p (variationVelocity Q p)).val
  refine ⟨W, ξ, P202.Geometry.VolumeFirstVariation.variation_hasVelocityAt Q, ?_, ?_⟩
  · intro p
    exact (P202.Geometry.GaussWeingarten.projection_decomposition
      (initialImmersion Q) P hP A p (variationVelocity Q p)).symm
  · intro p z
    change h.form _ _ _ = 0
    rw [h.symmetric]
    exact P202.Geometry.GaussWeingarten.tangent_normal_orthogonal
      (initialImmersion Q) P hP p z _

theorem variation_decomposition :
    P202Specs.Geometry.VolumeFirstVariation.variation_decompositionType.{u} := by
  intro n m a b M N _ _ S T Q h
  let P := Classical.choice
    (SmoothManifolds.BundleOperations.exists_pullback (tangentBundle T) S
      (Q.map 0) (initialImmersion Q).smooth)
  exact variation_decomposition_of_smooth_velocity Q h P (variationVelocity_smooth Q P)


end SmoothVariationSplitting

section DensityDifferentiation
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem metricTrace_eq_gram_trace (g : RiemannianMetric S) (p : M)
    (B : LinearMap.BilinForm ℝ (TangentSpace S p))
    (hB : ∀ v w, B v w = B w v)
    (e : Module.Basis (Fin n) ℝ (TangentSpace S p)) :
    metricTrace g p B =
      ((Matrix.of (fun i j => pairing g p (e i) (e j)))⁻¹ *
        Matrix.of (fun i j => B (e i) (e j))).trace := by
  let G : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => pairing g p (e i) (e j))
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => B (e i) (e j))
  let F := (musical g p).symm.toLinearMap.comp B
  let A := LinearMap.toMatrix e e F
  have hpos : G.PosDef := by
    exact SmoothManifolds.MetricVolumeResults.bilinear_gram_posDef
      (V := TangentSpace S p) (n := n) (pairing g p) (g.symmetric p) (g.positive p) e
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  have heq : G * A = D := by
    ext i j
    simp only [G, A, D, Matrix.mul_apply, Matrix.of_apply, LinearMap.toMatrix_apply]
    change (∑ k, pairing g p (e i) (e k) * e.repr (F (e j)) k) = B (e i) (e j)
    calc
      _ = pairing g p (e i) (∑ k, e.repr (F (e j)) k • e k) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [map_smul, smul_eq_mul, mul_comm]
      _ = pairing g p (e i) (F (e j)) := by rw [e.sum_repr]
      _ = pairing g p (F (e j)) (e i) := g.symmetric p _ _
      _ = B (e j) (e i) := by
        change musical g p ((musical g p).symm (B (e j))) (e i) = _
        rw [LinearEquiv.apply_symm_apply]
      _ = B (e i) (e j) := hB _ _
  have hA : A = G⁻¹ * D := by
    rw [← heq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]
  rw [metricTrace, LinearMap.trace_eq_matrix_trace ℝ e]
  exact congrArg Matrix.trace hA

open SmoothManifolds.TangentBundleData SmoothManifolds.MetricVolumeData
  P202.VolumeData

theorem densityCoefficient_hasDerivAt (g : ℝ → RiemannianMetric S)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (t : ℝ) (B : LinearMap.BilinForm ℝ (TangentSpace S p.val))
    (hB : ∀ v w, B v w = B w v)
    (hg : ∀ v w, HasDerivAt (fun s => pairing (g s) p.val v w) (B v w) t) :
    HasDerivAt (fun s => densityCoefficient K c hc p (density (g s) p.val))
      ((1 / 2 : ℝ) * metricTrace (g t) p.val B *
        densityCoefficient K c hc p (density (g t) p.val)) t := by
  let e := SmoothManifolds.MetricVolumeResults.coordinateBasis K c hc p
  let G : ℝ → Matrix (Fin n) (Fin n) ℝ := fun s =>
    Matrix.of (fun i j => pairing (g s) p.val (e i) (e j))
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => B (e i) (e j))
  have hd : ∀ i j, HasDerivAt (fun s => G s i j) (D i j) t := fun i j => hg (e i) (e j)
  have hpos : (G t).PosDef := by
    exact SmoothManifolds.MetricVolumeResults.bilinear_gram_posDef
      (V := TangentSpace S p.val) (n := n)
      (pairing (g t) p.val) ((g t).symmetric p.val) ((g t).positive p.val) e
  have hcoef (s : ℝ) : densityCoefficient K c hc p (density (g s) p.val) =
      Real.sqrt (G s).det := by
    exact SmoothManifolds.MetricVolumeResults.metricDensity_coefficient
      (P202.VolumeData.libraryMetric (g s)) K c hc p
  have ht := metricTrace_eq_gram_trace (g t) p.val B hB e
  change metricTrace (g t) p.val B = ((G t)⁻¹ * D).trace at ht
  simp_rw [hcoef]
  convert sqrt_det_derivative G D t hd hpos.det_pos using 1
  rw [ht]
  ring


theorem metricTrace_flip (g : RiemannianMetric S) (p : M)
    (B : LinearMap.BilinForm ℝ (TangentSpace S p)) :
    metricTrace g p B.flip = metricTrace g p B := by
  let e := P202.VolumeVariationData.fiberBasis S p
  have hex (D : LinearMap.BilinForm ℝ (TangentSpace S p)) :
      metricTrace g p D = ∑ i : Fin n, ∑ j : Fin n,
        (e.coord j) ((musical g p).symm (e.coord i)) * D (e i) (e j) := by
    have ht : metricTrace g p D = ∑ i : Fin n, D (e i) ((musical g p).symm (e.coord i)) := by
      simpa only [LinearMap.compr₂_id, LinearMap.id_apply] using
        (trace_pairing_in_basis g p D (LinearMap.id : ℝ →ₗ[ℝ] ℝ) e).symm
    rw [ht]
    change (∑ i : Fin n, D (e i) ((musical g p).symm (e.coord i))) = _
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => arg 2; rw [← e.sum_repr ((musical g p).symm (e.coord i))]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, smul_eq_mul]
    rfl
  rw [hex, hex, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [dual_metric_symmetry]
  rfl


theorem metricTrace_add (g : RiemannianMetric S) (p : M)
    (B D : LinearMap.BilinForm ℝ (TangentSpace S p)) :
    metricTrace g p (B + D) = metricTrace g p B + metricTrace g p D := by
  simp only [metricTrace, LinearMap.comp_add, map_add]

theorem metricTrace_smul (g : RiemannianMetric S) (p : M)
    (t : ℝ) (B : LinearMap.BilinForm ℝ (TangentSpace S p)) :
    metricTrace g p (t • B) = t * metricTrace g p B := by
  simp only [metricTrace, LinearMap.comp_smul, map_smul, smul_eq_mul]

theorem metricTrace_sub (g : RiemannianMetric S) (p : M)
    (B D : LinearMap.BilinForm ℝ (TangentSpace S p)) :
    metricTrace g p (B - D) = metricTrace g p B - metricTrace g p D := by
  have he : B - D = B + (-1 : ℝ) • D := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change B v w - D v w = B v w + (-1 : ℝ) * D v w
    ring
  rw [he, metricTrace_add, metricTrace_smul]
  ring

theorem metricTrace_pairing_endomorphism (g : RiemannianMetric S) (p : M)
    (A : TangentSpace S p →ₗ[ℝ] TangentSpace S p) :
    metricTrace g p ((pairing g p).compl₁₂ A LinearMap.id) =
      LinearMap.trace ℝ (TangentSpace S p) A := by
  unfold metricTrace
  congr 1
  apply LinearMap.ext
  intro v
  change (musical g p).symm (musical g p (A v)) = A v
  exact LinearEquiv.symm_apply_apply _ _

theorem metricTrace_symmetric_variation (g : RiemannianMetric S) (p : M)
    (A : TangentSpace S p →ₗ[ℝ] TangentSpace S p)
    (B : LinearMap.BilinForm ℝ (TangentSpace S p)) :
    let D : LinearMap.BilinForm ℝ (TangentSpace S p) := (pairing g p).compl₁₂ A LinearMap.id
    metricTrace g p (D + D.flip - B - B.flip) =
      2 * (LinearMap.trace ℝ (TangentSpace S p) A - metricTrace g p B) := by
  dsimp only
  rw [metricTrace_sub, metricTrace_sub, metricTrace_add]
  have ht := metricTrace_flip g p ((pairing g p).compl₁₂ A LinearMap.id)
  rw [ht, metricTrace_flip, metricTrace_pairing_endomorphism]
  ring

section LocalMetricDensity
open SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
  P202.ConnectionData
variable {m : ℕ} {b : ModelKind} {N : Type u}
  [TopologicalSpace N] {T : SmoothManifold m b N}

/-- The determinant and trace contraction step of the first variation.
The input is a derivative of the actual metric pairings, obtained below
from joint smoothness of the variation map. -/
theorem local_density_of_pairing_derivative
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (C : Connection (tangentBundle S))
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p))
    (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p))
    (hdot : ∀ p v w,
      HasDerivAt (fun s => pairing (g s) p v w)
        (pairing (g 0) p (pointDerivative C W.val p v) w +
         pairing (g 0) p v (pointDerivative C W.val p w) -
         pairing h (Q.map 0 p) (ξ p) (B p v w) -
         pairing h (Q.map 0 p) (ξ p) (B p w v)) 0) :
    LocalDensityVariation Q h g C B W ξ := by
  intro K c hc p
  let A : LinearMap.BilinForm ℝ (TangentSpace S p.val) :=
    (pairing (g 0) p.val).compl₁₂ (pointDerivative C W.val p.val) LinearMap.id
  let N : LinearMap.BilinForm ℝ (TangentSpace S p.val) :=
    (B p.val).compr₂ (pairing h (Q.map 0 p.val) (ξ p.val))
  let D : LinearMap.BilinForm ℝ (TangentSpace S p.val) := A + A.flip - N - N.flip
  have hsym : ∀ v w, D v w = D w v := by
    intro v w
    change A v w + A w v - N v w - N w v =
      A w v + A v w - N w v - N v w
    ring
  have hD : ∀ v w, HasDerivAt (fun s => pairing (g s) p.val v w) (D v w) 0 := by
    intro v w
    convert hdot p.val v w using 1
    change pairing (g 0) p.val (pointDerivative C W.val p.val v) w +
      pairing (g 0) p.val (pointDerivative C W.val p.val w) v - _ - _ = _
    have hs : pairing (g 0) p.val (pointDerivative C W.val p.val w) v =
        pairing (g 0) p.val v (pointDerivative C W.val p.val w) :=
      (g 0).symmetric p.val _ _
    rw [hs]
    rfl
  have hN : metricTrace (g 0) p.val N = normalIntegrand Q h (g 0) B ξ p.val := by
    exact (trace_pairing (E := TangentSpace T (Q.map 0 p.val))
      (g 0) p.val (B p.val) (pairing h (Q.map 0 p.val) (ξ p.val))).symm
  have htrace : metricTrace (g 0) p.val D =
      2 * (divergence C W p.val - normalIntegrand Q h (g 0) B ξ p.val) := by
    have ht := metricTrace_symmetric_variation (g 0) p.val
      (pointDerivative C W.val p.val) N
    change metricTrace (g 0) p.val D =
      2 * (divergence C W p.val - metricTrace (g 0) p.val N) at ht
    rw [hN] at ht
    exact ht
  convert densityCoefficient_hasDerivAt g K c hc p 0 D hsym hD using 1
  rw [htrace]
  ring

end LocalMetricDensity


end DensityDifferentiation

section IntegralParameters
open Set MeasureTheory Filter
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
 (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem hasDerivAt_integral_common_compact_support
 (F F' : ℝ → X → ℝ) (L : Set X) (hL : IsCompact L) (ε : ℝ) (hε : 0 < ε)
 (hF : ∀ s ∈ Ioo (-ε) ε, Continuous (F s))
 (hF' : ContinuousOn (Function.uncurry F') (Icc (-ε) ε ×ˢ L))
 (hF'₀ : AEStronglyMeasurable (F' 0) μ)
 (hder : ∀ p s, s ∈ Ioo (-ε) ε → HasDerivAt (fun t => F t p) (F' s p) s)
 (hsupp : ∀ s ∈ Ioo (-ε) ε, ∀ p ∉ L, F s p = 0) :
 HasDerivAt (fun s => ∫ p, F s p ∂μ) (∫ p, F' 0 p ∂μ) 0 := by
 have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
 obtain ⟨C, hC⟩ := (isCompact_Icc.prod hL).exists_bound_of_continuousOn hF'
 let B : X → ℝ := L.indicator (fun _ => max C 0)
 have hB : Integrable B μ :=
   (integrable_indicator_iff hL.measurableSet).mpr (integrableOn_const hL.measure_lt_top.ne)
 have hz : ∀ p ∉ L, ∀ s ∈ Ioo (-ε) ε, F' s p = 0 := by
   intro p hp s hs
   have heq : (fun t => F t p) =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
     filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
     exact hsupp t ht p hp
   exact ((hder p s hs).congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const s 0)
 apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
   (s := Ioo (-ε) ε) (bound := B) (isOpen_Ioo.mem_nhds h0) ?_ ?_ hF'₀ ?_ hB ?_).2
 · filter_upwards [isOpen_Ioo.mem_nhds h0] with s hs
   exact (hF s hs).aestronglyMeasurable
 · exact (hF 0 h0).integrable_of_hasCompactSupport (HasCompactSupport.intro hL (hsupp 0 h0))
 · apply ae_of_all
   intro p s hs
   by_cases hp : p ∈ L
   · exact (hC (s,p) ⟨⟨le_of_lt hs.1, le_of_lt hs.2⟩, hp⟩).trans
       (by simp [B, hp])
   · simp [hz p hp s hs, B, hp]
 · exact ae_of_all _ hder


end IntegralParameters

section DensityIntegralParameters
open Set MeasureTheory Filter
open SmoothManifolds.MetricVolumeData SmoothManifolds.DensityIntegrationData
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- Differentiation of compact densities reduces to a fixed Riemannian measure.
Only finiteness of that measure on the common compact support is used. -/
theorem densityIntegral_hasDerivAt_of_common_compact_support
    (g : RiemannianMetric S) (ρ : ℝ → CompactDensity S)
    (ψ : C_c(M, ℝ)) (F' : ℝ → M → ℝ)
    (L : Set M) (hL : IsCompact L) (ε : ℝ) (hε : 0 < ε)
    (hF' : ContinuousOn (Function.uncurry F') (Icc (-ε) ε ×ˢ L))
    (hF'₀ : ∀ p, F' 0 p = ψ p)
    (hder : ∀ p s, s ∈ Ioo (-ε) ε →
      HasDerivAt (fun t => densityRatio g (ρ t).field p) (F' s p) s)
    (hsupp : ∀ s ∈ Ioo (-ε) ε, ∀ p ∉ L, (ρ s).field p = 0) :
    HasDerivAt (fun s => P202.VolumeData.densityIntegral S (ρ s))
      (P202.VolumeData.integral g ψ) 0 := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  letI : T2Space M := S.topologicalManifold.hausdorff
  obtain ⟨μ, hμ, _⟩ := RiemannianVolume.measure_representation_exists g
  letI : IsFiniteMeasureOnCompacts μ := ⟨hμ.2.1⟩
  have he₀ : F' 0 = fun p => ψ p := funext hF'₀
  have hmeas : AEStronglyMeasurable (F' 0) μ := by
    rw [he₀]
    exact ψ.continuous.aestronglyMeasurable
  have hd := hasDerivAt_integral_common_compact_support μ
    (fun s p => densityRatio g (ρ s).field p) F' L hL ε hε
    (fun s _ => densityRatio_continuous g (ρ s).field (ρ s).continuous)
    hF' hmeas hder (fun s hs p hp => by
      simp only [densityRatio, hsupp s hs p hp, map_zero, zero_div])
  have hval (s : ℝ) : (∫ p, densityRatio g (ρ s).field p ∂μ) =
      P202.VolumeData.densityIntegral S (ρ s) :=
    (hμ.2.2 (scalarRepresentative g (ρ s))).trans
      (densityIntegral_scalarRepresentative g (ρ s)).symm
  have hval₀ : (∫ p, F' 0 p ∂μ) = P202.VolumeData.integral g ψ := by
    rw [he₀]
    exact hμ.2.2 ψ
  simpa only [hval, hval₀] using hd

end DensityIntegralParameters

section IntegralAssembly
open SmoothManifolds.MetricVolumeData SmoothManifolds.DensityIntegrationData
  SmoothManifolds.BoundaryData P202.GreenData P202.LeviCivitaData
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

theorem compact_density_difference [CompactSpace M]
    (g h : RiemannianMetric S) :
    ∃ ρ : CompactDensity S,
      ρ.field = fun p => P202.VolumeData.density g p - P202.VolumeData.density h p := by
  refine ⟨⟨(fun p => P202.VolumeData.density g p - P202.VolumeData.density h p), ?_, ?_⟩, rfl⟩
  · intro K c hc
    have h₁ := SmoothManifolds.DensityIntegrationResults.smooth_density_continuous
      (P202.VolumeData.density g)
      (SmoothManifolds.MetricVolumeResults.metricDensity_smooth (P202.VolumeData.libraryMetric g)) K c hc
    have h₀ := SmoothManifolds.DensityIntegrationResults.smooth_density_continuous
      (P202.VolumeData.density h)
      (SmoothManifolds.MetricVolumeResults.metricDensity_smooth (P202.VolumeData.libraryMetric h)) K c hc
    exact (h₁.sub h₀).congr (fun p => (map_sub (densityCoefficient K c hc p) _ _).symm)
  · exact isClosed_closure.isCompact

theorem localVolumeChange_eq_compactVolume_sub [CompactSpace M]
    (g : ℝ → RiemannianMetric S) (s : ℝ) :
    localVolumeChange g s = compactVolume (g s) - compactVolume (g 0) := by
  obtain ⟨ρ, hρ⟩ := compact_density_difference (g s) (g 0)
  rw [localVolumeChange_eq_densityIntegral g s ρ hρ]
  let one : C_c(M, ℝ) :=
    ⟨⟨fun _ => 1, continuous_const⟩, HasCompactSupport.of_compactSpace _⟩
  let ρs := P202.VolumeData.compactMetricDensity (g s) one
  let ρ₀ := P202.VolumeData.compactMetricDensity (g 0) one
  have hsum : ρs.field = ρ.field + ρ₀.field := by
    rw [hρ]
    funext p
    change (1 : ℝ) • P202.VolumeData.density (g s) p =
      (P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p) +
        (1 : ℝ) • P202.VolumeData.density (g 0) p
    simp only [one_smul, sub_add_cancel]
  have he := (RiemannianVolume.densityIntegral_properties S).1.1 ρ ρ₀ ρs hsum
  change P202.VolumeData.densityIntegral S ρ =
    P202.VolumeData.densityIntegral S ρs - P202.VolumeData.densityIntegral S ρ₀
  linarith

theorem compact_first_variation_of_supported :
    P202Specs.Geometry.VolumeFirstVariation.supported_first_variationType.{u} →
      P202Specs.Geometry.VolumeFirstVariation.compact_first_variationType.{u} := by
  intro hsupp n m a b M N _ _ _ S T Q h g hg C K hC hK B hB W ξ hdec bnd
  have hQ : CompactlySupportedVariation Q := by
    refine ⟨Set.univ, isCompact_univ, ?_⟩
    filter_upwards [Q.open_domain.mem_nhds Q.zero_mem] with s hs
    exact ⟨hs, fun p hp => False.elim (hp (Set.mem_univ p))⟩
  obtain ⟨f, q, hf, hq, hd⟩ := hsupp Q h g hg hQ C K hC hK B hB W ξ hdec bnd
  refine ⟨f, q, hf, hq, ?_⟩
  have he : (fun s => compactVolume (g s)) =
      (fun s => localVolumeChange g s + compactVolume (g 0)) := by
    funext s
    rw [localVolumeChange_eq_compactVolume_sub]
    ring
  rw [he]
  exact hd.add_const _

theorem first_variation_from_integrated_density
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (bnd : BoundaryGeometry g)
    (W : Field S) (hW : IsCompact (sectionSupport W.val))
    (ψ : M → ℝ) (r : C_c(M, ℝ))
    (hr : ∀ p, r p = divergence C W p - ψ p)
    (A : ℝ → ℝ) (hd : HasDerivAt A (P202.VolumeData.integral g r) 0) :
    ∃ (f : C_c(M, ℝ)) (q : C_c(intrinsicBoundary S, ℝ)),
      (∀ p, f p = ψ p) ∧ (∀ p, q p = flux g bnd W p) ∧
      HasDerivAt A (-P202.VolumeData.integral g f +
        P202.VolumeData.integral bnd.metric q) 0 := by
  obtain ⟨d, q, hdrep, hq, he⟩ := DivergenceGreen.divergence_theorem g C hC bnd W hW
  refine ⟨d - r, q, ?_, hq, ?_⟩
  · intro p
    change d p - r p = ψ p
    rw [hdrep, hr]
    ring
  · convert hd using 1
    rw [DivergenceGreen.metric_integral_sub, he]
    ring

section LocalVolumeParameters
open Set Filter
open SmoothManifolds.MetricVolumeData SmoothManifolds.DensityIntegrationData
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- A total compact-density representative; the variation theorem uses its
actual density-difference branch throughout a neighborhood of zero. -/
def localDensityDifference (g : ℝ → RiemannianMetric S) (s : ℝ) : CompactDensity S :=
  if h : ∃ ρ : CompactDensity S,
      ρ.field = fun p => P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p
  then h.choose else SmoothManifolds.DensityIntegralResults.compactZero S

theorem localDensityDifference_field (g : ℝ → RiemannianMetric S) (s : ℝ)
    (h : ∃ ρ : CompactDensity S,
      ρ.field = fun p => P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p) :
    (localDensityDifference g s).field =
      fun p => P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p := by
  unfold localDensityDifference
  rw [dite_eq_left h]
  exact h.choose_spec

theorem localVolumeChange_eq_localDensityDifference (g : ℝ → RiemannianMetric S) (s : ℝ) :
    localVolumeChange g s = P202.VolumeData.densityIntegral S (localDensityDifference g s) := by
  unfold localVolumeChange localDensityDifference
  split
  · rfl
  · exact (SmoothManifolds.DensityIntegralResults.integral_zero
      (RiemannianVolume.densityIntegral_properties S).1
      (SmoothManifolds.DensityIntegralResults.compactZero S) rfl).symm

/-- The analytic reduction for a local change of volume; no total volume or
measure of the whole manifold is assumed finite. -/
theorem localVolumeChange_hasDerivAt_of_parameter_data
    (g : ℝ → RiemannianMetric S) (ψ : C_c(M, ℝ)) (F' : ℝ → M → ℝ)
    (L : Set M) (hL : IsCompact L) (ε : ℝ) (hε : 0 < ε)
    (hcompact : ∀ s ∈ Ioo (-ε) ε, ∃ ρ : CompactDensity S,
      ρ.field = fun p => P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p)
    (hsupp : ∀ s ∈ Ioo (-ε) ε, ∀ p ∉ L,
      P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p = 0)
    (hF' : ContinuousOn (Function.uncurry F') (Icc (-ε) ε ×ˢ L))
    (hF'₀ : ∀ p, F' 0 p = ψ p)
    (hder : ∀ p s, s ∈ Ioo (-ε) ε →
      HasDerivAt (fun t => densityRatio (g 0)
        (fun q => P202.VolumeData.density (g t) q - P202.VolumeData.density (g 0) q) p)
        (F' s p) s) :
    HasDerivAt (localVolumeChange g) (P202.VolumeData.integral (g 0) ψ) 0 := by
  have hd := densityIntegral_hasDerivAt_of_common_compact_support (g 0)
    (localDensityDifference g) ψ F' L hL ε hε hF' hF'₀ ?_ ?_
  · simpa only [← localVolumeChange_eq_localDensityDifference] using hd
  · intro p s hs
    apply (hder p s hs).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    rw [localDensityDifference_field g t (hcompact t ht)]
  · intro s hs p hp
    rw [localDensityDifference_field g s (hcompact s hs)]
    exact hsupp s hs p hp

end LocalVolumeParameters


end IntegralAssembly

-- Insert inside namespace P202.Geometry.VolumeFirstVariation.
-- Requires imports P202.Geometry.ScalarCalculus and Mathlib.LinearAlgebra.Matrix.SesquilinearForm.
section GeometricRegularity
open SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
  SmoothManifolds.SectionExtensionData SmoothManifolds.FrameData
  P202.LeviCivitaData
open P202.Geometry
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

theorem metricTrace_eq_gram_trace_transpose (g : RiemannianMetric S) (p : M)
    (B : LinearMap.BilinForm ℝ (TangentSpace S p))
    (e : Module.Basis (Fin n) ℝ (TangentSpace S p)) :
    metricTrace g p B =
      ((Matrix.of (fun i j => pairing g p (e i) (e j)))⁻¹ *
        Matrix.of (fun i j => B (e j) (e i))).trace := by
  let G : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => pairing g p (e i) (e j))
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => B (e j) (e i))
  let F := (musical g p).symm.toLinearMap.comp B
  let A := LinearMap.toMatrix e e F
  have hpos : G.PosDef := by
    exact SmoothManifolds.MetricVolumeResults.bilinear_gram_posDef
      (V := TangentSpace S p) (n := n) (pairing g p) (g.symmetric p) (g.positive p) e
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  have heq : G * A = D := by
    ext i j
    simp only [G, A, D, Matrix.mul_apply, Matrix.of_apply, LinearMap.toMatrix_apply]
    change (∑ k, pairing g p (e i) (e k) * e.repr (F (e j)) k) = B (e j) (e i)
    calc
      _ = pairing g p (e i) (∑ k, e.repr (F (e j)) k • e k) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [map_smul, smul_eq_mul, mul_comm]
      _ = pairing g p (e i) (F (e j)) := by rw [e.sum_repr]
      _ = pairing g p (F (e j)) (e i) := g.symmetric p _ _
      _ = B (e j) (e i) := by
        change musical g p ((musical g p).symm (B (e j))) (e i) = _
        rw [LinearEquiv.apply_symm_apply]
  have hA : A = G⁻¹ * D := by
    rw [← heq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul]
  rw [metricTrace, LinearMap.trace_eq_matrix_trace ℝ e]
  exact congrArg Matrix.trace hA

/-- Contraction with a smooth metric preserves smoothness of a covariant
bilinear tensor, expressed by testing on ordinary smooth vector fields. -/
theorem metricTrace_smooth
    (g : RiemannianMetric S)
    (A : (p : M) → LinearMap.BilinForm ℝ (TangentSpace S p))
    (hA : ∀ (X Y : Field S), VectorSmooth S.smoothStructure.val
      (fun p => A p (X.val p) (Y.val p))) :
    VectorSmooth S.smoothStructure.val (fun p => metricTrace g p (A p)) := by
  intro p
  obtain ⟨c, hp⟩ := (tangentBundle S).covers p
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  have hU : IsOpen ((tangentBundle S).baseSet c) :=
    (tangentBundle S).trivialization_baseSet c ▸
      ((tangentBundle S).trivialization c).open_baseSet
  obtain ⟨X, hX⟩ := ConnectionForms.local_frame_representative (tangentBundle S) b ⟨p, hp⟩
  have hs : VectorSmoothAt S.smoothStructure.val
      (fun q => ∑ i : Fin n, ∑ j : Fin n,
        (metricMatrix g c q)⁻¹ i j * A q ((X i).val q) ((X j).val q)) p := by
    apply VectorSmoothAt.sum
    intro i
    apply VectorSmoothAt.sum
    intro j
    exact ((ScalarCalculus.inverse_metric_smooth g c ⟨p, hp⟩ i j).prod
      (hA (X i) (X j) p)).postcomp (contDiff_fst.mul contDiff_snd)
  apply hs.congr
  filter_upwards [hU.mem_nhds hp, Filter.eventually_all.mpr hX] with q hq hXq
  have he (j : Fin n) : (X j).val q = coordinateVector c j q := by
    rw [hXq j, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    exact ScalarCalculus.coordinate_frame_vector c ⟨q, hq⟩ j
  rw [metricTrace_eq_gram_trace_transpose g q (A q) (b.basis ⟨q, hq⟩)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  have hb (j : Fin n) : b.basis ⟨q, hq⟩ j = coordinateVector c j q :=
    ScalarCalculus.coordinate_frame_vector c ⟨q, hq⟩ j
  have hg : Matrix.of (fun i j => pairing g q (b.basis ⟨q, hq⟩ i) (b.basis ⟨q, hq⟩ j)) =
      metricMatrix g c q := by
    ext i j
    change pairing g q (b.basis ⟨q, hq⟩ i) (b.basis ⟨q, hq⟩ j) =
      pairing g q (coordinateVector c i q) (coordinateVector c j q)
    rw [hb i, hb j]
  rw [hg]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [he i, he j, hb i, hb j]


theorem secondForm_fields_ambient_smooth
    (h : RiemannianMetric T) (F : M → N) (i : SmoothImmersion S T F)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (F p))
    (hB : IsSecondFundamentalForm h F i C K B) (X Y : Field S) :
    IsSmoothMap S (tangentBundle T).totalManifold
      (fun p => (⟨F p, B p (X.val p) (Y.val p)⟩ :
        Bundle.TotalSpace (Euclidean m) (TangentSpace T))) := by
  obtain ⟨hBN, P, D, hDP, hGauss⟩ := hB
  letI := P.space.topology
  obtain ⟨V, hV, he⟩ := hGauss X Y
  let J := GaussWeingarten.mapSections (tangentBundle S) P.space.bundle
    (GaussWeingarten.differentialMorphism i P) (C.cov X Y)
  let Z : Section P.space.bundle := D.cov X V + (-1 : ℝ) • J
  have hZ : ∀ p, Z.val p = B p (X.val p) (Y.val p) := by
    intro p
    apply Subtype.ext
    apply LinearMap.ext
    intro r
    have hh := congrArg (fun v => v.val r) (he p)
    change ((D.cov X V).val p).val r =
      (i.differential p ((C.cov X Y).val p)).val r +
      (B p (X.val p) (Y.val p)).val r at hh
    change ((D.cov X V).val p).val r +
      (-1 : ℝ) * (i.differential p ((C.cov X Y).val p)).val r = _
    linarith
  have hZsmooth : SmoothSection P.space.bundle
      (fun p => B p (X.val p) (Y.val p)) := by
    have heq : Z.val = fun p => B p (X.val p) (Y.val p) := funext hZ
    rw [← heq]
    exact Z.property
  intro p
  exact SmoothManifolds.manifoldContDiffAt_comp
    P.space.bundle.totalManifold.smoothStructure.property.1.1 (hZsmooth p)
    (P.canonical_smooth _)

/-- The normal scalar in the variation formula is smooth for every supplied
second fundamental form and every orthogonal velocity decomposition. -/
theorem normalIntegrand_smooth
    (Q : SmoothVariation S T) (h : RiemannianMetric T) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p))
    (hB : IsSecondFundamentalForm h (Q.map 0) (initialImmersion Q) C K B)
    (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p))
    (hdec : VariationDecomposition Q h W ξ) :
    VectorSmooth S.smoothStructure.val (normalIntegrand Q h g B ξ) := by
  let A : (p : M) → LinearMap.BilinForm ℝ (TangentSpace S p) := fun p =>
    (B p).compr₂ (pairing h (Q.map 0 p) (variationVelocity Q p))
  have hA : ∀ (X Y : Field S), VectorSmooth S.smoothStructure.val
      (fun p => A p (X.val p) (Y.val p)) := by
    intro X Y p
    exact SmoothMetrics.metric_pairing_smoothAt S (tangentBundle T) h (Q.map 0)
      (variationVelocity Q) (fun p => B p (X.val p) (Y.val p)) p
      ((initialImmersion Q).smooth p) (variationVelocity_ambient_smooth Q p)
      (secondForm_fields_ambient_smooth h (Q.map 0) (initialImmersion Q) C K B hB X Y p)
  intro p
  apply (metricTrace_smooth g A hA p).congr
  apply Filter.Eventually.of_forall
  intro q
  rw [normalIntegrand_eq_velocity_pairing Q h g C K B hB W ξ hdec]
  unfold meanCurvature P202.VolumeVariationData.meanCurvature vectorMetricTrace
  simp only [Module.Basis.coe_dualBasis]
  rw [map_sum, metricTrace, LinearMap.trace_eq_matrix_trace ℝ (fiberBasis S q)]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.diag, LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change (fiberBasis S q).repr ((musical g q).symm (A q (fiberBasis S q j))) j = _
  exact VolumeFirstVariation.dual_metric_symmetry g q ((fiberBasis S q).coord j)
    (A q (fiberBasis S q j))
/-- Gauss and metric compatibility determine the tangential contraction of
an arbitrary variation velocity, without requiring the variation to be normal. -/
theorem variation_covariant_pairing
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hK : IsLeviCivita h K)
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p))
    (hB : IsSecondFundamentalForm h (Q.map 0) (initialImmersion Q) C K B)
    (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p))
    (hdec : VariationDecomposition Q h W ξ) :
    ∃ P : PullbackBundle (tangentBundle T) S (Q.map 0),
      letI := P.space.topology
      ∃ (D : Connection P.space.bundle) (V : Section P.space.bundle),
        P202.PullbackData.IsPullback (tangentBundle T) K (Q.map 0)
          (initialImmersion Q).smooth P D ∧
        (∀ p, V.val p = variationVelocity Q p) ∧
        ∀ (X Y : Field S) (p : M),
          pairing h (Q.map 0 p) ((D.cov X V).val p)
            ((initialImmersion Q).differential p (Y.val p)) =
          pairing (g 0) p ((C.cov X W).val p) (Y.val p) -
            pairing h (Q.map 0 p) (ξ p) (B p (X.val p) (Y.val p)) := by
  obtain ⟨hBN, P, D, hDP, hGauss⟩ := hB
  letI := P.space.topology
  let V : Section P.space.bundle := ⟨variationVelocity Q, variationVelocity_smooth Q P⟩
  let hP := GaussWeingarten.pullbackMetric h (initialImmersion Q).smooth P
  have hD : P202.TorsionMetricData.MetricCompatible P.space.bundle D hP :=
    TorsionAndMetric.metric_map_product (tangentBundle T) h K hK.2 (Q.map 0)
      (initialImmersion Q).smooth P D hDP
  refine ⟨P, D, V, hDP, fun _ => rfl, ?_⟩
  intro X Y p
  obtain ⟨J, hJ, hDJ⟩ := hGauss X W
  obtain ⟨L, hL, hDL⟩ := hGauss X Y
  let U : Section P.space.bundle := V + (-1 : ℝ) • J
  have hU : ∀ q, U.val q = ξ q := by
    intro q
    apply Subtype.ext
    apply LinearMap.ext
    intro r
    have he := congrArg (fun v => v.val r) (hdec.2.1 q)
    change (variationVelocity Q q).val r =
      ((initialImmersion Q).differential q (W.val q)).val r + (ξ q).val r at he
    change (variationVelocity Q q).val r + (-1 : ℝ) * (J.val q).val r = (ξ q).val r
    rw [hJ q]
    linarith
  have hfun : (fun q => hP.form q (U.val q) (L.val q)) = (fun _ : M => (0 : ℝ)) := by
    funext q
    change pairing h (Q.map 0 q) (U.val q) (L.val q) = 0
    rw [hU, hL]
    exact hdec.2.2 q (Y.val q)
  have hz : scalarDerivative S (fun _ : M => (0 : ℝ)) p (X.val p) = 0 := by
    have he : (fun _ : M => (0 : ℝ)) = (0 : GlobalSmooth S).val := rfl
    rw [he, ConnectionForms.scalarDerivative_global]
    exact congrArg (fun f : GlobalSmooth S => f.val p) (act S X).map_zero
  have hh := hD X U L p
  rw [hfun, hz] at hh
  change 0 = pairing h (Q.map 0 p) ((D.cov X U).val p) (L.val p) +
    pairing h (Q.map 0 p) (U.val p) ((D.cov X L).val p) at hh
  rw [hL, hU, hDL] at hh
  rw [(pairing h (Q.map 0 p) (ξ p)).map_add
    ((initialImmersion Q).differential p ((C.cov X Y).val p))
    (B p (X.val p) (Y.val p)), hdec.2.2 p, zero_add] at hh
  have htan : pairing h (Q.map 0 p) ((D.cov X J).val p)
      ((initialImmersion Q).differential p (Y.val p)) =
      pairing (g 0) p ((C.cov X W).val p) (Y.val p) := by
    rw [hDJ, map_add, LinearMap.add_apply, hBN, add_zero]
    exact (hg 0 Q.zero_mem p _ _).symm
  have hDU : D.cov X U = D.cov X V + (-1 : ℝ) • D.cov X J := by
    exact (D.cov X).map_add V ((-1 : ℝ) • J) |>.trans
      (congrArg (fun t => D.cov X V + t) ((D.cov X).map_smul (-1 : ℝ) J))
  rw [hDU] at hh
  simp only [ConnectionForms.section_add_apply, ConnectionForms.section_smul_apply,
    map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hh
  rw [htan] at hh
  linarith

theorem variation_pointDerivative_pairing
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hK : IsLeviCivita h K)
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p))
    (hB : IsSecondFundamentalForm h (Q.map 0) (initialImmersion Q) C K B)
    (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p))
    (hdec : VariationDecomposition Q h W ξ) :
    ∃ P : PullbackBundle (tangentBundle T) S (Q.map 0),
      letI := P.space.topology
      ∃ (D : Connection P.space.bundle) (V : Section P.space.bundle),
        P202.PullbackData.IsPullback (tangentBundle T) K (Q.map 0)
          (initialImmersion Q).smooth P D ∧
        (∀ p, V.val p = variationVelocity Q p) ∧
        ∀ (p : M) (v w : TangentSpace S p),
          pairing h (Q.map 0 p) (pointDerivative D V.val p v)
            ((initialImmersion Q).differential p w) =
          pairing (g 0) p (pointDerivative C W.val p v) w -
            pairing h (Q.map 0 p) (ξ p) (B p v w) := by
  obtain ⟨P, D, V, hDP, hV, hpair⟩ :=
    variation_covariant_pairing Q h g hg C K hK B hB W ξ hdec
  letI := P.space.topology
  refine ⟨P, D, V, hDP, hV, ?_⟩
  intro p v w
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p v
  obtain ⟨Y, hY⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p w
  rw [← hX, ← hY, ConnectionForms.pointDerivative_global P.space.bundle D V p X,
    ConnectionForms.pointDerivative_global (tangentBundle S) C W p X]
  exact hpair X Y p

end GeometricRegularity

section JointDensityRegularity
set_option maxHeartbeats 2500000
open SmoothManifolds.MapData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.DifferentialData
open Set Filter
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

theorem variation_differential_in_coordinates
    (Q : SmoothVariation S T) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (U : Set (ℝ × Euclidean n)) (f : ℝ × Euclidean n → Euclidean m)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (heq : ∀ t ∈ Q.domain, ∀ x : ModelSpace n a,
      (t, x.val) ∈ U → x ∈ c.target →
      Q.map t (c.symm x) ∈ d.source ∧
      f (t, x.val) = (d (Q.map t (c.symm x))).val)
    (s : ℝ) (hs : s ∈ Q.domain)
    (q : M) (hqc : q ∈ c.source) (hqu : (s, (c q).val) ∈ U) :
    ∃ hqd : Q.map s q ∈ d.source,
      ∀ v : TangentSpace S q,
      (tangentStructure T).fiberCoordinates.equiv d hd (Q.map s q) hqd
        ((Q.immersion s hs).differential q v) =
          fderiv ℝ f (s, (c q).val)
            (0, (tangentStructure S).fiberCoordinates.equiv c hc q hqc v) := by
  have hqd : Q.map s q ∈ d.source := by
    simpa only [c.left_inv hqc] using
      (heq s hs (c q) hqu (c.map_source hqc)).1
  refine ⟨hqd, ?_⟩
  let V : Set (Euclidean n) := (fun z => (s, z)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => f (s, z)) V :=
    hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => hz)
  have he : (fun y => f (s, (c y).val)) =ᶠ[𝓝 q]
      (fun y => (d (Q.map s y)).val) := by
    have hcontc : ContinuousAt (fun y : M => (c y).val) q :=
      continuous_subtype_val.continuousAt.comp (c.continuousAt hqc)
    filter_upwards [c.open_source.mem_nhds hqc,
      hcontc.preimage_mem_nhds (hV.mem_nhds hqu)] with y hyc hyV
    simpa only [c.left_inv hyc] using
      (heq s hs (c y) hyV (c.map_source hyc)).2
  intro v
  have hj := SmoothManifolds.differential_jacobian S T (Q.map s)
    (Q.immersion s hs).smooth q ((Q.immersion s hs).differential q)
    ((Q.immersion s hs).isDifferential q) c d hc hd hqc hqd
    ((tangentStructure S).fiberCoordinates.equiv c hc q hqc)
    ((tangentStructure T).fiberCoordinates.equiv d hd (Q.map s q) hqd)
    ((tangentStructure S).fiberCoordinates.isCoordinates c hc q hqc)
    ((tangentStructure T).fiberCoordinates.isCoordinates d hd (Q.map s q) hqd)
    V (fun z => f (s, z)) hV hqu hF he v
  rw [hj]
  have hdif : DifferentiableAt ℝ f (s, (c q).val) :=
    (hf.contDiffAt (hU.mem_nhds hqu)).differentiableAt (by simp)
  have hdpath := (hdif.hasFDerivAt.comp (c q).val
    ((hasFDerivAt_const s _).prodMk (hasFDerivAt_id (c q).val))).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.id_apply] using congrArg (fun L =>
    L ((tangentStructure S).fiberCoordinates.equiv c hc q hqc v)) hdpath


theorem metric_chart_gram_extension (h : RiemannianMetric T)
 (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val) (q₀ : N) (hq₀ : q₀ ∈ d.source) :
 ∃ (V : Set (Euclidean m)) (H : Euclidean m → Fin m → Fin m → ℝ),
  IsOpen V ∧ (d q₀).val ∈ V ∧ ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
  ∃ O : Set N, IsOpen O ∧ q₀ ∈ O ∧ ∃ hOsub : O ⊆ d.source,
  ∀ q (hq : q ∈ O), ∀ j k : Fin m,
   H (d q).val j k = pairing h q
     (((tangentStructure T).fiberCoordinates.equiv d hd q (hOsub hq)).symm (Pi.single j 1))
     (((tangentStructure T).fiberCoordinates.equiv d hd q (hOsub hq)).symm (Pi.single k 1)) := by
 let B := (tangentRealization T).space.bundle
 let idx : TangentIndex T := ⟨d,hd⟩
 let R : N → Fin m → Fin m → ℝ := fun q j k => h.form q
   ((B.trivialization idx).symm q (Pi.single j 1))
   ((B.trivialization idx).symm q (Pi.single k 1))
 have hbase : q₀ ∈ B.baseSet idx := by
   simpa only [B, (tangentRealization T).baseSet idx] using hq₀
 have hR : SmoothManifolds.FrameData.VectorSmoothAt T.smoothStructure.val R q₀ := by
   apply SmoothManifolds.FrameData.VectorSmoothAt.pi
   intro j
   apply SmoothManifolds.FrameData.VectorSmoothAt.pi
   intro k
   exact h.smooth idx j k q₀ hbase
 obtain ⟨V,hV,hqV,H,hH,heH⟩ := hR.2 d hd hq₀
 obtain ⟨O,hOsub,hO,hqO⟩ := mem_nhds_iff.mp heH
 refine ⟨V,H,hV,hqV,hH,O ∩ d.source,hO.inter d.open_source,⟨hqO,hq₀⟩,Set.inter_subset_right,?_⟩
 intro q hq j k
 have hcoord : B.fiberCoordinates idx q (by simpa only [B, (tangentRealization T).baseSet idx] using hq.2) =
      (tangentStructure T).fiberCoordinates.equiv d hd q hq.2 := by
   apply LinearEquiv.ext
   intro v
   rw [SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_apply,
       (tangentRealization T).coordinates idx q hq.2 v]
 have hsymm (j : Fin m) :
   (B.trivialization idx).symm q (Pi.single j 1) =
    ((tangentStructure T).fiberCoordinates.equiv d hd q hq.2).symm (Pi.single j 1) := by
   rw [← SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply B idx q
     (by simpa only [B, (tangentRealization T).baseSet idx] using hq.2), hcoord]
 have he := congrFun (congrFun (hOsub hq.1) j) k
 change H (d q).val j k = h.form q _ _
 exact he.trans (by dsimp only [R]; rw [hsymm,hsymm])


theorem induced_gram_local_extension
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (U : Set (ℝ × Euclidean n)) (f : ℝ × Euclidean n → Euclidean m)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (heq : ∀ t ∈ Q.domain, ∀ x : ModelSpace n a,
      (t, x.val) ∈ U → x ∈ c.target →
      Q.map t (c.symm x) ∈ d.source ∧
      f (t, x.val) = (d (Q.map t (c.symm x))).val)
    (s₀ : ℝ) (hs₀ : s₀ ∈ Q.domain)
    (p : M) (hpc : p ∈ c.source) (hpu : (s₀, (c p).val) ∈ U) :
    ∃ (W : Set (ℝ × Euclidean n)) (G : ℝ × Euclidean n → Fin n → Fin n → ℝ),
      IsOpen W ∧ (s₀,(c p).val) ∈ W ∧ W ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) G W ∧
      ∀ t (ht : t ∈ Q.domain) q (hqc : q ∈ c.source), (t,(c q).val) ∈ W →
        P202.VolumeData.gramMatrix (g t) (tangentStructure S).fiberCoordinates c hc ⟨q,hqc⟩ =
          Matrix.of (G (t,(c q).val)) := by
 have hqd₀ : Q.map s₀ p ∈ d.source := by
   simpa only [c.left_inv hpc] using (heq s₀ hs₀ (c p) hpu (c.map_source hpc)).1
 have hf₀ : f (s₀,(c p).val) = (d (Q.map s₀ p)).val := by
   simpa only [c.left_inv hpc] using (heq s₀ hs₀ (c p) hpu (c.map_source hpc)).2
 obtain ⟨V,H,hV,hpdV,hH,O,hO,hpO,hOsub,hHO⟩ :=
   metric_chart_gram_extension h d hd (Q.map s₀ p) hqd₀
 have hsymm : d.symm (d (Q.map s₀ p)) ∈ O := by
   simpa only [d.left_inv hqd₀] using hpO
 obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp
   ((d.continuousAt_symm (d.map_source hqd₀)).preimage_mem_nhds (hO.mem_nhds hsymm))
 let W := U ∩ f ⁻¹' (V ∩ Metric.ball (d (Q.map s₀ p)).val δ)
 have hW : IsOpen W :=
   hf.continuousOn.isOpen_inter_preimage hU (hV.inter (Metric.isOpen_ball : IsOpen (Metric.ball (d (Q.map s₀ p)).val δ)))
 have hpW : (s₀,(c p).val) ∈ W := by
   refine ⟨hpu,?_⟩
   change f (s₀,(c p).val) ∈ V ∩ Metric.ball (d (Q.map s₀ p)).val δ
   rw [hf₀]
   exact ⟨hpdV,Metric.mem_ball_self hδ⟩
 let G : ℝ × Euclidean n → Fin n → Fin n → ℝ := fun z i j =>
   ∑ k : Fin m, ∑ l : Fin m,
    (fderiv ℝ f z (0,(Pi.basisFun ℝ (Fin n)) i)) k *
      ((fderiv ℝ f z (0,(Pi.basisFun ℝ (Fin n)) j)) l * H (f z) k l)
 have hdf : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) U := by
   intro z hz
   exact ((hf.contDiffAt (hU.mem_nhds hz)).fderiv_right (by simp)).contDiffWithinAt
 have hG : ContDiffOn ℝ (⊤ : ℕ∞) G W := by
   apply contDiffOn_pi.mpr
   intro i
   apply contDiffOn_pi.mpr
   intro j
   apply ContDiffOn.sum
   intro k _
   apply ContDiffOn.sum
   intro l _
   have hfk : ContDiffOn ℝ (⊤ : ℕ∞)
       (fun z => (fderiv ℝ f z (0,(Pi.basisFun ℝ (Fin n)) i)) k) W := by
     exact ((ContinuousLinearMap.proj (R := ℝ) k).contDiff.comp_contDiffOn
       ((hdf.mono Set.inter_subset_left).clm_apply contDiffOn_const))
   have hfl : ContDiffOn ℝ (⊤ : ℕ∞)
       (fun z => (fderiv ℝ f z (0,(Pi.basisFun ℝ (Fin n)) j)) l) W := by
     exact ((ContinuousLinearMap.proj (R := ℝ) l).contDiff.comp_contDiffOn
       ((hdf.mono Set.inter_subset_left).clm_apply contDiffOn_const))
   have hHkl : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => H (f z) k l) W := by
     exact ((contDiffOn_pi.mp ((contDiffOn_pi.mp hH) k)) l).comp
       (hf.mono Set.inter_subset_left) (fun z hz => hz.2.1)
   exact hfk.mul (hfl.mul hHkl)
 refine ⟨W,G,hW,hpW,Set.inter_subset_left,hG,?_⟩
 intro t ht q hqc hqW
 obtain ⟨hqd,hdiff⟩ := variation_differential_in_coordinates Q c hc d hd U f hU hf heq t ht q hqc hqW.1
 have hfq : f (t,(c q).val) = (d (Q.map t q)).val := by
   simpa only [c.left_inv hqc] using (heq t ht (c q) hqW.1 (c.map_source hqc)).2
 have hqO : Q.map t q ∈ O := by
   have hball : d (Q.map t q) ∈ Metric.ball (d (Q.map s₀ p)) δ := by
     simpa only [Metric.mem_ball, Subtype.dist_eq, hfq] using hqW.2.2
   have hh := hδsub hball
   change d.symm (d (Q.map t q)) ∈ O at hh
   simpa only [d.left_inv hqd] using hh
 ext i j
 change pairing (g t) q _ _ = G (t,(c q).val) i j
 rw [hg t ht q]
 let ei := ((tangentStructure S).fiberCoordinates.equiv c hc q hqc).symm ((Pi.basisFun ℝ (Fin n)) i)
 let ej := ((tangentStructure S).fiberCoordinates.equiv c hc q hqc).symm ((Pi.basisFun ℝ (Fin n)) j)
 have hb := P202.Geometry.SmoothMetrics.bilinear_coordinates
   ((tangentStructure T).fiberCoordinates.equiv d hd (Q.map t q) hqd) (pairing h (Q.map t q))
   ((Q.immersion t ht).differential q ei) ((Q.immersion t ht).differential q ej)
 apply hb.trans
 dsimp only [G]
 apply Finset.sum_congr rfl
 intro k _
 apply Finset.sum_congr rfl
 intro l _
 rw [hdiff,hdiff,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
 rw [← hHO (Q.map t q) hqO k l, ← hfq]


theorem induced_density_local_extension
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (U : Set (ℝ × Euclidean n)) (f : ℝ × Euclidean n → Euclidean m)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (heq : ∀ t ∈ Q.domain, ∀ x : ModelSpace n a,
      (t, x.val) ∈ U → x ∈ c.target →
      Q.map t (c.symm x) ∈ d.source ∧
      f (t, x.val) = (d (Q.map t (c.symm x))).val)
    (s₀ : ℝ) (hs₀ : s₀ ∈ Q.domain)
    (p : M) (hpc : p ∈ c.source) (hpu : (s₀, (c p).val) ∈ U) :
    ∃ (W : Set (ℝ × Euclidean n)) (r : ℝ × Euclidean n → ℝ),
      IsOpen W ∧ (s₀,(c p).val) ∈ W ∧ W ⊆ U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) r W ∧
      ∀ t (ht : t ∈ Q.domain) q (hqc : q ∈ c.source), (t,(c q).val) ∈ W →
        SmoothManifolds.MetricVolumeData.densityCoefficient
          (tangentStructure S).fiberCoordinates c hc ⟨q,hqc⟩ (P202.VolumeData.density (g t) q) =
          r (t,(c q).val) := by
 obtain ⟨W,G,hW,hpW,hWU,hG,hGval⟩ :=
   induced_gram_local_extension Q h g hg c hc d hd U f hU hf heq s₀ hs₀ p hpc hpu
 let D : ℝ × Euclidean n → ℝ := fun z => (Matrix.of (G z)).det
 have hD : ContDiffOn ℝ (⊤ : ℕ∞) D W :=
   (SmoothManifolds.MetricVolumeResults.matrix_det_smooth n).comp_contDiffOn hG
 have hDpos : 0 < D (s₀,(c p).val) := by
   change 0 < (Matrix.of (G (s₀,(c p).val))).det
   rw [← hGval s₀ hs₀ p hpc hpW]
   exact SmoothManifolds.MetricVolumeResults.metricMatrix_det_pos
     (P202.VolumeData.libraryMetric (g s₀)) (tangentStructure S).fiberCoordinates c hc ⟨p,hpc⟩
 let W' := W ∩ D ⁻¹' Set.Ioi (0 : ℝ)
 have hW' : IsOpen W' := hD.continuousOn.isOpen_inter_preimage hW isOpen_Ioi
 refine ⟨W',fun z => Real.sqrt (D z),hW',⟨hpW,hDpos⟩,
   (fun z hz => hWU hz.1),(hD.mono Set.inter_subset_left).sqrt (fun z hz => ne_of_gt hz.2),?_⟩
 intro t ht q hqc hqW
 rw [P202.VolumeData.density, SmoothManifolds.MetricVolumeResults.metricDensity_coefficient]
 change Real.sqrt (P202.VolumeData.gramMatrix (g t) (tangentStructure S).fiberCoordinates c hc ⟨q,hqc⟩).det = _
 exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => Real.sqrt A.det) (hGval t ht q hqc hqW.1)


theorem metric_chart_density_extension (h : RiemannianMetric S)
 (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source) :
 ∃ (V : Set (Euclidean n)) (r : Euclidean n → ℝ),
  IsOpen V ∧ (c p).val ∈ V ∧ ContDiffOn ℝ (⊤ : ℕ∞) r V ∧
  (∀ x ∈ V, r x ≠ 0) ∧
  ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ ∃ hOsub : O ⊆ c.source,
  ∀ q (hq : q ∈ O),
   SmoothManifolds.MetricVolumeData.densityCoefficient
       (tangentStructure S).fiberCoordinates c hc ⟨q,hOsub hq⟩ (P202.VolumeData.density h q) = r (c q).val := by
 obtain ⟨V,H,hV,hpV,hH,O,hO,hpO,hOsub,hHO⟩ :=
   metric_chart_gram_extension h c hc p hp
 have hmat : ∀ q (hq : q ∈ O), P202.VolumeData.gramMatrix h
     (tangentStructure S).fiberCoordinates c hc ⟨q,hOsub hq⟩ = Matrix.of (H (c q).val) := by
   intro q hq
   ext i j
   simpa only [P202.VolumeData.gramMatrix,Matrix.of_apply,Pi.basisFun_apply] using (hHO q hq i j).symm
 let D : Euclidean n → ℝ := fun x => (Matrix.of (H x)).det
 have hD : ContDiffOn ℝ (⊤ : ℕ∞) D V :=
   (SmoothManifolds.MetricVolumeResults.matrix_det_smooth n).comp_contDiffOn hH
 have hDpos : 0 < D (c p).val := by
   change 0 < (Matrix.of (H (c p).val)).det
   rw [← hmat p hpO]
   exact SmoothManifolds.MetricVolumeResults.metricMatrix_det_pos
     (P202.VolumeData.libraryMetric h) (tangentStructure S).fiberCoordinates c hc ⟨p,hOsub hpO⟩
 let V' := V ∩ D ⁻¹' Set.Ioi (0 : ℝ)
 have hV' : IsOpen V' := hD.continuousOn.isOpen_inter_preimage hV isOpen_Ioi
 refine ⟨V',fun x => Real.sqrt (D x),hV',⟨hpV,hDpos⟩,
   (hD.mono Set.inter_subset_left).sqrt (fun x hx => ne_of_gt hx.2),
   (fun x hx => ne_of_gt (Real.sqrt_pos.mpr hx.2)),O,hO,hpO,hOsub,?_⟩
 intro q hq
 rw [P202.VolumeData.density, SmoothManifolds.MetricVolumeResults.metricDensity_coefficient]
 change Real.sqrt (P202.VolumeData.gramMatrix h (tangentStructure S).fiberCoordinates c hc ⟨q,hOsub hq⟩).det = _
 exact congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => Real.sqrt A.det) (hmat q hq)

theorem variation_densityRatio_local_extension
 (Q : SmoothVariation S T) (h : RiemannianMetric T)
 (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
 (g₀ : RiemannianMetric S) (s₀ : ℝ) (hs₀ : s₀ ∈ Q.domain) (p : M) :
 ∃ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
   (O : Set M), IsOpen O ∧ p ∈ O ∧ ∃ hOsub : O ⊆ c.source,
 ∃ (W : Set (ℝ × Euclidean n)) (r : ℝ × Euclidean n → ℝ),
   IsOpen W ∧ (s₀,(c p).val) ∈ W ∧ ContDiffOn ℝ (⊤ : ℕ∞) r W ∧
   ∀ t ∈ Q.domain, ∀ q ∈ O, (t,(c q).val) ∈ W →
     densityRatio g₀ (P202.VolumeData.density (g t)) q = r (t,(c q).val) := by
 obtain ⟨c,hc,d,hd,hpc,hpd,U,f,hU,hpu,hf,heq⟩ := Q.joint_smooth s₀ hs₀ p
 obtain ⟨W,r,hW,hpW,hWU,hr,hrval⟩ :=
   induced_density_local_extension Q h g hg c hc d hd U f hU hf heq s₀ hs₀ p hpc hpu
 obtain ⟨V,r₀,hV,hpV,hr₀,hr₀ne,O,hO,hpO,hOsub,hr₀val⟩ := metric_chart_density_extension g₀ c hc p hpc
 let W' := W ∩ Prod.snd ⁻¹' V
 have hW' : IsOpen W' := hW.inter (hV.preimage continuous_snd)
 have hr₀comp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : ℝ × Euclidean n => r₀ z.2) W' :=
   hr₀.comp contDiffOn_snd (fun z hz => hz.2)
 refine ⟨c,hc,O,hO,hpO,hOsub,W',fun z => r z / r₀ z.2,hW',⟨hpW,hpV⟩,
   (hr.mono Set.inter_subset_left).div hr₀comp (fun z hz => hr₀ne z.2 hz.2),?_⟩
 intro t ht q hq hqW
 rw [densityRatio_coefficient g₀ _ (tangentStructure S).fiberCoordinates c hc ⟨q,hOsub hq⟩,
     hrval t ht q (hOsub hq) hqW.1,hr₀val q hq]


theorem variation_densityRatio_continuousAt
 (Q : SmoothVariation S T) (h : RiemannianMetric T)
 (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
 (g₀ : RiemannianMetric S) (s₀ : ℝ) (hs₀ : s₀ ∈ Q.domain) (p : M) :
 ContinuousAt (fun z : ℝ × M => densityRatio g₀ (P202.VolumeData.density (g z.1)) z.2) (s₀,p) := by
 obtain ⟨c,hc,O,hO,hpO,hOsub,W,r,hW,hpW,hr,hval⟩ :=
   variation_densityRatio_local_extension Q h g hg g₀ s₀ hs₀ p
 have hp : p ∈ c.source := hOsub hpO
 have hccont : ContinuousAt (fun z : ℝ × M => (z.1,(c z.2).val)) (s₀,p) :=
   continuousAt_fst.prodMk (continuous_subtype_val.continuousAt.comp ((c.continuousAt hp).comp continuousAt_snd))
 have heq : (fun z : ℝ × M => densityRatio g₀ (P202.VolumeData.density (g z.1)) z.2) =ᶠ[𝓝 (s₀,p)]
    (fun z => r (z.1,(c z.2).val)) := by
   filter_upwards [continuousAt_fst.preimage_mem_nhds (Q.open_domain.mem_nhds hs₀),
      continuousAt_snd.preimage_mem_nhds (hO.mem_nhds hpO),
      hccont.preimage_mem_nhds (hW.mem_nhds hpW)] with z hz hzO hzW
   exact hval z.1 hz z.2 hzO hzW
 have hrc : ContinuousAt r (s₀,(c p).val) := (hr.contDiffAt (hW.mem_nhds hpW)).continuousAt
 exact (hrc.comp (f := fun z : ℝ × M => (z.1,(c z.2).val)) hccont).congr_of_eventuallyEq heq


theorem densityRatio_hasDerivAt_of_local_extension
 (Q : SmoothVariation S T) (g : ℝ → RiemannianMetric S) (g₀ : RiemannianMetric S)
 (c : ModelChart n a M) (O : Set M)
 (W : Set (ℝ × Euclidean n)) (r : ℝ × Euclidean n → ℝ)
 (hW : IsOpen W) (hr : ContDiffOn ℝ (⊤ : ℕ∞) r W)
 (hval : ∀ t ∈ Q.domain, ∀ q ∈ O, (t,(c q).val) ∈ W →
     densityRatio g₀ (P202.VolumeData.density (g t)) q = r (t,(c q).val))
 (t : ℝ) (ht : t ∈ Q.domain) (q : M) (hq : q ∈ O) (hqW : (t,(c q).val) ∈ W) :
 HasDerivAt (fun s => densityRatio g₀ (P202.VolumeData.density (g s)) q)
    (fderiv ℝ r (t,(c q).val) (1,0)) t := by
 have hrAt := hr.contDiffAt (hW.mem_nhds hqW)
 have hrd := (hrAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
   ((hasDerivAt_id t).prodMk (hasDerivAt_const t (c q).val))
 have heq : (fun s => densityRatio g₀ (P202.VolumeData.density (g s)) q) =ᶠ[𝓝 t]
     (fun s => r (s,(c q).val)) := by
   have hpath : ContinuousAt (fun s : ℝ => (s,(c q).val)) t :=
     continuousAt_id.prodMk continuousAt_const
   filter_upwards [Q.open_domain.mem_nhds ht,hpath.preimage_mem_nhds (hW.mem_nhds hqW)] with s hs hsW
   exact hval s hs q hq hsW
 exact hrd.congr_of_eventuallyEq heq

theorem variation_densityRatio_hasDerivAt
 (Q : SmoothVariation S T) (h : RiemannianMetric T)
 (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
 (g₀ : RiemannianMetric S) (s₀ : ℝ) (hs₀ : s₀ ∈ Q.domain) (p : M) :
 HasDerivAt (fun s => densityRatio g₀ (P202.VolumeData.density (g s)) p)
   (deriv (fun s => densityRatio g₀ (P202.VolumeData.density (g s)) p) s₀) s₀ := by
 obtain ⟨c,hc,O,hO,hpO,hOsub,W,r,hW,hpW,hr,hval⟩ :=
   variation_densityRatio_local_extension Q h g hg g₀ s₀ hs₀ p
 have hh := densityRatio_hasDerivAt_of_local_extension Q g g₀ c O W r hW hr hval s₀ hs₀ p hpO hpW
 exact hh.deriv.symm ▸ hh

theorem variation_densityRatio_deriv_continuousAt
 (Q : SmoothVariation S T) (h : RiemannianMetric T)
 (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
 (g₀ : RiemannianMetric S) (s₀ : ℝ) (hs₀ : s₀ ∈ Q.domain) (p : M) :
 ContinuousAt (fun z : ℝ × M =>
    deriv (fun s => densityRatio g₀ (P202.VolumeData.density (g s)) z.2) z.1) (s₀,p) := by
 obtain ⟨c,hc,O,hO,hpO,hOsub,W,r,hW,hpW,hr,hval⟩ :=
   variation_densityRatio_local_extension Q h g hg g₀ s₀ hs₀ p
 have hp : p ∈ c.source := hOsub hpO
 have hccont : ContinuousAt (fun z : ℝ × M => (z.1,(c z.2).val)) (s₀,p) :=
   continuousAt_fst.prodMk (continuous_subtype_val.continuousAt.comp ((c.continuousAt hp).comp continuousAt_snd))
 have hdr : ContinuousAt (fun z => fderiv ℝ r z (1,0)) (s₀,(c p).val) :=
   ((((hr.contDiffAt (hW.mem_nhds hpW)).fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).continuousAt)
 have heq : (fun z : ℝ × M =>
    deriv (fun s => densityRatio g₀ (P202.VolumeData.density (g s)) z.2) z.1) =ᶠ[𝓝 (s₀,p)]
    (fun z => fderiv ℝ r (z.1,(c z.2).val) (1,0)) := by
   filter_upwards [continuousAt_fst.preimage_mem_nhds (Q.open_domain.mem_nhds hs₀),
      continuousAt_snd.preimage_mem_nhds (hO.mem_nhds hpO),
      hccont.preimage_mem_nhds (hW.mem_nhds hpW)] with z hz hzO hzW
   exact (densityRatio_hasDerivAt_of_local_extension Q g g₀ c O W r hW hr hval z.1 hz z.2 hzO hzW).deriv
 have hcomp : ContinuousAt (fun z : ℝ × M => fderiv ℝ r (z.1,(c z.2).val) (1,0)) (s₀,p) :=
   ContinuousAt.comp (g := fun z : ℝ × Euclidean n => fderiv ℝ r z (1,0))
     (f := fun z : ℝ × M => (z.1,(c z.2).val)) hdr hccont
 exact hcomp.congr_of_eventuallyEq heq


end JointDensityRegularity

section InducedMetricDerivative
open SmoothManifolds.MapData SmoothManifolds.BundleOperationsData
  SmoothManifolds.TangentBundleData SmoothManifolds.DifferentialData
  SmoothManifolds.BundleData SmoothManifolds.FrameData
  P202.LeviCivitaData
open Set Filter
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

section EuclideanMixed
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_partial_space (f : ℝ × E → F) (s : ℝ) (x v : E)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (s, x)) :
    HasDerivAt (fun t => fderiv ℝ f (t, x) (0, v))
      (fderiv ℝ (fderiv ℝ f) (s, x) (1, 0) (0, v)) s := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (s, x) :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hpath := hdf.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  simpa using hpath.clm_apply (hasDerivAt_const s (0, v))

theorem fderiv_partial_time (f : ℝ × E → F) (s : ℝ) (x v : E)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (s, x)) :
    fderiv ℝ (fun y => fderiv ℝ f (s, y) (1, 0)) x v =
      fderiv ℝ (fderiv ℝ f) (s, x) (0, v) (1, 0) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (s, x) :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hspace := hdf.hasFDerivAt.comp x
    ((hasFDerivAt_const s x).prodMk (hasFDerivAt_id x))
  have he := (hspace.clm_apply (hasFDerivAt_const (1, (0 : E)) x)).fderiv
  simpa using congrArg (fun L => L v) he

theorem hasDerivAt_partial_space_eq_space_time (f : ℝ × E → F) (s : ℝ) (x v : E)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (s, x)) :
    HasDerivAt (fun t => fderiv ℝ f (t, x) (0, v))
      (fderiv ℝ (fun y => fderiv ℝ f (s, y) (1, 0)) x v) s := by
  rw [fderiv_partial_time f s x v hf]
  rw [← (hf.isSymmSndFDerivAt (by simp)).eq (1, 0) (0, v)]
  exact hasDerivAt_partial_space f s x v hf


theorem hasDerivAt_pullback_gram
    (f : ℝ × Euclidean n → Euclidean m) (s : ℝ) (x v w : Euclidean n)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (s, x))
    (H : Euclidean m → Matrix (Fin m) (Fin m) ℝ)
    (hH : ∀ a b, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => H y a b) (f (s, x))) :
    HasDerivAt (fun t => ∑ a : Fin m, ∑ b : Fin m,
      H (f (t, x)) a b * (fderiv ℝ f (t, x) (0, v)) a *
        (fderiv ℝ f (t, x) (0, w)) b)
      (∑ a : Fin m, ∑ b : Fin m,
        ((fderiv ℝ (fun y => H y a b) (f (s, x)) (fderiv ℝ f (s, x) (1, 0))) *
          (fderiv ℝ f (s, x) (0, v)) a * (fderiv ℝ f (s, x) (0, w)) b +
        H (f (s, x)) a b * (fderiv ℝ (fun y => fderiv ℝ f (s, y) (1, 0)) x v) a *
          (fderiv ℝ f (s, x) (0, w)) b +
        H (f (s, x)) a b * (fderiv ℝ f (s, x) (0, v)) a *
          (fderiv ℝ (fun y => fderiv ℝ f (s, y) (1, 0)) x w) b)) s := by
  have hpath : HasDerivAt (fun t => f (t, x)) (fderiv ℝ f (s, x) (1, 0)) s :=
    (hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have hHp (a b : Fin m) :=
    ((hH a b).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s hpath
  have hv := hasDerivAt_partial_space_eq_space_time f s x v hf
  have hw := hasDerivAt_partial_space_eq_space_time f s x w hf
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
      ((hHp a b).mul (hasDerivAt_pi.mp hv a)).mul (hasDerivAt_pi.mp hw b)))
  convert hh using 1
  · funext t
    simp only [Pi.mul_apply, Function.comp_apply]
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [Pi.mul_apply, Function.comp_apply]
    ring

end EuclideanMixed

section MetricCompatibility
open SmoothManifolds.BundleData SmoothManifolds.FrameData P202.LeviCivitaData

theorem metricMatrix_scalarDerivative (h : RiemannianMetric T)
    (K : Connection (tangentBundle T)) (hK : IsMetricCompatible h K)
    (c : TangentIndex T) (p : N) (hp : p ∈ (tangentBundle T).baseSet c)
    (v : TangentSpace T p) (i j : Fin m) :
    scalarDerivative T (fun q => metricMatrix h c q i j) p v =
      pairing h p (pointDerivative K (coordinateVector c i) p v) (coordinateVector c j p) +
      pairing h p (coordinateVector c i p) (pointDerivative K (coordinateVector c j) p v) := by
  let B := tangentBundle T
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hO : IsOpen (B.baseSet c) :=
    B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  obtain ⟨e, he⟩ := P202.Geometry.ConnectionForms.local_frame_representative B b ⟨p, hp⟩
  have hec (r : Fin m) : ∀ᶠ q in 𝓝 p, (e r).val q = coordinateVector c r q := by
    filter_upwards [he r, hO.mem_nhds hp] with q hq hq'
    rw [hq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq']
    exact P202.Geometry.LeviCivita.trivializationFrame_section c r ⟨q, hq'⟩
  have heval (r : Fin m) : (e r).val p = coordinateVector c r p :=
    (hec r).self_of_nhds
  obtain ⟨X, hX⟩ := P202.Geometry.ConnectionForms.section_evaluation_surjective B p v
  have hscalar : (P202.Geometry.LeviCivita.fieldPairing h (e i) (e j)).val =ᶠ[𝓝 p]
      (fun q => metricMatrix h c q i j) := by
    filter_upwards [hec i, hec j] with q hi hj
    change pairing h q ((e i).val q) ((e j).val q) = _
    rw [hi, hj]
    rfl
  have hder (r : Fin m) : pointDerivative K (coordinateVector c r) p v =
      (K.cov X (e r)).val p := by
    rw [← hX]
    have hd := P202.Geometry.ConnectionForms.pointDerivative_congr B K (e r).val
      (coordinateVector c r) p ⟨e r, Eventually.of_forall (fun _ => rfl)⟩ (hec r)
    exact (congrArg (fun L : TangentSpace T p →ₗ[ℝ] TangentSpace T p => L (X.val p)) hd).symm.trans
      (P202.Geometry.ConnectionForms.pointDerivative_global B K (e r) p X)
  rw [← P202.Geometry.LeviCivita.scalarDerivative_of_germ _ _ p hscalar]
  have hc := hK X (e i) (e j) p
  rw [hX, heval i, heval j] at hc
  rw [hder i, hder j]
  exact hc


theorem coordinate_correction_symm
    (K : Connection (tangentBundle T)) (hK : IsTorsionFree K)
    (c : TangentIndex T) (p : N) (hp : p ∈ (tangentBundle T).baseSet c)
    (i j : Fin m) :
    pointDerivative K (coordinateVector c i) p (coordinateVector c j p) =
      pointDerivative K (coordinateVector c j) p (coordinateVector c i p) := by
  let B := tangentBundle T
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hO : IsOpen (B.baseSet c) :=
    B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  obtain ⟨e, he⟩ := P202.Geometry.ConnectionForms.local_frame_representative B b ⟨p, hp⟩
  have hec (r : Fin m) : ∀ᶠ q in 𝓝 p, (e r).val q = coordinateVector c r q := by
    filter_upwards [he r, hO.mem_nhds hp] with q hq hq'
    rw [hq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq']
    exact P202.Geometry.LeviCivita.trivializationFrame_section c r ⟨q, hq'⟩
  have heval (r : Fin m) : (e r).val p = coordinateVector c r p :=
    (hec r).self_of_nhds
  have hder (r k : Fin m) :
      pointDerivative K (coordinateVector c r) p (coordinateVector c k p) =
      (K.cov (e k) (e r)).val p := by
    rw [← heval k]
    have hd := P202.Geometry.ConnectionForms.pointDerivative_congr B K (e r).val
      (coordinateVector c r) p ⟨e r, Eventually.of_forall (fun _ => rfl)⟩ (hec r)
    exact (congrArg (fun L : TangentSpace T p →ₗ[ℝ] TangentSpace T p => L ((e k).val p)) hd).symm.trans
      (P202.Geometry.ConnectionForms.pointDerivative_global B K (e r) p (e k))
  rw [hder i j, hder j i]
  have hb := P202.Geometry.LeviCivita.coordinate_bracket_zero c p hp i j (e i) (e j)
    (hec i) (hec j)
  have hc := P202.Geometry.LeviCivita.bracket_eq_cov_sub
    P202.Geometry.TorsionAndMetric.torsion_apply K hK (e i) (e j) p
  exact (sub_eq_zero.mp (hc.symm.trans hb)).symm


theorem pullback_derivative_frame
    (F : M → N) (hF : IsSmoothMap S T F)
    (K : Connection (tangentBundle T))
    (P : PullbackBundle (tangentBundle T) S F) :
    letI := P.space.topology
    ∀ (D : Connection P.space.bundle)
      (hD : P202.PullbackData.IsPullback (tangentBundle T) K F hF P D)
      (U : Set N) (hU : IsOpen U)
      (e : LocalFrame (tangentBundle T) U hU)
      (V : Section P.space.bundle) (p : M) (hp : F p ∈ U)
      (v : TangentSpace S p) (i : Fin m),
    (e.basis ⟨F p, hp⟩).equivFun (pointDerivative D V.val p v) i =
      scalarDerivative S (SmoothManifolds.FrameData.totalize
        (fun q : F ⁻¹' U => (e.basis ⟨F q.val, q.property⟩).equivFun (V.val q.val) i)) p v +
        ∑ j, connectionForm K e ⟨F p, hp⟩ i j
          (SmoothManifolds.differential S T F hF p v) *
            (e.basis ⟨F p, hp⟩).equivFun (V.val p) j := by
  letI := P.space.topology
  intro D hD U hU e V p hp v i
  let hO := hU.preimage (continuous_iff_continuousAt.mpr (fun q => (hF q).1))
  let b := P202.Geometry.PullbackConnections.pullFrame (tangentBundle T) F hF P hU e
  let s := restrictGlobalSection V (F ⁻¹' U) hO
  have heq : ∀ᶠ q in 𝓝 p, V.val q =
      SmoothManifolds.SectionExtension.totalSection (E := fun q => TangentSpace T (F q)) s.val q := by
    filter_upwards [hO.mem_nhds hp] with q hq
    simp only [SmoothManifolds.SectionExtension.totalSection_of_mem
      (E := fun q => TangentSpace T (F q)) _ q hq]
    rfl
  have hd := P202.Geometry.ConnectionForms.pointDerivative_congr P.space.bundle D
    V.val (SmoothManifolds.SectionExtension.totalSection s.val) p
    ⟨V, Eventually.of_forall (fun _ => rfl)⟩ heq
  have ht := P202.Geometry.ConnectionForms.local_frame_formula P.space.bundle D b s ⟨p, hp⟩ v i
  have hγ := P202.Geometry.PullbackConnections.frame_rule_of_isPullback
    (tangentBundle T) F hF P K D hD U hU hO e b (fun _ _ => rfl)
  simp_rw [hγ] at ht
  change (e.basis ⟨F p, hp⟩).equivFun
      (pointDerivative D (SmoothManifolds.SectionExtension.totalSection s.val) p v) i = _ at ht
  exact (congrArg (fun L : TangentSpace S p →ₗ[ℝ] TangentSpace T (F p) =>
    (e.basis ⟨F p, hp⟩).equivFun (L v) i) hd).trans ht


def coordinateCorrection (K : Connection (tangentBundle T))
    (c : TangentIndex T) (p : N) (hp : p ∈ (tangentBundle T).baseSet c)
    (v w : TangentSpace T p) : TangentSpace T p :=
  ∑ j : Fin m, ((tangentBundle T).fiberCoordinates c p hp w) j •
    pointDerivative K (coordinateVector c j) p v

theorem coordinateCorrection_symm (K : Connection (tangentBundle T)) (hK : IsTorsionFree K)
    (c : TangentIndex T) (p : N) (hp : p ∈ (tangentBundle T).baseSet c)
    (v w : TangentSpace T p) :
    coordinateCorrection K c p hp v w = coordinateCorrection K c p hp w v := by
  have hd (v : TangentSpace T p) (j : Fin m) :
      pointDerivative K (coordinateVector c j) p v =
        ∑ i : Fin m, ((tangentBundle T).fiberCoordinates c p hp v) i •
          pointDerivative K (coordinateVector c j) p (coordinateVector c i p) := by
    have he := congrArg (pointDerivative K (coordinateVector c j) p)
      (P202.Geometry.LeviCivita.coordinate_expansion c p hp v)
    simpa only [map_sum, map_smul] using he.symm
  unfold coordinateCorrection
  simp_rw [hd v, hd w, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinate_correction_symm K hK c p hp i j, mul_comm]


theorem metricDerivative_coordinate_sum (h : RiemannianMetric T)
    (K : Connection (tangentBundle T)) (hK : IsMetricCompatible h K)
    (c : TangentIndex T) (p : N) (hp : p ∈ (tangentBundle T).baseSet c)
    (V u w : TangentSpace T p) :
    (∑ i : Fin m, ∑ j : Fin m,
      ((tangentBundle T).fiberCoordinates c p hp u) i *
        (((tangentBundle T).fiberCoordinates c p hp w) j *
          scalarDerivative T (fun q => metricMatrix h c q i j) p V)) =
      pairing h p (coordinateCorrection K c p hp V u) w +
        pairing h p u (coordinateCorrection K c p hp V w) := by
  have hpw (z : TangentSpace T p) : pairing h p z w =
      ∑ j : Fin m, ((tangentBundle T).fiberCoordinates c p hp w) j *
        pairing h p z (coordinateVector c j p) := by
    have he := congrArg (pairing h p z)
      (P202.Geometry.LeviCivita.coordinate_expansion c p hp w)
    simpa only [map_sum, map_smul, smul_eq_mul, mul_comm] using he.symm
  have hpu (z : TangentSpace T p) : pairing h p u z =
      ∑ i : Fin m, ((tangentBundle T).fiberCoordinates c p hp u) i *
        pairing h p (coordinateVector c i p) z := by
    have he := congrArg (fun x => pairing h p x z)
      (P202.Geometry.LeviCivita.coordinate_expansion c p hp u)
    simpa only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      using he.symm
  simp_rw [metricMatrix_scalarDerivative h K hK c p hp V]
  simp only [coordinateCorrection, map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  simp_rw [hpw, hpu, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i =>
    ((tangentBundle T).fiberCoordinates c p hp w) j *
      (((tangentBundle T).fiberCoordinates c p hp u) i *
        pairing h p (coordinateVector c i p) (pointDerivative K (coordinateVector c j) p V)))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring


theorem tangent_coordinates_eq (c : TangentIndex T) (p : N)
    (hp : p ∈ (tangentBundle T).baseSet c)
    (hpc : p ∈ c.val.source) :
    (tangentBundle T).fiberCoordinates c p hp =
      (tangentStructure T).fiberCoordinates.equiv c.val c.property p hpc := by
  apply LinearEquiv.ext
  intro v
  rw [SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_apply,
    (tangentRealization T).coordinates c p hpc v]

theorem metric_extension_derivative (h : RiemannianMetric T)
    (c : TangentIndex T) (p : N) (hp : p ∈ (tangentBundle T).baseSet c)
    (H : Euclidean m → Matrix (Fin m) (Fin m) ℝ) (U : Set (Euclidean m))
    (hU : IsOpen U) (hpU : (c.val p).val ∈ U)
    (hH : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => H y i j) U)
    (he : ∀ᶠ q in 𝓝 p, ∀ i j, H (c.val q).val i j = metricMatrix h c q i j)
    (V : TangentSpace T p) (i j : Fin m) :
    fderiv ℝ (fun y => H y i j) (c.val p).val
      ((tangentBundle T).fiberCoordinates c p hp V) =
      scalarDerivative T (fun q => metricMatrix h c q i j) p V := by
  have hpc : p ∈ c.val.source := (tangentRealization T).baseSet c ▸ hp
  rw [tangent_coordinates_eq c p hp hpc]
  symm
  apply P202.Geometry.GreenDivergenceCore.scalarDerivative_ambient c.val c.property p hpc
    (h.smooth c i j p hp) (fun y => H y i j) U hU hpU
  · exact hH i j
  · filter_upwards [he] with q hq
    exact hq i j


theorem pullback_derivative_frame_chart
    (F : M → N) (hF : IsSmoothMap S T F)
    (K : Connection (tangentBundle T))
    (P : PullbackBundle (tangentBundle T) S F) :
    letI := P.space.topology
    ∀ (D : Connection P.space.bundle)
      (hD : P202.PullbackData.IsPullback (tangentBundle T) K F hF P D)
      (U : Set N) (hU : IsOpen U)
      (e : LocalFrame (tangentBundle T) U hU)
      (V : Section P.space.bundle) (p : M) (hp : F p ∈ U)
      (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hpc : p ∈ c.source)
      (A : Set (Euclidean n)) (hA : IsOpen A) (hpA : (c p).val ∈ A)
      (w : Fin m → Euclidean n → ℝ)
      (hw : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (w i) A)
      (he : ∀ i, (fun q => w i (c q).val) =ᶠ[𝓝 p]
        SmoothManifolds.FrameData.totalize
          (fun q : F ⁻¹' U => (e.basis ⟨F q.val, q.property⟩).equivFun (V.val q.val) i))
      (v : TangentSpace S p) (i : Fin m),
    (e.basis ⟨F p, hp⟩).equivFun (pointDerivative D V.val p v) i =
      fderiv ℝ (w i) (c p).val
        ((tangentStructure S).fiberCoordinates.equiv c hc p hpc v) +
        ∑ j, connectionForm K e ⟨F p, hp⟩ i j
          (SmoothManifolds.differential S T F hF p v) *
            (e.basis ⟨F p, hp⟩).equivFun (V.val p) j := by
  letI := P.space.topology
  intro D hD U hU e V p hp c hc hpc A hA hpA w hw he v i
  let hO := hU.preimage (continuous_iff_continuousAt.mpr (fun q => (hF q).1))
  let b := P202.Geometry.PullbackConnections.pullFrame (tangentBundle T) F hF P hU e
  let s := restrictGlobalSection V (F ⁻¹' U) hO
  have hcoeff := (SmoothManifolds.Frames.smooth_section_iff_coefficients
    P.space.bundle (F ⁻¹' U) hO b s.val).mp s.property
  have hscalar := SmoothManifolds.FrameData.VectorSmoothAt.totalize hO (hcoeff i ⟨p, hp⟩)
  have hd := P202.Geometry.GreenDivergenceCore.scalarDerivative_ambient c hc p hpc
    hscalar (w i) A hA hpA (hw i) (he i) v
  change scalarDerivative S (SmoothManifolds.FrameData.totalize
    (fun q : F ⁻¹' U => (e.basis ⟨F q.val, q.property⟩).equivFun (V.val q.val) i)) p v = _ at hd
  have ht := pullback_derivative_frame F hF K P D hD U hU e V p hp v i
  rw [hd] at ht
  exact ht


theorem coordinate_metric_pairing_sum (h : RiemannianMetric T)
    (c : TangentIndex T) (p : N) (hp : p ∈ (tangentBundle T).baseSet c)
    (v w : TangentSpace T p) :
    (∑ i : Fin m, ∑ j : Fin m, metricMatrix h c p i j *
      ((tangentBundle T).fiberCoordinates c p hp v) i *
      ((tangentBundle T).fiberCoordinates c p hp w) j) = pairing h p v w := by
  rw [P202.Geometry.SmoothMetrics.bilinear_coordinates
    ((tangentBundle T).fiberCoordinates c p hp) (pairing h p) v w]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [metricMatrix, coordinateVector,
    SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply]
  ring

theorem hasDerivAt_metric_of_chart_data
    (h : RiemannianMetric T) (K : Connection (tangentBundle T))
    (hK : IsLeviCivita h K)
    (c : TangentIndex T) (p : N) (hp : p ∈ (tangentBundle T).baseSet c)
    (f : ℝ × Euclidean n → Euclidean m) (s : ℝ) (x dv dw : Euclidean n)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f (s, x))
    (H : Euclidean m → Matrix (Fin m) (Fin m) ℝ) (U : Set (Euclidean m))
    (hU : IsOpen U) (hpU : (c.val p).val ∈ U)
    (hH : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => H y i j) U)
    (he : ∀ᶠ q in 𝓝 p, ∀ i j, H (c.val q).val i j = metricMatrix h c q i j)
    (hfp : f (s, x) = (c.val p).val)
    (u w V A B : TangentSpace T p)
    (hu : fderiv ℝ f (s, x) (0, dv) = (tangentBundle T).fiberCoordinates c p hp u)
    (hw : fderiv ℝ f (s, x) (0, dw) = (tangentBundle T).fiberCoordinates c p hp w)
    (hV : fderiv ℝ f (s, x) (1, 0) = (tangentBundle T).fiberCoordinates c p hp V)
    (hA : fderiv ℝ (fun y => fderiv ℝ f (s, y) (1, 0)) x dv =
      (tangentBundle T).fiberCoordinates c p hp A)
    (hB : fderiv ℝ (fun y => fderiv ℝ f (s, y) (1, 0)) x dw =
      (tangentBundle T).fiberCoordinates c p hp B) :
    HasDerivAt (fun t => ∑ i : Fin m, ∑ j : Fin m,
      H (f (t, x)) i j * (fderiv ℝ f (t, x) (0, dv)) i *
        (fderiv ℝ f (t, x) (0, dw)) j)
      (pairing h p (A + coordinateCorrection K c p hp u V) w +
        pairing h p u (B + coordinateCorrection K c p hp w V)) s := by
  have hH' (i j : Fin m) : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => H y i j) (f (s, x)) := by
    rw [hfp]
    exact (hH i j).contDiffAt (hU.mem_nhds hpU)
  have hh := hasDerivAt_pullback_gram f s x dv dw hf H hH'
  have hdH (i j : Fin m) := metric_extension_derivative h c p hp H U hU hpU hH he V i j
  have hval := he.self_of_nhds
  simp only [hu, hw, hV, hA, hB, hfp] at hh
  simp_rw [hdH, hval] at hh
  convert hh using 1
  simp only [map_add, LinearMap.add_apply]
  rw [coordinateCorrection_symm K hK.1 c p hp u V,
    coordinateCorrection_symm K hK.1 c p hp w V]
  have hfirst := metricDerivative_coordinate_sum h K hK.2 c p hp V u w
  have hsecond := coordinate_metric_pairing_sum h c p hp A w
  have hthird := coordinate_metric_pairing_sum h c p hp u B
  simp only [Finset.sum_add_distrib]
  have hfirst' :
      (∑ i : Fin m, ∑ j : Fin m,
        scalarDerivative T (fun q => metricMatrix h c q i j) p V *
          ((tangentBundle T).fiberCoordinates c p hp u) i *
          ((tangentBundle T).fiberCoordinates c p hp w) j) =
      pairing h p (coordinateCorrection K c p hp V u) w +
        pairing h p u (coordinateCorrection K c p hp V w) := by
    convert hfirst using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfirst', hsecond, hthird]
  ring


theorem induced_pairing_eq_chart_gram_eventually
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (U : Set (ℝ × Euclidean n)) (f : ℝ × Euclidean n → Euclidean m)
    (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (heq : ∀ t ∈ Q.domain, ∀ x : ModelSpace n a,
      (t, x.val) ∈ U → x ∈ c.target →
      Q.map t (c.symm x) ∈ d.source ∧
      f (t, x.val) = (d (Q.map t (c.symm x))).val)
    (p : M) (hpc : p ∈ c.source) (h0 : (0, (c p).val) ∈ U)
    (H : Euclidean m → Matrix (Fin m) (Fin m) ℝ)
    (heH : ∀ᶠ q in 𝓝 (Q.map 0 p), ∀ i j,
      H (d q).val i j = metricMatrix h ⟨d, hd⟩ q i j)
    (v w : TangentSpace S p) :
    (fun t => pairing (g t) p v w) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => ∑ i : Fin m, ∑ j : Fin m,
        H (f (t, (c p).val)) i j *
          (fderiv ℝ f (t, (c p).val)
            (0, (tangentStructure S).fiberCoordinates.equiv c hc p hpc v)) i *
          (fderiv ℝ f (t, (c p).val)
            (0, (tangentStructure S).fiberCoordinates.equiv c hc p hpc w)) j) := by
  have hcont : ContinuousAt (fun t => Q.map t p) 0 :=
    (Q.continuous.continuousAt ((Q.open_domain.prod isOpen_univ).mem_nhds
      ⟨Q.zero_mem, mem_univ p⟩)).comp (continuousAt_id.prodMk continuousAt_const)
  have hpath : ContinuousAt (fun t : ℝ => (t, (c p).val)) 0 :=
    continuousAt_id.prodMk continuousAt_const
  filter_upwards [Q.open_domain.mem_nhds Q.zero_mem,
    hpath.preimage_mem_nhds (hU.mem_nhds h0), hcont.tendsto.eventually heH]
      with t ht htu htH
  obtain ⟨hqd, hdiff⟩ := variation_differential_in_coordinates Q c hc d hd U f hU hf heq
    t ht p hpc htu
  let idx : TangentIndex T := ⟨d, hd⟩
  have hbase : Q.map t p ∈ (tangentBundle T).baseSet idx :=
    (tangentRealization T).baseSet idx ▸ hqd
  let E := (tangentBundle T).fiberCoordinates idx (Q.map t p) hbase
  have hE := tangent_coordinates_eq idx (Q.map t p) hbase hqd
  have hv : E ((Q.immersion t ht).differential p v) =
      fderiv ℝ f (t, (c p).val)
        (0, (tangentStructure S).fiberCoordinates.equiv c hc p hpc v) :=
    (congrArg (fun L => L ((Q.immersion t ht).differential p v)) hE).trans (hdiff v)
  have hw : E ((Q.immersion t ht).differential p w) =
      fderiv ℝ f (t, (c p).val)
        (0, (tangentStructure S).fiberCoordinates.equiv c hc p hpc w) :=
    (congrArg (fun L => L ((Q.immersion t ht).differential p w)) hE).trans (hdiff w)
  have hfval : f (t, (c p).val) = (d (Q.map t p)).val := by
    simpa only [c.left_inv hpc] using (heq t ht (c p) htu (c.map_source hpc)).2
  rw [hg t ht p v w,
    P202.Geometry.SmoothMetrics.bilinear_coordinates E (pairing h (Q.map t p))]
  simp only [hv, hw]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hHij : H (f (t, (c p).val)) i j =
      pairing h (Q.map t p) (E.symm (Pi.single i 1)) (E.symm (Pi.single j 1)) := by
    rw [hfval, htH i j]
    simp only [E, metricMatrix, coordinateVector,
      SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply]
    rfl
  rw [hHij]
  ring


theorem metric_matrix_chart_extension (h : RiemannianMetric T)
    (c : TangentIndex T) (p : N) (hp : p ∈ c.val.source) :
    ∃ (U : Set (Euclidean m)) (H : Euclidean m → Matrix (Fin m) (Fin m) ℝ),
      IsOpen U ∧ (c.val p).val ∈ U ∧
      (∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => H y i j) U) ∧
      ∀ᶠ q in 𝓝 p, ∀ i j, H (c.val q).val i j = metricMatrix h c q i j := by
  let R : N → Fin m → Fin m → ℝ := fun q i j => metricMatrix h c q i j
  have hbase : p ∈ (tangentBundle T).baseSet c := (tangentRealization T).baseSet c ▸ hp
  have hR : SmoothManifolds.FrameData.VectorSmoothAt T.smoothStructure.val R p := by
    apply SmoothManifolds.FrameData.VectorSmoothAt.pi
    intro i
    apply SmoothManifolds.FrameData.VectorSmoothAt.pi
    intro j
    exact h.smooth c i j p hbase
  obtain ⟨U, hU, hpU, H, hH, he⟩ := hR.2 c.val c.property hp
  refine ⟨U, (fun y => Matrix.of (H y)), hU, hpU, ?_, ?_⟩
  · intro i j
    exact contDiffOn_pi.mp (contDiffOn_pi.mp hH i) j
  · filter_upwards [he] with q hq i j
    exact congrFun (congrFun hq i) j


theorem fderiv_component_apply (W : Euclidean n → Euclidean m) (x v : Euclidean n)
    (hW : DifferentiableAt ℝ W x) (i : Fin m) :
    fderiv ℝ (fun y => W y i) x v = (fderiv ℝ W x v) i := by
  have hc := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp x hW.hasFDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.proj_apply] using congrArg (fun L => L v) hc.fderiv


theorem connectionForm_coordinate_frame (K : Connection (tangentBundle T))
    (c : TangentIndex T) (p : N) (hp : p ∈ (tangentBundle T).baseSet c)
    (i j : Fin m) (v : TangentSpace T p) :
    connectionForm K (SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle T) c)
      ⟨p,hp⟩ i j v =
      ((tangentBundle T).fiberCoordinates c p hp
        (pointDerivative K (coordinateVector c j) p v)) i := by
  let B := tangentBundle T
  let e := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hO : IsOpen (B.baseSet c) :=
    B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  obtain ⟨E, hE⟩ := P202.Geometry.ConnectionForms.local_frame_representative B e ⟨p,hp⟩
  have hEc : ∀ᶠ q in 𝓝 p, (E j).val q = coordinateVector c j q := by
    filter_upwards [hE j, hO.mem_nhds hp] with q he hq
    rw [he, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    exact P202.Geometry.LeviCivita.trivializationFrame_section c j ⟨q,hq⟩
  have h₁ := P202.Geometry.ConnectionForms.pointDerivative_congr B K (E j).val
    (SmoothManifolds.SectionExtension.totalSection (e.section_ j)) p
    ⟨E j, Eventually.of_forall (fun _ => rfl)⟩ (hE j)
  have h₂ := P202.Geometry.ConnectionForms.pointDerivative_congr B K (E j).val (coordinateVector c j) p
    ⟨E j, Eventually.of_forall (fun _ => rfl)⟩ hEc
  have hder : pointDerivative K (SmoothManifolds.SectionExtension.totalSection (e.section_ j)) p =
      pointDerivative K (coordinateVector c j) p := h₁.symm.trans h₂
  change (e.basis ⟨p,hp⟩).equivFun
    (pointDerivative K (SmoothManifolds.SectionExtension.totalSection (e.section_ j)) p v) i = _
  rw [hder]
  exact congrFun (P202.Geometry.LeviCivita.trivializationFrame_coordinates c ⟨p,hp⟩
    (pointDerivative K (coordinateVector c j) p v)) i

theorem coordinate_frame_correction_coeff (K : Connection (tangentBundle T))
    (c : TangentIndex T) (p : N) (hp : p ∈ (tangentBundle T).baseSet c)
    (v w : TangentSpace T p) (i : Fin m) :
    ((tangentBundle T).fiberCoordinates c p hp
      (∑ j : Fin m, ((tangentBundle T).fiberCoordinates c p hp w) j •
        pointDerivative K (coordinateVector c j) p v)) i =
      ∑ j : Fin m,
        connectionForm K (SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle T) c)
          ⟨p,hp⟩ i j v * ((tangentBundle T).fiberCoordinates c p hp w) j := by
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [connectionForm_coordinate_frame]
  ring


theorem pullback_derivative_vector_chart
    (F : M → N) (hF : IsSmoothMap S T F)
    (K : Connection (tangentBundle T))
    (P : PullbackBundle (tangentBundle T) S F) :
    letI := P.space.topology
    ∀ (D : Connection P.space.bundle)
      (hD : P202.PullbackData.IsPullback (tangentBundle T) K F hF P D)
      (d : TangentIndex T) (V : Section P.space.bundle) (p : M)
      (hpd : F p ∈ (tangentBundle T).baseSet d)
      (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (hpc : p ∈ c.source)
      (A : Set (Euclidean n)) (hA : IsOpen A) (hpA : (c p).val ∈ A)
      (w : Fin m → Euclidean n → ℝ)
      (hw : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (w i) A)
      (he : ∀ i, (fun q => w i (c q).val) =ᶠ[𝓝 p]
        SmoothManifolds.FrameData.totalize
          (fun q : F ⁻¹' (tangentBundle T).baseSet d =>
            ((SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle T) d).basis
              ⟨F q.val, q.property⟩).equivFun (V.val q.val) i))
      (v : TangentSpace S p),
    pointDerivative D V.val p v =
      ((tangentBundle T).fiberCoordinates d (F p) hpd).symm
        (fun i => fderiv ℝ (w i) (c p).val
          ((tangentStructure S).fiberCoordinates.equiv c hc p hpc v)) +
      coordinateCorrection K d (F p) hpd
        (SmoothManifolds.differential S T F hF p v) (V.val p) := by
  letI := P.space.topology
  intro D hD d V p hpd c hc hpc A hA hpA w hw he v
  let B := tangentBundle T
  let e := SmoothManifolds.ConstantRankBundles.trivializationFrame B d
  have hO : IsOpen (B.baseSet d) :=
    B.trivialization_baseSet d ▸ (B.trivialization d).open_baseSet
  apply (B.fiberCoordinates d (F p) hpd).injective
  rw [map_add, LinearEquiv.apply_symm_apply]
  funext i
  have ht := pullback_derivative_frame_chart F hF K P D hD
    (B.baseSet d) hO e V p hpd c hc hpc A hA hpA w hw he v i
  rw [P202.Geometry.LeviCivita.trivializationFrame_coordinates,
    P202.Geometry.LeviCivita.trivializationFrame_coordinates] at ht
  change (B.fiberCoordinates d (F p) hpd (pointDerivative D V.val p v)) i =
    fderiv ℝ (w i) (c p).val ((tangentStructure S).fiberCoordinates.equiv c hc p hpc v) + _
  rw [ht]
  congr 1
  exact (coordinate_frame_correction_coeff K d (F p) hpd
    (SmoothManifolds.differential S T F hF p v) (V.val p) i).symm



theorem variation_velocity_frame_chart_data
 (Q : SmoothVariation S T) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
 (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
 (U : Set (ℝ × Euclidean n)) (f : ℝ × Euclidean n → Euclidean m)
 (hU : IsOpen U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
 (heq : ∀ t ∈ Q.domain, ∀ x : ModelSpace n a,
      (t, x.val) ∈ U → x ∈ c.target →
      Q.map t (c.symm x) ∈ d.source ∧
      f (t, x.val) = (d (Q.map t (c.symm x))).val)
 (p : M) (hpc : p ∈ c.source) (hpu : (0,(c p).val) ∈ U)
 (P : PullbackBundle (tangentBundle T) S (Q.map 0)) :
 letI := P.space.topology
 ∀ (V : Section P.space.bundle) (hV : ∀ q, V.val q = variationVelocity Q q),
 let A : Set (Euclidean n) := (fun x => ((0 : ℝ),x)) ⁻¹' U
 let w : Fin m → Euclidean n → ℝ := fun i x => fderiv ℝ f (0,x) (1,0) i
 let idx : TangentIndex T := ⟨d,hd⟩
 IsOpen A ∧ (c p).val ∈ A ∧
 (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (w i) A) ∧
 (∀ i, (fun q => w i (c q).val) =ᶠ[𝓝 p]
   SmoothManifolds.FrameData.totalize
    (fun q : Q.map 0 ⁻¹' (tangentBundle T).baseSet idx =>
     ((SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle T) idx).basis
        ⟨Q.map 0 q.val,q.property⟩).equivFun (V.val q.val) i)) := by
 letI := P.space.topology
 intro V hV
 let A : Set (Euclidean n) := (fun x => ((0 : ℝ),x)) ⁻¹' U
 let w : Fin m → Euclidean n → ℝ := fun i x => fderiv ℝ f (0,x) (1,0) i
 let idx : TangentIndex T := ⟨d,hd⟩
 change IsOpen A ∧ (c p).val ∈ A ∧ _
 have hA : IsOpen A := hU.preimage (continuous_const.prodMk continuous_id)
 have hdf : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) U := by
   intro z hz
   exact ((hf.contDiffAt (hU.mem_nhds hz)).fderiv_right (by simp)).contDiffWithinAt
 have hwvec : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : Euclidean n => fderiv ℝ f (0,x) (1,0)) A :=
   (hdf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)).clm_apply contDiffOn_const
 refine ⟨hA,hpu,?_,?_⟩
 · intro i
   exact (ContinuousLinearMap.proj (R := ℝ) i).contDiff.comp_contDiffOn hwvec
 · intro i
   have hccont : ContinuousAt (fun q : M => (c q).val) p :=
     continuous_subtype_val.continuousAt.comp (c.continuousAt hpc)
   filter_upwards [c.open_source.mem_nhds hpc,
      hccont.preimage_mem_nhds (hA.mem_nhds hpu)] with q hqc hqA
   obtain ⟨hqd,hvel⟩ := variationVelocity_in_coordinates
      Q c d hd U f hU hf heq q hqc hqA
   have hbase : Q.map 0 q ∈ (tangentBundle T).baseSet idx :=
     (tangentRealization T).baseSet idx ▸ hqd
   rw [SmoothManifolds.FrameData.totalize_of_mem _ q hbase,
       P202.Geometry.LeviCivita.trivializationFrame_coordinates,hV q]
   change fderiv ℝ f (0,(c q).val) (1,0) i =
      ((tangentBundle T).fiberCoordinates idx (Q.map 0 q) hbase (variationVelocity Q q)) i
   rw [tangent_coordinates_eq idx (Q.map 0 q) hbase hqd,hvel]



theorem induced_metric_hasDerivAt
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
    (K : Connection (tangentBundle T)) (hK : IsLeviCivita h K)
    (P : PullbackBundle (tangentBundle T) S (Q.map 0)) :
    letI := P.space.topology
    ∀ (D : Connection P.space.bundle)
      (hD : P202.PullbackData.IsPullback (tangentBundle T) K (Q.map 0)
        (initialImmersion Q).smooth P D)
      (V : Section P.space.bundle) (hV : ∀ q, V.val q = variationVelocity Q q)
      (p : M) (v w : TangentSpace S p),
    HasDerivAt (fun t => pairing (g t) p v w)
      (pairing h (Q.map 0 p) (pointDerivative D V.val p v)
        ((initialImmersion Q).differential p w) +
      pairing h (Q.map 0 p) ((initialImmersion Q).differential p v)
        (pointDerivative D V.val p w)) 0 := by
  letI := P.space.topology
  intro D hD V hV p v w
  obtain ⟨c, hc, d, hd, hpc, hpd, U, f, hU, h0, hf, heq⟩ :=
    Q.joint_smooth 0 Q.zero_mem p
  let idx : TangentIndex T := ⟨d, hd⟩
  have hbase : Q.map 0 p ∈ (tangentBundle T).baseSet idx :=
    (tangentRealization T).baseSet idx ▸ hpd
  let E := (tangentBundle T).fiberCoordinates idx (Q.map 0 p) hbase
  let L := (tangentStructure S).fiberCoordinates.equiv c hc p hpc
  let Wvec : Euclidean n → Euclidean m := fun y => fderiv ℝ f (0, y) (1, 0)
  have hf0 : ContDiffAt ℝ (⊤ : ℕ∞) f (0, (c p).val) :=
    hf.contDiffAt (hU.mem_nhds h0)
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) (0, (c p).val) :=
    (hf0.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hWdif : DifferentiableAt ℝ Wvec (c p).val := by
    exact ((hdf.comp (c p).val (differentiableAt_const (0 : ℝ) |>.prodMk differentiableAt_id)).clm_apply
      (differentiableAt_const (1, (0 : Euclidean n))))
  let A := E.symm (fderiv ℝ Wvec (c p).val (L v))
  let B := E.symm (fderiv ℝ Wvec (c p).val (L w))
  obtain ⟨R, H, hR, hpR, hH, heH⟩ := metric_matrix_chart_extension h idx (Q.map 0 p) hpd
  have hfval : f (0, (c p).val) = (d (Q.map 0 p)).val := by
    simpa only [c.left_inv hpc] using
      (heq 0 Q.zero_mem (c p) h0 (c.map_source hpc)).2
  obtain ⟨hpd', hdifferential⟩ := variation_differential_in_coordinates
    Q c hc d hd U f hU hf heq 0 Q.zero_mem p hpc h0
  have hE := tangent_coordinates_eq idx (Q.map 0 p) hbase hpd
  have hdiff (z : TangentSpace S p) :
      fderiv ℝ f (0, (c p).val) (0, L z) = E ((initialImmersion Q).differential p z) := by
    exact ((congrArg (fun J => J ((initialImmersion Q).differential p z)) hE).trans
      (hdifferential z)).symm
  obtain ⟨hpd'', hvelocity⟩ := variationVelocity_in_coordinates Q c d hd U f hU hf heq p hpc h0
  have hvel : fderiv ℝ f (0, (c p).val) (1, 0) = E (V.val p) := by
    change _ = (tangentBundle T).fiberCoordinates idx (Q.map 0 p) hbase (V.val p)
    rw [hE, hV p]
    exact hvelocity.symm
  have hAvec : fderiv ℝ Wvec (c p).val (L v) = E A :=
    (E.apply_symm_apply _).symm
  have hBvec : fderiv ℝ Wvec (c p).val (L w) = E B :=
    (E.apply_symm_apply _).symm
  have hchart := hasDerivAt_metric_of_chart_data h K hK idx (Q.map 0 p) hbase
    f 0 (c p).val (L v) (L w) hf0 H R hR hpR hH heH hfval
    ((initialImmersion Q).differential p v) ((initialImmersion Q).differential p w)
    (V.val p) A B (hdiff v) (hdiff w) hvel hAvec hBvec
  have hpair := induced_pairing_eq_chart_gram_eventually Q h g hg c hc d hd U f hU hf heq
    p hpc h0 H heH v w
  have hactual := hchart.congr_of_eventuallyEq hpair
  let Cset : Set (Euclidean n) := (fun x => ((0 : ℝ), x)) ⁻¹' U
  let wi : Fin m → Euclidean n → ℝ := fun i x => Wvec x i
  obtain ⟨hCset, hpCset, hwi, heV⟩ := variation_velocity_frame_chart_data
    Q c hc d hd U f hU hf heq p hpc h0 P V hV
  have hcanonical : SmoothManifolds.differential S T (Q.map 0)
      (initialImmersion Q).smooth p = (initialImmersion Q).differential p :=
    ((SmoothManifolds.differential_exists S T (Q.map 0) (initialImmersion Q).smooth p).unique
      ((initialImmersion Q).isDifferential p)
      (SmoothManifolds.differential_spec S T (Q.map 0) (initialImmersion Q).smooth p)).symm
  have hcov (z : TangentSpace S p) : pointDerivative D V.val p z =
      E.symm (fderiv ℝ Wvec (c p).val (L z)) +
        coordinateCorrection K idx (Q.map 0 p) hbase
          ((initialImmersion Q).differential p z) (V.val p) := by
    have ht := pullback_derivative_vector_chart (Q.map 0) (initialImmersion Q).smooth
      K P D hD idx V p hbase c hc hpc Cset hCset hpCset wi hwi heV z
    have htuple : (fun i => fderiv ℝ (wi i) (c p).val (L z)) =
        fderiv ℝ Wvec (c p).val (L z) := by
      funext i
      exact fderiv_component_apply Wvec (c p).val (L z) hWdif i
    rw [htuple, hcanonical] at ht
    exact ht
  change HasDerivAt (fun t => pairing (g t) p v w)
    (pairing h (Q.map 0 p)
      (E.symm (fderiv ℝ Wvec (c p).val (L v)) + coordinateCorrection K idx (Q.map 0 p) hbase
        ((initialImmersion Q).differential p v) (V.val p))
      ((initialImmersion Q).differential p w) +
    pairing h (Q.map 0 p) ((initialImmersion Q).differential p v)
      (E.symm (fderiv ℝ Wvec (c p).val (L w)) + coordinateCorrection K idx (Q.map 0 p) hbase
        ((initialImmersion Q).differential p w) (V.val p))) 0 at hactual
  rw [← hcov v, ← hcov w] at hactual
  exact hactual

end MetricCompatibility

end InducedMetricDerivative

-- Insert inside current P202.Geometry.VolumeFirstVariation namespace after source parameter regularity and root volume reducers.
section SupportedAssembly
open Set Filter SmoothManifolds.MapData
  SmoothManifolds.DensityIntegrationData SmoothManifolds.BoundaryData
  P202.LeviCivitaData P202.GreenData
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}

theorem supported_first_variation_of_local_density_and_parameter_regularity
    (Q : SmoothVariation S T) (h : RiemannianMetric T)
    (g : ℝ → RiemannianMetric S) (hg : InducedMetrics Q h g)
    (hQ : CompactlySupportedVariation Q)
    (C : Connection (tangentBundle S)) (K : Connection (tangentBundle T))
    (hC : IsLeviCivita (g 0) C) (hK : IsLeviCivita h K)
    (B : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace S p →ₗ[ℝ] TangentSpace T (Q.map 0 p))
    (hB : IsSecondFundamentalForm h (Q.map 0) (initialImmersion Q) C K B)
    (W : Field S) (ξ : (p : M) → TangentSpace T (Q.map 0 p))
    (hdec : VariationDecomposition Q h W ξ)
    (hloc : LocalDensityVariation Q h g C B W ξ)
    (hderFam : ∀ s ∈ Q.domain, ∀ p : M,
      HasDerivAt (fun t => densityRatio (g 0) (P202.VolumeData.density (g t)) p)
        (deriv (fun t => densityRatio (g 0) (P202.VolumeData.density (g t)) p) s) s)
    (hcontFam : ∀ s ∈ Q.domain, ∀ p : M,
      ContinuousAt (fun z : ℝ × M =>
        deriv (fun t => densityRatio (g 0) (P202.VolumeData.density (g t)) z.2) z.1) (s,p))
    (bnd : BoundaryGeometry (g 0)) :
    ∃ (f : C_c(M, ℝ)) (q : C_c(intrinsicBoundary S, ℝ)),
      (∀ p, f p = normalIntegrand Q h (g 0) B ξ p) ∧
      (∀ p, q p = flux (g 0) bnd W p) ∧
      HasDerivAt (localVolumeChange g)
        (-P202.VolumeData.integral (g 0) f + P202.VolumeData.integral bnd.metric q) 0 := by
  letI := S.topologicalManifold.hausdorff
  obtain ⟨L, hL, hmap⟩ := hQ
  have hdensity : ∀ᶠ s in 𝓝 (0 : ℝ),
      s ∈ Q.domain ∧
      (∃ ρ : CompactDensity S,
        ρ.field = fun p => P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p) ∧
      ∀ p ∉ L, P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p = 0 := by
    filter_upwards [hmap, density_difference_compact Q h g hg ⟨L, hL, hmap⟩] with s hs hcompact
    refine ⟨hs.1, hcompact, ?_⟩
    intro p hp
    apply sub_eq_zero.mpr
    apply density_eq_of_pairing_eq
    intro v w
    rw [hg s hs.1 p v w, hg 0 Q.zero_mem p v w]
    apply pullback_pairing_congr (initialImmersion Q).smooth h _ _
      ((Q.immersion s hs.1).isDifferential p) ((initialImmersion Q).isDifferential p)
    filter_upwards [hL.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hs.2 q hq
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hdensity
  let ε : ℝ := δ / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hsmall : ∀ s ∈ Icc (-ε) ε,
      s ∈ Q.domain ∧
      (∃ ρ : CompactDensity S,
        ρ.field = fun p => P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p) ∧
      ∀ p ∉ L, P202.VolumeData.density (g s) p - P202.VolumeData.density (g 0) p = 0 := by
    intro s hs
    apply hδsub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    dsimp only [ε] at hs
    constructor <;> linarith [hs.1, hs.2]
  let F' : ℝ → M → ℝ := fun s p =>
    deriv (fun t => densityRatio (g 0) (P202.VolumeData.density (g t)) p) s
  have hder : ∀ p s, s ∈ Ioo (-ε) ε →
      HasDerivAt (fun t => densityRatio (g 0)
        (fun q => P202.VolumeData.density (g t) q - P202.VolumeData.density (g 0) q) p)
        (F' s p) s := by
    intro p s hs
    change HasDerivAt (fun t => densityRatio (g 0)
      (P202.VolumeData.density (g t) - P202.VolumeData.density (g 0)) p) (F' s p) s
    simpa only [densityRatio_sub, sub_zero, Pi.sub_apply] using
      (hderFam s (hsmall s ⟨hs.1.le, hs.2.le⟩).1 p).fun_sub
        (hasDerivAt_const s (densityRatio (g 0) (P202.VolumeData.density (g 0)) p))
  have hF' : ContinuousOn (Function.uncurry F') (Icc (-ε) ε ×ˢ L) := by
    intro z hz
    exact (hcontFam z.1 (hsmall z.1 hz.1).1 z.2).continuousWithinAt
  have hF₀ : Continuous (fun p => F' 0 p) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (hcontFam 0 Q.zero_mem p).comp (continuousAt_const.prodMk continuousAt_id)
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have hFzero : ∀ p ∉ L, F' 0 p = 0 := by
    intro p hp
    have he : (fun t => densityRatio (g 0)
        (fun q => P202.VolumeData.density (g t) q - P202.VolumeData.density (g 0) q) p) =ᶠ[𝓝 (0 : ℝ)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds h0] with t ht
      simp only [densityRatio, (hsmall t ⟨ht.1.le, ht.2.le⟩).2.2 p hp, map_zero, zero_div]
    exact ((hder p 0 h0).congr_of_eventuallyEq he.symm).unique (hasDerivAt_const 0 0)
  let r : C_c(M, ℝ) := ⟨⟨fun p => F' 0 p, hF₀⟩, by
    apply hL.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hL.isClosed
    intro p hp
    by_contra hn
    exact hp (hFzero p hn)⟩
  have hr : ∀ p, r p = divergence C W p - normalIntegrand Q h (g 0) B ξ p := by
    intro p
    exact (hder p 0 h0).unique (densityRatio_variation_hasDerivAt Q h g C B W ξ hloc p)
  have hd := localVolumeChange_hasDerivAt_of_parameter_data g r F' L hL ε hε
    (fun s hs => (hsmall s ⟨hs.1.le, hs.2.le⟩).2.1)
    (fun s hs => (hsmall s ⟨hs.1.le, hs.2.le⟩).2.2)
    hF' (fun _ => rfl) hder
  exact first_variation_from_integrated_density (g 0) C hC bnd W
    (decomposition_compact_support Q h g hg ⟨L, hL, hmap⟩ W ξ hdec)
    (normalIntegrand Q h (g 0) B ξ) r hr (localVolumeChange g) hd
end SupportedAssembly

theorem supported_first_variation_of_local_density :
    P202Specs.Geometry.VolumeFirstVariation.local_densityType.{u} →
      P202Specs.Geometry.VolumeFirstVariation.supported_first_variationType.{u} := by
  intro hloc n m a b M N _ _ S T Q h g hg hQ C K hC hK B hB W ξ hdec bnd
  exact supported_first_variation_of_local_density_and_parameter_regularity
    Q h g hg hQ C K hC hK B hB W ξ hdec
    (hloc Q h g hg C K hC hK B hB W ξ hdec)
    (fun s hs p => variation_densityRatio_hasDerivAt Q h g hg (g 0) s hs p)
    (fun s hs p => variation_densityRatio_deriv_continuousAt Q h g hg (g 0) s hs p) bnd

/-- The intrinsic density first variation of Proposition 7.7. -/
theorem local_density :
    P202Specs.Geometry.VolumeFirstVariation.local_densityType.{u} := by
  intro n m a b M N _ _ S T Q h g hg C K hC hK B hB W ξ hdec
  obtain ⟨P, D, V, hD, hV, hpair⟩ :=
    variation_pointDerivative_pairing Q h g hg C K hK B hB W ξ hdec
  letI := P.space.topology
  apply local_density_of_pairing_derivative Q h g C B W ξ
  intro p v w
  have hd := induced_metric_hasDerivAt Q h g hg K hK P D hD V hV p v w
  have hs : pairing h (Q.map 0 p) ((initialImmersion Q).differential p v)
      (pointDerivative D V.val p w) =
      pairing h (Q.map 0 p) (pointDerivative D V.val p w)
        ((initialImmersion Q).differential p v) := h.symmetric _ _ _
  rw [hs, hpair p v w, hpair p w v] at hd
  have hsg : pairing (g 0) p (pointDerivative C W.val p w) v =
      pairing (g 0) p v (pointDerivative C W.val p w) := (g 0).symmetric _ _ _
  rw [hsg] at hd
  convert hd using 1
  ring

/-- Compact support requires no finiteness assumption on total volume. Only
flux across the original intrinsic boundary occurs. -/
theorem supported_first_variation :
    P202Specs.Geometry.VolumeFirstVariation.supported_first_variationType.{u} :=
  supported_first_variation_of_local_density local_density

/-- First variation of total volume on a compact source, with its actual
smooth boundary, arbitrary codimension and no orientation assumption. -/
theorem compact_first_variation :
    P202Specs.Geometry.VolumeFirstVariation.compact_first_variationType.{u} :=
  compact_first_variation_of_supported supported_first_variation

end P202.Geometry.VolumeFirstVariation
