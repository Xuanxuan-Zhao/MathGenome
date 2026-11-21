import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ConvexNormalNeighborhoods
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.NormalMinimality
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ExponentialNormalCoordinates
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LocalCurveTrapping
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! The full Gauss lemma and convex normal neighborhood theorem (Theorem 6.9).
The uniform endpoint inverse yields normal charts on a common radius, global
minimizing affine segments, joint smoothness, and smooth squared distance.
Small coordinate-square sublevels give arbitrarily small convex neighborhoods.
All constructions use the original tangent bundle, metric, and geodesic flow. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace P202.Geometry.ConvexNormalNeighborhoods
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.MaximalFlowData
  SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.CurveData P202.GeodesicData
  P202.LeviCivitaData P202.ExponentialData P202.DistanceData
  P202.ConvexNormalData
open Set Filter
open scoped Topology
universe u v

section Topology
variable {X : Type u} [TopologicalSpace X]

/-- A neighborhood of a diagonal point contains a product of the same open
neighborhood with itself. This is the base shrinking used after the IFT. -/
theorem diagonal_product_neighborhood {p : X} {W : Set (X × X)}
    (hW : W ∈ 𝓝 (p, p)) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ×ˢ V ⊆ W := by
  obtain ⟨A, B, hA, hpA, hB, hpB, hAB⟩ := mem_nhds_prod_iff'.mp hW
  refine ⟨A ∩ B, hA.inter hB, ⟨hpA, hpB⟩, ?_⟩
  intro x hx
  exact hAB ⟨hx.1.1, hx.2.2⟩

/-- Shrinking can simultaneously stay in a prescribed neighborhood and
make a continuous scalar quantity of the inverse uniformly small. -/
theorem diagonal_product_shrink {p : X} {W : Set (X × X)}
    (hW : W ∈ 𝓝 (p, p)) {f : X × X → ℝ}
    (hf : ContinuousAt f (p, p)) {δ : ℝ} (hδ : f (p, p) < δ)
    {O : Set X} (hO : O ∈ 𝓝 p) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ V ⊆ O ∧
      V ×ˢ V ⊆ W ∧ ∀ q ∈ V, ∀ z ∈ V, f (q, z) < δ := by
  have hsmall : {x | f x < δ} ∈ 𝓝 (p, p) :=
    hf.preimage_mem_nhds (isOpen_Iio.mem_nhds hδ)
  have hprod : O ×ˢ O ∈ 𝓝 (p, p) := prod_mem_nhds hO hO
  obtain ⟨V, hV, hpV, hsub⟩ :=
    diagonal_product_neighborhood (inter_mem (inter_mem hW hsmall) hprod)
  refine ⟨V, hV, hpV, ?_, ?_, ?_⟩
  · intro q hq
    exact (hsub (show (q, p) ∈ V ×ˢ V from ⟨hq, hpV⟩)).2.1
  · intro x hx
    exact (hsub hx).1.1
  · intro q hq z hz
    exact (hsub ⟨hq, hz⟩).1.2

end Topology

section Linear
variable (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The differential of the endpoint map at a zero vector in bundle
coordinates. Its inverse sends (a,b) to (a,b-a), including in dimension zero. -/
def endpointShear : (E × E) ≃L[ℝ] E × E where
  toFun x := (x.1, x.1 + x.2)
  invFun x := (x.1, x.2 - x.1)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp; abel
  map_smul' c x := by ext <;> simp [smul_add]
  continuous_toFun := continuous_fst.prodMk (continuous_fst.add continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_fst)

/-- The zero-section identity and the fiber derivative determine the full
first derivative of the exponential in bundle coordinates. -/
theorem derivative_from_zero_section_and_fiber
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E × E → E} {a : E}
    (hf : DifferentiableAt ℝ f (a, 0))
    (hzero : (fun x => f (x, 0)) =ᶠ[𝓝 a] (fun x => x))
    (hfiber : HasFDerivAt (fun y => f (a, y)) (ContinuousLinearMap.id ℝ E) 0) :
    HasFDerivAt f (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) (a, 0) := by
  let L := fderiv ℝ f (a, 0)
  have hleft : HasFDerivAt (fun x => f (x, 0))
      (L.comp ((ContinuousLinearMap.id ℝ E).prod 0)) a :=
    hf.hasFDerivAt.comp a ((hasFDerivAt_id a).prodMk (hasFDerivAt_const (0 : E) a))
  have hright : HasFDerivAt (fun y => f (a, y))
      (L.comp ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))) 0 :=
    hf.hasFDerivAt.comp 0 ((hasFDerivAt_const a (0 : E)).prodMk (hasFDerivAt_id (0 : E)))
  have hl : L.comp ((ContinuousLinearMap.id ℝ E).prod 0) = ContinuousLinearMap.id ℝ E :=
    (hleft.congr_of_eventuallyEq hzero.symm).unique (hasFDerivAt_id a)
  have hr : L.comp ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) =
      ContinuousLinearMap.id ℝ E := hright.unique hfiber
  have hL : L = ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E := by
    apply ContinuousLinearMap.ext
    intro x
    have hx : L (x.1, 0) = x.1 := congrArg (fun A : E →L[ℝ] E => A x.1) hl
    have hy : L (0, x.2) = x.2 := congrArg (fun A : E →L[ℝ] E => A x.2) hr
    calc
      L x = L ((x.1, 0) + (0, x.2)) := by congr 1; ext <;> simp
      _ = L (x.1, 0) + L (0, x.2) := map_add L _ _
      _ = x.1 + x.2 := by rw [hx, hy]
      _ = _ := rfl
  rw [← hL]
  exact hf.hasFDerivAt

end Linear

/-- Coordinate IFT with a fixed open smoothness domain. Both smoothness
claims concern the original atlases, and the source stays in the prescribed
open domain of the actual map. -/
theorem local_inverse_from_coordinates
    {k l : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {A : Set (ModelChart k .euclidean X)} {B : Set (ModelChart l .euclidean Y)}
    (hA : IsContDiffAtlas (⊤ : ℕ∞) A) (hB : IsContDiffAtlas (⊤ : ℕ∞) B)
    (f : X → Y) (p : X) (O : Set X) (hO : IsOpen O) (hpO : p ∈ O)
    (e : ModelChart k .euclidean X) (he : e ∈ A) (hp : p ∈ e.source)
    (d : ModelChart l .euclidean Y) (hd : d ∈ B) (hfp : f p ∈ d.source)
    (hfc : ContinuousAt f p)
    (G : Euclidean k → Euclidean l) (W : Set (Euclidean k))
    (hW : IsOpen W) (hpW : (e p).val ∈ W)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G W)
    (L : Euclidean k ≃L[ℝ] Euclidean l)
    (hL : HasFDerivAt G L.toContinuousLinearMap (e p).val)
    (hgerm : (fun x => G (e x).val) =ᶠ[𝓝 p] (fun x => (d (f x)).val)) :
    ∃ h : OpenPartialHomeomorph X Y,
      p ∈ h.source ∧ h.source ⊆ O ∧ EqOn h f h.source ∧
      ManifoldSmoothOn A B h h.source ∧ ManifoldSmoothOn B A h.symm h.target := by
  obtain ⟨j, hpj, hj, hji⟩ := SmoothManifolds.InteriorInverse.euclidean_inverse
    (⊤ : ℕ∞) (by simp) G W hW hG (e p).val hpW L hL L.bijective
  let E := SmoothManifolds.InteriorInverse.ambientChart e
  let D := SmoothManifolds.InteriorInverse.ambientChart d
  have hpE : p ∈ E.source := by
    change p ∈ e.source ∩ (fun x => (e x).val) ⁻¹' interior (modelSet k .euclidean)
    exact ⟨hp, by simp [modelSet]⟩
  have hfpD : f p ∈ D.source := by
    change f p ∈ d.source ∩ (fun y => (d y).val) ⁻¹' interior (modelSet l .euclidean)
    exact ⟨hfp, by simp [modelSet]⟩
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp
    (inter_mem hgerm (inter_mem
      (hfc.preimage_mem_nhds (D.open_source.mem_nhds hfpD)) (hO.mem_nhds hpO)))
  let j' := j.restrOpen W hW
  let h₀ := (E.trans j').trans D.symm
  let h := h₀.restrOpen V hV
  have hjp : j' (E p) = D (f p) := by
    change j (e p).val = (d (f p)).val
    rw [hj]
    exact hgerm.eq_of_nhds
  have hph₀ : p ∈ h₀.source := by
    refine ⟨⟨hpE, hpj, hpW⟩, ?_⟩
    change j' (E p) ∈ D.target
    rw [hjp]
    exact D.map_source hfpD
  have hforward : EqOn h f h.source := by
    intro x hx
    have hxV := hVsub hx.2
    change D.symm (j (E x)) = f x
    have hgx : j (E x) = D (f x) := by
      change j (e x).val = (d (f x)).val
      rw [hj]
      exact hxV.1
    rw [hgx, D.left_inv hxV.2.1]
  refine ⟨h, ⟨hph₀, hpV⟩, (fun x hx => (hVsub hx.2).2.2), hforward, ?_, ?_⟩
  · intro x hx
    apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) A B hA hB h x).mpr
    have hxt := h.map_source hx
    refine ⟨h.continuousAt hx, e, he, d, hd, hx.1.1.1.1, hxt.1.1.1, ?_⟩
    refine ⟨W, hW, hx.1.1.2.2, G, hG, ?_⟩
    filter_upwards [h.open_source.mem_nhds hx] with z hz
    have hzD : j' (E z) ∈ D.target := hz.1.2
    change G (e z).val = D (D.symm (j' (E z)))
    rw [D.right_inv hzD]
    exact congrFun hj (e z).val |>.symm
  · intro y hy
    apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) B A hB hA h.symm y).mpr
    have hsy := h.map_target hy
    refine ⟨h.symm.continuousAt hy, d, hd, e, he, hy.1.1.1, hsy.1.1.1.1, ?_⟩
    refine ⟨j.target, j.open_target, hy.1.2.1.1, j.symm, hji, ?_⟩
    filter_upwards [h.open_target.mem_nhds hy] with z hz
    have hzE : j'.symm (D z) ∈ E.target := hz.1.2.2
    change j.symm (d z).val = E (E.symm (j.symm (D z)))
    exact (E.right_inv hzE).symm

section Geometry
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem squaredDistance_component (g : RiemannianMetric S) (p : M)
    (q z : connectedComponent p) :
    squaredDistance S g (q.val, z.val) = componentDistance g p q z ^ 2 := rfl

theorem endpointMap_zero (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M) :
    endpointMap S F ⟨p, 0⟩ = (p, p) := by
  exact Prod.ext rfl (ExponentialNormalCoordinates.zero_section_at C F hF p).2

/-- The first component of a local logarithm is forced to be its first
endpoint, by the actual inverse law. -/
theorem inverse_base (F : CurveFamily (Phase S))
    (h : OpenPartialHomeomorph (Phase S) (M × M))
    (heq : EqOn h (endpointMap S F) h.source) {x : M × M}
    (hx : x ∈ h.target) : (h.symm x).1 = x.1 := by
  have hright := h.right_inv hx
  rw [heq (h.map_target hx)] at hright
  exact congrArg Prod.fst hright

theorem inverse_diagonal (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (h : OpenPartialHomeomorph (Phase S) (M × M))
    (heq : EqOn h (endpointMap S F) h.source)
    (q : M) (hq : (⟨q, 0⟩ : Phase S) ∈ h.source) :
    h.symm (q, q) = (⟨q, 0⟩ : Phase S) := by
  have hz : h (⟨q, 0⟩ : Phase S) = (q, q) :=
    (heq hq).trans (endpointMap_zero C F hF q)
  rw [← hz, h.left_inv hq]

/-- The square removes the square-root singularity of the norm at zero. -/
theorem squaredDistance_eq_pairing (g : RiemannianMetric S) (q z : M)
    (v : TangentSpace S q) (hd : sInf (pathLengths g q z) = tangentNorm g q v) :
    squaredDistance S g (q, z) = pairing g q v v := by
  change sInf (pathLengths g q z) ^ 2 = _
  rw [hd, P202.Geometry.SmoothMetrics.tangentNorm_sq]

/-- Squared norm is smooth on the *whole* tangent bundle, including its zero
section. The metric realization maps relate the two original tangent models. -/
theorem squaredNorm_smooth (g : RiemannianMetric S) (w : Phase S) :
    VectorSmoothAt (phaseManifold S).smoothStructure.val
      (fun v : Phase S => pairing g v.1 v.2 v.2) w := by
  exact P202.Geometry.SmoothMetrics.metric_pairing_smoothAt
    (phaseManifold S) (tangentRealization S).space.bundle g
    (fun v : Phase S => v.1) (fun v => v.2) (fun v => v.2) w
    (SmoothManifolds.TangentBundle.projection_smooth S (tangentStructure S) w)
    ((tangentRealization S).smooth_from_original w)
    ((tangentRealization S).smooth_from_original w)

/-- The analytic smoothness step in the squared-distance formula only uses
the smooth logarithm and a locally valid distance identity. It does not
assume differentiability of the norm at the diagonal. -/
theorem squaredDistance_smooth_of_log (g : RiemannianMetric S)
    (L : M × M → Phase S) (x : M × M)
    (hL : ManifoldSmoothAt (endpointAtlas S) (phaseManifold S).smoothStructure.val L x)
    (hd : squaredDistance S g =ᶠ[𝓝 x]
      (fun y => pairing g (L y).1 (L y).2 (L y).2)) :
    VectorSmoothAt (endpointAtlas S) (squaredDistance S g) x := by
  exact ((squaredNorm_smooth g (L x)).comp
    (phaseManifold S).smoothStructure.property.1.1 hL).congr hd.symm

/-- The metric norm is continuous on the whole original tangent bundle. -/
theorem phaseNorm_continuous (g : RiemannianMetric S) :
    Continuous (fun w : Phase S => tangentNorm g w.1 w.2) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  exact Real.continuous_sqrt.continuousAt.comp (squaredNorm_smooth g w).1

/-- An open neighborhood of a zero vector contains closed metric fiber balls
of one fixed radius over an open base neighborhood. The final premise is the
local lower metric bound in the chosen tangent trivialization. -/
theorem uniform_fiber_ball_of_coordinate_bound (g : RiemannianMetric S)
    (p : M) (W : Set (Phase S)) (hW : IsOpen W)
    (hpW : (⟨p, 0⟩ : Phase S) ∈ W)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source)
    (hbound : ∃ C : ℝ, 0 < C ∧ ∃ N : Set M, IsOpen N ∧ p ∈ N ∧ N ⊆ e.source ∧
      ∀ (q : M) (hq : q ∈ e.source) (v : TangentSpace S q), q ∈ N →
        ‖(tangentStructure S).fiberCoordinates.equiv e he q hq v‖ ≤ C * tangentNorm g q v) :
    ∃ (r : ℝ) (N : Set M), 0 < r ∧ IsOpen N ∧ p ∈ N ∧
      ∀ q ∈ N, ∀ v : TangentSpace S q, tangentNorm g q v ≤ r →
        (⟨q, v⟩ : Phase S) ∈ W := by
  obtain ⟨H, hH⟩ := SmoothManifolds.TangentBundle.locallyTrivial S (tangentStructure S) e he
  let p₀ : (projection S ⁻¹' e.source) := ⟨⟨p, 0⟩, hp⟩
  have hzero : H p₀ = (⟨p, hp⟩, (0 : Euclidean n)) := by
    apply Prod.ext
    · exact Subtype.ext (hH p₀).1
    · simpa only [p₀, map_zero] using (hH p₀).2
  let K : Set (e.source × Euclidean n) := (fun y => (H.symm y).val) ⁻¹' W
  have hK : IsOpen K := hW.preimage (continuous_subtype_val.comp H.symm.continuous)
  have hpK : (⟨p, hp⟩, (0 : Euclidean n)) ∈ K := by
    change (H.symm (⟨p, hp⟩, 0)).val ∈ W
    rw [← hzero, H.symm_apply_apply]
    exact hpW
  obtain ⟨A, B, hA, hpA, hB, h0B, hAB⟩ := mem_nhds_prod_iff'.mp (hK.mem_nhds hpK)
  obtain ⟨δ, hδ, hδB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds h0B)
  obtain ⟨C, hC, N, hN, hpN, hNe, hbound⟩ := hbound
  let V : Set M := Subtype.val '' A ∩ N
  have hV : IsOpen V := (e.open_source.isOpenMap_subtype_val A hA).inter hN
  have hpV : p ∈ V := ⟨⟨⟨p, hp⟩, hpA, rfl⟩, hpN⟩
  refine ⟨δ / (2 * C), V, div_pos hδ (mul_pos (by norm_num) hC), hV, hpV, ?_⟩
  intro q hq v hv
  have hqe : q ∈ e.source := hNe hq.2
  let E := (tangentStructure S).fiberCoordinates.equiv e he q hqe
  have hEv : ‖E v‖ < δ := by
    have hb := hbound q hqe v hq.2
    have hmul : C * tangentNorm g q v ≤ δ / 2 := by
      calc
        _ ≤ C * (δ / (2 * C)) := mul_le_mul_of_nonneg_left hv hC.le
        _ = δ / 2 := by field_simp
    exact lt_of_le_of_lt (hb.trans hmul) (half_lt_self hδ)
  have hqA : (⟨q, hqe⟩ : e.source) ∈ A := by
    obtain ⟨q', hq', heq⟩ := hq.1
    have hEq : q' = (⟨q, hqe⟩ : e.source) := Subtype.ext heq
    exact hEq ▸ hq'
  have hBv : E v ∈ B := hδB (by simpa only [Metric.mem_ball, dist_zero_right] using hEv)
  let w : projection S ⁻¹' e.source := ⟨⟨q, v⟩, hqe⟩
  have hHw : H w = (⟨q, hqe⟩, E v) := by
    apply Prod.ext
    · exact Subtype.ext (hH w).1
    · exact (hH w).2
  have hKmem := hAB (show (⟨q, hqe⟩, E v) ∈ A ×ˢ B from ⟨hqA, hBv⟩)
  change (H.symm (⟨q, hqe⟩, E v)).val ∈ W at hKmem
  rw [← hHw, H.symm_apply_apply] at hKmem
  exact hKmem

/-- The shrinking step upgrades a local endpoint inverse to the uniform
normal inverse interface once its source contains uniform closed fiber balls. -/
theorem uniform_inverse_of_fiber_ball (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M)
    (h : OpenPartialHomeomorph (Phase S) (M × M))
    (hp0 : (⟨p, 0⟩ : Phase S) ∈ h.source)
    (hz : h (⟨p, 0⟩ : Phase S) = (p, p))
    (hdomain : h.source ⊆ exponentialDomain F)
    (heq : EqOn h (endpointMap S F) h.source)
    (hs : ManifoldSmoothOn (phaseManifold S).smoothStructure.val (endpointAtlas S) h h.source)
    (hi : ManifoldSmoothOn (endpointAtlas S) (phaseManifold S).smoothStructure.val h.symm h.target)
    (hball : ∃ (r : ℝ) (N : Set M), 0 < r ∧ IsOpen N ∧ p ∈ N ∧
      ∀ q ∈ N, ∀ v : TangentSpace S q, tangentNorm g q v ≤ r →
        (⟨q, v⟩ : Phase S) ∈ h.source) :
    UniformExponentialInverse S g F p := by
  obtain ⟨r, N, hr, hN, hpN, hball⟩ := hball
  have hpp : (p, p) ∈ h.target := hz ▸ h.map_source hp0
  let f : M × M → ℝ := fun x => tangentNorm g (h.symm x).1 (h.symm x).2
  have hf : ContinuousAt f (p, p) :=
    (phaseNorm_continuous g).continuousAt.comp (h.symm.continuousAt hpp)
  have hsmall : f (p, p) < r / 2 := by
    have hzero : h.symm (p, p) = (⟨p, 0⟩ : Phase S) := by rw [← hz, h.left_inv hp0]
    dsimp only [f]
    rw [hzero, SmoothMetrics.tangentNorm_zero]
    exact half_pos hr
  obtain ⟨V, hV, hpV, hVN, hVV, hnorm⟩ := diagonal_product_shrink
    (h.open_target.mem_nhds hpp) hf hsmall (hN.mem_nhds hpN)
  refine ⟨r, V, h, hr, hV, hpV, hp0, hdomain, heq, hs, hi, ?_, hVV, ?_⟩
  · intro q hq v hv
    exact hball q (hVN hq) v hv
  · intro q hq z hz
    exact ⟨inverse_base F h heq (hVV ⟨hq, hz⟩), hnorm q hq z hz⟩

/-- The uniform closed-ball step uses the proved local comparison of the
actual metric with the tangent-trivialization norm. -/
theorem uniform_fiber_ball (g : RiemannianMetric S) (p : M)
    (W : Set (Phase S)) (hW : IsOpen W) (hpW : (⟨p, 0⟩ : Phase S) ∈ W) :
    ∃ (r : ℝ) (N : Set M), 0 < r ∧ IsOpen N ∧ p ∈ N ∧
      ∀ q ∈ N, ∀ v : TangentSpace S q, tangentNorm g q v ≤ r →
        (⟨q, v⟩ : Phase S) ∈ W := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  exact uniform_fiber_ball_of_coordinate_bound g p W hW hpW e he hp
    (LocalCurveTrapping.local_coordinate_bound g ⟨e, he⟩ p hp)

/-- All the uniform-radius and inverse-vector estimates follow from a
genuine smooth local inverse of the endpoint map at (p,0). Existence of that
local inverse remains a separate analytic step. -/
theorem uniform_inverse_of_local_inverse (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M)
    (h : OpenPartialHomeomorph (Phase S) (M × M))
    (hp0 : (⟨p, 0⟩ : Phase S) ∈ h.source)
    (hdomain : h.source ⊆ exponentialDomain F)
    (heq : EqOn h (endpointMap S F) h.source)
    (hs : ManifoldSmoothOn (phaseManifold S).smoothStructure.val (endpointAtlas S) h h.source)
    (hi : ManifoldSmoothOn (endpointAtlas S) (phaseManifold S).smoothStructure.val h.symm h.target) :
    UniformExponentialInverse S g F p := by
  apply uniform_inverse_of_fiber_ball g F p h hp0
    ((heq hp0).trans (endpointMap_zero C F hF p)) hdomain heq hs hi
  exact uniform_fiber_ball g p h.source h.open_source hp0

/-- A smooth local coordinate representative of the actual endpoint map,
with its full zero-section differential, rather than just its fiber derivative. -/
theorem endpoint_coordinate_differential (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source) :
    let b := (tangentStructure S).chart e he
    let A := (tangentStructure S).productCoordinates.linearEquiv
    let a := (e p).val
    ∃ K : (Euclidean n × Euclidean n) → (Euclidean n × Euclidean n),
      ContDiffAt ℝ (⊤ : ℕ∞) K (a, 0) ∧
      (∃ W : Set (Euclidean n × Euclidean n),
        IsOpen W ∧ (a, 0) ∈ W ∧ ContDiffOn ℝ (⊤ : ℕ∞) K W) ∧
      HasFDerivAt K (endpointShear (Euclidean n)).toContinuousLinearMap (a, 0) ∧
      K (a, 0) = (a, a) ∧
      (fun w : Phase S => K (A.symm (b w).val)) =ᶠ[𝓝 (⟨p, 0⟩ : Phase S)]
        (fun w => ((e w.1).val, (e (exponential F w)).val)) := by
  dsimp only
  let B := tangentStructure S
  let b := B.chart e he
  let A := B.productCoordinates.linearEquiv
  let a := (e p).val
  let w₀ : Phase S := ⟨p, 0⟩
  have hw : w₀ ∈ b.source := by
    simpa only [b, B.chart_source, mem_preimage, projection, w₀] using hp
  have hb := SmoothManifolds.TangentBundle.chart_mem S B e he
  have hb0 : (b w₀).val = A (a, 0) := by
    change ((B.chart e he) w₀).val = _
    rw [B.chart_apply e he w₀ hp]
    simp only [w₀, map_zero]
    rfl
  have hexp0 : exponential F w₀ = p :=
    (ExponentialNormalCoordinates.zero_section_at C F hF p).2
  obtain ⟨U, hU, hwU, H, hH, heq⟩ :=
    (ExponentialNormalCoordinates.exponential_smooth C F hF w₀
      (ExponentialNormalCoordinates.zero_section_at C F hF p).1).2 b hb e he hw
      (by rw [hexp0]; exact hp)
  let f : Euclidean n × Euclidean n → Euclidean n := fun x => H (A x)
  have haU : A (a, 0) ∈ U := hb0 ▸ hwU
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) f (a, 0) :=
    (hH.contDiffAt (hU.mem_nhds haU)).comp (a, 0) A.contDiff.contDiffAt
  have hzero : (fun x => f (x, 0)) =ᶠ[𝓝 a] (fun x => x) := by
    let j : Euclidean n → M := fun x => e.symm ⟨x, mem_univ _⟩
    have hja : j a = p := e.left_inv hp
    have hj : ContinuousAt j a := by
      have h := (e.symm.continuousAt (e.map_source hp)).comp
        (f := fun x : Euclidean n => (⟨x, mem_univ _⟩ : ModelSpace n .euclidean))
        (show ContinuousAt (fun x : Euclidean n => (⟨x, mem_univ _⟩ : ModelSpace n .euclidean)) a from
          tendsto_subtype_rng.mpr continuousAt_id)
      exact h
    let z : Euclidean n → Phase S := fun x => ⟨j x, 0⟩
    have hz : ContinuousAt z a := by
      have hh := (SmoothManifolds.TangentBundle.zero_smooth S B p).1
      have hh' := hh.comp_of_eq hj hja
      exact hh'
    have hza : z a = w₀ := by change (⟨j a, 0⟩ : Phase S) = ⟨p, 0⟩; rw [hja]
    have hz' : Tendsto z (𝓝 a) (𝓝 w₀) := by
      have hh := hz.tendsto
      rwa [hza] at hh
    have hh := heq.comp_tendsto hz'
    have htarget : ∀ᶠ x in 𝓝 a, (⟨x, mem_univ _⟩ : ModelSpace n .euclidean) ∈ e.target :=
      (show ContinuousAt (fun x : Euclidean n => (⟨x, mem_univ _⟩ : ModelSpace n .euclidean)) a from
        tendsto_subtype_rng.mpr continuousAt_id).preimage_mem_nhds
        (e.open_target.mem_nhds (e.map_source hp))
    filter_upwards [hh, htarget] with x hx hxt
    have hjx : j x ∈ e.source := e.map_target hxt
    have hjcoords : (e (j x)).val = x := congrArg Subtype.val (e.right_inv hxt)
    have hzcoords : (b (z x)).val = A (x, 0) := by
      change ((B.chart e he) (z x)).val = _
      rw [B.chart_apply e he (z x) hjx]
      change B.productCoordinates.linearEquiv ((e (j x)).val, B.fiberCoordinates.equiv e he (j x) hjx 0) = _
      rw [map_zero, hjcoords]
    have hexp : exponential F (z x) = j x :=
      (ExponentialNormalCoordinates.zero_section_at C F hF (j x)).2
    change H (A (x, 0)) = x
    dsimp only [Function.comp_def] at hx
    rw [← hzcoords, hx, hexp, hjcoords]
  have hfiber : HasFDerivAt (fun y => f (a, y))
      (ContinuousLinearMap.id ℝ (Euclidean n)) 0 := by
    let E := B.fiberCoordinates.equiv e he p hp
    have hcont := ExponentialNormalCoordinates.fiberInclusion_continuousAt p e he hp (0 : Euclidean n)
    have hcont' : Tendsto (fun y : Euclidean n => (⟨p, E.symm y⟩ : Phase S)) (𝓝 0) (𝓝 w₀) := by
      simpa only [map_zero, w₀, E, B] using hcont.tendsto
    have hh := heq.comp_tendsto hcont'
    have hEq : (fun y => f (a, y)) =ᶠ[𝓝 0]
        (fun y => (e (fiberExponential F p (E.symm y))).val) := by
      simpa only [Function.comp_def, f, a, A, b, E, B,
        ExponentialNormalCoordinates.fiberInclusion_chart p e he hp,
        fiberExponential] using hh
    exact (ExponentialNormalCoordinates.derivative_zero_at C F hF p e he hp).congr_of_eventuallyEq hEq
  have hd := derivative_from_zero_section_and_fiber (hf.differentiableAt (by simp)) hzero hfiber
  let K : (Euclidean n × Euclidean n) → (Euclidean n × Euclidean n) := fun x => (x.1, f x)
  have hK : HasFDerivAt K (endpointShear (Euclidean n)).toContinuousLinearMap (a, 0) := by
    have hlin : (endpointShear (Euclidean n)).toContinuousLinearMap =
        (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n)).prod
          (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n) +
            ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)) := by
      apply ContinuousLinearMap.ext
      intro x
      rfl
    rw [hlin]
    exact (hasFDerivAt_fst (𝕜 := ℝ) (p := (a, (0 : Euclidean n)))).prodMk hd
  refine ⟨K, contDiffAt_fst.prodMk hf, ?_, hK, ?_, ?_⟩
  · refine ⟨A ⁻¹' U, hU.preimage A.continuous, haU, ?_⟩
    exact contDiffOn_fst.prodMk (hH.comp A.contDiff.contDiffOn (fun _ hx => hx))
  · change (a, f (a, 0)) = (a, a)
    rw [hzero.eq_of_nhds]
  · filter_upwards [heq, b.open_source.mem_nhds hw] with w hwH hwb
    have hwe : w.1 ∈ e.source := by
      simpa only [b, B.chart_source, mem_preimage, projection] using hwb
    have hcoords := B.chart_apply e he w hwe
    change (b w).val = A ((e w.1).val, B.fiberCoordinates.equiv e he w.1 hwe w.2) at hcoords
    apply Prod.ext
    · change (A.symm (b w).val).1 = (e w.1).val
      rw [hcoords, A.symm_apply_apply]
    · change H (A (A.symm (b w).val)) = (e (exponential F w)).val
      rw [A.apply_symm_apply, hwH]

/-- Uniform invertibility of the endpoint map follows from its full
zero-section derivative and the coordinate inverse function theorem. -/
theorem uniform_inverse :
    P202Specs.Geometry.ConvexNormalNeighborhoods.uniform_inverseType.{u} := by
  intro n M _ S g C F hF p
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let b := (tangentStructure S).chart e he
  let A := (tangentStructure S).productCoordinates.linearEquiv
  let a := (e p).val
  let d := SmoothManifolds.ProductData.productChart
    (tangentStructure S).productCoordinates e e
  let w₀ : Phase S := ⟨p, 0⟩
  have hb : b ∈ (phaseManifold S).smoothStructure.val :=
    SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) e he
  have hw : w₀ ∈ b.source := by
    simpa only [b, (tangentStructure S).chart_source, mem_preimage, projection, w₀] using hp
  have hb0 : (b w₀).val = A (a, 0) := by
    rw [(tangentStructure S).chart_apply e he w₀ hp]
    simp only [w₀, map_zero]
    rfl
  have hd : d ∈ endpointAtlas S := ⟨e, he, e, he, rfl⟩
  have hfd : endpointMap S F w₀ ∈ d.source := by
    rw [endpointMap_zero C F hF p]
    simpa only [d, SmoothManifolds.productChart_source] using
      (show (p,p) ∈ e.source ×ˢ e.source from ⟨hp,hp⟩)
  have hfc : ContinuousAt (endpointMap S F) w₀ :=
    (SmoothManifolds.TangentBundle.projection_smooth S (tangentStructure S) w₀).1.prodMk
      (ExponentialNormalCoordinates.exponential_smooth C F hF w₀
        (ExponentialNormalCoordinates.zero_section_at C F hF p).1).1
  obtain ⟨K, _, ⟨W, hW, haW, hK⟩, hKD, _, hgerm⟩ :=
    endpoint_coordinate_differential C F hF p e he hp
  let G : Euclidean (n + n) → Euclidean (n + n) := fun x => A (K (A.symm x))
  let L := (A.symm.trans (endpointShear (Euclidean n))).trans A
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G (A.symm ⁻¹' W) :=
    A.contDiff.contDiffOn.comp
      (hK.comp A.symm.contDiff.contDiffOn (fun _ hx => hx)) (fun _ _ => mem_univ _)
  have hL : HasFDerivAt G L.toContinuousLinearMap (b w₀).val := by
    rw [hb0]
    have hKD' : HasFDerivAt K (endpointShear (Euclidean n)).toContinuousLinearMap
        (A.symm (A (a,0))) := by
      simpa only [A.symm_apply_apply] using hKD
    have h := A.hasFDerivAt.comp (A (a, 0))
      (hKD'.comp (A (a, 0)) A.symm.hasFDerivAt)
    convert h using 1
    · rfl
    · ext x
      rfl
  have hg : (fun w => G (b w).val) =ᶠ[𝓝 w₀]
      (fun w => (d (endpointMap S F w)).val) := by
    filter_upwards [hgerm] with w hw
    exact congrArg A hw
  have htarget : IsContDiffAtlas (⊤ : ℕ∞) (endpointAtlas S) :=
    SmoothManifolds.productAtlas_isContDiffAtlas _ _ _ _
      S.smoothStructure.property.1 S.smoothStructure.property.1
  obtain ⟨h, hwh, hdom, heq, hs, hi⟩ := local_inverse_from_coordinates
    (phaseManifold S).smoothStructure.property.1 htarget
    (endpointMap S F) w₀ (exponentialDomain F)
    (ExponentialNormalCoordinates.domain_isOpen C F hF)
    (ExponentialNormalCoordinates.zero_section_at C F hF p).1
    b hb hw d hd hfd hfc G (A.symm ⁻¹' W) (hW.preimage A.symm.continuous)
    (by rw [hb0, mem_preimage, A.symm_apply_apply]; exact haW) hG L hL hg
  exact uniform_inverse_of_local_inverse g C F hF p h hwh hdom heq hs hi

end Geometry

section Convexity

/-- The scalar step at the end of the convex-ball proof. Endpoints in a
strict sublevel set keep the entire affine parameter interval in that set. -/
theorem convex_sublevel_segment {f : ℝ → ℝ} (hf : ConvexOn ℝ (Icc 0 1) f)
    {c : ℝ} (h0 : f 0 < c) (h1 : f 1 < c) {t : ℝ} (ht : t ∈ Icc 0 1) :
    f t < c := by
  have hh := hf.2 (by simp : (0 : ℝ) ∈ Icc 0 1)
    (by simp : (1 : ℝ) ∈ Icc 0 1) (sub_nonneg.mpr ht.2) ht.1
    (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at hh
  have hmax : max (f 0) (f 1) < c := max_lt h0 h1
  have hbound : (1 - t) * f 0 + t * f 1 ≤ max (f 0) (f 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (le_max_left (f 0) (f 1))),
      mul_nonneg ht.1 (sub_nonneg.mpr (le_max_right (f 0) (f 1)))]
  exact lt_of_le_of_lt (hh.trans hbound) hmax

theorem sublevel_of_second_derivative {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1))
    (hf' : DifferentiableOn ℝ f (Ioo 0 1))
    (hf'' : DifferentiableOn ℝ (deriv f) (Ioo 0 1))
    (hpos : ∀ t ∈ Ioo 0 1, 0 ≤ deriv (deriv f) t)
    {c : ℝ} (h0 : f 0 < c) (h1 : f 1 < c) {t : ℝ} (ht : t ∈ Icc 0 1) :
    f t < c := by
  apply convex_sublevel_segment (c := c) (t := t) ?_ h0 h1 ht
  apply convexOn_of_deriv2_nonneg (convex_Icc (0 : ℝ) 1) hf
  · simpa only [interior_Icc] using hf'
  · simpa only [interior_Icc] using hf''
  · simpa only [interior_Icc, Function.iterate_succ_apply', Function.iterate_zero_apply]
      using hpos

/-- The triangle inequality traps a short minimizing segment in the larger
ball before convexity of squared distance is applied. -/
theorem short_segment_in_triple_ball {X : Type v} [PseudoMetricSpace X]
    (p q z : X) {ε : ℝ} (hq : dist q p < ε) (hz : dist z p < ε)
    (γ : ℝ → X) (hshort : ∀ t ∈ Icc (0 : ℝ) 1, dist q (γ t) ≤ dist q z) :
    ∀ t ∈ Icc (0 : ℝ) 1, dist (γ t) p < 3 * ε := by
  intro t ht
  have h1 := dist_triangle (γ t) q p
  have h2 := dist_triangle q p z
  have h3 := hshort t ht
  rw [dist_comm (γ t) q] at h1
  rw [dist_comm p z] at h2
  linarith

/-- Convexity of squared distance gives invariance of the smaller ball,
with strict inequalities retained at both endpoints. -/
theorem ball_invariant_of_convex_squared_distance {X : Type v} [PseudoMetricSpace X]
    (p : X) (γ : ℝ → X) {ε : ℝ} (hε : 0 < ε)
    (h0 : dist (γ 0) p < ε) (h1 : dist (γ 1) p < ε)
    (hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => dist (γ t) p ^ 2)) :
    ∀ t ∈ Icc (0 : ℝ) 1, dist (γ t) p < ε := by
  intro t ht
  have hs : dist (γ t) p ^ 2 < ε ^ 2 := by
    apply convex_sublevel_segment hconv (t := t) (c := ε ^ 2) ?_ ?_ ht
    · nlinarith [dist_nonneg (x := γ 0) (y := p)]
    · nlinarith [dist_nonneg (x := γ 1) (y := p)]
  nlinarith [dist_nonneg (x := γ t) (y := p)]

end Convexity

end P202.Geometry.ConvexNormalNeighborhoods


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.ConvexNormalNeighborhoods
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.CurveData P202.GeodesicData
  P202.LeviCivitaData P202.ExponentialData P202.DistanceData
  P202.ConvexNormalData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

def fiberLog (h : OpenPartialHomeomorph (Phase S) (M × M))
    (q : M) (E : TangentSpace S q ≃ₗ[ℝ] Euclidean n)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hq : q ∈ e.source) (z : M) : Euclidean n :=
  let K := (tangentStructure S).fiberCoordinates.equiv e he q hq
  let A := (tangentStructure S).productCoordinates.linearEquiv
  (K.symm.trans E) (A.symm ((tangentStructure S).chart e he (h.symm (q,z))).val).2

theorem fiberLog_reconstruct (F : CurveFamily (Phase S))
    (h : OpenPartialHomeomorph (Phase S) (M × M))
    (heq : EqOn h (endpointMap S F) h.source)
    (q : M) (E : TangentSpace S q ≃ₗ[ℝ] Euclidean n)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hq : q ∈ e.source) (z : M) (hz : (q,z) ∈ h.target) :
    h.symm (q,z) = (⟨q,E.symm (fiberLog h q E e he hq z)⟩ : Phase S) := by
  have hbase := inverse_base F h heq hz
  generalize hw : h.symm (q,z) = w at *
  rcases w with ⟨q',v⟩
  change q' = q at hbase
  subst q'
  dsimp only [fiberLog]
  rw [hw, (tangentStructure S).chart_apply e he ⟨q,v⟩ hq]
  simp only [ContinuousLinearEquiv.symm_apply_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

/-- The fixed-base slice of the smooth endpoint inverse has smooth fiber
coordinates. -/
theorem fiberLog_smooth (F : CurveFamily (Phase S))
    (h : OpenPartialHomeomorph (Phase S) (M × M))
    (heq : EqOn h (endpointMap S F) h.source)
    (hi : ManifoldSmoothOn (endpointAtlas S) (phaseManifold S).smoothStructure.val
      h.symm h.target)
    (q : M) (E : TangentSpace S q ≃ₗ[ℝ] Euclidean n)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hq : q ∈ e.source) (z : M) (hz : (q,z) ∈ h.target) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val
      (fiberLog h q E e he hq) z := by
  let b := (tangentStructure S).chart e he
  let A := (tangentStructure S).productCoordinates.linearEquiv
  let K := (tangentStructure S).fiberCoordinates.equiv e he q hq
  let L := (K.symm.trans E).toContinuousLinearEquiv
  have hbase := inverse_base F h heq hz
  have hwb : h.symm (q,z) ∈ b.source := by
    rw [(tangentStructure S).chart_source]
    change (h.symm (q,z)).1 ∈ e.source
    rwa [hbase]
  have hb := SmoothManifolds.TangentBundle.chart_mem S (tangentStructure S) e he
  have hin : ContinuousAt (fun y : M => (q,y)) z := continuousAt_const.prodMk continuousAt_id
  have hc1 : ContinuousAt (fun y : M => h.symm (q,y)) z :=
    (hi (q,z) hz).1.comp hin
  have hc2 : ContinuousAt (fun y : M => (b (h.symm (q,y))).val) z :=
    continuous_subtype_val.continuousAt.comp ((b.continuousAt hwb).comp (f := fun y : M => h.symm (q,y)) hc1)
  have hc3 : ContinuousAt (fun y : M => (A.symm (b (h.symm (q,y))).val).2) z :=
    continuousAt_snd.comp (A.symm.continuousAt.comp hc2)
  have hlogcont : ContinuousAt (fiberLog h q E e he hq) z :=
    L.continuousAt.comp hc3
  refine ⟨hlogcont, ?_⟩
  intro d hd hzd
  let c := SmoothManifolds.ProductData.productChart (tangentStructure S).productCoordinates e d
  have hc : c ∈ endpointAtlas S := ⟨e,he,d,hd,rfl⟩
  have hzc : (q,z) ∈ c.source := by
    simpa only [c, SmoothManifolds.productChart_source] using
      (show (q,z) ∈ e.source ×ˢ d.source from ⟨hq,hzd⟩)
  obtain ⟨U,hU,hpt,H,hH,hgerm⟩ := (hi (q,z) hz).2 c hc b hb hzc hwb
  let J : Euclidean n → Euclidean (n+n) := fun x => A ((e q).val,x)
  have hJ : ContDiff ℝ (⊤ : ℕ∞) J := A.contDiff.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨J ⁻¹' U, hU.preimage hJ.continuous, hpt, ?_, ?_, ?_⟩
  · exact fun x => L (A.symm (H (J x))).2
  · exact L.contDiff.comp_contDiffOn
      ((contDiff_snd.comp A.symm.contDiff).comp_contDiffOn
        (hH.comp hJ.contDiffOn (fun _ hx => hx)))
  · have hg := hgerm.comp_tendsto hin
    filter_upwards [hg] with y hy
    change H (A ((e q).val,(d y).val)) = (b (h.symm (q,y))).val at hy
    rw [hy]
    rfl

/-- A fixed metric ball in the source of a smooth endpoint inverse gives a
normal chart on precisely that ball, without reducing its radius. -/
theorem normal_chart_of_fiber_ball
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (g : RiemannianMetric S)
    (h : OpenPartialHomeomorph (Phase S) (M × M))
    (hdomain : h.source ⊆ exponentialDomain F)
    (heq : EqOn h (endpointMap S F) h.source)
    (hi : ManifoldSmoothOn (endpointAtlas S) (phaseManifold S).smoothStructure.val
      h.symm h.target)
    (q : M) (E : TangentSpace S q ≃ₗ[ℝ] Euclidean n)
    (hE : IsOrthonormalCoordinates g q E) (R : ℝ) (hR : 0 < R)
    (hball : ∀ v : TangentSpace S q, tangentNorm g q v ≤ R →
      (⟨q,v⟩ : Phase S) ∈ h.source) :
    ∃ d : ModelChart n .euclidean M, IsNormalChart g F q E R d := by
  obtain ⟨e,he,hqe⟩ := S.smoothStructure.property.1.1 q
  let f : Euclidean n → M := fun x => fiberExponential F q (E.symm x)
  let l : M → Euclidean n := fiberLog h q E e he hqe
  let B : Set (Euclidean n) := {x | tangentNorm g q (E.symm x) < R}
  let D : Set M := {z | (q,z) ∈ h.target ∧
    tangentNorm g (h.symm (q,z)).1 (h.symm (q,z)).2 < R}
  have hB : IsOpen B := (ExponentialNormalCoordinates.orthonormal_norm_continuous g q E hE).isOpen_preimage _ isOpen_Iio
  have hD : IsOpen D := by
    have hopen : IsOpen (h.target ∩ (fun x => tangentNorm g (h.symm x).1 (h.symm x).2) ⁻¹' Iio R) :=
      ((phaseNorm_continuous g).continuousOn.comp h.symm.continuousOn
        (fun _ hx => mem_univ _)).isOpen_inter_preimage h.open_target isOpen_Iio
    exact hopen.preimage (continuous_const.prodMk continuous_id)
  have hxsrc (x : Euclidean n) (hx : x ∈ B) : (⟨q,E.symm x⟩ : Phase S) ∈ h.source :=
    hball _ hx.le
  have hfwd (x : Euclidean n) (hx : x ∈ B) : h (⟨q,E.symm x⟩ : Phase S) = (q,f x) := heq (hxsrc x hx)
  have hinv (x : Euclidean n) (hx : x ∈ B) : h.symm (q,f x) = (⟨q,E.symm x⟩ : Phase S) := by
    rw [← hfwd x hx, h.left_inv (hxsrc x hx)]
  have hlf (x : Euclidean n) (hx : x ∈ B) : l (f x) = x := by
    dsimp only [l,fiberLog]
    rw [hinv x hx, (tangentStructure S).chart_apply e he ⟨q,E.symm x⟩ hqe]
    simp only [ContinuousLinearEquiv.symm_apply_apply, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  have hrec (z : M) (hz : z ∈ D) : h.symm (q,z) = (⟨q,E.symm (l z)⟩ : Phase S) :=
    fiberLog_reconstruct F h heq q E e he hqe z hz.1
  have hlB (z : M) (hz : z ∈ D) : l z ∈ B := by
    have hh := hz.2
    rw [hrec z hz] at hh
    exact hh
  have hfl (z : M) (hz : z ∈ D) : f (l z) = z := by
    have hh := h.right_inv hz.1
    rw [hrec z hz, hfwd (l z) (hlB z hz)] at hh
    exact congrArg Prod.snd hh
  let j : OpenPartialHomeomorph (Euclidean n) M := {
    toFun := f
    invFun := l
    source := B
    target := D
    map_source' := by
      intro x hx
      refine ⟨?_, ?_⟩
      · rw [← hfwd x hx]
        exact h.map_source (hxsrc x hx)
      · rw [hinv x hx]
        exact hx
    map_target' := hlB
    left_inv' := hlf
    right_inv' := hfl
    open_source := hB
    open_target := hD
    continuousOn_toFun := by
      intro x hx
      exact ((ExponentialNormalCoordinates.exponential_smooth C F hF _ (hdomain (hxsrc x hx))).1.comp
        (f := fun y : Euclidean n => (⟨q,E.symm y⟩ : Phase S))
        (ExponentialNormalCoordinates.fiberInclusion_continuous_basis q E).continuousAt).continuousWithinAt
    continuousOn_invFun := by
      intro z hz
      exact (fiberLog_smooth F h heq hi q E e he hqe z hz.1).1.continuousWithinAt }
  have hzeroB : (0 : Euclidean n) ∈ B := by
    simpa only [B,mem_ofPred_eq,map_zero,SmoothMetrics.tangentNorm_zero] using hR
  have hfzero : f 0 = q := by
    simpa only [f,map_zero] using (ExponentialNormalCoordinates.zero_section_at C F hF q).2
  let d := ExponentialNormalCoordinates.parametrizationChart j
  have hd : d ∈ S.smoothStructure.val :=
    ExponentialNormalCoordinates.parametrizationChart_mem j
      (by
        intro x hx c hc hxc
        exact ExponentialNormalCoordinates.fiberExponential_contDiffAt_basis C F hF q E c hc x
          (hdomain (hxsrc x hx)) hxc)
      (by
        intro z hz
        exact fiberLog_smooth F h heq hi q E e he hqe z hz.1)
  have hq : q ∈ d.source := by
    rw [ExponentialNormalCoordinates.parametrizationChart_source]
    have hh := j.map_source hzeroB
    change f 0 ∈ D at hh
    rwa [hfzero] at hh
  refine ⟨d,hR,hd,hq,?_,?_,?_⟩
  · change l q = 0
    rw [← hfzero]
    exact hlf 0 hzeroB
  · rw [ExponentialNormalCoordinates.parametrizationChart_target]
    rfl
  · intro x hx
    exact ⟨hdomain (hxsrc x.val hx),rfl⟩


/-- The uniform inverse supplies normal charts on one common exact radius
at every center in its base neighborhood. -/
theorem uniform_normal_charts_of_inverse
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (g : RiemannianMetric S) (p : M)
    (hInv : UniformExponentialInverse S g F p) :
    ∃ (r : ℝ) (V : Set M) (h : OpenPartialHomeomorph (Phase S) (M × M)),
      0 < r ∧ IsOpen V ∧ p ∈ V ∧ (⟨p,0⟩ : Phase S) ∈ h.source ∧
      h.source ⊆ exponentialDomain F ∧ EqOn h (endpointMap S F) h.source ∧
      ManifoldSmoothOn (phaseManifold S).smoothStructure.val (endpointAtlas S)
        h h.source ∧
      ManifoldSmoothOn (endpointAtlas S) (phaseManifold S).smoothStructure.val
        h.symm h.target ∧
      (∀ q ∈ V, ∀ v : TangentSpace S q, tangentNorm g q v ≤ r →
        (⟨q,v⟩ : Phase S) ∈ h.source) ∧
      V ×ˢ V ⊆ h.target ∧
      (∀ q ∈ V, ∀ z ∈ V,
        (h.symm (q,z)).1 = q ∧
        tangentNorm g (h.symm (q,z)).1 (h.symm (q,z)).2 < r/2) ∧
      ∀ q ∈ V, ∃ (E : TangentSpace S q ≃ₗ[ℝ] Euclidean n)
        (d : ModelChart n .euclidean M),
        IsOrthonormalCoordinates g q E ∧ IsNormalChart g F q E r d := by
  obtain ⟨r,V,h,hr,hV,hpV,hp0,hdom,heq,hs,hi,hball,hVV,hinv⟩ := hInv
  refine ⟨r,V,h,hr,hV,hpV,hp0,hdom,heq,hs,hi,hball,hVV,hinv,?_⟩
  intro q hq
  obtain ⟨E,hE⟩ := ExponentialNormalCoordinates.orthonormal_coordinates_exist g q
  obtain ⟨d,hd⟩ := normal_chart_of_fiber_ball C F hF g h hdom heq hi q E hE r hr
    (hball q hq)
  exact ⟨E,d,hE,hd⟩

end P202.Geometry.ConvexNormalNeighborhoods


set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace P202.Geometry.ConvexNormalNeighborhoods
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.CurveData P202.CurveConnectionData
  P202.GeodesicData P202.LeviCivitaData P202.ExponentialData P202.DistanceData
  P202.NormalMinimalityData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem geodesic_speed_eq_initial (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (V : ℝ → Phase S) (hV : IsGeodesicOn S C (Icc 0 1) V) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      tangentNorm g (V t).1 (V t).2 = tangentNorm g (V 0).1 (V 0).2 := by
  let f (t : ℝ) := pairing g (V t).1 (V t).2 (V t).2
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f 0 t := by
    have h := GeodesicIVP.pairing_self_derivative g C hC.2 (hV t ht).1 (hV t ht).2
    simpa only [map_zero, LinearMap.zero_apply, add_zero] using h
  have heq := constant_of_has_deriv_right_zero
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
  intro t ht
  exact congrArg Real.sqrt (heq t ht)

theorem affine_geodesic_prefix_length (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (γ : PiecewiseC1Curve S 0 1)
    (V : ℝ → Phase S) (hV : IsGeodesicOn S C (Icc 0 1) V)
    (hγV : EqOn γ (fun t => (V t).1) (Icc 0 1)) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ s in (0 : ℝ)..t, speed g γ s) = t * length g γ := by
  let K : ℝ := tangentNorm g (V 0).1 (V 0).2
  have hs (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : speed g γ t = K := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hv : HasVelocityAt S (fun s => (V s).1) t (V t).2 := by
      simpa only [HasVelocityAt, HasVelocityWithinAt, continuousWithinAt_univ,
        hasDerivWithinAt_univ] using (hV t ht').1
    have heq : (fun s => (V s).1) =ᶠ[𝓝 t] γ := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
      exact (hγV hs).symm
    have hc := PiecewiseCurves.speed_congr_of_eventuallyEq g
      (by simpa only [PiecewiseCurves.velocity_eq hv] using hv) heq
    calc
      speed g γ t = speed g (fun s => (V s).1) t := hc.symm
      _ = tangentNorm g (V t).1 (V t).2 := by
        unfold speed
        rw [PiecewiseCurves.velocity_eq hv]
      _ = K := geodesic_speed_eq_initial g C hC V hV t ht'
  have hint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ s in (0 : ℝ)..t, speed g γ s) = t * K := by
    calc
      _ = ∫ _s in (0 : ℝ)..t, K := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht.1
        intro s hs'
        exact hs s ⟨hs'.1, hs'.2.trans_le ht.2⟩
      _ = t * K := by simp
  have hL : length g γ = K := by
    change (∫ s in (0 : ℝ)..1, speed g γ s) = K
    simpa only [one_mul] using hint 1 ⟨zero_le_one, le_rfl⟩
  intro t ht
  rw [hint t ht, hL]

/-- An affine geodesic attaining the normal-chart radial bound has the
canonical affine parameter, including at zero initial displacement. -/
theorem affine_normal_minimizer (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < R)
    (γ : PiecewiseC1Curve S 0 1) (h0 : γ 0 = p)
    (h1 : γ 1 = fiberExponential F p v)
    (hsource : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ d.source)
    (hL : length g γ = tangentNorm g p v)
    (hgeo : ∃ V : ℝ → Phase S, IsGeodesicOn S C (Icc 0 1) V ∧
      EqOn γ (fun t => (V t).1) (Icc 0 1)) :
    EqOn γ (fun t => fiberExponential F p (t • v)) (Icc 0 1) := by
  obtain ⟨V, hV, hγV⟩ := hgeo
  obtain ⟨ρ, hρcont, hρmono, hρ0, hρ1, hρeq⟩ :=
    NormalMinimality.chart_rigidity S g C hC F hF p E R d hd v hv γ h0 h1 hsource hL
  by_cases hv0 : v = 0
  · subst v
    intro t ht
    simpa only [smul_zero] using hρeq t ht
  have hN : 0 < tangentNorm g p v :=
    lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg g p v)
      (fun h => hv0 ((SmoothMetrics.tangentNorm_eq_zero_iff g p v).mp h.symm))
  have hprefix :=
    (NormalMinimality.normal_chart_minimizing_prefix g C hC F hF p E R d hd v hv γ
      h0 h1 hsource hL).1
  have hint := affine_geodesic_prefix_length g C hC γ V hV hγV
  intro t ht
  have hr0 : 0 ≤ ρ t := by
    rw [← hρ0]
    exact hρmono ⟨le_rfl, zero_le_one⟩ ht ht.1
  have hr1 : ρ t ≤ tangentNorm g p v := by
    rw [← hρ1]
    exact hρmono ht ⟨zero_le_one, le_rfl⟩ ht.2
  have hscale : tangentNorm g p ((ρ t / tangentNorm g p v) • v) = ρ t := by
    rw [SmoothMetrics.tangentNorm_smul, abs_of_nonneg (div_nonneg hr0 hN.le),
      div_mul_cancel₀ _ hN.ne']
  have hcoord : tangentNorm g p (E.symm (d (γ t)).val) = ρ t := by
    rw [hρeq t ht,
      (NormalMinimality.normal_chart_exp g F p E R d hd _ (by rw [hscale]; exact hr1.trans_lt hv)).2.2,
      E.symm_apply_apply, hscale]
  have hr : ρ t = t * tangentNorm g p v := by
    rw [← hcoord, ← hprefix t ht, hint t ht, hL]
  rw [hρeq t ht, hr, mul_div_cancel_right₀ _ hN.ne']

/-- The canonical radial segment attains the global infimum. -/
theorem radial_minimizing_segment (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (r₀ R : ℝ)
    (d : ModelChart n .euclidean M) (hr₀ : 0 < r₀) (hrR : r₀ < R)
    (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < r₀) :
    ∃ γ : PiecewiseC1Curve S 0 1,
      EqOn γ (fun t => fiberExponential F p (t • v)) (Icc 0 1) ∧
      P202.ConvexNormalData.IsMinimizingGeodesic S g C p (fiberExponential F p v) γ := by
  obtain ⟨γ, h0, h1, hrad, hphase, hgeo, hL⟩ :=
    NormalMinimality.radial_segment_exists S g C hC F hF p E R d hd v (hv.trans hrR)
  obtain ⟨hz, hdist⟩ := NormalMinimality.componentDistance_eq_of_radial_comparison
    g F p v γ h0 h1 hL (fun c hc0 hc1 =>
      (NormalMinimality.global_comparison S g C hC F hF p E r₀ R d hr₀ hrR hd v hv
        c hc0 hc1).1)
  exact ⟨γ, hrad, h0, h1, ⟨F.curve ⟨p, v⟩, hgeo, hphase⟩, hL.trans hdist.symm⟩

/-- Global affine uniqueness, with competitors free to leave the normal ball. -/
theorem minimizing_geodesic_eq_radial (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (r₀ R : ℝ)
    (d : ModelChart n .euclidean M) (hr₀ : 0 < r₀) (hrR : r₀ < R)
    (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < r₀)
    (γ : PiecewiseC1Curve S 0 1)
    (hγ : P202.ConvexNormalData.IsMinimizingGeodesic S g C p
      (fiberExponential F p v) γ) :
    EqOn γ (fun t => fiberExponential F p (t • v)) (Icc 0 1) := by
  have hvR := hv.trans hrR
  obtain ⟨δ, hδ0, hδ1, _, _, _, hδL⟩ :=
    NormalMinimality.radial_segment_exists S g C hC F hF p E R d hd v hvR
  have hcomp {a b : ℝ} (c : PiecewiseC1Curve S a b)
      (hc0 : c a = p) (hc1 : c b = fiberExponential F p v) :=
    NormalMinimality.global_comparison S g C hC F hF p E r₀ R d hr₀ hrR hd v hv c hc0 hc1
  obtain ⟨hz, hdist⟩ := NormalMinimality.componentDistance_eq_of_radial_comparison
    g F p v δ hδ0 hδ1 hδL (fun c hc0 hc1 => (hcomp c hc0 hc1).1)
  have hL : length g γ = tangentNorm g p v := hγ.2.2.2.trans hdist
  have hsource := (hcomp γ hγ.1 hγ.2.1).2 (by rw [hL]; exact hv)
  exact affine_normal_minimizer g C hC F hF p E R d hd v hvR γ hγ.1 hγ.2.1
    hsource hL hγ.2.2.1

end P202.Geometry.ConvexNormalNeighborhoods

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace P202.Geometry.ConvexNormalNeighborhoods
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.CurveData P202.CurveConnectionData
  P202.GeodesicData P202.LeviCivitaData P202.ExponentialData P202.DistanceData
  P202.NormalMinimalityData P202.ConvexNormalData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- A sufficiently small endpoint neighborhood traps every global minimizer
in the prescribed open set. The competitors may be arbitrary minimizing
geodesics in the entire manifold. -/
theorem minimizing_geodesics_trapped (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (p : M)
    (W : Set M) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ B : Set M, IsOpen B ∧ p ∈ B ∧ B ⊆ W ∧ B ⊆ connectedComponent p ∧
      ∀ q ∈ B, ∀ z ∈ B, ∀ γ : PiecewiseC1Curve S 0 1,
        IsMinimizingGeodesic S g C q z γ →
        ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ W := by
  obtain ⟨ε, hε, htrap⟩ := LengthDistance.local_curve_trapping g p W hW hpW
  obtain ⟨B, hB, hpB, hshort⟩ :=
    LengthDistance.local_short_curves g p (ε / 4) (by linarith)
  refine ⟨B, hB, hpB, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨a, b, c, hc0, hc1, hLc⟩ := hshort q hq
    exact hc1 ▸ htrap c hc0 (hLc.trans (by linarith))
  · intro q hq
    obtain ⟨a, b, c, hc0, hc1, _⟩ := hshort q hq
    exact LengthDistance.path_mem_component ⟨a, b, c, hc0, hc1⟩
  · intro q hq z hz γ hγ t ht
    obtain ⟨a, b, cq, hcq0, hcq1, hLq⟩ := hshort q hq
    obtain ⟨l, r, cz, hcz0, hcz1, hLz⟩ := hshort z hz
    have hpq : length g cq ∈ pathLengths g p q := ⟨a, b, cq, hcq0, hcq1, rfl⟩
    have hqp : length g cq ∈ pathLengths g q p := by
      have heq : pathLengths g p q = pathLengths g q p :=
        LengthDistance.pathLengths_symm g p q
      exact heq ▸ hpq
    have hpz : length g cz ∈ pathLengths g p z := ⟨l, r, cz, hcz0, hcz1, rfl⟩
    have hγbound : length g γ ≤ length g cq + length g cz :=
      hγ.2.2.2.trans_le (csInf_le (LengthDistance.pathLengths_bddBelow g q z)
        (LengthDistance.pathLengths_add g hqp hpz))
    let cp := PiecewiseCurves.restrict γ 0 t le_rfl ht.1 ht.2
    have hcp : length g cp ∈ pathLengths g q (γ t) :=
      ⟨0, t, cp, hγ.1, rfl, rfl⟩
    have hLp : length g cp ≤ length g γ :=
      NormalMinimality.length_restrict_le g γ le_rfl ht.1 ht.2
    obtain ⟨u, v, c, hc0, hc1, hLc⟩ := LengthDistance.pathLengths_add g hpq hcp
    have hcshort : length g c < ε := by
      rw [← hLc]
      linarith
    exact hc1 ▸ htrap c hc0 hcshort

end P202.Geometry.ConvexNormalNeighborhoods

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace P202.Geometry.ConvexNormalNeighborhoods
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.MaximalFlowData
  SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.CurveData P202.GeodesicData
  P202.LeviCivitaData P202.ExponentialData P202.DistanceData
  P202.ConvexNormalData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Smooth local logarithms give joint smoothness of the affine segment,
including at both endpoint times and on the diagonal. -/
theorem segment_smooth_of_log (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (L : M × M → Phase S) (x : ℝ × (M × M))
    (hL : ManifoldSmoothAt (endpointAtlas S) (phaseManifold S).smoothStructure.val L x.2)
    (ht : x.1 ∈ (F.interval (L x.2)).carrier) :
    SegmentSmoothAt S (fun q z t => (F.curve (L (q, z)) t).1) x := by
  have hpos := ((GeodesicIVP.domain_open_smooth S C F hF).2 (x.1, L x.2) ht).2
  have hmap : ContinuousAt (fun w : ℝ × (M × M) => (w.1, L w.2)) x :=
    continuousAt_fst.prodMk (hL.1.comp continuousAt_snd)
  refine ⟨hpos.1.comp (f := fun w : ℝ × (M × M) => (w.1, L w.2)) hmap, ?_⟩
  intro e he d hd c hc hxe hxd hxc
  obtain ⟨b, hb, hxb⟩ := (phaseManifold S).smoothStructure.property.1.1 (L x.2)
  let a := SmoothManifolds.ProductData.productChart
    (tangentStructure S).productCoordinates e d
  have ha : a ∈ endpointAtlas S := ⟨e, he, d, hd, rfl⟩
  have hxa : x.2 ∈ a.source := by
    rw [(SmoothManifolds.productChart_source_apply _ e d).1]
    exact ⟨hxe, hxd⟩
  obtain ⟨W, hW, hxW, K, hK, hKgerm⟩ := hL.2 a ha b hb hxa hxb
  obtain ⟨U, hU, hxU, H, hH, hHgerm⟩ := hpos.2 b hb c hc hxb hxc
  let A := (tangentStructure S).productCoordinates.linearEquiv
  let J : ℝ × (Euclidean n × Euclidean n) → ℝ × Euclidean (n + n) :=
    fun y => (y.1, K (A y.2))
  let V : Set (ℝ × (Euclidean n × Euclidean n)) :=
    (fun y : ℝ × (Euclidean n × Euclidean n) => A y.2) ⁻¹' W ∩ J ⁻¹' U
  have hcoord : (a x.2).val = A ((e x.2.1).val, (d x.2.2).val) := rfl
  have hgK : K (a x.2).val = (b (L x.2)).val := hKgerm.eq_of_nhds
  have hJ : ContDiffOn ℝ (⊤ : ℕ∞) J
      ((fun y : ℝ × (Euclidean n × Euclidean n) => A y.2) ⁻¹' W) :=
    contDiffOn_fst.prodMk
      (hK.comp (A.contDiff.comp contDiff_snd).contDiffOn (fun _ hy => hy))
  have hV : IsOpen V :=
    hJ.continuousOn.isOpen_inter_preimage
      (hW.preimage (A.continuous.comp continuous_snd)) hU
  refine ⟨V, hV, ?_, (fun y => H (J y)), ?_, ?_⟩
  · constructor
    · exact hxW
    · change (x.1, K (A ((e x.2.1).val, (d x.2.2).val))) ∈ U
      rw [← hcoord, hgK]
      exact hxU
  · exact hH.comp (hJ.mono inter_subset_left) (fun _ hy => hy.2)
  · have hgl := hKgerm.comp_tendsto continuousAt_snd.tendsto
    have hgh := hHgerm.comp_tendsto hmap.tendsto
    filter_upwards [hgl, hgh] with y hyK hyH
    change H (y.1, K (A ((e y.2.1).val, (d y.2.2).val))) = _
    change K (A ((e y.2.1).val, (d y.2.2).val)) = _ at hyK
    rw [hyK]
    exact hyH
end P202.Geometry.ConvexNormalNeighborhoods

namespace P202.Geometry.ConvexNormalNeighborhoods
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.MaximalFlowData
  SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.CurveData P202.GeodesicData
  P202.LeviCivitaData P202.ExponentialData P202.DistanceData
  P202.ConvexNormalData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Global radial comparison on a prescribed normal chart identifies the
actual global distance infimum and supplies a minimizing affine segment. -/
theorem normal_chart_minimizing_segment (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (r R : ℝ) (d : ModelChart n .euclidean M)
    (hr : 0 < r) (hrR : r < R) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < r) :
    sInf (pathLengths g p (fiberExponential F p v)) = tangentNorm g p v ∧
    ∃ γ : PiecewiseC1Curve S 0 1,
      EqOn γ (fun t => (F.curve ⟨p, v⟩ t).1) (Icc 0 1) ∧
      IsMinimizingGeodesic S g C p (fiberExponential F p v) γ := by
  obtain ⟨γ, hγ0, hγ1, _, hγcurve, hγgeo, hγlen⟩ :=
    NormalMinimality.radial_segment_exists S g C hC F hF p E R d hd v (hv.trans hrR)
  obtain ⟨hq, hdist⟩ := NormalMinimality.componentDistance_eq_of_radial_comparison
    g F p v γ hγ0 hγ1 hγlen (fun c hc0 hc1 =>
      (NormalMinimality.global_comparison S g C hC F hF p E r R d
        hr hrR hd v hv c hc0 hc1).1)
  change sInf (pathLengths g p (fiberExponential F p v)) = _ at hdist
  refine ⟨hdist, γ, hγcurve, hγ0, hγ1, ?_, hγlen.trans hdist.symm⟩
  exact ⟨F.curve ⟨p, v⟩, hγgeo, hγcurve⟩

end P202.Geometry.ConvexNormalNeighborhoods

namespace P202.Geometry.ConvexNormalNeighborhoods
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.MaximalFlowData
  SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.CurveData P202.GeodesicData
  P202.LeviCivitaData P202.ExponentialData P202.DistanceData
  P202.ConvexNormalData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem log_distance_eq (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (h : OpenPartialHomeomorph (Phase S) (M × M))
    (heq : EqOn h (endpointMap S F) h.source)
    (r : ℝ) (hr : 0 < r) (V : Set M)
    (hchart : ∀ q ∈ V, ∃ (E : TangentSpace S q ≃ₗ[ℝ] Euclidean n)
      (d : ModelChart n .euclidean M), IsNormalChart g F q E r d)
    (hVV : V ×ˢ V ⊆ h.target)
    (hnorm : ∀ x ∈ V ×ˢ V,
      tangentNorm g (h.symm x).1 (h.symm x).2 < r / 2)
    (x : M × M) (hx : x ∈ V ×ˢ V) :
    sInf (pathLengths g x.1 x.2) = tangentNorm g (h.symm x).1 (h.symm x).2 ∧
    ∃ γ : PiecewiseC1Curve S 0 1,
      EqOn γ (fun t => (F.curve (h.symm x) t).1) (Icc 0 1) ∧
      IsMinimizingGeodesic S g C x.1 x.2 γ := by
  let w := h.symm x
  have hpair : (w.1, fiberExponential F w.1 w.2) = x :=
    (heq (h.map_target (hVV hx))).symm.trans (h.right_inv (hVV hx))
  have hwV : w.1 ∈ V := by
    rw [show w.1 = x.1 from congrArg Prod.fst hpair]
    exact hx.1
  obtain ⟨E, d, hd⟩ := hchart w.1 hwV
  obtain ⟨hdist, γ, hγ, hγmin⟩ := normal_chart_minimizing_segment
    g C hC F hF w.1 E (r / 2) r d (half_pos hr) (by linarith) hd w.2 (hnorm x hx)
  have hdist' : sInf (pathLengths g x.1 x.2) = tangentNorm g w.1 w.2 := by
    rw [← congrArg Prod.fst hpair, ← congrArg Prod.snd hpair]
    exact hdist
  refine ⟨hdist', γ, hγ, ?_⟩
  rw [← congrArg Prod.fst hpair, ← congrArg Prod.snd hpair]
  exact hγmin

/-- The logarithm formula proves smooth squared distance on the entire
product neighborhood, including its diagonal. -/
theorem log_squared_distance_smooth (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (h : OpenPartialHomeomorph (Phase S) (M × M))
    (heq : EqOn h (endpointMap S F) h.source)
    (hi : ManifoldSmoothOn (endpointAtlas S) (phaseManifold S).smoothStructure.val h.symm h.target)
    (r : ℝ) (hr : 0 < r) (V : Set M) (hV : IsOpen V)
    (hchart : ∀ q ∈ V, ∃ (E : TangentSpace S q ≃ₗ[ℝ] Euclidean n)
      (d : ModelChart n .euclidean M), IsNormalChart g F q E r d)
    (hVV : V ×ˢ V ⊆ h.target)
    (hnorm : ∀ x ∈ V ×ˢ V,
      tangentNorm g (h.symm x).1 (h.symm x).2 < r / 2)
    (x : M × M) (hx : x ∈ V ×ˢ V) :
    VectorSmoothAt (endpointAtlas S) (squaredDistance S g) x := by
  apply squaredDistance_smooth_of_log g h.symm x (hi x (hVV hx))
  filter_upwards [(hV.prod hV).mem_nhds hx] with y hy
  unfold squaredDistance
  rw [(log_distance_eq g C hC F hF h heq r hr V hchart hVV hnorm y hy).1,
    SmoothMetrics.tangentNorm_sq]

end P202.Geometry.ConvexNormalNeighborhoods

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace P202.Geometry.ConvexNormalNeighborhoods
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
open Set Filter
open scoped Topology
universe u

theorem norm_lt_of_coordinate_square_lt {n : ℕ} (a v : Euclidean n)
    {δ : ℝ} (hδ : 0 < δ) (hv : (∑ i : Fin n, (v i - a i)^2) < δ^2) :
    ‖v - a‖ < δ := by
  apply (pi_norm_lt_iff hδ).2
  intro i
  have hi : (v i - a i)^2 ≤ ∑ j : Fin n, (v j - a j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j - a j)) (Finset.mem_univ i)
  change |v i - a i| < δ
  exact (sq_lt_sq₀ (abs_nonneg _) hδ.le).mp (by simpa only [sq_abs] using hi.trans_lt hv)

/-- Small coordinate-square sublevels are actual arbitrarily small open
neighborhoods, without assuming the chart is globally defined smoothly. -/
theorem coordinate_sublevel_neighborhood {n : ℕ} {M : Type u} [TopologicalSpace M]
    (c : ModelChart n .euclidean M) (p : M) (hp : p ∈ c.source)
    (N : Set M) (hN : IsOpen N) (hpN : p ∈ N) :
    ∃ δ : ℝ, 0 < δ ∧
      let U := {q ∈ c.source | (∑ i : Fin n, ((c q).val i - (c p).val i)^2) < δ^2}
      IsOpen U ∧ p ∈ U ∧ U ⊆ N := by
  let a := (c p).val
  let j : Euclidean n → M := fun x => c.symm ⟨x, mem_univ _⟩
  have hja : j a = p := c.left_inv hp
  have hj : ContinuousAt j a := by
    exact (c.symm.continuousAt (c.map_source hp)).comp
      (f := fun x : Euclidean n => (⟨x, mem_univ _⟩ : ModelSpace n .euclidean))
      (show ContinuousAt (fun x : Euclidean n =>
        (⟨x, mem_univ _⟩ : ModelSpace n .euclidean)) a from
        tendsto_subtype_rng.mpr continuousAt_id)
  have hnear : j ⁻¹' N ∈ 𝓝 a := by
    apply hj.preimage_mem_nhds
    rw [hja]
    exact hN.mem_nhds hpN
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, hδ, ?_, ?_, ?_⟩
  · have hQ : Continuous (fun v : Euclidean n => ∑ i : Fin n, (v i - a i)^2) := by
      fun_prop
    have hcoords : ContinuousOn (fun q => (c q).val) c.source :=
      continuous_subtype_val.comp_continuousOn c.continuousOn
    exact (hQ.comp_continuousOn hcoords).isOpen_inter_preimage c.open_source isOpen_Iio
  · refine ⟨hp, ?_⟩
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] using sq_pos_of_pos hδ
  · intro q hq
    have hcoord : ‖(c q).val - a‖ < δ := norm_lt_of_coordinate_square_lt a (c q).val hδ hq.2
    have hball : (c q).val ∈ Metric.ball a δ := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hcoord
    have hqN := hδsub hball
    change c.symm (c q) ∈ N at hqN
    rwa [c.left_inv hq.1] at hqN
end P202.Geometry.ConvexNormalNeighborhoods

open Set Filter
open scoped Topology
noncomputable section
namespace P202.Geometry.ConvexNormalNeighborhoods.CoordinateConvex

theorem product_le_sum_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (i j : ι) : |v i * v j| ≤ ∑ k, (v k)^2 := by
  have hi : (v i)^2 ≤ ∑ k, (v k)^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ i)
  have hj : (v j)^2 ≤ ∑ k, (v k)^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ j)
  rw [abs_mul]
  nlinarith [sq_nonneg (|v i| - |v j|), sq_abs (v i), sq_abs (v j)]

theorem quadratic_error_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ι → ℝ) (v : ι → ℝ) :
    ∑ i, ∑ j, b i j * v i * v j ≤ (∑ i, ∑ j, |b i j|) * (∑ k, (v k)^2) := by
  simp only [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  calc
    b i j * v i * v j ≤ |b i j * v i * v j| := le_abs_self _
    _ = |b i j| * |v i * v j| := by rw [mul_assoc, abs_mul]
    _ ≤ |b i j| * (∑ k, (v k)^2) :=
      mul_le_mul_of_nonneg_left (product_le_sum_sq v i j) (abs_nonneg _)

theorem coordinate_hessian_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ : ι → ι → ι → ℝ) (x v : ι → ℝ)
    (hsmall : ∑ k, ∑ i, ∑ j, |x k * Γ k i j| ≤ 1) :
    0 ≤ (∑ i, (v i)^2) - ∑ k, ∑ i, ∑ j, x k * Γ k i j * v i * v j := by
  have hterm (k : ι) :
      ∑ i, ∑ j, x k * Γ k i j * v i * v j ≤
        (∑ i, ∑ j, |x k * Γ k i j|) * (∑ i, (v i)^2) :=
    quadratic_error_bound (fun i j => x k * Γ k i j) v
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
  rw [← Finset.sum_mul] at hsum
  have hQ : 0 ≤ ∑ i, (v i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right hsmall hQ]

theorem square_radius_deriv {ι : Type*} [Fintype ι]
    (x v : ℝ → ι → ℝ) (a : ι → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v t i) t) :
    HasDerivAt (fun s => ∑ i, (x s i - a i)^2)
      (2 * ∑ i, (x t i - a i) * v t i) t := by
  have hd := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => ((hx i).sub_const (a i)).pow 2)
  convert hd using 1; simp [Finset.mul_sum, mul_assoc]

theorem square_radius_deriv2 {ι : Type*} [Fintype ι]
    (x v : ℝ → ι → ℝ) (a acc : ι → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun s => x s i) (v t i) t)
    (hv : ∀ i, HasDerivAt (fun s => v s i) (acc i) t) :
    HasDerivAt (fun s => 2 * ∑ i, (x s i - a i) * v s i)
      (2 * (∑ i, (v t i)^2) + 2 * ∑ i, (x t i - a i) * acc i) t := by
  have hd := (HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
    ((hx i).sub_const (a i)).mul (hv i))).const_mul 2
  convert hd using 1
  rw [Finset.sum_add_distrib, mul_add]
  congr 1
  simp only [pow_two]


theorem exists_open_coordinate_hessian_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type*} [TopologicalSpace X]
    (x : X → ι → ℝ) (Γ : X → ι → ι → ι → ℝ)
    (hx : Continuous x) (hΓ : ∀ k i j, Continuous (fun q => Γ q k i j)) (p : X) :
    ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ ∀ q ∈ W, ∀ v : ι → ℝ,
      0 ≤ (∑ i, (v i)^2) -
        ∑ k, ∑ i, ∑ j, (x q k - x p k) * Γ q k i j * v i * v j := by
  let A : X → ℝ := fun q => ∑ k, ∑ i, ∑ j, |(x q k - x p k) * Γ q k i j|
  have hA : Continuous A := by
    apply continuous_finsetSum
    intro k _
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (((continuous_apply k).comp hx).sub continuous_const).mul (hΓ k i j) |>.abs
  refine ⟨A ⁻¹' Iio 1, isOpen_Iio.preimage hA, ?_, ?_⟩
  · simp [A]
  · intro q hq v
    exact coordinate_hessian_nonneg (Γ q) (fun k => x q k - x p k) v (le_of_lt hq)


theorem square_radius_convex {ι : Type*} [Fintype ι]
    (x v acc : ℝ → ι → ℝ) (a : ι → ℝ)
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, HasDerivAt (fun s => x s i) (v t i) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i, HasDerivAt (fun s => v s i) (acc t i) t)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1,
      0 ≤ (∑ i, (v t i)^2) + ∑ i, (x t i - a i) * acc t i) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun s => ∑ i, (x s i - a i)^2) := by
  let f : ℝ → ℝ := fun s => ∑ i, (x s i - a i)^2
  let f₁ : ℝ → ℝ := fun s => 2 * ∑ i, (x s i - a i) * v s i
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (f₁ t) t :=
    square_radius_deriv x v a t (hx t ht)
  have hdf (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      deriv f =ᶠ[𝓝 t] f₁ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact (hd s ⟨le_of_lt hs.1, le_of_lt hs.2⟩).deriv
  have hd₂ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (deriv f)
        (2 * (∑ i, (v t i)^2) + 2 * ∑ i, (x t i - a i) * acc t i) t := by
    exact (square_radius_deriv2 x v a (acc t) t
      (hx t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
      (hv t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)).congr_of_eventuallyEq (hdf t ht)
  apply convexOn_of_deriv2_nonneg (convex_Icc (0 : ℝ) 1)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hd t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (hd₂ t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    change 0 ≤ deriv (deriv f) t
    rw [(hd₂ t ht).deriv]
    linarith [hpos t ⟨le_of_lt ht.1, le_of_lt ht.2⟩]

end P202.Geometry.ConvexNormalNeighborhoods.CoordinateConvex

namespace P202.Geometry.ConvexNormalNeighborhoods
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData SmoothManifolds.FrameData
  P202.ConnectionData P202.GeodesicData P202.LeviCivitaData P202.MetricData
open CoordinateConvex
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem local_coordinate_hessian_nonneg
    (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : M) (hp : p ∈ (tangentBundle S).baseSet c) :
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ⊆ (tangentBundle S).baseSet c ∧
      ∀ q ∈ W, ∀ hq : q ∈ (tangentBundle S).baseSet c, ∀ v : Euclidean n,
        0 ≤ (∑ i, (v i)^2) - ∑ k, ∑ i, ∑ j,
          ((c.val q).val k - (c.val p).val k) * christoffel C c ⟨q, hq⟩ k i j * v i * v j := by
  let D := (tangentBundle S).baseSet c
  have hD : IsOpen D := GeodesicIVP.tangent_baseSet_isOpen c
  let x : D → Euclidean n := fun q => (c.val q.val).val
  let Γ : D → Fin n → Fin n → Fin n → ℝ := fun q k i j => christoffel C c q k i j
  have hx : Continuous x := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hq : q.val ∈ c.val.source := (tangentRealization S).baseSet c ▸ q.property
    exact continuous_subtype_val.continuousAt.comp
      ((c.val.continuousOn.continuousAt (c.val.open_source.mem_nhds hq)).comp
        continuous_subtype_val.continuousAt)
  have hΓ : ∀ k i j, Continuous (fun q => Γ q k i j) := by
    intro k i j
    exact continuous_iff_continuousAt.mpr fun q => (GeodesicIVP.christoffel_smooth C c k i j q).1
  obtain ⟨A, hA, hpA, hpos⟩ := exists_open_coordinate_hessian_nonneg x Γ hx hΓ ⟨p, hp⟩
  refine ⟨Subtype.val '' A, hD.isOpenMap_subtype_val _ hA, ⟨⟨p, hp⟩, hpA, rfl⟩,
    ?_, ?_⟩
  · rintro q ⟨q', _, rfl⟩
    exact q'.property
  · rintro q ⟨q', hq', rfl⟩ hq v
    exact hpos q' hq' v


/-- In sufficiently small coordinate neighborhoods the Euclidean square
radius has nonnegative second derivative along every affine geodesic.
No Riemannian compatibility of the connection is needed. -/
theorem local_coordinate_square_convex
    (C : Connection (tangentBundle S))
    (c : SmoothManifolds.BundleOperationsData.TangentIndex S)
    (p : M) (hp : p ∈ (tangentBundle S).baseSet c) :
    ∃ W : Set M, IsOpen W ∧ p ∈ W ∧ W ⊆ (tangentBundle S).baseSet c ∧
      ∀ (q : ℝ → Phase S), IsGeodesicOn S C (Icc 0 1) q →
        (∀ t ∈ Icc (0 : ℝ) 1, (q t).1 ∈ W) →
        ConvexOn ℝ (Icc (0 : ℝ) 1)
          (fun t => ∑ i, ((c.val (q t).1).val i - (c.val p).val i)^2) := by
  classical
  obtain ⟨W, hW, hpW, hWD, hpos⟩ := local_coordinate_hessian_nonneg C c p hp
  refine ⟨W, hW, hpW, hWD, ?_⟩
  intro q hq hqW
  let x : ℝ → Euclidean n := fun t => (c.val (q t).1).val
  let v : ℝ → Euclidean n := chartVelocity S c q
  let acc : ℝ → Euclidean n := fun t => if h : (q t).1 ∈ (tangentBundle S).baseSet c
    then coordinateAcceleration S C c ⟨(q t).1, h⟩ (v t) else 0
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    GeodesicIVP.geodesic_coordinate_equation C hq ht c (hWD (hqW t ht))
  have hacc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      acc t = coordinateAcceleration S C c ⟨(q t).1, hWD (hqW t ht)⟩ (v t) := by
    simp [acc, hWD (hqW t ht)]
  apply square_radius_convex x v acc (c.val p).val
  · intro t ht i
    exact hasDerivAt_pi.mp (hd t ht).1 i
  · intro t ht i
    rw [hacc t ht]
    exact hasDerivAt_pi.mp (hd t ht).2 i
  · intro t ht
    rw [hacc t ht]
    have H := hpos (q t).1 (hqW t ht) (hWD (hqW t ht)) (v t)
    simpa only [x, coordinateAcceleration, mul_neg, Finset.mul_sum,
      Finset.sum_neg_distrib, ← mul_assoc, sub_eq_add_neg] using H

end P202.Geometry.ConvexNormalNeighborhoods

namespace P202.Geometry.ConvexNormalNeighborhoods
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.CurveData
  P202.GeodesicData P202.LeviCivitaData P202.ExponentialData P202.DistanceData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem log_minimizer_unique (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (h : OpenPartialHomeomorph (Phase S) (M × M))
    (heq : EqOn h (P202.ConvexNormalData.endpointMap S F) h.source)
    (r : ℝ) (hr : 0 < r) (V : Set M)
    (hchart : ∀ q ∈ V, ∃ (E : TangentSpace S q ≃ₗ[ℝ] Euclidean n)
      (d : ModelChart n .euclidean M), IsNormalChart g F q E r d)
    (hVV : V ×ˢ V ⊆ h.target)
    (hnorm : ∀ x ∈ V ×ˢ V,
      tangentNorm g (h.symm x).1 (h.symm x).2 < r / 2)
    (x : M × M) (hx : x ∈ V ×ˢ V)
    (γ : PiecewiseC1Curve S 0 1)
    (hγ : P202.ConvexNormalData.IsMinimizingGeodesic S g C x.1 x.2 γ) :
    EqOn γ (fun t => (F.curve (h.symm x) t).1) (Icc 0 1) := by
  let w := h.symm x
  have hpair : (w.1, fiberExponential F w.1 w.2) = x :=
    (heq (h.map_target (hVV hx))).symm.trans (h.right_inv (hVV hx))
  have hwV : w.1 ∈ V := by
    change (w.1, fiberExponential F w.1 w.2).1 ∈ V
    rw [hpair]
    exact hx.1
  obtain ⟨E, d, hd⟩ := hchart w.1 hwV
  have hγ' : P202.ConvexNormalData.IsMinimizingGeodesic S g C w.1
      (fiberExponential F w.1 w.2) γ := by
    change P202.ConvexNormalData.IsMinimizingGeodesic S g C
      (w.1, fiberExponential F w.1 w.2).1
      (w.1, fiberExponential F w.1 w.2).2 γ
    rw [hpair]
    exact hγ
  have hrad := minimizing_geodesic_eq_radial g C hC F hF w.1 E (r / 2) r d
    (half_pos hr) (by linarith) hd w.2 (hnorm x hx) γ hγ'
  have hwR : tangentNorm g w.1 w.2 < r := (hnorm x hx).trans (by linarith)
  have hwD := (NormalMinimality.normal_chart_exp g F w.1 E r d hd w.2 hwR).1
  have hI := NormalMinimality.radial_interval C F hF w.1 w.2 hwD
  intro t ht
  exact (hrad ht).trans
    (ExponentialNormalCoordinates.radial_identity_at C F hF w.1 w.2 t (hI ht)).2


/-- The segment formula on the diagonal is constant for every time. -/
theorem log_segment_diagonal (g : RiemannianMetric S)
    (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (h : OpenPartialHomeomorph (Phase S) (M × M))
    (heq : EqOn h (P202.ConvexNormalData.endpointMap S F) h.source)
    (r : ℝ) (hr : 0 < r) (V : Set M)
    (hball : ∀ q ∈ V, ∀ v : TangentSpace S q, tangentNorm g q v ≤ r →
      (⟨q, v⟩ : Phase S) ∈ h.source) :
    ∀ q ∈ V, ∀ t : ℝ, (F.curve (h.symm (q, q)) t).1 = q := by
  intro q hq t
  have hzero : (⟨q, 0⟩ : Phase S) ∈ h.source :=
    hball q hq 0 (by simpa only [SmoothMetrics.tangentNorm_zero] using hr.le)
  rw [inverse_diagonal C F hF h heq q hzero]
  exact congrArg Sigma.fst ((ExponentialNormalCoordinates.zero_family C F hF q).2 t)

end P202.Geometry.ConvexNormalNeighborhoods

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace P202.Geometry.ConvexNormalNeighborhoods
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData SmoothManifolds.MaximalFlowData
  SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.CurveData P202.GeodesicData
  P202.LeviCivitaData P202.ExponentialData P202.DistanceData
  P202.ConvexNormalData
open Set Filter
open scoped Topology
universe u

/-- Arbitrarily small convex normal neighborhoods, with global minimizing
uniqueness and the full joint smoothness conclusions of Theorem 6.9. -/
theorem convex_neighborhoods :
    P202Specs.Geometry.ConvexNormalNeighborhoods.convex_neighborhoodsType.{u} := by
  intro n M _ S g C hC p O hO hpO
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists S C
  obtain ⟨r, V, h, hr, hV, hpV, _, hdom, heq, _, hi, hball, hVV, hinv, hcharts⟩ :=
    uniform_normal_charts_of_inverse C F hF g p (uniform_inverse S g C F hF p)
  have hchart : ∀ q ∈ V, ∃ (E : TangentSpace S q ≃ₗ[ℝ] Euclidean n)
      (d : ModelChart n .euclidean M), IsNormalChart g F q E r d := by
    intro q hq
    obtain ⟨E, d, _, hd⟩ := hcharts q hq
    exact ⟨E, d, hd⟩
  have hnorm (x : M × M) (hx : x ∈ V ×ˢ V) :
      tangentNorm g (h.symm x).1 (h.symm x).2 < r / 2 :=
    (hinv x.1 hx.1 x.2 hx.2).2
  have htime (x : M × M) (hx : x ∈ V ×ˢ V) :
      Icc (0 : ℝ) 1 ⊆ (F.interval (h.symm x)).carrier :=
    (F.interval (h.symm x)).ordConnected.out (hF (h.symm x)).1
      (hdom (h.map_target (hVV hx)))
  have hgeo (x : M × M) (hx : x ∈ V ×ˢ V) :
      IsGeodesicOn S C (Icc 0 1) (F.curve (h.symm x)) :=
    fun t ht => (hF (h.symm x)).2.2.1 t (htime x hx ht)
  let σ : M → M → ℝ → M := fun q z t => (F.curve (h.symm (q,z)) t).1
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  let d : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc⟩
  have hpd : p ∈ (tangentBundle S).baseSet d := by
    rw [(tangentRealization S).baseSet d]
    exact hpc
  obtain ⟨W, hW, hpW, hWd, hconv⟩ := local_coordinate_square_convex C d p hpd
  obtain ⟨B, hB, hpB, _, hBcomp, htrap⟩ := minimizing_geodesics_trapped g C p W hW hpW
  obtain ⟨δ, hδ, hU, hpU, hUN⟩ := coordinate_sublevel_neighborhood c p hpc
    ((B ∩ V) ∩ O) ((hB.inter hV).inter hO) ⟨⟨hpB, hpV⟩, hpO⟩
  let U : Set M := {q ∈ c.source |
    (∑ i : Fin n, ((c q).val i - (c p).val i)^2) < δ^2}
  have hUB (q : M) (hq : q ∈ U) : q ∈ B := (hUN hq).1.1
  have hUV (q : M) (hq : q ∈ U) : q ∈ V := (hUN hq).1.2
  refine ⟨U, (fun q hq => (hUN hq).2), hU, hpU,
    (fun q hq => hBcomp (hUB q hq)), σ, ?_, ?_⟩
  · intro q hq z hz
    have hx : (q,z) ∈ V ×ˢ V := ⟨hUV q hq, hUV z hz⟩
    obtain ⟨_, γ, hγσ, hγmin⟩ := log_distance_eq g C hC F hF h heq r hr V hchart
      hVV hnorm (q,z) hx
    have hσ0 : σ q z 0 = q := (hγσ (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)).symm.trans hγmin.1
    have hσ1 : σ q z 1 = z := (hγσ (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)).symm.trans hγmin.2.1
    have hstay : ∀ t ∈ Icc (0 : ℝ) 1, σ q z t ∈ W := by
      intro t ht
      have htw := htrap q (hUB q hq) z (hUB z hz) γ hγmin t ht
      exact Eq.mp (congrArg (fun y : M => y ∈ W) (hγσ ht)) htw
    have hcf : ConvexOn ℝ (Icc (0 : ℝ) 1)
        (fun t => ∑ i, ((c (σ q z t)).val i - (c p).val i)^2) :=
      hconv (F.curve (h.symm (q,z))) (hgeo (q,z) hx) hstay
    have hstaysU : ∀ t ∈ Icc (0 : ℝ) 1, σ q z t ∈ U := by
      intro t ht
      refine ⟨?_, ?_⟩
      · exact (tangentRealization S).baseSet d ▸ hWd (hstay t ht)
      · exact convex_sublevel_segment hcf (by rw [hσ0]; exact hq.2)
          (by rw [hσ1]; exact hz.2) ht
    refine ⟨⟨γ, hγσ, hγmin⟩, hstaysU, ?_, ?_, ?_⟩
    · intro η hη
      exact log_minimizer_unique g C hC F hF h heq r hr V hchart hVV hnorm
        (q,z) hx η hη
    · intro hqz t ht
      subst z
      exact log_segment_diagonal g C F hF h heq r hr V hball q (hUV q hq) t
    · intro t ht
      exact segment_smooth_of_log C F hF h.symm (t,q,z)
        (hi (q,z) (hVV hx)) (htime (q,z) hx ht)
  · intro x hx
    exact log_squared_distance_smooth g C hC F hF h heq hi r hr V hV hchart hVV hnorm
      x ⟨hUV x.1 hx.1, hUV x.2 hx.2⟩

/-- The complete Theorem 6.9: Gauss's formula, centered radial minimality,
uniform normal inverses, and arbitrarily small convex normal neighborhoods. -/
theorem gauss_normal :
    P202Specs.Geometry.ConvexNormalNeighborhoods.gauss_normalType.{u} := by
  exact ⟨GaussLemma.gauss_lemma, NormalMinimality.normal_minimality,
    uniform_inverse, convex_neighborhoods⟩

end P202.Geometry.ConvexNormalNeighborhoods
