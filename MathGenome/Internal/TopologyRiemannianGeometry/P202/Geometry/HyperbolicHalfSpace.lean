import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.HyperbolicHalfSpace
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.HyperboloidModel
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.EuclideanSphericalModels
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PullbackConnections
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace P202.Geometry.HyperbolicHalfSpace
open P202.HyperboloidData P202.HalfSpaceData

lemma spatialDot_self_nonneg {m : ℕ} (y : Spatial m) : 0 ≤ spatialDot y y :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (y i))

lemma lorentz_null {m : ℕ} (p : Ambient (m + 1)) :
    lorentz p p = spatialDot (fun i => p.1 i.castSucc) (fun i => p.1 i.castSucc) -
      nullU p * nullV p := by
  unfold lorentz spatialDot nullU nullV
  rw [Fin.sum_univ_castSucc]
  ring

lemma nullU_positive {m : ℕ} {a : ℝ} (ha : 0 < a)
    (p : Hyperboloid (m + 1) a) : 0 < nullU p.val := by
  have heq := p.property.1
  have hpos := p.property.2
  have hn := spatialDot_self_nonneg (fun i : Fin m => p.val.1 i.castSucc)
  rw [lorentz_null] at heq
  unfold nullU nullV at *
  nlinarith [sq_nonneg (p.val.2 - p.val.1 (Fin.last m)), sq_pos_of_pos ha]

lemma toHyperboloid_nullU {m : ℕ} (a : ℝ) (q : Coordinates m) :
    nullU (toHyperboloid a q) = a / q.2 := by
  simp [nullU, toHyperboloid]
  ring

lemma toHyperboloid_nullV {m : ℕ} (a : ℝ) (q : Coordinates m) :
    nullV (toHyperboloid a q) = a * (spatialDot q.1 q.1 + q.2 ^ 2) / q.2 := by
  simp [nullV, toHyperboloid]
  ring

lemma toHyperboloid_mem {m : ℕ} {a : ℝ} (ha : 0 < a)
    (q : HalfSpace m) : toHyperboloid a q.val ∈ upperSheet (m + 1) a := by
  have hz : 0 < q.val.2 := q.property
  constructor
  · rw [lorentz_null, toHyperboloid_nullU, toHyperboloid_nullV]
    simp only [toHyperboloid, Fin.snoc_castSucc]
    simp only [spatialDot, div_mul_div_comm, ← Finset.sum_div,
      show ∀ i : Fin m, a * q.val.1 i * (a * q.val.1 i) =
        a ^ 2 * (q.val.1 i * q.val.1 i) by intro i; ring,
      ← Finset.mul_sum]
    field_simp [ne_of_gt hz]
    ring
  · change 0 < (a * (spatialDot q.val.1 q.val.1 + q.val.2 ^ 2) / q.val.2 +
        a / q.val.2) / 2
    have hy := spatialDot_self_nonneg q.val.1
    positivity

lemma from_to {m : ℕ} {a : ℝ} (ha : 0 < a) (q : HalfSpace m) :
    fromHyperboloid a (toHyperboloid a q.val) = q.val := by
  have hz : q.val.2 ≠ 0 := ne_of_gt q.property
  have han : a ≠ 0 := ne_of_gt ha
  ext i
  · change (toHyperboloid a q.val).1 i.castSucc / nullU (toHyperboloid a q.val) = q.val.1 i
    rw [toHyperboloid_nullU]
    simp only [toHyperboloid, Fin.snoc_castSucc]
    field_simp
  · simp only [fromHyperboloid, toHyperboloid_nullU]
    field_simp

lemma fromHyperboloid_mem {m : ℕ} {a : ℝ} (ha : 0 < a)
    (p : Hyperboloid (m + 1) a) : fromHyperboloid a p.val ∈ domain m :=
  div_pos ha (nullU_positive ha p)

lemma to_from {m : ℕ} {a : ℝ} (ha : 0 < a) (p : Hyperboloid (m + 1) a) :
    toHyperboloid a (fromHyperboloid a p.val) = p.val := by
  have hU := nullU_positive ha p
  have han : a ≠ 0 := ne_of_gt ha
  have hUn : nullU p.val ≠ 0 := ne_of_gt hU
  have hUV : spatialDot (fun i : Fin m => p.val.1 i.castSucc)
      (fun i => p.val.1 i.castSucc) + a ^ 2 = nullU p.val * nullV p.val := by
    have h := p.property.1
    rw [lorentz_null] at h
    linarith
  have hsum : spatialDot (fromHyperboloid a p.val).1 (fromHyperboloid a p.val).1 =
      spatialDot (fun i : Fin m => p.val.1 i.castSucc)
        (fun i => p.val.1 i.castSucc) / nullU p.val ^ 2 := by
    simp only [fromHyperboloid, spatialDot, div_mul_div_comm, ← Finset.sum_div, pow_two]
  have hFu : nullU (toHyperboloid a (fromHyperboloid a p.val)) = nullU p.val := by
    rw [toHyperboloid_nullU]
    dsimp [fromHyperboloid]
    field_simp
  have hFv : nullV (toHyperboloid a (fromHyperboloid a p.val)) = nullV p.val := by
    rw [toHyperboloid_nullV, hsum]
    change a * (_ + (a / nullU p.val) ^ 2) / (a / nullU p.val) = _
    field_simp
    nlinarith [hUV]
  apply Prod.ext
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · dsimp [nullU, nullV] at hFu hFv
      linarith
    · simp only [toHyperboloid, fromHyperboloid, Fin.snoc_castSucc]
      field_simp
  · dsimp [nullU, nullV] at hFu hFv
    linarith

/-- The actual prescribed bijection, before its smoothness and metric proofs. -/
def halfSpaceEquiv {m : ℕ} {a : ℝ} (ha : 0 < a) :
    HalfSpace m ≃ Hyperboloid (m + 1) a where
  toFun q := ⟨toHyperboloid a q.val, toHyperboloid_mem ha q⟩
  invFun p := ⟨fromHyperboloid a p.val, fromHyperboloid_mem ha p⟩
  left_inv q := Subtype.ext (from_to ha q)
  right_inv p := Subtype.ext (to_from ha p)

lemma toHyperboloid_contDiffAt {m : ℕ} (a : ℝ) (q : Coordinates m) (hz : q.2 ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (toHyperboloid a) q := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : Coordinates m => spatialDot p.1 p.1) := by
    unfold spatialDot
    fun_prop
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.2
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      fun_prop (disch := assumption)
    · simp only [Fin.snoc_castSucc]
      fun_prop (disch := assumption)
  · change ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p : Coordinates m =>
        (a * (spatialDot p.1 p.1 + p.2 ^ 2) / p.2 + a / p.2) / 2) q
    fun_prop (disch := assumption)

lemma smooth_forward {m : ℕ} (a : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (toHyperboloid a) (domain m) := by
  intro q hq
  exact (toHyperboloid_contDiffAt a q (ne_of_gt hq)).contDiffWithinAt

lemma smooth_inverse {m : ℕ} (a : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fromHyperboloid a)
      {p : Ambient (m + 1) | 0 < nullU p} := by
  intro p hp
  have hU : nullU p ≠ 0 := ne_of_gt hp
  apply ContDiffAt.contDiffWithinAt
  have hnull : ContDiff ℝ (⊤ : ℕ∞) (@nullU m) := by unfold nullU; fun_prop
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi.2
    intro i
    change ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Ambient (m + 1) => q.1 i.castSucc / nullU q) p
    fun_prop (disch := assumption)
  · change ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Ambient (m + 1) => a / nullU q) p
    fun_prop (disch := assumption)

/-- Differential written in null coordinates, with no tangent certificate assumed. -/
def halfSpaceDifferential {m : ℕ} (a : ℝ) (q v : Coordinates m) : Ambient (m + 1) :=
  let du := -(a * v.2) / q.2 ^ 2
  let dv := (a * (2 * spatialDot q.1 v.1 + 2 * q.2 * v.2) * q.2 -
    a * (spatialDot q.1 q.1 + q.2 ^ 2) * v.2) / q.2 ^ 2
  (Fin.snoc (fun i => (a * v.1 i * q.2 - a * q.1 i * v.2) / q.2 ^ 2)
    ((dv - du) / 2), (dv + du) / 2)

lemma derivative_along_line {m : ℕ} (a : ℝ) (q v : Coordinates m) (hz : q.2 ≠ 0) :
    HasDerivAt (fun t : ℝ => toHyperboloid a
      ((fun i => q.1 i + t * v.1 i), q.2 + t * v.2))
      (halfSpaceDifferential a q v) 0 := by
  have hy (i : Fin m) : HasDerivAt (fun t : ℝ => q.1 i + t * v.1 i) (v.1 i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.1 i)).const_add (q.1 i)
  have ht : HasDerivAt (fun t : ℝ => q.2 + t * v.2) v.2 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_add q.2
  have hd : HasDerivAt (fun t : ℝ => spatialDot
      (fun i => q.1 i + t * v.1 i) (fun i => q.1 i + t * v.1 i))
      (2 * spatialDot q.1 v.1) 0 := by
    have h := HasDerivAt.sum (u := Finset.univ) (fun i _ => (hy i).mul (hy i))
    convert h using 1 <;>
      simp [spatialDot, Finset.sum_add_distrib, mul_comm, two_mul]
    funext t
    simp
  have hu : HasDerivAt (fun t : ℝ => a / (q.2 + t * v.2))
      (-(a * v.2) / q.2 ^ 2) 0 := by
    convert (hasDerivAt_const (0 : ℝ) a).div ht (by simpa using hz) using 1 <;> simp
  have hv : HasDerivAt (fun t : ℝ =>
      a * (spatialDot (fun i => q.1 i + t * v.1 i)
        (fun i => q.1 i + t * v.1 i) + (q.2 + t * v.2) ^ 2) / (q.2 + t * v.2))
      ((a * (2 * spatialDot q.1 v.1 + 2 * q.2 * v.2) * q.2 -
        a * (spatialDot q.1 q.1 + q.2 ^ 2) * v.2) / q.2 ^ 2) 0 := by
    convert ((hd.add (ht.pow 2)).const_mul a).div ht (by simpa using hz) using 1 <;> simp
  apply HasDerivAt.prodMk
  · apply hasDerivAt_pi.2
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [toHyperboloid, halfSpaceDifferential, Fin.snoc_last, Pi.sub_apply] using
        (hv.sub hu).div_const 2
    · simp only [Fin.snoc_castSucc]
      convert ((hy j).const_mul a).div ht (by simpa using hz) using 1 <;> simp
  · simpa only [toHyperboloid, halfSpaceDifferential, Pi.add_apply] using (hv.add hu).div_const 2

lemma fderiv_eq {m : ℕ} (a : ℝ) (q v : Coordinates m) (hz : q.2 ≠ 0) :
    fderiv ℝ (toHyperboloid a) q v = halfSpaceDifferential a q v := by
  have hc : HasDerivAt (fun t : ℝ =>
      ((fun i => q.1 i + t * v.1 i), q.2 + t * v.2)) v 0 := by
    apply HasDerivAt.prodMk
    · apply hasDerivAt_pi.2
      intro i
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.1 i)).const_add (q.1 i)
    · simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_add q.2
  have hF := (toHyperboloid_contDiffAt a q hz).differentiableAt (by simp)
  exact (hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by simp)).unique
    (derivative_along_line a q v hz)

lemma lorentz_bilinear_null {m : ℕ} (p r : Ambient (m + 1)) :
    lorentz p r = spatialDot (fun i => p.1 i.castSucc) (fun i => r.1 i.castSucc) -
      (nullU p * nullV r + nullV p * nullU r) / 2 := by
  unfold lorentz spatialDot nullU nullV
  rw [Fin.sum_univ_castSucc]
  ring

lemma differential_nullU {m : ℕ} (a : ℝ) (q v : Coordinates m) :
    nullU (halfSpaceDifferential a q v) = -(a * v.2) / q.2 ^ 2 := by
  simp [nullU, halfSpaceDifferential]
  ring

lemma differential_nullV {m : ℕ} (a : ℝ) (q v : Coordinates m) :
    nullV (halfSpaceDifferential a q v) =
      (a * (2 * spatialDot q.1 v.1 + 2 * q.2 * v.2) * q.2 -
        a * (spatialDot q.1 q.1 + q.2 ^ 2) * v.2) / q.2 ^ 2 := by
  simp [nullV, halfSpaceDifferential]
  ring

lemma differential_spatialDot {m : ℕ} (a : ℝ) (q v w : Coordinates m) (hz : q.2 ≠ 0) :
    spatialDot (fun i => (halfSpaceDifferential a q v).1 i.castSucc)
      (fun i => (halfSpaceDifferential a q w).1 i.castSucc) =
    (a ^ 2 * q.2 ^ 2 * spatialDot v.1 w.1 -
      a ^ 2 * q.2 * w.2 * spatialDot v.1 q.1 -
      a ^ 2 * q.2 * v.2 * spatialDot q.1 w.1 +
      a ^ 2 * v.2 * w.2 * spatialDot q.1 q.1) / q.2 ^ 4 := by
  simp only [halfSpaceDifferential, Fin.snoc_castSucc, spatialDot, div_mul_div_comm]
  rw [← Finset.sum_div]
  have h (i : Fin m) :
      (a * v.1 i * q.2 - a * q.1 i * v.2) * (a * w.1 i * q.2 - a * q.1 i * w.2) =
      a ^ 2 * q.2 ^ 2 * (v.1 i * w.1 i) -
      a ^ 2 * q.2 * w.2 * (v.1 i * q.1 i) -
      a ^ 2 * q.2 * v.2 * (q.1 i * w.1 i) +
      a ^ 2 * v.2 * w.2 * (q.1 i * q.1 i) := by ring
  simp_rw [h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp

lemma metric_pullback {m : ℕ} (a : ℝ) (q : HalfSpace m) (v w : Coordinates m) :
    lorentz (fderiv ℝ (toHyperboloid a) q.val v)
      (fderiv ℝ (toHyperboloid a) q.val w) = halfMetric a q.val v w := by
  have hz : q.val.2 ≠ 0 := ne_of_gt q.property
  rw [fderiv_eq a q.val v hz, fderiv_eq a q.val w hz, lorentz_bilinear_null,
    differential_nullU, differential_nullU, differential_nullV, differential_nullV,
    differential_spatialDot a q.val v w hz]
  have hcomm : spatialDot v.1 q.val.1 = spatialDot q.val.1 v.1 := by
    unfold spatialDot
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcomm]
  unfold halfMetric
  field_simp
  ring

/-- Coordinate proof of the genuine smooth bijective isometry. -/
def halfSpaceIsometry {m : ℕ} {a : ℝ} (ha : 0 < a) : HalfSpaceIsometry m a where
  equiv := halfSpaceEquiv ha
  forward _ := rfl
  inverse _ := rfl
  positive_null := nullU_positive ha
  smooth_forward := smooth_forward a
  smooth_inverse := smooth_inverse a
  metric_pullback := metric_pullback a

/-- The prescribed bijection is also a homeomorphism for the original
subspace topologies.  Both maps have smooth ambient extensions. -/
def halfSpaceHomeomorph {m : ℕ} {a : ℝ} (ha : 0 < a) :
    HalfSpace m ≃ₜ Hyperboloid (m + 1) a where
  toEquiv := halfSpaceEquiv ha
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (smooth_forward a).continuousOn.comp_continuous continuous_subtype_val
      (fun q => q.property)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (smooth_inverse a).continuousOn.comp_continuous continuous_subtype_val
      (fun p => nullU_positive ha p)

/-- Positive definiteness of the specified half-space coordinate metric. -/
lemma halfMetric_positive {m : ℕ} {a : ℝ} (ha : 0 < a)
    (q : HalfSpace m) (v : Coordinates m) (hv : v ≠ 0) :
    0 < halfMetric a q.val v v := by
  have hdot := spatialDot_self_nonneg v.1
  have hsum : 0 < spatialDot v.1 v.1 + v.2 * v.2 := by
    by_contra h
    have he : spatialDot v.1 v.1 + v.2 * v.2 = 0 := by nlinarith [mul_self_nonneg v.2]
    have hz : v.2 = 0 := by nlinarith [mul_self_nonneg v.2]
    have hy : v.1 = 0 := by
      funext i
      have hi : v.1 i * v.1 i ≤ spatialDot v.1 v.1 :=
        Finset.single_le_sum (fun j _ => mul_self_nonneg (v.1 j)) (Finset.mem_univ i)
      have : v.1 i = 0 := by nlinarith [mul_self_nonneg (v.1 i)]
      exact this
    exact hv (Prod.ext hy hz)
  unfold halfMetric
  exact mul_pos (div_pos (sq_pos_of_pos ha) (sq_pos_of_pos q.property)) hsum

open SmoothManifolds.ModelData (ModelChart)
open SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.DifferentialData P202.ConnectionData P202.MetricData
open Set Filter
open scoped Topology

/-- Standard linear concatenation of horizontal and vertical coordinates. -/
def snocLinear (m : ℕ) : Coordinates m ≃L[ℝ] Spatial (m + 1) where
  toFun q := Fin.snoc q.1 q.2
  invFun x := ((fun i => x i.castSucc), x (Fin.last m))
  left_inv q := by ext <;> simp
  right_inv x := by funext i; exact Fin.lastCases (by simp) (fun j => by simp) i
  map_add' q r := by ext i; exact Fin.lastCases (by simp) (fun j => by simp) i
  map_smul' r q := by ext i; exact Fin.lastCases (by simp) (fun j => by simp) i
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using (continuous_snd : Continuous (fun q : Coordinates m => q.2))
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        (continuous_apply j).comp (continuous_fst : Continuous (fun q : Coordinates m => q.1))
  continuous_invFun := by fun_prop

lemma domain_open (m : ℕ) : IsOpen (domain m) :=
  isOpen_lt continuous_const continuous_snd

instance halfSpace_nonempty (m : ℕ) : Nonempty (HalfSpace m) :=
  ⟨⟨(0, 1), by change (0 : ℝ) < 1; norm_num⟩⟩

/-- The one global chart uses the literal coordinates (y,z), with z>0. -/
def halfSpaceChart (m : ℕ) : ModelChart (m + 1) .euclidean (HalfSpace m) :=
  (⟨domain m, domain_open m⟩ : TopologicalSpace.Opens (Coordinates m)).openPartialHomeomorphSubtypeCoe
    ⟨⟨(0, 1), by change (0 : ℝ) < 1; norm_num⟩⟩ |>.trans
    ((snocLinear m).toHomeomorph.trans
      (P202.Geometry.HyperboloidModel.euclideanModelHomeomorph (m + 1))).toOpenPartialHomeomorph

@[simp] lemma halfSpaceChart_apply (m : ℕ) (q : HalfSpace m) :
    (halfSpaceChart m q).val = Fin.snoc q.val.1 q.val.2 := rfl

@[simp] lemma halfSpaceChart_source (m : ℕ) : (halfSpaceChart m).source = univ := by
  ext q; simp [halfSpaceChart]

lemma halfSpaceChart_target (m : ℕ) :
    (halfSpaceChart m).target = {x | 0 < x.val (Fin.last m)} := by
  unfold halfSpaceChart
  rw [OpenPartialHomeomorph.trans_target,
    TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  ext x
  simp [domain, snocLinear, P202.Geometry.HyperboloidModel.euclideanModelHomeomorph]
  rfl

lemma halfSpaceChart_atlas (m : ℕ) :
    IsContDiffAtlas (⊤ : ℕ∞) {halfSpaceChart m} := by
  constructor
  · intro q
    exact ⟨halfSpaceChart m, mem_singleton _, halfSpaceChart_source m ▸ mem_univ _⟩
  · intro c hc d hd
    rcases mem_singleton_iff.mp hc with rfl
    rcases mem_singleton_iff.mp hd with rfl
    constructor <;> intro x hx <;>
      refine ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
    all_goals
      intro y hy _
      have he := (halfSpaceChart m).right_inv hy.1
      simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.symm_symm, id_eq] using congrArg Subtype.val he.symm

/-- Standard smooth structure on the open upper half-space. -/
def halfSpaceManifold (m : ℕ) : SmoothManifold (m + 1) .euclidean (HalfSpace m) where
  topologicalManifold :=
    { hausdorff := inferInstance
      secondCountable := inferInstance
      atlas := {halfSpaceChart m}
      covers := (halfSpaceChart_atlas m).1 }
  smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) {halfSpaceChart m},
    SmoothManifolds.maximalExtension_isMaximal (halfSpaceChart_atlas m)⟩

lemma halfSpaceChart_mem (m : ℕ) :
    halfSpaceChart m ∈ (halfSpaceManifold m).smoothStructure.val :=
  SmoothManifolds.subset_maximalExtension (halfSpaceChart_atlas m) (mem_singleton _)

/-- Tangent coordinates are the intrinsic chart-coordinate equivalence. -/
def halfSpaceCoordinates {m : ℕ} (q : HalfSpace m) :
    TangentSpace (halfSpaceManifold m) q ≃ₗ[ℝ] Coordinates m :=
  ((tangentStructure (halfSpaceManifold m)).fiberCoordinates.equiv
    (halfSpaceChart m) (halfSpaceChart_mem m) q
    (halfSpaceChart_source m ▸ mem_univ _)).trans (snocLinear m).symm.toLinearEquiv

lemma halfSpaceCoordinates_standard {m : ℕ} (q : HalfSpace m)
    (v : TangentSpace (halfSpaceManifold m) q) :
    halfSpaceCoordinates q v =
      ((fun i => scalarDerivative (halfSpaceManifold m) (fun p => p.val.1 i) q v),
        scalarDerivative (halfSpaceManifold m) (fun p => p.val.2) q v) := by
  apply Prod.ext
  · funext i
    symm
    change scalarDerivative (halfSpaceManifold m) (fun p => p.val.1 i) q v = _
    rw [P202.Geometry.HyperboloidModel.scalarDerivative_chart
      (halfSpaceManifold m) (halfSpaceChart m) (halfSpaceChart_mem m) q
      (halfSpaceChart_source m ▸ mem_univ _) (fun p => p.val.1 i) (fun x => x i.castSucc)
      (contDiff_apply ℝ (fun _ : Fin (m + 1) => ℝ) i.castSucc)
      (fun p => by simp)]
    rw [(hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin (m + 1) => ℝ) i.castSucc _).fderiv]
    rfl
  · symm
    rw [P202.Geometry.HyperboloidModel.scalarDerivative_chart
      (halfSpaceManifold m) (halfSpaceChart m) (halfSpaceChart_mem m) q
      (halfSpaceChart_source m ▸ mem_univ _) (fun p => p.val.2) (fun x => x (Fin.last m))
      (contDiff_apply ℝ (fun _ : Fin (m + 1) => ℝ) (Fin.last m))
      (fun p => by simp)]
    rw [(hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin (m + 1) => ℝ) (Fin.last m) _).fderiv]
    rfl

/-- Smoothness of the explicit map for every standard projection atlas on
its target, using the literal open half-space chart on its source. -/
lemma halfSpace_forward_smooth {m : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold (m + 1) .euclidean (Hyperboloid (m + 1) a))
    (c : ModelChart (m + 1) .euclidean (Hyperboloid (m + 1) a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1) :
    IsSmoothMap (halfSpaceManifold m) S (halfSpaceEquiv ha) := by
  intro q
  apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart _ _ _
    (halfSpaceManifold m).smoothStructure.property.1 S.smoothStructure.property.1 _ q).mpr
  refine ⟨(halfSpaceHomeomorph ha).continuous.continuousAt,
    halfSpaceChart m, halfSpaceChart_mem m, c, hc,
    halfSpaceChart_source m ▸ mem_univ _, hs ▸ mem_univ _, ?_⟩
  refine ⟨{x | 0 < x (Fin.last m)}, isOpen_lt continuous_const (continuous_apply _),
    ?_, (fun x => (toHyperboloid a ((snocLinear m).symm x)).1), ?_, ?_⟩
  · simpa only [Set.mem_ofPred_eq, halfSpaceChart_apply, Fin.snoc_last] using (show 0 < q.val.2 from q.property)
  · apply ((smooth_forward a).fst).comp (snocLinear m).symm.contDiff.contDiffOn
    intro x hx
    exact hx
  · apply Eventually.of_forall
    intro p
    dsimp only
    rw [hproj]
    change (toHyperboloid a ((snocLinear m).symm ((snocLinear m) p.val))).1 = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl

lemma halfSpace_inverse_smooth {m : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold (m + 1) .euclidean (Hyperboloid (m + 1) a))
    (c : ModelChart (m + 1) .euclidean (Hyperboloid (m + 1) a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1) :
    IsSmoothMap S (halfSpaceManifold m) (halfSpaceEquiv ha).symm := by
  intro p
  apply (SmoothManifolds.manifoldContDiffAt_iff_oneChart _ _ _
    S.smoothStructure.property.1 (halfSpaceManifold m).smoothStructure.property.1 _ p).mpr
  refine ⟨(halfSpaceHomeomorph ha).symm.continuous.continuousAt,
    c, hc, halfSpaceChart m, halfSpaceChart_mem m,
    hs ▸ mem_univ _, halfSpaceChart_source m ▸ mem_univ _, ?_⟩
  refine ⟨univ, isOpen_univ, mem_univ _,
    (fun x => snocLinear m (fromHyperboloid a (graphPoint a x))), ?_, ?_⟩
  · apply (snocLinear m).contDiff.contDiffOn.comp
      ((smooth_inverse a).comp
        (P202.Geometry.HyperboloidModel.graph_smooth (m + 1) a ha).contDiffOn ?_)
      (mapsTo_univ _ _)
    intro x _
    exact nullU_positive ha ⟨graphPoint a x, P202.Geometry.HyperboloidModel.graphPoint_mem ha x⟩
  · apply Eventually.of_forall
    intro r
    dsimp only
    rw [hproj, show graphPoint a r.val.1 = r.val from
      P202.Geometry.HyperboloidModel.graphPoint_projection r]
    rfl

/-- An actual diffeomorphism between the original intrinsic smooth structures. -/
def halfSpaceDiffeomorph {m : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold (m + 1) .euclidean (Hyperboloid (m + 1) a))
    (c : ModelChart (m + 1) .euclidean (Hyperboloid (m + 1) a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1) :
    Diffeomorph (halfSpaceManifold m).smoothStructure.val S.smoothStructure.val where
  toEquiv := halfSpaceEquiv ha
  contDiff_toFun := halfSpace_forward_smooth ha S c hc hs hproj
  contDiff_invFun := halfSpace_inverse_smooth ha S c hc hs hproj

/-- Local chart representatives compute scalar differentiation on the
intrinsic derivation tangent fibers. Only smoothness near the point is needed. -/
lemma scalarDerivative_localChart {n : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (c : ModelChart n .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (f : M → ℝ) (F : Spatial n → ℝ) (U : Set (Spatial n))
    (hU : IsOpen U) (hpU : (c p).val ∈ U) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hf : ∀ q, F (c q).val = f q) (v : TangentSpace S p) :
    scalarDerivative S f p v = fderiv ℝ F (c p).val
      ((tangentStructure S).fiberCoordinates.equiv c hc p hp v) := by
  have hscalar := SmoothManifolds.scalarContDiffAt_of_chart
    S.smoothStructure.property.1 hc hp
    ⟨U, hU, hpU, F, hF, Eventually.of_forall hf⟩
  have hrep : (scalarGerm S f p).val = Germ.ofFun f := by
    simp only [scalarGerm, dite_eq_left hscalar]
  exact SmoothManifolds.VectorFields.tangent_action_coordinates S
    (tangentStructure S).fiberCoordinates p c hc hp v (scalarGerm S f p) F
    ⟨⟨U, hU, hpU, hF⟩,
      (Germ.coe_eq.mpr (Eventually.of_forall hf)).trans hrep.symm⟩

/-- Differentiating a scalar function in the actual open half-space chart
agrees with its ambient Fréchet derivative. -/
lemma halfSpace_scalarDerivative {m : ℕ} (F : Coordinates m → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (domain m))
    (q : HalfSpace m) (v : TangentSpace (halfSpaceManifold m) q) :
    scalarDerivative (halfSpaceManifold m) (fun p => F p.val) q v =
      fderiv ℝ F q.val (halfSpaceCoordinates q v) := by
  let U : Set (Spatial (m + 1)) := {x | 0 < x (Fin.last m)}
  let G : Spatial (m + 1) → ℝ := fun x => F ((snocLinear m).symm x)
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G U :=
    hF.comp (snocLinear m).symm.contDiff.contDiffOn (fun x hx => hx)
  rw [scalarDerivative_localChart (halfSpaceManifold m) (halfSpaceChart m)
    (halfSpaceChart_mem m) q (halfSpaceChart_source m ▸ mem_univ _) _ G U
    (isOpen_lt continuous_const (continuous_apply _))
    (by simpa only [U, Set.mem_ofPred_eq, halfSpaceChart_apply, Fin.snoc_last] using (show 0 < q.val.2 from q.property)) hG
    (fun p => (snocLinear m).symm_apply_apply p.val ▸ rfl)]
  have hdF : DifferentiableAt ℝ F q.val :=
    ((hF q.val q.property).contDiffAt ((domain_open m).mem_nhds q.property)).differentiableAt (by simp)
  have hdG : HasFDerivAt G
      ((fderiv ℝ F q.val).comp (snocLinear m).symm.toContinuousLinearMap)
      ((snocLinear m) q.val) := by
    have hdF' : HasFDerivAt F (fderiv ℝ F q.val)
        ((snocLinear m).symm ((snocLinear m) q.val)) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hdF.hasFDerivAt
    exact hdF'.comp ((snocLinear m) q.val) (snocLinear m).symm.hasFDerivAt
  change fderiv ℝ G ((snocLinear m) q.val) _ = _
  rw [hdG.fderiv]
  rfl

/-- The intrinsic differential of the isometry is exactly the already
computed ambient derivative, with the prescribed source tangent coordinates. -/
lemma halfSpace_differential_ambient {m : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold (m + 1) .euclidean (Hyperboloid (m + 1) a))
    (c : ModelChart (m + 1) .euclidean (Hyperboloid (m + 1) a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1)
    (q : HalfSpace m) (v : TangentSpace (halfSpaceManifold m) q) :
    ambientDifferential S (halfSpaceEquiv ha q)
      (SmoothManifolds.differential (halfSpaceManifold m) S (halfSpaceEquiv ha)
        (halfSpace_forward_smooth ha S c hc hs hproj) q v) =
      fderiv ℝ (toHyperboloid a) q.val (halfSpaceCoordinates q v) := by
  let hf := halfSpace_forward_smooth ha S c hc hs hproj
  have hinc := P202.Geometry.HyperboloidModel.inclusion_smoothAt ha S c hc hs hproj
    (halfSpaceEquiv ha q)
  have hdF := (toHyperboloid_contDiffAt a q.val (ne_of_gt q.property)).differentiableAt (by simp)
  apply Prod.ext
  · funext i
    change scalarDerivative S (fun p => p.val.1 i) _ _ = _
    rw [← P202.Geometry.PullbackConnections.scalar_chain_local (halfSpaceEquiv ha) hf
      (fun p => p.val.1 i) q
      ((SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr
        (hinc.postcomp ((ContinuousLinearMap.proj (R := ℝ) i).comp
          (ContinuousLinearMap.fst ℝ (Spatial (m + 1)) ℝ)).contDiff)) v]
    change scalarDerivative (halfSpaceManifold m) (fun p => (toHyperboloid a p.val).1 i) q v = _
    rw [halfSpace_scalarDerivative _ (contDiffOn_pi.mp (smooth_forward a).fst i)]
    exact congrArg (fun L => L (halfSpaceCoordinates q v))
      (((ContinuousLinearMap.proj (R := ℝ) i).comp
        (ContinuousLinearMap.fst ℝ (Spatial (m + 1)) ℝ)).hasFDerivAt.comp q.val hdF.hasFDerivAt).fderiv
  · change scalarDerivative S (fun p => p.val.2) _ _ = _
    rw [← P202.Geometry.PullbackConnections.scalar_chain_local (halfSpaceEquiv ha) hf
      (fun p => p.val.2) q
      ((SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr
        (hinc.postcomp (ContinuousLinearMap.snd ℝ (Spatial (m + 1)) ℝ).contDiff)) v]
    change scalarDerivative (halfSpaceManifold m) (fun p => (toHyperboloid a p.val).2) q v = _
    rw [halfSpace_scalarDerivative _ (smooth_forward a).snd]
    exact congrArg (fun L => L (halfSpaceCoordinates q v)) ((ContinuousLinearMap.snd ℝ (Spatial (m + 1)) ℝ).hasFDerivAt.comp q.val hdF.hasFDerivAt).fderiv

/-- The pullback of any induced target metric is the specified half-space
metric on the original derivation tangent fibers. -/
lemma intrinsicHalfSpaceIsometry {m : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold (m + 1) .euclidean (Hyperboloid (m + 1) a))
    (g : RiemannianMetric S)
    (hchart : ∃ c ∈ S.smoothStructure.val, c.source = univ ∧ c.target = univ ∧
      ∀ p, (c p).val = p.val.1) (hg : IsInduced g) :
    ∃ H : HalfSpaceModel m a,
    ∃ d : Diffeomorph H.manifold.smoothStructure.val S.smoothStructure.val,
      (∀ q, (d.toEquiv q).val = toHyperboloid a q.val) ∧
      (∀ p, (d.toEquiv.symm p).val = fromHyperboloid a p.val) ∧
      ∃ L : (q : HalfSpace m) →
        TangentSpace H.manifold q →ₗ[ℝ] TangentSpace S (d.toEquiv q),
        (∀ q, IsDifferential H.manifold S d.toEquiv q (L q)) ∧
        IsMetricPreserving H.metric g d.toEquiv L := by
  obtain ⟨c, hc, hs, _ht, hproj⟩ := hchart
  let d := halfSpaceDiffeomorph ha S c hc hs hproj
  let hf := halfSpace_forward_smooth ha S c hc hs hproj
  let L := SmoothManifolds.differential (halfSpaceManifold m) S (halfSpaceEquiv ha) hf
  have hL := SmoothManifolds.differential_spec (halfSpaceManifold m) S (halfSpaceEquiv ha) hf
  have hinj (q : HalfSpace m) : Function.Injective (L q) := by
    obtain ⟨E, hE⟩ := SmoothManifolds.differential_diffeomorph (halfSpaceManifold m) S d q
    have he := (SmoothManifolds.differential_exists (halfSpaceManifold m) S
      (halfSpaceEquiv ha) hf q).unique (hL q) hE
    rw [show L q = E.toLinearMap from he]
    exact E.injective
  let i : SmoothImmersion (halfSpaceManifold m) S (halfSpaceEquiv ha) := ⟨hf, L, hL, hinj⟩
  let gH := P202.Geometry.SmoothMetrics.pullbackMetric g (halfSpaceEquiv ha) i
  have hmetric (q : HalfSpace m) (v w : TangentSpace (halfSpaceManifold m) q) :
      pairing gH q v w = halfMetric a q.val (halfSpaceCoordinates q v) (halfSpaceCoordinates q w) := by
    change pairing g (halfSpaceEquiv ha q) (L q v) (L q w) = _
    rw [hg]
    rw [halfSpace_differential_ambient ha S c hc hs hproj q v,
      halfSpace_differential_ambient ha S c hc hs hproj q w]
    exact metric_pullback a q _ _
  let H : HalfSpaceModel m a :=
    { manifold := halfSpaceManifold m
      standard_chart := ⟨halfSpaceChart m, halfSpaceChart_mem m, halfSpaceChart_source m,
        halfSpaceChart_target m, halfSpaceChart_apply m⟩
      coordinates := halfSpaceCoordinates
      coordinates_standard := halfSpaceCoordinates_standard
      metric := gH
      metric_standard := hmetric }
  exact ⟨H, d, fun _ => rfl, fun _ => rfl, L, hL, fun _ _ _ => rfl⟩

/-- The hyperbolic portion of the three-model theorem is fully intrinsic. -/
lemma hyperbolic_models :
    P202Specs.Geometry.HyperboloidModel.intrinsic_modelType ∧
    P202Specs.Geometry.HyperboloidModel.topologyType ∧
    P202Specs.Geometry.HyperbolicHalfSpace.isometryType ∧
    P202Specs.Geometry.HyperbolicHalfSpace.intrinsicIsometryType := by
  refine ⟨P202.Geometry.HyperboloidModel.intrinsic_model,
    P202.Geometry.HyperboloidModel.topology, ?_, ?_⟩
  · intro m a ha
    exact ⟨halfSpaceIsometry ha⟩
  · intro m _hm a ha S g hchart hg
    exact intrinsicHalfSpaceIsometry ha S g hchart hg

/-- The explicit smooth coordinate isometry, for every positive radius. -/
theorem isometry : P202Specs.Geometry.HyperbolicHalfSpace.isometryType :=
  hyperbolic_models.2.2.1

/-- The same isometry on the canonical intrinsic tangent fibers and metrics. -/
theorem intrinsic_isometry : P202Specs.Geometry.HyperbolicHalfSpace.intrinsicIsometryType :=
  hyperbolic_models.2.2.2

/-- The complete three-model theorem, including the half-space isometry.
The Euclidean, spherical and hyperbolic conclusions are all proved upstream;
none is an additional premise of this theorem. -/
theorem models : P202Specs.Geometry.HyperbolicHalfSpace.modelsType :=
  ⟨P202.Geometry.EuclideanSphericalModels.models, hyperbolic_models⟩

end P202.Geometry.HyperbolicHalfSpace
