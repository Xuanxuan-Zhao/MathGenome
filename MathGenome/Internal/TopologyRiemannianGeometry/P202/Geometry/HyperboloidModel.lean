import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.HyperboloidModel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.SmoothMaps
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothMetrics
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GeodesicIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.HopfRinow
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
open scoped BigOperators
namespace P202.Geometry.HyperboloidModel
open P202.HyperboloidData

abbrev lorentz := @P202.HyperboloidData.lorentz
abbrev upperSheet := P202.HyperboloidData.upperSheet
noncomputable abbrev graphPoint := @P202.HyperboloidData.graphPoint
noncomputable abbrev unitCurve := @P202.HyperboloidData.unitCurve

variable {n : ℕ}

lemma spatialDot_comm (x y : Spatial n) : spatialDot x y = spatialDot y x := by
  simp only [spatialDot, mul_comm]

lemma spatialDot_self_nonneg (x : Spatial n) : 0 ≤ spatialDot x x := by
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

lemma spatialDot_self_eq_zero (x : Spatial n) : spatialDot x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have hi : x i * x i ≤ spatialDot x x :=
      Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
    have : x i = 0 := by nlinarith
    exact this
  · rintro rfl
    simp [spatialDot]

lemma spatialDot_cauchy (x y : Spatial n) :
    spatialDot x y ^ 2 ≤ spatialDot x x * spatialDot y y := by
  simpa only [spatialDot, ← pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y)

lemma lorentz_comm (p q : Ambient n) : lorentz p q = lorentz q p := by
  simp only [lorentz, P202.HyperboloidData.lorentz, spatialDot_comm, mul_comm]

lemma lorentz_add_left (p q r : Ambient n) :
    lorentz (p + q) r = lorentz p r + lorentz q r := by
  simp only [lorentz, P202.HyperboloidData.lorentz, spatialDot, Prod.fst_add,
    Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

lemma lorentz_smul_left (c : ℝ) (p q : Ambient n) :
    lorentz (c • p) q = c * lorentz p q := by
  simp only [lorentz, P202.HyperboloidData.lorentz, spatialDot, Prod.smul_fst,
    Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

lemma lorentz_add_right (p q r : Ambient n) :
    lorentz p (q + r) = lorentz p q + lorentz p r := by
  rw [lorentz_comm, lorentz_add_left, lorentz_comm q p, lorentz_comm r p]

lemma lorentz_smul_right (c : ℝ) (p q : Ambient n) :
    lorentz p (c • q) = c * lorentz p q := by
  rw [lorentz_comm, lorentz_smul_left, lorentz_comm q p]

lemma graphPoint_mem {a : ℝ} (ha : 0 < a) (x : Spatial n) :
    graphPoint a x ∈ upperSheet n a := by
  have hpos : 0 < a ^ 2 + spatialDot x x :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (spatialDot_self_nonneg x)
  constructor
  · change spatialDot x x - Real.sqrt (a ^ 2 + spatialDot x x) *
      Real.sqrt (a ^ 2 + spatialDot x x) = -(a ^ 2)
    nlinarith [Real.sq_sqrt hpos.le]
  · exact Real.sqrt_pos.mpr hpos

lemma graphPoint_projection {a : ℝ} (p : Hyperboloid n a) :
    graphPoint a p.val.1 = p.val := by
  apply Prod.ext
  · rfl
  change Real.sqrt (a ^ 2 + spatialDot p.val.1 p.val.1) = p.val.2
  have he := p.property.1
  change spatialDot p.val.1 p.val.1 - p.val.2 * p.val.2 = -(a ^ 2) at he
  have hs : a ^ 2 + spatialDot p.val.1 p.val.1 = p.val.2 ^ 2 := by nlinarith
  rw [hs, Real.sqrt_sq p.property.2.le]

noncomputable def projectionHomeomorph (n : ℕ) (a : ℝ) (ha : 0 < a) :
    Hyperboloid n a ≃ₜ Spatial n where
  toFun p := p.val.1
  invFun x := ⟨graphPoint a x, graphPoint_mem ha x⟩
  left_inv p := Subtype.ext (graphPoint_projection p)
  right_inv _ := rfl
  continuous_toFun := continuous_fst.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    unfold graphPoint P202.HyperboloidData.graphPoint spatialDot
    fun_prop

theorem projection_homeomorph :
    P202Specs.Geometry.HyperboloidModel.projection_homeomorphType := by
  intro n a ha
  exact ⟨projectionHomeomorph n a ha, fun _ => rfl, fun _ => rfl⟩

lemma tangent_time {a : ℝ} {p v : Ambient n} (hp : p ∈ upperSheet n a)
    (hv : v ∈ tangentPlane p) : v.2 = spatialDot p.1 v.1 / p.2 := by
  apply (eq_div_iff (ne_of_gt hp.2)).mpr
  change spatialDot p.1 v.1 - p.2 * v.2 = 0 at hv
  nlinarith

lemma tangent_coercivity {a : ℝ} {p v : Ambient n}
    (hp : p ∈ upperSheet n a) (hv : v ∈ tangentPlane p) :
    a ^ 2 * spatialDot v.1 v.1 ≤ p.2 ^ 2 * lorentz v v := by
  have hcs := spatialDot_cauchy p.1 v.1
  change spatialDot p.1 v.1 - p.2 * v.2 = 0 at hv
  have he := hp.1
  change spatialDot p.1 p.1 - p.2 * p.2 = -(a ^ 2) at he
  change a ^ 2 * spatialDot v.1 v.1 ≤
    p.2 ^ 2 * (spatialDot v.1 v.1 - v.2 * v.2)
  have he' : spatialDot p.1 p.1 = p.2 ^ 2 - a ^ 2 := by nlinarith
  rw [sub_eq_zero.mp hv, he'] at hcs
  nlinarith

theorem tangent_lower_bound :
    P202Specs.Geometry.HyperboloidModel.tangent_lower_boundType := by
  intro n a ha p hp v hv
  have ht : 0 < p.2 ^ 2 := sq_pos_of_pos hp.2
  rw [div_mul_eq_mul_div, div_le_iff₀ ht]
  simpa only [mul_comm] using tangent_coercivity hp hv

theorem tangent_positive :
    P202Specs.Geometry.HyperboloidModel.tangent_positiveType := by
  intro n a ha p hp v hv hne
  have hx : v.1 ≠ 0 := by
    intro hx
    have ht := tangent_time hp hv
    have hz : v.2 = 0 := by simpa [hx, spatialDot] using ht
    apply hne
    exact Prod.ext hx hz
  have hd : 0 < spatialDot v.1 v.1 :=
    lt_of_le_of_ne (spatialDot_self_nonneg _) (Ne.symm fun h => hx ((spatialDot_self_eq_zero _).mp h))
  have hpos : 0 < a ^ 2 * spatialDot v.1 v.1 := mul_pos (sq_pos_of_pos ha) hd
  have hc := tangent_coercivity hp hv
  have ht : 0 < p.2 ^ 2 := sq_pos_of_pos hp.2
  exact (mul_pos_iff_of_pos_left ht).mp (lt_of_lt_of_le hpos hc)

lemma unitCurve_zero (a : ℝ) (p u : Ambient n) : unitCurve a p u 0 = p := by
  simp [unitCurve, P202.HyperboloidData.unitCurve]

lemma unitVelocity_zero (a : ℝ) (p u : Ambient n) : unitVelocity a p u 0 = u := by
  simp [unitVelocity]

lemma unitCurve_deriv {a : ℝ} (ha : a ≠ 0) (p u : Ambient n) (t : ℝ) :
    HasDerivAt (unitCurve a p u) (unitVelocity a p u t) t := by
  have hd : HasDerivAt (fun s : ℝ => s / a) (1 / a) t :=
    (hasDerivAt_id t).div_const a
  convert (hd.cosh.smul_const p).add ((hd.sinh.const_mul a).smul_const u) using 1 <;>
    simp only [unitCurve, unitVelocity] <;>
    congr 1 <;> field_simp

lemma unitVelocity_deriv {a : ℝ} (ha : a ≠ 0) (p u : Ambient n) (t : ℝ) :
    HasDerivAt (unitVelocity a p u) (unitAcceleration a p u t) t := by
  have hd : HasDerivAt (fun s : ℝ => s / a) (1 / a) t :=
    (hasDerivAt_id t).div_const a
  convert ((hd.sinh.div_const a).smul_const p).add (hd.cosh.smul_const u) using 1
  · rfl
  · simp only [unitAcceleration, P202.HyperboloidData.unitCurve,
      smul_add, smul_smul]
    congr 1 <;> congr 1 <;> field_simp

lemma unitCurve_lorentz {a : ℝ} {p u : Ambient n}
    (hp : lorentz p p = -(a ^ 2)) (hpu : lorentz p u = 0)
    (hu : lorentz u u = 1) (t : ℝ) :
    lorentz (unitCurve a p u t) (unitCurve a p u t) = -(a ^ 2) := by
  have hup : lorentz u p = 0 := (lorentz_comm u p).trans hpu
  simp only [unitCurve, P202.HyperboloidData.unitCurve, lorentz_add_left,
    lorentz_add_right, lorentz_smul_left, lorentz_smul_right, hp, hpu, hup, hu]
  nlinarith [Real.cosh_sq_sub_sinh_sq (t / a)]

lemma unitVelocity_lorentz {a : ℝ} (ha : a ≠ 0) {p u : Ambient n}
    (hp : lorentz p p = -(a ^ 2)) (hpu : lorentz p u = 0)
    (hu : lorentz u u = 1) (t : ℝ) :
    lorentz (unitVelocity a p u t) (unitVelocity a p u t) = 1 := by
  have hup : lorentz u p = 0 := (lorentz_comm u p).trans hpu
  simp only [unitVelocity, lorentz_add_left, lorentz_add_right,
    lorentz_smul_left, lorentz_smul_right, hp, hpu, hup, hu]
  field_simp
  ring_nf
  rw [Real.cosh_sq]
  ring

lemma unitCurve_velocity_orthogonal {a : ℝ} (ha : a ≠ 0) {p u : Ambient n}
    (hp : lorentz p p = -(a ^ 2)) (hpu : lorentz p u = 0)
    (hu : lorentz u u = 1) (t : ℝ) :
    lorentz (unitCurve a p u t) (unitVelocity a p u t) = 0 := by
  have hup : lorentz u p = 0 := (lorentz_comm u p).trans hpu
  simp only [unitCurve, P202.HyperboloidData.unitCurve, unitVelocity,
    lorentz_add_left, lorentz_add_right, lorentz_smul_left, lorentz_smul_right,
    hp, hpu, hup, hu]
  field_simp
  ring

lemma unitCurve_upper {a : ℝ} (ha : 0 < a) {p u : Ambient n}
    (hp : p ∈ upperSheet n a) (hpu : lorentz p u = 0)
    (hu : lorentz u u = 1) (t : ℝ) : unitCurve a p u t ∈ upperSheet n a := by
  have he (s : ℝ) := unitCurve_lorentz hp.1 hpu hu s
  refine ⟨he t, ?_⟩
  have hnonzero (s : ℝ) : (unitCurve a p u s).2 ≠ 0 := by
    intro hz
    have h := he s
    change spatialDot (unitCurve a p u s).1 (unitCurve a p u s).1 -
      (unitCurve a p u s).2 * (unitCurve a p u s).2 = -(a ^ 2) at h
    rw [hz] at h
    nlinarith [spatialDot_self_nonneg (unitCurve a p u s).1, sq_pos_of_pos ha]
  by_contra! ht
  have hc : Continuous (fun s => (unitCurve a p u s).2) := by
    unfold unitCurve P202.HyperboloidData.unitCurve
    fun_prop
  have h0 : 0 ≤ (unitCurve a p u 0).2 := by rw [unitCurve_zero]; exact hp.2.le
  obtain ⟨s, hs⟩ := intermediate_value_univ t 0 hc ⟨ht, h0⟩
  exact hnonzero s hs

theorem unit_curve_ambient : P202Specs.Geometry.HyperboloidModel.unit_curve_ambientType := by
  intro n a ha p hp u hu hunit
  exact ⟨unitCurve_zero a p u, unitVelocity_zero a p u, fun t =>
    ⟨unitCurve_upper ha hp hu hunit t, unitCurve_deriv (ne_of_gt ha) p u t,
      unitVelocity_deriv (ne_of_gt ha) p u t,
      unitCurve_velocity_orthogonal (ne_of_gt ha) hp.1 hu hunit t,
      unitVelocity_lorentz (ne_of_gt ha) hp.1 hu hunit t⟩⟩

theorem topology : P202Specs.Geometry.HyperboloidModel.topologyType := by
  intro n a ha
  haveI : ContractibleSpace (Hyperboloid n a) :=
    (projectionHomeomorph n a ha).contractibleSpace
  exact ⟨inferInstance, inferInstance⟩

theorem graph_smooth : P202Specs.Geometry.HyperboloidModel.graph_smoothType := by
  intro n a ha
  have hp (x : Spatial n) : 0 < a ^ 2 + spatialDot x x :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (spatialDot_self_nonneg x)
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x : Spatial n => a ^ 2 + spatialDot x x) := by
    unfold spatialDot
    fun_prop
  exact contDiff_id.prodMk (hd.sqrt fun x => ne_of_gt (hp x))

open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData

/-- The ordinary Euclidean model differs only by a redundant membership proof. -/
def euclideanModelHomeomorph (n : ℕ) : Spatial n ≃ₜ ModelSpace n .euclidean where
  toFun x := ⟨x, Set.mem_univ x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

noncomputable def projectionChart (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ModelChart n .euclidean (Hyperboloid n a) :=
  ((projectionHomeomorph n a ha).trans (euclideanModelHomeomorph n)).toOpenPartialHomeomorph

lemma global_chart_atlas {M : Type} [TopologicalSpace M]
    (e : M ≃ₜ ModelSpace n .euclidean) :
    IsContDiffAtlas (⊤ : ℕ∞) {e.toOpenPartialHomeomorph} := by
  constructor
  · intro p
    exact ⟨e.toOpenPartialHomeomorph, Set.mem_singleton _, Set.mem_univ _⟩
  · intro c hc d hd
    rcases Set.mem_singleton_iff.mp hc with rfl
    rcases Set.mem_singleton_iff.mp hd with rfl
    constructor <;> intro x hx <;>
      refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, id, contDiffOn_id, ?_⟩
    all_goals intro y hy hyU; simp

/-- Construction in the existing P104 manifold model, using the actual subspace
 topology and the maximal smooth extension of the projection chart. -/
theorem smooth_manifold : P202Specs.Geometry.HyperboloidModel.smooth_manifoldType := by
  intro n a ha
  let e := (projectionHomeomorph n a ha).trans (euclideanModelHomeomorph n)
  let c := e.toOpenPartialHomeomorph
  have hA : IsContDiffAtlas (⊤ : ℕ∞) {c} := global_chart_atlas e
  let S : SmoothManifold n .euclidean (Hyperboloid n a) :=
    { topologicalManifold :=
        { hausdorff := inferInstance
          secondCountable := inferInstance
          atlas := {c}
          covers := hA.1 }
      smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) {c},
        SmoothManifolds.maximalExtension_isMaximal hA⟩ }
  exact ⟨S, c, SmoothManifolds.subset_maximalExtension hA (Set.mem_singleton _),
    rfl, rfl, fun _ => rfl, fun _ => rfl⟩

noncomputable def globalChartManifold {M : Type} [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M] (e : M ≃ₜ ModelSpace n .euclidean) :
    SmoothManifold n .euclidean M where
  topologicalManifold :=
    { hausdorff := inferInstance
      secondCountable := inferInstance
      atlas := {e.toOpenPartialHomeomorph}
      covers := (global_chart_atlas e).1 }
  smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) {e.toOpenPartialHomeomorph},
    SmoothManifolds.maximalExtension_isMaximal (global_chart_atlas e)⟩

lemma globalChartManifold_smooth {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [SecondCountableTopology M] [T2Space N] [SecondCountableTopology N]
    (e : M ≃ₜ ModelSpace n .euclidean) (d : N ≃ₜ ModelSpace n .euclidean)
    (f : M ≃ₜ N) (hf : ∀ x, d (f x) = e x) :
    ManifoldContDiff (⊤ : ℕ∞) (globalChartManifold e).smoothStructure.val
      (globalChartManifold d).smoothStructure.val f := by
  apply (SmoothManifolds.manifoldContDiff_maximalExtension_iff (⊤ : ℕ∞)
    {e.toOpenPartialHomeomorph} {d.toOpenPartialHomeomorph}
    (global_chart_atlas e) (global_chart_atlas d) f).mpr
  intro x
  refine ⟨f.continuous.continuousAt, ?_⟩
  intro c hc c' hc' hx hx'
  rcases Set.mem_singleton_iff.mp hc with rfl
  rcases Set.mem_singleton_iff.mp hc' with rfl
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, id, contDiffOn_id, ?_⟩
  exact Filter.Eventually.of_forall (fun y => congrArg Subtype.val (hf y).symm)

theorem projection_diffeomorph :
    P202Specs.Geometry.HyperboloidModel.projection_diffeomorphType := by
  intro n a ha
  let h := projectionHomeomorph n a ha
  let d := euclideanModelHomeomorph n
  let e := h.trans d
  let S := globalChartManifold e
  let E := globalChartManifold d
  refine ⟨S, E, ⟨d.toOpenPartialHomeomorph,
    SmoothManifolds.subset_maximalExtension (global_chart_atlas d) (Set.mem_singleton _),
    rfl, rfl, fun _ => rfl⟩, ?_⟩
  refine ⟨⟨h.toEquiv, globalChartManifold_smooth e d h (fun _ => rfl),
    globalChartManifold_smooth d e h.symm (fun x => ?_)⟩, fun _ => rfl, fun _ => rfl⟩
  exact congrArg d (h.apply_symm_apply x)

/-- Affine changes of speed supply global ambient solutions for every tangent
initial velocity, including zero. Intrinsic geodesicity still requires the
Levi-Civita projection adapter. -/
theorem all_velocity_ambient :
    P202Specs.Geometry.HyperboloidModel.all_velocity_ambientType := by
  intro n a ha p hp v hv
  by_cases hz : v = 0
  · subst v
    refine ⟨fun _ => p, fun _ => 0, rfl, rfl, ?_⟩
    intro t
    refine ⟨hp, hasDerivAt_const t p, ?_, ?_⟩
    · simpa [lorentz, P202.HyperboloidData.lorentz, spatialDot] using
        (hasDerivAt_const t (0 : Ambient n))
    · rfl
  · have hpos := tangent_positive ha p hp v hv hz
    let c := Real.sqrt (lorentz v v)
    have hc : 0 < c := Real.sqrt_pos.mpr hpos
    have hc0 : c ≠ 0 := ne_of_gt hc
    have hcsq : c ^ 2 = lorentz v v := Real.sq_sqrt hpos.le
    let u : Ambient n := c⁻¹ • v
    have hu : lorentz p u = 0 := by
      rw [lorentz_smul_right]
      change lorentz p v = 0 at hv
      rw [hv, mul_zero]
    have huu : lorentz u u = 1 := by
      change lorentz (c⁻¹ • v) (c⁻¹ • v) = 1
      rw [lorentz_smul_left, lorentz_smul_right, ← hcsq]
      field_simp
    refine ⟨fun t => unitCurve a p u (c * t),
      fun t => c • unitVelocity a p u (c * t), ?_, ?_, ?_⟩
    · simp [unitCurve_zero]
    · simp [unitVelocity_zero, u, smul_smul, hc0]
    · intro t
      have hd : HasDerivAt (fun s : ℝ => c * s) c t := by
        simpa using (hasDerivAt_id t).const_mul c
      refine ⟨unitCurve_upper ha hp hu huu (c * t), ?_, ?_, ?_⟩
      · exact (unitCurve_deriv (ne_of_gt ha) p u (c * t)).scomp t hd
      · convert ((unitVelocity_deriv (ne_of_gt ha) p u (c * t)).scomp t hd).const_smul c using 1
        · rfl
        · simp only [unitAcceleration, smul_smul]
          congr 1
          change lorentz v v / a ^ 2 = c * (c * (a ^ 2)⁻¹)
          rw [← hcsq]
          field_simp
      · change lorentz (c • unitVelocity a p u (c * t))
          (c • unitVelocity a p u (c * t)) = lorentz v v
        rw [lorentz_smul_left, lorentz_smul_right,
          unitVelocity_lorentz (ne_of_gt ha) hp.1 hu huu (c * t)]
        nlinarith [hcsq]

open SmoothManifolds.TangentData P202.MetricData P202.ConnectionData
open scoped Topology

/-- Evaluate the actual scalar differential in a smooth chart. -/
lemma scalarDerivative_chart {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (c : ModelChart n .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (f : M → ℝ) (F : Spatial n → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hf : ∀ q, F (c q).val = f q) (v : TangentSpace S p) :
    scalarDerivative S f p v = fderiv ℝ F (c p).val
      ((tangentStructure S).fiberCoordinates.equiv c hc p hp v) := by
  classical
  have hs := SmoothManifolds.scalarContDiffAt_of_chart
    S.smoothStructure.property.1 hc hp
    ⟨Set.univ, isOpen_univ, Set.mem_univ _, F, hF.contDiffOn,
      Filter.Eventually.of_forall hf⟩
  have hg : (scalarGerm S f p).val = Filter.Germ.ofFun f := by
    simp only [scalarGerm, dite_eq_left hs]
  exact SmoothManifolds.VectorFields.tangent_action_coordinates S
    (tangentStructure S).fiberCoordinates p c hc hp v (scalarGerm S f p) F
    ⟨⟨Set.univ, isOpen_univ, Set.mem_univ _, hF.contDiffOn⟩,
      (Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall hf)).trans hg.symm⟩

lemma graphHeight_fderiv {a : ℝ} (ha : 0 < a) (x w : Spatial n) :
    fderiv ℝ (fun y : Spatial n => Real.sqrt (a ^ 2 + spatialDot y y)) x w =
      spatialDot x w / Real.sqrt (a ^ 2 + spatialDot x x) := by
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) i x).mul
      (hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) i x))
  have hp : 0 < a ^ 2 + spatialDot x x :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (spatialDot_self_nonneg x)
  have hd' := (hd.const_add (a ^ 2)).sqrt (ne_of_gt hp)
  change fderiv ℝ (fun y : Spatial n => Real.sqrt (a ^ 2 + ∑ i, y i * y i)) x w = _
  simp only [Pi.mul_apply] at hd'
  rw [hd'.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  simp only [spatialDot]
  simp_rw [← two_mul]
  rw [← Finset.mul_sum]
  field_simp

/-- In the global projection chart the inclusion differential is the graph
of x·w/τ, on the canonical intrinsic tangent fibers. -/
lemma ambientDifferential_formula {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hsource : c.source = Set.univ)
    (hprojection : ∀ q, (c q).val = q.val.1)
    (p : Hyperboloid n a) (v : TangentSpace S p) :
    ambientDifferential S p v =
      let w := (tangentStructure S).fiberCoordinates.equiv c hc p
        (hsource ▸ Set.mem_univ p) v
      (w, spatialDot p.val.1 w / p.val.2) := by
  have hp : p ∈ c.source := hsource ▸ Set.mem_univ p
  apply Prod.ext
  · funext i
    change scalarDerivative S (fun q => q.val.1 i) p v = _
    rw [scalarDerivative_chart S c hc p hp _ (fun x => x i)
      (contDiff_apply ℝ (fun _ : Fin n => ℝ) i)
      (fun q => congrFun (hprojection q) i)]
    simp only [(hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin n => ℝ) i
      (c p).val).fderiv, ContinuousLinearMap.proj_apply]
  · change scalarDerivative S (fun q => q.val.2) p v = _
    have hs : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Spatial n => Real.sqrt (a ^ 2 + spatialDot x x)) :=
      (graph_smooth n a ha).snd
    have hrep (q : Hyperboloid n a) :
        Real.sqrt (a ^ 2 + spatialDot (c q).val (c q).val) = q.val.2 := by
      rw [hprojection]
      exact congrArg Prod.snd (graphPoint_projection q)
    rw [scalarDerivative_chart S c hc p hp _ _ hs hrep,
      graphHeight_fderiv ha, hprojection, ← hrep p, hprojection]

/-- Inclusion identifies every intrinsic tangent fiber with the entire
Lorentz-orthogonal plane, rather than merely mapping into it. -/
theorem tangent_identification :
    P202Specs.Geometry.HyperboloidModel.tangent_identificationType := by
  intro n a ha S c hc hs hproj p
  let hp : p ∈ c.source := hs ▸ Set.mem_univ p
  let e := (tangentStructure S).fiberCoordinates.equiv c hc p hp
  have hformula (v : TangentSpace S p) :
      ambientDifferential S p v = (e v, spatialDot p.val.1 (e v) / p.val.2) :=
    ambientDifferential_formula ha S c hc hs hproj p v
  constructor
  · intro v w h
    apply e.injective
    simpa only [hformula] using congrArg Prod.fst h
  · ext v
    constructor
    · rintro ⟨w, rfl⟩
      rw [hformula]
      change spatialDot p.val.1 (e w) - p.val.2 *
        (spatialDot p.val.1 (e w) / p.val.2) = 0
      field_simp [ne_of_gt p.property.2]
      ring
    · intro hv
      refine ⟨e.symm v.1, ?_⟩
      rw [hformula, e.apply_symm_apply]
      exact Prod.ext rfl (tangent_time p.property hv).symm

/-- The inclusion differential, as an actual linear map on derivation fibers. -/
noncomputable def ambientLinear {a : ℝ}
    (S : SmoothManifold n .euclidean (Hyperboloid n a)) (p : Hyperboloid n a) :
    TangentSpace S p →ₗ[ℝ] Ambient n where
  toFun := ambientDifferential S p
  map_add' v w := by
    apply Prod.ext
    · funext i; exact map_add (scalarDerivative S (fun q => q.val.1 i) p) v w
    · exact map_add (scalarDerivative S (fun q => q.val.2) p) v w
  map_smul' r v := by
    apply Prod.ext
    · funext i; exact map_smul (scalarDerivative S (fun q => q.val.1 i) p) r v
    · exact map_smul (scalarDerivative S (fun q => q.val.2) p) r v

/-- The ambient Lorentz bilinear form carries no positivity assumption. -/
def lorentzBilinear : LinearMap.BilinForm ℝ (Ambient n) :=
  LinearMap.mk₂ ℝ lorentz lorentz_add_left
    (fun r v w => lorentz_smul_left r v w) lorentz_add_right
    (fun r v w => lorentz_smul_right r v w)

noncomputable def inducedForm {a : ℝ}
    (S : SmoothManifold n .euclidean (Hyperboloid n a)) (p : Hyperboloid n a) :
    LinearMap.BilinForm ℝ (TangentSpace S p) :=
  lorentzBilinear.compl₁₂ (ambientLinear S p) (ambientLinear S p)

@[simp] lemma inducedForm_apply {a : ℝ}
    (S : SmoothManifold n .euclidean (Hyperboloid n a)) (p : Hyperboloid n a)
    (v w : TangentSpace S p) : inducedForm S p v w =
      lorentz (ambientDifferential S p v) (ambientDifferential S p w) := rfl

/-- Smoothness of the original ambient inclusion in the prescribed chart. -/
lemma inclusion_smoothAt {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) (p : Hyperboloid n a) :
    SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val
      (fun q : Hyperboloid n a => q.val) p := by
  have hsp : SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val
      (fun q : Hyperboloid n a => q.val.1) p := by
    apply SmoothManifolds.FrameData.VectorSmoothAt.pi
    intro i
    apply (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mp
    exact SmoothManifolds.scalarContDiffAt_of_chart S.smoothStructure.property.1
      hc (hs ▸ Set.mem_univ p)
      ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun x => x i,
        (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).contDiffOn,
        Filter.Eventually.of_forall (fun q => congrFun (hproj q) i)⟩
  apply (hsp.postcomp (graph_smooth n a ha)).congr
  exact Filter.Eventually.of_forall (fun q => graphPoint_projection q)

/-- The Lorentz restriction is smooth in the canonical tangent trivializations. -/
lemma inducedForm_smooth {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (i : SmoothManifolds.BundleOperationsData.TangentIndex S) (j k : Fin n)
    (p : Hyperboloid n a) (hi : p ∈ (tangentBundle S).baseSet i) :
    SmoothManifolds.FrameData.VectorSmoothAt S.smoothStructure.val
      (fun q => inducedForm S q
        (((tangentBundle S).trivialization i).symm q (Pi.single j 1))
        (((tangentBundle S).trivialization i).symm q (Pi.single k 1))) p := by
  let B := tangentBundle S
  let d : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨c, hc⟩
  let w (l : Fin n) (q : Hyperboloid n a) : Spatial n :=
    ((B.trivialization d) ⟨q, (B.trivialization i).symm q (Pi.single l 1)⟩).2
  have hw (l : Fin n) : SmoothManifolds.FrameData.VectorSmoothAt
      S.smoothStructure.val (w l) p := by
    have hp : p ∈ B.baseSet d := by
      rw [(tangentRealization S).baseSet]
      exact hs ▸ Set.mem_univ p
    exact (SmoothManifolds.Frames.trivializationCoordinates_smoothAt B d
      ⟨p, (B.trivialization i).symm p (Pi.single l 1)⟩ hp).comp
      (g := fun q : Hyperboloid n a => (⟨q,
        (B.trivialization i).symm q (Pi.single l 1)⟩ :
        Bundle.TotalSpace (Spatial n) (TangentSpace S)))
      B.totalManifold.smoothStructure.property.1.1
      (P202.Geometry.SmoothMetrics.localFrame_smoothAt i l p hi)
  let F : Ambient n × (Spatial n × Spatial n) → ℝ := fun z =>
    spatialDot z.2.1 z.2.2 - (spatialDot z.1.1 z.2.1 / z.1.2) *
      (spatialDot z.1.1 z.2.2 / z.1.2)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F {z | z.1.2 ≠ 0} := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    dsimp only [F]
    unfold spatialDot
    fun_prop (disch := exact hz)
  have htotal := ((inclusion_smoothAt ha S c hc hs hproj p).prod
    ((hw j).prod (hw k))).postcompOn
      (isOpen_ne_fun (by fun_prop) continuous_const) (ne_of_gt p.property.2) hF
  apply htotal.congr
  apply Filter.Eventually.of_forall
  intro q
  have heq (l : Fin n) : ambientDifferential S q
      ((B.trivialization i).symm q (Pi.single l 1)) =
      (w l q, spatialDot q.val.1 (w l q) / q.val.2) := by
    rw [ambientDifferential_formula ha S c hc hs hproj]
    have hcoords := (tangentRealization S).coordinates d q
      (hs ▸ Set.mem_univ q) ((B.trivialization i).symm q (Pi.single l 1))
    change w l q = _ at hcoords
    rw [← hcoords]
  change F (q.val, w j q, w k q) = lorentz
    (ambientDifferential S q ((B.trivialization i).symm q (Pi.single j 1)))
    (ambientDifferential S q ((B.trivialization i).symm q (Pi.single k 1)))
  rw [heq j, heq k]
  rfl

/-- The actual smooth positive-definite restriction of the Lorentz form. -/
noncomputable def inducedMetric {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) : RiemannianMetric S where
  form := inducedForm S
  symmetric p v w := lorentz_comm _ _
  positive p v hv := by
    have ht := tangent_identification n a ha S c hc hs hproj p
    apply tangent_positive ha p.val p.property (ambientDifferential S p v)
    · rw [← ht.2]
      exact ⟨v, rfl⟩
    · intro hz
      apply hv
      apply ht.1
      exact hz.trans (map_zero (ambientLinear S p)).symm
  smooth := inducedForm_smooth ha S c hc hs hproj

theorem induced_metric : P202Specs.Geometry.HyperboloidModel.induced_metricType := by
  intro n a ha
  obtain ⟨S, c, hc, hs, ht, hp, hinv⟩ := smooth_manifold n a ha
  refine ⟨S, ⟨c, hc, hs, ht, hp, hinv⟩, inducedMetric ha S c hc hs hp, ?_, ?_⟩
  · intro p v w
    rfl
  · exact tangent_identification n a ha S c hc hs hp

/-- Existence and uniqueness here are for the induced metric just constructed,
not for an independently chosen metric on the same smooth manifold. -/
theorem induced_leviCivita : P202Specs.Geometry.HyperboloidModel.induced_leviCivitaType := by
  intro n a ha
  obtain ⟨S, hchart, g, hg, ht⟩ := induced_metric n a ha
  exact ⟨S, hchart, g, hg, ht, P202.Geometry.LeviCivita.exists_unique g⟩


/-- The original spatial coordinate, as an actual globally smooth scalar. -/
noncomputable def spatialCoordinate {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) (i : Fin n) :
    SmoothManifolds.TangentData.GlobalSmooth S :=
  ⟨fun q => q.val.1 i,
    (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr (fun p =>
      (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr
        ((inclusion_smoothAt ha S c hc hs hproj p).postcomp
          (show ContDiff ℝ (⊤ : ℕ∞) (fun z : Ambient n => z.1 i) by fun_prop)))⟩

/-- The original time coordinate, as an actual globally smooth scalar. -/
noncomputable def timeCoordinate {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) :
    SmoothManifolds.TangentData.GlobalSmooth S :=
  ⟨fun q => q.val.2,
    (SmoothManifolds.mem_globalSmoothAlgebra_iff S _).mpr (fun p =>
      (SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr
        ((inclusion_smoothAt ha S c hc hs hproj p).postcomp
          (show ContDiff ℝ (⊤ : ℕ∞) (fun z : Ambient n => z.2) by fun_prop)))⟩

/-- Ambient components of a smooth field are derivatives of the original
smooth coordinate functions, with no alternate tangent-space model. -/
lemma ambientDifferential_act {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) (X : Field S) (p : Hyperboloid n a) :
    ambientDifferential S p (X.val p) =
      ((fun i => (act S X (spatialCoordinate ha S c hc hs hproj i)).val p),
        (act S X (timeCoordinate ha S c hc hs hproj)).val p) := by
  apply Prod.ext
  · funext i
    exact P202.Geometry.ConnectionForms.scalarDerivative_global
      (spatialCoordinate ha S c hc hs hproj i) X p
  · exact P202.Geometry.ConnectionForms.scalarDerivative_global
      (timeCoordinate ha S c hc hs hproj) X p

/-- The Lorentz tangential projection along the timelike normal line. -/
noncomputable def lorentzProjection (a : ℝ) (p w : Ambient n) : Ambient n :=
  w + (lorentz p w / a ^ 2) • p

lemma lorentzProjection_tangent {a : ℝ} (ha : a ≠ 0)
    {p : Ambient n} (hp : lorentz p p = -(a ^ 2)) (w : Ambient n) :
    lorentzProjection a p w ∈ tangentPlane p := by
  change lorentz p (w + (lorentz p w / a ^ 2) • p) = 0
  rw [lorentz_add_right, lorentz_smul_right, hp]
  field_simp
  <;> ring

lemma lorentzProjection_of_tangent {a : ℝ} {p w : Ambient n}
    (hw : w ∈ tangentPlane p) : lorentzProjection a p w = w := by
  change lorentz p w = 0 at hw
  simp [lorentzProjection, hw]

lemma lorentzProjection_normal {a : ℝ} (ha : a ≠ 0)
    {p : Ambient n} (hp : lorentz p p = -(a ^ 2)) (r : ℝ) :
    lorentzProjection a p (r • p) = 0 := by
  unfold lorentzProjection
  rw [lorentz_smul_right, hp]
  have hcoeff : r * -(a ^ 2) / a ^ 2 = -r := by field_simp
  rw [hcoeff, neg_smul, add_neg_cancel]

lemma lorentzProjection_pairing {a : ℝ} {p v : Ambient n}
    (hv : v ∈ tangentPlane p) (w : Ambient n) :
    lorentz (lorentzProjection a p w) v = lorentz w v := by
  change lorentz p v = 0 at hv
  simp only [lorentzProjection, lorentz_add_left, lorentz_smul_left, hv,
    mul_zero, add_zero]

lemma lorentzProjection_decomposition (a : ℝ) (p w : Ambient n) :
    w = lorentzProjection a p w - (lorentz p w / a ^ 2) • p := by
  simp only [lorentzProjection, add_sub_cancel_right]

/-- A tangent vector and a normal scalar are uniquely determined by their sum. -/
lemma tangent_normal_unique {a : ℝ} (ha : a ≠ 0) {p v w : Ambient n}
    (hp : lorentz p p = -(a ^ 2)) (hv : v ∈ tangentPlane p)
    (hw : w ∈ tangentPlane p) {r s : ℝ}
    (h : v + r • p = w + s • p) : v = w ∧ r = s := by
  have he := congrArg (fun z => lorentz p z) h
  change lorentz p v = 0 at hv
  change lorentz p w = 0 at hw
  simp only [lorentz_add_right, lorentz_smul_right, hv, hw, hp, zero_add] at he
  have hrs : r = s := by
    apply (mul_right_cancel₀ (neg_ne_zero.mpr (pow_ne_zero 2 ha)))
    exact he
  subst s
  exact ⟨add_right_cancel h, rfl⟩

/-- The proved ambient acceleration of the unit curve has zero tangential
projection. Interpreting this as covariant acceleration uses the connection
projection identity, which is a separate intrinsic calculation. -/
lemma unitAcceleration_projection {a : ℝ} (ha : a ≠ 0) {p u : Ambient n}
    (hp : lorentz p p = -(a ^ 2)) (hu : lorentz p u = 0)
    (hunit : lorentz u u = 1) (t : ℝ) :
    lorentzProjection a (unitCurve a p u t) (unitAcceleration a p u t) = 0 := by
  exact lorentzProjection_normal ha (unitCurve_lorentz hp hu hunit t) _

end P202.Geometry.HyperboloidModel


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
open scoped BigOperators
namespace HyperboloidAdapter
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MapData P202.ConnectionData
universe u
variable {m n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold m k M}
abbrev SmoothAmbient (S : SmoothManifold m k M) (n : ℕ) :=
  (Fin n → GlobalSmooth S) × GlobalSmooth S

def functionLorentz (U V : SmoothAmbient S n) : GlobalSmooth S :=
  (∑ i, U.1 i * V.1 i) - U.2 * V.2

noncomputable def ordinaryDerivative (X : Field S) (U : SmoothAmbient S n) : SmoothAmbient S n :=
  (fun i => act S X (U.1 i), act S X U.2)

lemma functionLorentz_comm (U V : SmoothAmbient S n) :
    functionLorentz U V = functionLorentz V U := by
  simp only [functionLorentz, mul_comm]

lemma functionLorentz_add_left (U V W : SmoothAmbient S n) :
    functionLorentz (U + V) W = functionLorentz U W + functionLorentz V W := by
  simp only [functionLorentz, Prod.fst_add, Prod.snd_add, Pi.add_apply,
    add_mul, Finset.sum_add_distrib]
  ring

lemma functionLorentz_sub_left (U V W : SmoothAmbient S n) :
    functionLorentz (U - V) W = functionLorentz U W - functionLorentz V W := by
  simp only [functionLorentz, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply,
    sub_mul, Finset.sum_sub_distrib]
  ring

lemma ordinaryDerivative_pairing (X : Field S) (U V : SmoothAmbient S n) :
    act S X (functionLorentz U V) =
      functionLorentz (ordinaryDerivative X U) V +
      functionLorentz U (ordinaryDerivative X V) := by
  simp only [functionLorentz, ordinaryDerivative, map_sub, map_sum, Derivation.leibniz,
    smul_eq_mul, Finset.sum_add_distrib]
  have hsum : (∑ i, V.1 i * act S X (U.1 i)) =
      ∑ i, act S X (U.1 i) * V.1 i :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [hsum]
  ring

lemma functionLorentz_sub_right (U V W : SmoothAmbient S n) :
    functionLorentz U (V - W) = functionLorentz U V - functionLorentz U W := by
  rw [functionLorentz_comm, functionLorentz_sub_left,
    functionLorentz_comm V U, functionLorentz_comm W U]

lemma ordinaryKoszul
    (f : Field S → SmoothAmbient S n)
    (X Y Z XY YZ ZX : Field S)
    (hXY : f XY = ordinaryDerivative X (f Y) - ordinaryDerivative Y (f X))
    (hYZ : f YZ = ordinaryDerivative Y (f Z) - ordinaryDerivative Z (f Y))
    (hZX : f ZX = ordinaryDerivative Z (f X) - ordinaryDerivative X (f Z)) :
    act S X (functionLorentz (f Y) (f Z)) +
    act S Y (functionLorentz (f Z) (f X)) -
    act S Z (functionLorentz (f X) (f Y)) -
    functionLorentz (f X) (f YZ) +
    functionLorentz (f Y) (f ZX) +
    functionLorentz (f Z) (f XY) =
    2 * functionLorentz (ordinaryDerivative X (f Y)) (f Z) := by
  simp only [ordinaryDerivative_pairing, hXY, hYZ, hZX, functionLorentz_sub_right]
  rw [functionLorentz_comm (f Y) (ordinaryDerivative X (f Z)),
    functionLorentz_comm (f Z) (ordinaryDerivative Y (f X)),
    functionLorentz_comm (f X) (ordinaryDerivative Y (f Z)),
    functionLorentz_comm (f X) (ordinaryDerivative Z (f Y)),
    functionLorentz_comm (f Y) (ordinaryDerivative Z (f X)),
    functionLorentz_comm (f Z) (ordinaryDerivative X (f Y))]
  ring


def evaluateAmbient (U : SmoothAmbient S n) (p : M) : (Fin n → ℝ) × ℝ :=
  (fun i => (U.1 i).val p, U.2.val p)

@[simp] lemma evaluateAmbient_add (U V : SmoothAmbient S n) (p : M) :
    evaluateAmbient (U + V) p = evaluateAmbient U p + evaluateAmbient V p := rfl

@[simp] lemma evaluateAmbient_sub (U V : SmoothAmbient S n) (p : M) :
    evaluateAmbient (U - V) p = evaluateAmbient U p - evaluateAmbient V p := rfl

@[simp] lemma functionLorentz_evaluate (U V : SmoothAmbient S n) (p : M) :
    (functionLorentz U V).val p =
      (∑ i, (evaluateAmbient U p).1 i * (evaluateAmbient V p).1 i) -
        (evaluateAmbient U p).2 * (evaluateAmbient V p).2 := by
  simp [functionLorentz, evaluateAmbient]

@[simp] lemma evaluateAmbient_smul (h : GlobalSmooth S) (U : SmoothAmbient S n) (p : M) :
    evaluateAmbient (h • U) p = h.val p • evaluateAmbient U p := rfl

lemma evaluateAmbient_ext {U V : SmoothAmbient S n}
    (h : ∀ p, evaluateAmbient U p = evaluateAmbient V p) : U = V := by
  apply Prod.ext
  · funext i
    apply Subtype.ext
    funext p
    exact congrArg (fun z : (Fin n → ℝ) × ℝ => z.1 i) (h p)
  · apply Subtype.ext
    funext p
    exact congrArg (fun z : (Fin n → ℝ) × ℝ => z.2) (h p)

end HyperboloidAdapter


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
open scoped BigOperators
namespace P202.Geometry.HyperboloidModel
open P202.HyperboloidData HyperboloidAdapter
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.TorsionMetricData
variable {n : ℕ} {a : ℝ}

noncomputable def coordinateFunctions (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) : SmoothAmbient S n :=
  (spatialCoordinate ha S c hc hs hproj, timeCoordinate ha S c hc hs hproj)

@[simp] lemma evaluate_coordinateFunctions (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) (p : Hyperboloid n a) :
    evaluateAmbient (coordinateFunctions ha S c hc hs hproj) p = p.val := rfl

noncomputable def ambientField (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) (X : Field S) : SmoothAmbient S n :=
  ordinaryDerivative X (coordinateFunctions ha S c hc hs hproj)

@[simp] lemma evaluate_ambientField (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) (X : Field S) (p : Hyperboloid n a) :
    evaluateAmbient (ambientField ha S c hc hs hproj X) p =
      ambientDifferential S p (X.val p) :=
  (ambientDifferential_act ha S c hc hs hproj X p).symm

lemma ambientField_bracket (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) (X Y : Field S) :
    ambientField ha S c hc hs hproj (bracket X Y) =
      ordinaryDerivative X (ambientField ha S c hc hs hproj Y) -
      ordinaryDerivative Y (ambientField ha S c hc hs hproj X) := by
  apply Prod.ext
  · funext i
    apply Subtype.ext
    funext p
    exact P202.Geometry.LeviCivita.bracket_action X Y _ p
  · apply Subtype.ext
    funext p
    exact P202.Geometry.LeviCivita.bracket_action X Y _ p

lemma fieldPairing_ambient (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g) (X Y : Field S) :
    LeviCivita.fieldPairing g X Y =
      functionLorentz (ambientField ha S c hc hs hproj X)
        (ambientField ha S c hc hs hproj Y) := by
  apply Subtype.ext
  funext p
  rw [LeviCivita.fieldPairing_apply, hg, functionLorentz_evaluate]
  rw [evaluate_ambientField, evaluate_ambientField]
  rfl

lemma covariant_pairing_ambient (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (X Y Z : Field S) (p : Hyperboloid n a) :
    pairing g p ((C.cov X Y).val p) (Z.val p) =
      lorentz (evaluateAmbient (ordinaryDerivative X
        (ambientField ha S c hc hs hproj Y)) p)
        (ambientDifferential S p (Z.val p)) := by
  let f := ambientField ha S c hc hs hproj
  have hmetric (U V : Field S) :
      LeviCivita.fieldPairing g U V = functionLorentz (f U) (f V) :=
    fieldPairing_ambient ha S c hc hs hproj g hg U V
  have hk := LeviCivita.koszul_formula g C hC X Y Z p
  change 2 * pairing g p ((C.cov X Y).val p) (Z.val p) =
      scalarDerivative S (LeviCivita.fieldPairing g Y Z).val p (X.val p) +
      scalarDerivative S (LeviCivita.fieldPairing g Z X).val p (Y.val p) -
      scalarDerivative S (LeviCivita.fieldPairing g X Y).val p (Z.val p) -
      (LeviCivita.fieldPairing g X (bracket Y Z)).val p +
      (LeviCivita.fieldPairing g Y (bracket Z X)).val p +
      (LeviCivita.fieldPairing g Z (bracket X Y)).val p at hk
  simp only [ConnectionForms.scalarDerivative_global, hmetric] at hk
  have halg := congrArg (fun F : GlobalSmooth S => F.val p)
    (ordinaryKoszul f X Y Z (bracket X Y) (bracket Y Z) (bracket Z X)
      (ambientField_bracket ha S c hc hs hproj X Y)
      (ambientField_bracket ha S c hc hs hproj Y Z)
      (ambientField_bracket ha S c hc hs hproj Z X))
  change (act S X (functionLorentz (f Y) (f Z))).val p +
      (act S Y (functionLorentz (f Z) (f X))).val p -
      (act S Z (functionLorentz (f X) (f Y))).val p -
      (functionLorentz (f X) (f (bracket Y Z))).val p +
      (functionLorentz (f Y) (f (bracket Z X))).val p +
      (functionLorentz (f Z) (f (bracket X Y))).val p =
      2 * (functionLorentz (ordinaryDerivative X (f Y)) (f Z)).val p at halg
  have he : pairing g p ((C.cov X Y).val p) (Z.val p) =
      (functionLorentz (ordinaryDerivative X (f Y)) (f Z)).val p := by
    linarith
  rw [he, functionLorentz_evaluate]
  change lorentz (evaluateAmbient (ordinaryDerivative X (f Y)) p)
      (evaluateAmbient (f Z) p) = _
  rw [evaluate_ambientField]

lemma covariant_ambient_projection (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (X Y : Field S) (p : Hyperboloid n a) :
    ambientDifferential S p ((C.cov X Y).val p) =
      lorentzProjection a p.val (evaluateAmbient (ordinaryDerivative X
        (ambientField ha S c hc hs hproj Y)) p) := by
  let w := evaluateAmbient (ordinaryDerivative X (ambientField ha S c hc hs hproj Y)) p
  have ht := tangent_identification n a ha S c hc hs hproj p
  have hp : lorentzProjection a p.val w ∈ tangentPlane p.val :=
    lorentzProjection_tangent (ne_of_gt ha) p.property.1 w
  rw [← ht.2] at hp
  obtain ⟨v, hv⟩ := hp
  have heq : (C.cov X Y).val p = v := by
    apply LeviCivita.pairing_ext g p
    intro Z
    rw [covariant_pairing_ambient ha S c hc hs hproj g hg C hC X Y Z p,
      hg, hv]
    symm
    exact lorentzProjection_pairing (by
      rw [← ht.2]
      exact ⟨Z.val p, rfl⟩) w
  rw [heq, hv]

lemma ordinaryDerivative_normal_pairing (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g)
    (X Y : Field S) (p : Hyperboloid n a) :
    lorentz p.val (evaluateAmbient (ordinaryDerivative X
      (ambientField ha S c hc hs hproj Y)) p) =
      -pairing g p (X.val p) (Y.val p) := by
  let P := coordinateFunctions ha S c hc hs hproj
  let f := ambientField ha S c hc hs hproj
  have hzero : functionLorentz P (f Y) = 0 := by
    apply Subtype.ext
    funext q
    rw [functionLorentz_evaluate]
    change lorentz (evaluateAmbient P q) (evaluateAmbient (f Y) q) = 0
    rw [evaluate_coordinateFunctions, evaluate_ambientField]
    have ht := tangent_identification n a ha S c hc hs hproj q
    have hv : ambientDifferential S q (Y.val q) ∈ tangentPlane q.val := by
      rw [← ht.2]
      exact ⟨Y.val q, rfl⟩
    exact hv
  have hd := ordinaryDerivative_pairing X P (f Y)
  rw [hzero, map_zero] at hd
  have he := congrArg (fun F : GlobalSmooth S => F.val p) hd
  change 0 = (functionLorentz (f X) (f Y)).val p +
      (functionLorentz P (ordinaryDerivative X (f Y))).val p at he
  rw [functionLorentz_evaluate, functionLorentz_evaluate] at he
  change 0 = lorentz (evaluateAmbient (f X) p) (evaluateAmbient (f Y) p) +
      lorentz (evaluateAmbient P p) (evaluateAmbient (ordinaryDerivative X (f Y)) p) at he
  rw [evaluate_ambientField, evaluate_ambientField, evaluate_coordinateFunctions] at he
  have hpair := hg p (X.val p) (Y.val p)
  change pairing g p (X.val p) (Y.val p) =
    lorentz (ambientDifferential S p (X.val p)) (ambientDifferential S p (Y.val p)) at hpair
  rw [← hpair] at he
  linarith

/-- The Lorentz Gauss formula for the actual induced Levi-Civita connection. -/
lemma covariant_ambient_formula (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (X Y : Field S) (p : Hyperboloid n a) :
    ambientDifferential S p ((C.cov X Y).val p) =
      evaluateAmbient (ordinaryDerivative X (ambientField ha S c hc hs hproj Y)) p -
        (pairing g p (X.val p) (Y.val p) / a ^ 2) • p.val := by
  rw [covariant_ambient_projection ha S c hc hs hproj g hg C hC X Y p]
  unfold lorentzProjection
  rw [ordinaryDerivative_normal_pairing ha S c hc hs hproj g hg X Y p]
  simp only [neg_div, neg_smul, sub_eq_add_neg]

lemma covariant_ambient_smooth (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (X Y : Field S) :
    ambientField ha S c hc hs hproj (C.cov X Y) =
      ordinaryDerivative X (ambientField ha S c hc hs hproj Y) -
        (((a ^ 2)⁻¹) • LeviCivita.fieldPairing g X Y) •
          coordinateFunctions ha S c hc hs hproj := by
  apply evaluateAmbient_ext
  intro p
  rw [evaluate_ambientField, evaluateAmbient_sub, evaluateAmbient_smul,
    evaluate_coordinateFunctions,
    covariant_ambient_formula ha S c hc hs hproj g hg C hC X Y p]
  congr 2
  change pairing g p (X.val p) (Y.val p) / a ^ 2 =
    (a ^ 2)⁻¹ * pairing g p (X.val p) (Y.val p)
  ring

end P202.Geometry.HyperboloidModel


set_option autoImplicit false
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
open P202.MetricData

namespace P202.Geometry.HyperboloidModel
universe u

lemma sectionalValue_of_constantTensor
    {n : ℕ} {b : SmoothManifolds.ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n b M} (g : RiemannianMetric S) (p : M)
    (X Y R : TangentSpace S p) (k : ℝ)
    (hR : R = k • (pairing g p Y Y • X - pairing g p X Y • Y))
    (hden : pairing g p X X * pairing g p Y Y - pairing g p X Y ^ 2 ≠ 0) :
    pairing g p R X /
      (pairing g p X X * pairing g p Y Y - pairing g p X Y ^ 2) = k := by
  rw [hR]
  unfold pairing at *
  rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.sub_left,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_left, g.symmetric p Y X]
  apply (div_eq_iff hden).mpr
  ring

end P202.Geometry.HyperboloidModel

namespace HyperboloidAdapter
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MapData P202.ConnectionData
universe u
variable {m n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold m k M}

lemma ordinaryDerivative_sub (X : Field S) (U V : SmoothAmbient S n) :
    ordinaryDerivative X (U - V) = ordinaryDerivative X U - ordinaryDerivative X V := by
  apply Prod.ext
  · funext i
    exact map_sub (act S X) (U.1 i) (V.1 i)
  · exact map_sub (act S X) U.2 V.2

lemma ordinaryDerivative_smul (X : Field S) (h : GlobalSmooth S) (U : SmoothAmbient S n) :
    ordinaryDerivative X (h • U) = (act S X h) • U + h • ordinaryDerivative X U := by
  apply Prod.ext
  · funext i
    change act S X (h * U.1 i) = act S X h * U.1 i + h * act S X (U.1 i)
    rw [Derivation.leibniz]
    ring
  · change act S X (h * U.2) = act S X h * U.2 + h * act S X U.2
    rw [Derivation.leibniz]
    ring

/-- The flat ambient commutator and the projected connection identity yield
constant negative curvature; metric compatibility cancels the normal terms. -/
lemma projected_curvature
    (cov : Field S → Field S → Field S)
    (f : Field S → SmoothAmbient S n) (coords : SmoothAmbient S n)
    (B : Field S → Field S → GlobalSmooth S)
    (X Y Z XY : Field S)
    (hproj : ∀ A E, f (cov A E) = ordinaryDerivative A (f E) - B A E • coords)
    (hcoords : ∀ A, ordinaryDerivative A coords = f A)
    (hflat : ordinaryDerivative X (ordinaryDerivative Y (f Z)) -
      ordinaryDerivative Y (ordinaryDerivative X (f Z)) = ordinaryDerivative XY (f Z))
    (hcomp : ∀ A E F, act S A (B E F) = B (cov A E) F + B E (cov A F))
    (htors : B XY Z = B (cov X Y) Z - B (cov Y X) Z) :
    f (cov X (cov Y Z)) - f (cov Y (cov X Z)) - f (cov XY Z) =
      -(B Y Z) • f X + B X Z • f Y := by
  rw [hproj X (cov Y Z), hproj Y (cov X Z), hproj XY Z,
    hproj Y Z, hproj X Z,
    ordinaryDerivative_sub, ordinaryDerivative_sub,
    ordinaryDerivative_smul, ordinaryDerivative_smul, hcoords X, hcoords Y,
    hcomp X Y Z, hcomp Y X Z, htors]
  apply Prod.ext
  · funext i
    have hh := congrArg (fun U : SmoothAmbient S n => U.1 i) hflat
    simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hh ⊢
    linear_combination hh
  · have hh := congrArg (fun U : SmoothAmbient S n => U.2) hflat
    simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hh ⊢
    linear_combination hh

end HyperboloidAdapter

namespace P202.Geometry.HyperboloidModel
open P202.HyperboloidData P202.ConnectionData

lemma sectionalCurvature_of_tensor
    {n : ℕ} {a : ℝ}
    {S : SmoothManifold n .euclidean (Hyperboloid n a)}
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hR : ∀ (X Y Z : Field S) (p : Hyperboloid n a),
      (curvatureField C X Y Z).val p =
        (-(a ^ 2)⁻¹) • (pairing g p (Y.val p) (Z.val p) • X.val p -
          pairing g p (X.val p) (Z.val p) • Y.val p))
    (X Y : Field S) (p : Hyperboloid n a)
    (hden : pairing g p (X.val p) (X.val p) * pairing g p (Y.val p) (Y.val p) -
      pairing g p (X.val p) (Y.val p) ^ 2 ≠ 0) :
    pairing g p ((curvatureField C X Y Y).val p) (X.val p) /
      (pairing g p (X.val p) (X.val p) * pairing g p (Y.val p) (Y.val p) -
        pairing g p (X.val p) (Y.val p) ^ 2) = -(a ^ 2)⁻¹ := by
  exact sectionalValue_of_constantTensor g p (X.val p) (Y.val p) _ _ (hR X Y Y p) hden

end P202.Geometry.HyperboloidModel

namespace HyperboloidAdapter
open SmoothManifolds (ModelKind)
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MapData P202.ConnectionData P202.MetricData P202.LeviCivitaData
  P202.TorsionMetricData
universe u
variable {m n : ℕ} {k : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold m k M}

lemma ordinaryDerivative_bracket (X Y : Field S) (U : SmoothAmbient S n) :
    ordinaryDerivative (bracket X Y) U =
      ordinaryDerivative X (ordinaryDerivative Y U) - ordinaryDerivative Y (ordinaryDerivative X U) := by
  apply Prod.ext
  · funext i
    apply Subtype.ext
    funext p
    exact P202.Geometry.LeviCivita.bracket_action X Y (U.1 i) p
  · apply Subtype.ext
    funext p
    exact P202.Geometry.LeviCivita.bracket_action X Y U.2 p

lemma fieldPairing_derivative (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C) (X Y Z : Field S) :
    act S X (P202.Geometry.LeviCivita.fieldPairing g Y Z) =
      P202.Geometry.LeviCivita.fieldPairing g (C.cov X Y) Z +
        P202.Geometry.LeviCivita.fieldPairing g Y (C.cov X Z) := by
  apply Subtype.ext
  funext p
  exact (P202.Geometry.ConnectionForms.scalarDerivative_global
    (P202.Geometry.LeviCivita.fieldPairing g Y Z) X p).symm.trans (hC.2 X Y Z p)

lemma scaled_fieldPairing_derivative (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C) (r : ℝ)
    (X Y Z : Field S) :
    act S X (r • P202.Geometry.LeviCivita.fieldPairing g Y Z) =
      r • P202.Geometry.LeviCivita.fieldPairing g (C.cov X Y) Z +
        r • P202.Geometry.LeviCivita.fieldPairing g Y (C.cov X Z) := by
  rw [Derivation.map_smul, fieldPairing_derivative g C hC, smul_add]

lemma scaled_fieldPairing_bracket (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C) (r : ℝ)
    (X Y Z : Field S) :
    r • P202.Geometry.LeviCivita.fieldPairing g (bracket X Y) Z =
      r • P202.Geometry.LeviCivita.fieldPairing g (C.cov X Y) Z -
        r • P202.Geometry.LeviCivita.fieldPairing g (C.cov Y X) Z := by
  apply Subtype.ext
  funext p
  change r * pairing g p ((bracket X Y).val p) (Z.val p) =
    r * pairing g p ((C.cov X Y).val p) (Z.val p) -
      r * pairing g p ((C.cov Y X).val p) (Z.val p)
  rw [P202.Geometry.LeviCivita.bracket_eq_cov_sub
    P202.Geometry.TorsionAndMetric.torsion_apply C hC.1 X Y p]
  unfold pairing
  rw [LinearMap.BilinForm.sub_left]
  ring

lemma projected_curvature_leviCivita (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (f : Field S → SmoothAmbient S n) (coords : SmoothAmbient S n) (r : ℝ)
    (hproj : ∀ A E, f (C.cov A E) = ordinaryDerivative A (f E) -
      (r • P202.Geometry.LeviCivita.fieldPairing g A E) • coords)
    (hcoords : ∀ A, ordinaryDerivative A coords = f A) (X Y Z : Field S) :
    f (C.cov X (C.cov Y Z)) - f (C.cov Y (C.cov X Z)) - f (C.cov (bracket X Y) Z) =
      -(r • P202.Geometry.LeviCivita.fieldPairing g Y Z) • f X +
        (r • P202.Geometry.LeviCivita.fieldPairing g X Z) • f Y := by
  exact projected_curvature (fun A E => C.cov A E) f coords
    (fun A E => r • P202.Geometry.LeviCivita.fieldPairing g A E)
    X Y Z (bracket X Y) hproj hcoords
    (ordinaryDerivative_bracket X Y (f Z)).symm
    (scaled_fieldPairing_derivative g C hC r)
    (scaled_fieldPairing_bracket g C hC r X Y Z)

end HyperboloidAdapter

namespace P202.Geometry.HyperboloidModel
open P202.HyperboloidData HyperboloidAdapter
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.TorsionMetricData
variable {n : ℕ} {a : ℝ}

/-- The actual intrinsic curvature, calculated by the flat Lorentz Gauss formula. -/
theorem constant_curvature_tensor (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (X Y Z : Field S) (p : Hyperboloid n a) :
    (curvatureField C X Y Z).val p =
      (-(a ^ 2)⁻¹) • (pairing g p (Y.val p) (Z.val p) • X.val p -
        pairing g p (X.val p) (Z.val p) • Y.val p) := by
  have h := projected_curvature_leviCivita g C hC
    (ambientField ha S c hc hs hproj) (coordinateFunctions ha S c hc hs hproj)
    ((a ^ 2)⁻¹)
    (covariant_ambient_smooth ha S c hc hs hproj g hg C hC)
    (fun _ => rfl) X Y Z
  have hh := congrArg (fun U => evaluateAmbient U p) h
  simp only [evaluateAmbient_sub, evaluateAmbient_add, evaluateAmbient_smul,
    evaluate_ambientField] at hh
  change ambientDifferential S p ((C.cov X (C.cov Y Z)).val p) -
    ambientDifferential S p ((C.cov Y (C.cov X Z)).val p) -
    ambientDifferential S p ((C.cov (bracket X Y) Z).val p) =
      (-((a ^ 2)⁻¹ * pairing g p (Y.val p) (Z.val p))) • ambientDifferential S p (X.val p) +
      ((a ^ 2)⁻¹ * pairing g p (X.val p) (Z.val p)) • ambientDifferential S p (Y.val p) at hh
  apply (tangent_identification n a ha S c hc hs hproj p).1
  change ambientLinear S p ((curvatureField C X Y Z).val p) =
    ambientLinear S p ((-(a ^ 2)⁻¹) •
      (pairing g p (Y.val p) (Z.val p) • X.val p -
        pairing g p (X.val p) (Z.val p) • Y.val p))
  change ambientLinear S p
    ((C.cov X (C.cov Y Z)).val p + (-1 : ℝ) • (C.cov Y (C.cov X Z)).val p +
      (-1 : ℝ) • (C.cov (bracket X Y) Z).val p) = _
  simp only [map_add, map_smul]
  change ambientDifferential S p ((C.cov X (C.cov Y Z)).val p) +
    (-1 : ℝ) • ambientDifferential S p ((C.cov Y (C.cov X Z)).val p) +
    (-1 : ℝ) • ambientDifferential S p ((C.cov (bracket X Y) Z).val p) = _
  rw [neg_one_smul, neg_one_smul, ← sub_eq_add_neg, ← sub_eq_add_neg, hh]
  rw [LeviCivita.tangent_sub_as_add]
  simp only [map_add, map_smul, smul_add, smul_smul, neg_mul, neg_smul, smul_neg, neg_neg, one_mul]
  rfl

/-- Every nondegenerate tangent two-plane has the prescribed sectional value. -/
theorem constant_sectional_curvature (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (X Y : Field S) (p : Hyperboloid n a)
    (hden : pairing g p (X.val p) (X.val p) * pairing g p (Y.val p) (Y.val p) -
      pairing g p (X.val p) (Y.val p) ^ 2 ≠ 0) :
    pairing g p ((curvatureField C X Y Y).val p) (X.val p) /
      (pairing g p (X.val p) (X.val p) * pairing g p (Y.val p) (Y.val p) -
        pairing g p (X.val p) (Y.val p) ^ 2) = -(a ^ 2)⁻¹ := by
  exact sectionalCurvature_of_tensor g C
    (constant_curvature_tensor ha S c hc hs hproj g hg C hC) X Y p hden

end P202.Geometry.HyperboloidModel


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
open scoped BigOperators Topology
namespace P202.Geometry.HyperboloidModel
open P202.HyperboloidData SmoothManifolds.AtlasData SmoothManifolds.ModelData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData
variable {n : ℕ} {a : ℝ}

noncomputable def projectionFrame
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ) (j : Fin n) : Field S :=
  ⟨fun p => coordinateVector (⟨c, hc⟩ : TangentIndex S) j p, fun p =>
    P202.Geometry.SmoothMetrics.localFrame_smoothAt (⟨c, hc⟩ : TangentIndex S) j p
      (by rw [(tangentRealization S).baseSet]; exact hs ▸ Set.mem_univ p)⟩

lemma projectionFrame_coordinates
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ) (j : Fin n)
    (p : Hyperboloid n a) :
    (tangentStructure S).fiberCoordinates.equiv c hc p (hs ▸ Set.mem_univ p)
      ((projectionFrame S c hc hs j).val p) = Pi.single j 1 := by
  let i : TangentIndex S := ⟨c, hc⟩
  let hp : p ∈ (tangentBundle S).baseSet i := by
    rw [(tangentRealization S).baseSet]; exact hs ▸ Set.mem_univ p
  have hcoord := (tangentRealization S).coordinates i p
    (hs ▸ Set.mem_univ p) ((projectionFrame S c hc hs j).val p)
  rw [← hcoord]
  change (tangentBundle S).fiberCoordinates i p hp
    (((tangentBundle S).trivialization i).symm p (Pi.single j 1)) = Pi.single j 1
  exact ((tangentBundle S).fiberCoordinates i p hp).apply_symm_apply _

lemma projectionFrame_ambient (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) (j : Fin n) (p : Hyperboloid n a) :
    ambientDifferential S p ((projectionFrame S c hc hs j).val p) =
      (Pi.single j 1, spatialDot p.val.1 (Pi.single j 1) / p.val.2) := by
  rw [ambientDifferential_formula ha S c hc hs hproj, projectionFrame_coordinates]

lemma projectionFrame_coordinate_action (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) (i j : Fin n) :
    act S (projectionFrame S c hc hs j) (spatialCoordinate ha S c hc hs hproj i) =
      if j = i then 1 else 0 := by
  apply Subtype.ext
  funext p
  have h := congrFun (congrArg Prod.fst
    ((ambientDifferential_act ha S c hc hs hproj
      (projectionFrame S c hc hs j) p).symm.trans
      (projectionFrame_ambient ha S c hc hs hproj j p))) i
  split_ifs with hji <;> simpa [Pi.single_apply, hji, eq_comm] using h

lemma frameCoordinates_ambient (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (p : (tangentBundle S).baseSet (⟨c, hc⟩ : TangentIndex S))
    (v : TangentSpace S p.val) :
    ((SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S)
      (⟨c, hc⟩ : TangentIndex S)).basis p).equivFun v =
      (ambientDifferential S p.val v).1 := by
  change ((Pi.basisFun ℝ (Fin n)).map
    ((tangentBundle S).fiberCoordinates (⟨c, hc⟩ : TangentIndex S)
      p.val p.property).symm).equivFun v = _
  rw [Module.Basis.map_equivFun]
  simp only [Pi.basisFun_equivFun, LinearEquiv.symm_symm, LinearEquiv.trans_refl]
  rw [ambientDifferential_formula ha S c hc hs hproj]
  exact (tangentRealization S).coordinates (⟨c, hc⟩ : TangentIndex S) p.val
    (hs ▸ Set.mem_univ _) v

lemma christoffel_eq_spatialCov (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (C : Connection (tangentBundle S))
    (p : (tangentBundle S).baseSet (⟨c, hc⟩ : TangentIndex S)) (k i j : Fin n) :
    christoffel C (⟨c, hc⟩ : TangentIndex S) p k i j =
      (ambientDifferential S p.val
        ((C.cov (projectionFrame S c hc hs i) (projectionFrame S c hc hs j)).val p.val)).1 k := by
  let B := tangentBundle S
  let d : TangentIndex S := ⟨c, hc⟩
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B d
  let e := projectionFrame S c hc hs
  have heq (l : Fin n) : ∀ᶠ q in 𝓝 p.val, (e l).val q =
      SmoothManifolds.SectionExtension.totalSection (b.section_ l) q := by
    apply Filter.Eventually.of_forall
    intro q
    have hq : q ∈ B.baseSet d := by
      rw [(tangentRealization S).baseSet]; exact hs ▸ Set.mem_univ q
    rw [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    change coordinateVector d l q = ((Pi.basisFun ℝ (Fin n)).map
      (B.fiberCoordinates d q hq).symm) l
    simp only [Module.Basis.map_apply, Pi.basisFun_apply,
      SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply]
    rfl
  have hder := (P202.Geometry.ConnectionForms.pointDerivative_congr B C
    (e j).val _ p.val ⟨e j, Filter.Eventually.of_forall (fun _ => rfl)⟩ (heq j)).symm
  change pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val =
    pointDerivative C (e j).val p.val at hder
  change ((b.basis p).equivFun
    (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) p.val
      (coordinateVector d i p.val))) k = _
  rw [hder]
  change ((b.basis p).equivFun (pointDerivative C (e j).val p.val ((e i).val p.val))) k = _
  rw [P202.Geometry.ConnectionForms.pointDerivative_global B C]
  exact congrFun (frameCoordinates_ambient ha S c hc hs hproj p _) k

open HyperboloidAdapter
lemma projectionFrame_ambientDerivative_spatial (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1) (j : Fin n) (X : Field S) (p : Hyperboloid n a) :
    (evaluateAmbient (ordinaryDerivative X
      (ambientField ha S c hc hs hproj (projectionFrame S c hc hs j))) p).1 = 0 := by
  funext i
  change (act S X (act S (projectionFrame S c hc hs j)
    (spatialCoordinate ha S c hc hs hproj i))).val p = 0
  rw [projectionFrame_coordinate_action]
  split_ifs <;> simp

lemma hyperboloid_christoffel (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (p : (tangentBundle S).baseSet (⟨c, hc⟩ : TangentIndex S)) (k i j : Fin n) :
    christoffel C (⟨c, hc⟩ : TangentIndex S) p k i j =
      -(metricMatrix g (⟨c, hc⟩ : TangentIndex S) p.val i j / a ^ 2) * p.val.val.1 k := by
  rw [christoffel_eq_spatialCov ha S c hc hs hproj,
    covariant_ambient_formula ha S c hc hs hproj g hg C hC]
  simp only [Prod.fst_sub, Prod.smul_fst, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    projectionFrame_ambientDerivative_spatial, Pi.zero_apply, zero_sub, neg_mul]
  rfl

lemma hyperboloid_coordinateAcceleration (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = Set.univ)
    (hproj : ∀ q, (c q).val = q.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (p : (tangentBundle S).baseSet (⟨c, hc⟩ : TangentIndex S))
    (v : TangentSpace S p.val) :
    P202.GeodesicData.coordinateAcceleration S C (⟨c, hc⟩ : TangentIndex S) p
      (ambientDifferential S p.val v).1 =
      (pairing g p.val v v / a ^ 2) • p.val.val.1 := by
  classical
  let d : TangentIndex S := ⟨c, hc⟩
  let w := (ambientDifferential S p.val v).1
  have hcoords : (tangentBundle S).fiberCoordinates d p.val p.property v = w := by
    have h := frameCoordinates_ambient ha S c hc hs hproj p v
    change ((Pi.basisFun ℝ (Fin n)).map
      ((tangentBundle S).fiberCoordinates d p.val p.property).symm).equivFun v = _ at h
    simpa only [Module.Basis.map_equivFun, Pi.basisFun_equivFun,
      LinearEquiv.symm_symm, LinearEquiv.trans_refl] using h
  have hexp : (∑ j : Fin n, w j • coordinateVector d j p.val) = v := by
    simpa only [hcoords] using P202.Geometry.LeviCivita.coordinate_expansion d p.val p.property v
  have hpair : pairing g p.val v v =
      ∑ i : Fin n, ∑ j : Fin n, metricMatrix g d p.val i j * w i * w j := by
    conv_lhs => rw [← hexp]
    unfold pairing
    rw [LinearMap.map_sum₂]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    change w i * (w j * metricMatrix g d p.val i j) = _
    ring
  funext k
  change -(∑ i : Fin n, ∑ j : Fin n,
    christoffel C d p k i j * w i * w j) = (pairing g p.val v v / a ^ 2) * p.val.val.1 k
  have hgamma (i j : Fin n) : christoffel C d p k i j =
      -(metricMatrix g d p.val i j / a ^ 2) * p.val.val.1 k :=
    hyperboloid_christoffel ha S c hc hs hproj g hg C hC p k i j
  simp_rw [hgamma]
  rw [hpair]
  simp only [Finset.sum_div, Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end P202.Geometry.HyperboloidModel


set_option autoImplicit false
namespace P202.Geometry.HyperboloidModel
open P202.HyperboloidData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  P202.MetricData P202.ConnectionData P202.CurveConnectionData P202.GeodesicData
open Set
open scoped BigOperators
lemma lorentz_curve_deriv {n : ℕ} {γ δ : ℝ → Ambient n} {γ' δ' : Ambient n} {t : ℝ}
    (hγ : HasDerivAt γ γ' t) (hδ : HasDerivAt δ δ' t) :
    HasDerivAt (fun s => lorentz (γ s) (δ s))
      (lorentz γ' (δ t) + lorentz (γ t) δ') t := by
  have hγfst : HasDerivAt (fun s => (γ s).1) γ'.1 t :=
    (ContinuousLinearMap.fst ℝ (Spatial n) ℝ).hasFDerivAt.comp_hasDerivAt t hγ
  have hδfst : HasDerivAt (fun s => (δ s).1) δ'.1 t :=
    (ContinuousLinearMap.fst ℝ (Spatial n) ℝ).hasFDerivAt.comp_hasDerivAt t hδ
  have hγsnd : HasDerivAt (fun s => (γ s).2) γ'.2 t :=
    (ContinuousLinearMap.snd ℝ (Spatial n) ℝ).hasFDerivAt.comp_hasDerivAt t hγ
  have hδsnd : HasDerivAt (fun s => (δ s).2) δ'.2 t :=
    (ContinuousLinearMap.snd ℝ (Spatial n) ℝ).hasFDerivAt.comp_hasDerivAt t hδ
  have hsp := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_pi.mp hγfst i).mul
      (hasDerivAt_pi.mp hδfst i))
  convert hsp.sub (hγsnd.mul hδsnd) using 1
  · rfl
  · simp only [lorentz, P202.HyperboloidData.lorentz, spatialDot]
    rw [Finset.sum_add_distrib]
    ring
lemma ambient_curve_velocity_tangent {n : ℕ} {a : ℝ} {γ δ : ℝ → Ambient n} {t : ℝ}
    (hγ : HasDerivAt γ (δ t) t) (hnorm : ∀ s, lorentz (γ s) (γ s) = -(a^2)) :
    lorentz (γ t) (δ t) = 0 := by
  have hd := lorentz_curve_deriv hγ hγ
  have hc : HasDerivAt (fun s => lorentz (γ s) (γ s)) 0 t := by
    simpa only [hnorm] using hasDerivAt_const t (-(a^2))
  have he := hd.unique hc
  rw [lorentz_comm (δ t) (γ t)] at he
  linarith

lemma ambient_curve_lift_of_formula {n : ℕ} {a : ℝ}
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1)
    (hformula : ∀ (p : Hyperboloid n a) (v : TangentSpace S p),
      ambientDifferential S p v =
        let w := (tangentStructure S).fiberCoordinates.equiv c hc p
          (hs ▸ mem_univ p) v
        (w, spatialDot p.val.1 w / p.val.2))
    (γ δ : ℝ → Ambient n) (hmem : ∀ t, γ t ∈ upperSheet n a)
    (hder : ∀ t, HasDerivAt γ (δ t) t) :
    ∃ q : ℝ → Phase S,
      (∀ t, (q t).1.val = γ t) ∧
      (∀ t, ambientDifferential S (q t).1 (q t).2 = δ t) ∧
      ∀ t, HasVelocityWithinAt S (fun s => (q s).1) univ t (q t).2 := by
  let γH : ℝ → Hyperboloid n a := fun t => ⟨γ t, hmem t⟩
  let V : (t : ℝ) → TangentSpace S (γH t) := fun t =>
    ((tangentStructure S).fiberCoordinates.equiv c hc (γH t)
      (hs ▸ mem_univ _)).symm (δ t).1
  let q : ℝ → Phase S := fun t => ⟨γH t, V t⟩
  refine ⟨q, fun _ => rfl, ?_, ?_⟩
  · intro t
    change ambientDifferential S (γH t) (V t) = δ t
    rw [hformula]
    simp only [V, LinearEquiv.apply_symm_apply]
    refine Prod.ext rfl ?_
    have ht := ambient_curve_velocity_tangent (hder t) (fun s => (hmem s).1)
    change spatialDot (γ t).1 (δ t).1 - (γ t).2 * (δ t).2 = 0 at ht
    change spatialDot (γ t).1 (δ t).1 / (γ t).2 = (δ t).2
    apply (div_eq_iff (ne_of_gt (hmem t).2)).mpr
    linarith
  · intro t
    change HasVelocityWithinAt S γH univ t (V t)
    refine ⟨((hder t).continuousAt.codRestrict hmem).continuousWithinAt,
      c, hc, hs ▸ mem_univ _, ?_⟩
    simp only [V, LinearEquiv.apply_symm_apply]
    have hd : HasDerivAt (fun s => (γ s).1) (δ t).1 t :=
      (ContinuousLinearMap.fst ℝ (Spatial n) ℝ).hasFDerivAt.comp_hasDerivAt t (hder t)
    simpa only [hproj, γH] using hd.hasDerivWithinAt

lemma phase_ambient_injective {n : ℕ} {a : ℝ}
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (hinj : ∀ p, Function.Injective (ambientDifferential S p)) :
    Function.Injective (fun q : Phase S =>
      (q.1.val, ambientDifferential S q.1 q.2)) := by
  rintro ⟨p, v⟩ ⟨p', v'⟩ h
  have hp : p = p' := Subtype.ext (congrArg Prod.fst h)
  subst p'
  apply congrArg (Sigma.mk p)
  apply hinj p
  exact congrArg Prod.snd h

lemma all_velocity_lift_of_ambient {n : ℕ} {a : ℝ}
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1)
    (hformula : ∀ (p : Hyperboloid n a) (v : TangentSpace S p),
      ambientDifferential S p v =
        let w := (tangentStructure S).fiberCoordinates.equiv c hc p
          (hs ▸ mem_univ p) v
        (w, spatialDot p.val.1 w / p.val.2))
    (htangent : ∀ p, Function.Injective (ambientDifferential S p) ∧
      range (ambientDifferential S p) = tangentPlane p.val)
    (hambient : ∀ (p : Ambient n), p ∈ upperSheet n a →
      ∀ v ∈ tangentPlane p,
      ∃ γ δ : ℝ → Ambient n, γ 0 = p ∧ δ 0 = v ∧
        ∀ t : ℝ, γ t ∈ upperSheet n a ∧
          HasDerivAt γ (δ t) t ∧
          HasDerivAt δ ((lorentz v v / a ^ 2) • γ t) t ∧
          lorentz (δ t) (δ t) = lorentz v v) :
    ∀ w : Phase S, ∃ q : ℝ → Phase S,
      q 0 = w ∧
      (∀ t, HasVelocityWithinAt S (fun s => (q s).1) univ t (q t).2) ∧
      ∀ t, HasDerivAt (fun s => ambientDifferential S (q s).1 (q s).2)
        ((lorentz (ambientDifferential S w.1 w.2)
            (ambientDifferential S w.1 w.2) / a ^ 2) • (q t).1.val) t := by
  intro w
  have hv : ambientDifferential S w.1 w.2 ∈ tangentPlane w.1.val := by
    rw [← (htangent w.1).2]
    exact ⟨w.2, rfl⟩
  obtain ⟨γ, δ, hγ0, hδ0, hγδ⟩ := hambient w.1.val w.1.property _ hv
  obtain ⟨q, hqpos, hqvel, hqactual⟩ := ambient_curve_lift_of_formula
    S c hc hs hproj hformula γ δ (fun t => (hγδ t).1) (fun t => (hγδ t).2.1)
  refine ⟨q, ?_, hqactual, ?_⟩
  · apply phase_ambient_injective S (fun p => (htangent p).1)
    exact Prod.ext ((hqpos 0).trans hγ0) ((hqvel 0).trans hδ0)
  · intro t
    simpa only [hqvel, hqpos] using (hγδ t).2.2.1

lemma ambient_curve_lift {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1)
    (γ δ : ℝ → Ambient n) (hmem : ∀ t, γ t ∈ upperSheet n a)
    (hder : ∀ t, HasDerivAt γ (δ t) t) :
    ∃ q : ℝ → Phase S,
      (∀ t, (q t).1.val = γ t) ∧
      (∀ t, ambientDifferential S (q t).1 (q t).2 = δ t) ∧
      ∀ t, HasVelocityWithinAt S (fun s => (q s).1) univ t (q t).2 := by
  exact ambient_curve_lift_of_formula S c hc hs hproj
    (ambientDifferential_formula ha S c hc hs hproj) γ δ hmem hder

lemma all_velocity_lift {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1) :
    ∀ w : Phase S, ∃ q : ℝ → Phase S,
      q 0 = w ∧
      (∀ t, HasVelocityWithinAt S (fun s => (q s).1) univ t (q t).2) ∧
      ∀ t, HasDerivAt (fun s => ambientDifferential S (q s).1 (q s).2)
        ((lorentz (ambientDifferential S w.1 w.2)
            (ambientDifferential S w.1 w.2) / a ^ 2) • (q t).1.val) t := by
  exact all_velocity_lift_of_ambient S c hc hs hproj
    (ambientDifferential_formula ha S c hc hs hproj)
    (tangent_identification n a ha S c hc hs hproj)
    (all_velocity_ambient ha)


lemma unit_curve_lift {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g)
    (p : Hyperboloid n a) (u : TangentSpace S p) (hu : pairing g p u u = 1) :
    ∃ q : ℝ → Phase S, q 0 = ⟨p, u⟩ ∧
      (∀ t, HasVelocityWithinAt S (fun s => (q s).1) univ t (q t).2) ∧
      ∀ t, (q t).1.val = unitCurve a p.val (ambientDifferential S p u) t ∧
        ambientDifferential S (q t).1 (q t).2 =
          unitVelocity a p.val (ambientDifferential S p u) t ∧
        pairing g (q t).1 (q t).2 (q t).2 = 1 ∧
        HasDerivAt (fun s => ambientDifferential S (q s).1 (q s).2)
          ((a^2)⁻¹ • (q t).1.val) t := by
  have ht := tangent_identification n a ha S c hc hs hproj
  have hutan : ambientDifferential S p u ∈ tangentPlane p.val := by
    rw [← (ht p).2]
    exact ⟨u, rfl⟩
  have huL : lorentz (ambientDifferential S p u) (ambientDifferential S p u) = 1 := by
    exact (hg p u u).symm.trans hu
  have hunit := unit_curve_ambient ha p.val p.property _ hutan huL
  obtain ⟨q, hqpos, hqvel, hqactual⟩ := ambient_curve_lift ha S c hc hs hproj
    (unitCurve a p.val (ambientDifferential S p u))
    (unitVelocity a p.val (ambientDifferential S p u))
    (fun t => (hunit.2.2 t).1) (fun t => (hunit.2.2 t).2.1)
  refine ⟨q, ?_, hqactual, ?_⟩
  · apply phase_ambient_injective S (fun p => (ht p).1)
    exact Prod.ext ((hqpos 0).trans hunit.1) ((hqvel 0).trans hunit.2.1)
  · intro t
    refine ⟨hqpos t, hqvel t, ?_, ?_⟩
    · rw [hg, hqvel]
      exact (hunit.2.2 t).2.2.2.2
    · simpa only [hqvel, hqpos, unitAcceleration] using (hunit.2.2 t).2.2.1


lemma all_velocity_lift_induced {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g) :
    ∀ w : Phase S, ∃ q : ℝ → Phase S, q 0 = w ∧
      (∀ t, HasVelocityWithinAt S (fun s => (q s).1) univ t (q t).2) ∧
      ∀ t, pairing g (q t).1 (q t).2 (q t).2 = pairing g w.1 w.2 w.2 ∧
        HasDerivAt (fun s => ambientDifferential S (q s).1 (q s).2)
          ((pairing g (q t).1 (q t).2 (q t).2 / a^2) • (q t).1.val) t := by
  intro w
  have ht := tangent_identification n a ha S c hc hs hproj
  have hv : ambientDifferential S w.1 w.2 ∈ tangentPlane w.1.val := by
    rw [← (ht w.1).2]
    exact ⟨w.2, rfl⟩
  obtain ⟨γ, δ, hγ0, hδ0, hγδ⟩ := all_velocity_ambient ha
    w.1.val w.1.property _ hv
  obtain ⟨q, hqpos, hqvel, hqactual⟩ := ambient_curve_lift
    ha S c hc hs hproj γ δ (fun t => (hγδ t).1) (fun t => (hγδ t).2.1)
  refine ⟨q, ?_, hqactual, ?_⟩
  · apply phase_ambient_injective S (fun p => (ht p).1)
    exact Prod.ext ((hqpos 0).trans hγ0) ((hqvel 0).trans hδ0)
  · intro t
    have henergy : pairing g (q t).1 (q t).2 (q t).2 = pairing g w.1 w.2 w.2 := by
      rw [hg, hqvel, hg]
      exact (hγδ t).2.2.2
    refine ⟨henergy, ?_⟩
    rw [henergy, hg]
    simpa only [hqvel, hqpos] using (hγδ t).2.2.1

end P202.Geometry.HyperboloidModel


set_option autoImplicit false
namespace P202.Geometry.HyperboloidModel
open P202.HyperboloidData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleOperationsData
  P202.MetricData P202.ConnectionData P202.CurveConnectionData P202.GeodesicData
open Set
open scoped BigOperators

lemma chartVelocity_ambient {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1)
    (q : ℝ → Phase S) (t : ℝ) :
    chartVelocity S (⟨c, hc⟩ : TangentIndex S) q t =
      (ambientDifferential S (q t).1 (q t).2).1 := by
  have hp : (q t).1 ∈ (tangentBundle S).baseSet (⟨c, hc⟩ : TangentIndex S) := by
    rw [(tangentRealization S).baseSet]
    exact hs ▸ mem_univ _
  rw [chartVelocity, CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hp]
  exact frameCoordinates_ambient ha S c hc hs hproj ⟨(q t).1, hp⟩ (q t).2

lemma geodesic_of_normal_ambient {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1)
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hcoord : ∀ (p : (tangentBundle S).baseSet (⟨c, hc⟩ : TangentIndex S))
        (v : TangentSpace S p.val),
      coordinateAcceleration S C (⟨c, hc⟩ : TangentIndex S) p
          (ambientDifferential S p.val v).1 =
        (pairing g p.val v v / a^2) • p.val.val.1)
    (q : ℝ → Phase S)
    (hactual : ∀ t, HasVelocityWithinAt S (fun s => (q s).1) univ t (q t).2)
    (haccel : ∀ t, HasDerivAt (fun s => ambientDifferential S (q s).1 (q s).2)
      ((pairing g (q t).1 (q t).2 (q t).2 / a^2) • (q t).1.val) t) :
    IsGeodesicOn S C univ q := by
  intro t _
  have hp : (q t).1 ∈ (tangentBundle S).baseSet (⟨c, hc⟩ : TangentIndex S) := by
    rw [(tangentRealization S).baseSet]
    exact hs ▸ mem_univ _
  apply P202.Geometry.GeodesicIVP.coordinate_equation_implies_geodesic_at C q t
    (⟨c, hc⟩ : TangentIndex S) hp
  · exact (continuousWithinAt_univ _ _).mp (hactual t).1
  · rw [chartVelocity_ambient ha S c hc hs hproj q t]
    have hd := CurveCovariantDerivative.velocity_coordinates
      (hactual t) (mem_univ t) c hc (hs ▸ mem_univ _)
    rw [hasDerivWithinAt_univ] at hd
    have heq := congrArg Prod.fst
      (ambientDifferential_formula ha S c hc hs hproj (q t).1 (q t).2)
    dsimp only at heq
    rwa [← heq] at hd
  · have heq : chartVelocity S (⟨c, hc⟩ : TangentIndex S) q =
        fun s => (ambientDifferential S (q s).1 (q s).2).1 := by
      funext s
      exact chartVelocity_ambient ha S c hc hs hproj q s
    rw [heq, hcoord]
    have hd := (ContinuousLinearMap.fst ℝ (Spatial n) ℝ).hasFDerivAt.comp_hasDerivAt t
      (haccel t)
    exact hd

lemma global_geodesic_exists_of_coordinateAcceleration {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g) (C : Connection (tangentBundle S))
    (hcoord : ∀ (p : (tangentBundle S).baseSet (⟨c, hc⟩ : TangentIndex S))
        (v : TangentSpace S p.val),
      coordinateAcceleration S C (⟨c, hc⟩ : TangentIndex S) p
          (ambientDifferential S p.val v).1 =
        (pairing g p.val v v / a^2) • p.val.val.1) :
    ∀ w : Phase S, ∃ q : ℝ → Phase S, q 0 = w ∧ IsGeodesicOn S C univ q := by
  intro w
  obtain ⟨q, hq0, hactual, hq⟩ := all_velocity_lift_induced ha S c hc hs hproj g hg w
  exact ⟨q, hq0, geodesic_of_normal_ambient ha S c hc hs hproj g C hcoord q
    hactual (fun t => (hq t).2)⟩


lemma unit_global_geodesic {n : ℕ} {a : ℝ} (ha : 0 < a)
    (S : SmoothManifold n .euclidean (Hyperboloid n a))
    (c : ModelChart n .euclidean (Hyperboloid n a))
    (hc : c ∈ S.smoothStructure.val) (hs : c.source = univ)
    (hproj : ∀ p, (c p).val = p.val.1)
    (g : RiemannianMetric S) (hg : IsInduced g) (C : Connection (tangentBundle S))
    (hcoord : ∀ (p : (tangentBundle S).baseSet (⟨c, hc⟩ : TangentIndex S))
        (v : TangentSpace S p.val),
      coordinateAcceleration S C (⟨c, hc⟩ : TangentIndex S) p
          (ambientDifferential S p.val v).1 =
        (pairing g p.val v v / a^2) • p.val.val.1)
    (p : Hyperboloid n a) (u : TangentSpace S p) (hu : pairing g p u u = 1) :
    ∃ q : ℝ → Phase S,
      q 0 = ⟨p, u⟩ ∧ IsGeodesicOn S C univ q ∧
      (∀ r : ℝ → Phase S, r 0 = ⟨p, u⟩ → IsGeodesicOn S C univ r → r = q) ∧
      ∀ t : ℝ,
        (q t).1.val = unitCurve a p.val (ambientDifferential S p u) t ∧
        ambientDifferential S (q t).1 (q t).2 =
          unitVelocity a p.val (ambientDifferential S p u) t ∧
        pairing g (q t).1 (q t).2 (q t).2 = 1 := by
  obtain ⟨q, hq0, hactual, hq⟩ := unit_curve_lift ha S c hc hs hproj g hg p u hu
  have hgeodesic : IsGeodesicOn S C univ q :=
    geodesic_of_normal_ambient ha S c hc hs hproj g C hcoord q hactual (by
      intro t
      simpa only [(hq t).2.2.1, one_div] using (hq t).2.2.2)
  refine ⟨q, hq0, hgeodesic, ?_, ?_⟩
  · intro r hr0 hr
    have heq := P202.Geometry.GeodesicIVP.overlap_unique S C
      D13Unified.OpenTimeInterval.whole D13Unified.OpenTimeInterval.whole
      r q hr hgeodesic 0 (by trivial) (hr0.trans hq0.symm)
    funext t
    exact heq (by trivial)
  · intro t
    exact ⟨(hq t).1, (hq t).2.1, (hq t).2.2.1⟩

end P202.Geometry.HyperboloidModel


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
namespace P202.Geometry.HyperboloidModel
open SmoothManifolds.AtlasData
  P202.ConnectionData P202.GeodesicData P202.HopfRinowData
universe u

/-- Existence on all real times forces the domain of every maximal geodesic
to contain all real times, by the original maximality property. -/
lemma geodesicallyComplete_of_global_geodesics
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M)
    (C : Connection (tangentBundle S))
    (hglobal : ∀ w : Phase S, ∃ q : ℝ → Phase S,
      q 0 = w ∧ IsGeodesicOn S C Set.univ q) :
    GeodesicallyComplete S C := by
  intro w I q hmax
  obtain ⟨r, hr0, hr⟩ := hglobal w
  let J : D13Unified.OpenTimeInterval :=
    ⟨⟨Set.univ, Set.univ_nonempty, Set.ordConnected_univ⟩, isOpen_univ⟩
  have hsub := (hmax.2.2.2 J r (Set.mem_univ 0) hr0 hr).1
  exact Set.Subset.antisymm (Set.subset_univ _) hsub

end P202.Geometry.HyperboloidModel


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

namespace P202.Geometry.HyperboloidModel
open P202.HyperboloidData
open SmoothManifolds.AtlasData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.HopfRinowData P202.CompletenessData

theorem intrinsic_model : P202Specs.Geometry.HyperboloidModel.intrinsic_modelType := by
  intro n _hn a ha
  obtain ⟨S, c, hc, hs, ht, hproj, hinv⟩ := smooth_manifold n a ha
  let g := inducedMetric ha S c hc hs hproj
  have hg : IsInduced g := by intro p v w; rfl
  obtain ⟨C, hC, _hunique⟩ := P202.Geometry.LeviCivita.exists_unique g
  have hcoord := hyperboloid_coordinateAcceleration ha S c hc hs hproj g hg C hC
  have hglobal := global_geodesic_exists_of_coordinateAcceleration ha S c hc hs hproj g hg C hcoord
  have hcomplete : GeodesicallyComplete S C :=
    geodesicallyComplete_of_global_geodesics S C hglobal
  letI : ConnectedSpace (Hyperboloid n a) := (topology n a ha).1
  exact ⟨S, ⟨c, hc, hs, ht, hproj, hinv⟩, g, hg,
    tangent_identification n a ha S c hc hs hproj, C, hC,
    constant_curvature_tensor ha S c hc hs hproj g hg C hC,
    constant_sectional_curvature ha S c hc hs hproj g hg C hC,
    unit_global_geodesic ha S c hc hs hproj g hg C hcoord,
    hcomplete, P202.Geometry.HopfRinow.complete_of_geodesicallyComplete g C hC hcomplete⟩

end P202.Geometry.HyperboloidModel
