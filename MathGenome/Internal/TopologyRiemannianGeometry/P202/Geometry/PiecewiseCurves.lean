import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PiecewiseCurves
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SmoothMetrics
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.Piecewise

set_option autoImplicit false
namespace P202.Geometry.PiecewiseCurves
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapData SmoothManifolds.TangentData
  SmoothManifolds.TangentBundleData P202.MetricData P202.CurveData
open Set Filter
open scoped Topology
universe u

variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

/- One-sided velocities are proof tools for integrability at piece endpoints.
They are constructed from the coordinate C¹ extensions, not stored in curves. -/
def HasVelocityWithinAt (S : SmoothManifold n kind M) (c : ℝ → M) (J : Set ℝ)
    (t : ℝ) (v : TangentSpace S (c t)) : Prop :=
  ContinuousWithinAt c J t ∧
    ∃ e, ∃ he : e ∈ S.smoothStructure.val, ∃ hp : c t ∈ e.source,
      HasDerivWithinAt (fun s => (e (c s)).val)
        ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp v) J t

noncomputable def withinVelocity (S : SmoothManifold n kind M) (c : ℝ → M)
    (J : Set ℝ) (t : ℝ) : TangentSpace S (c t) := by
  classical
  exact if h : ∃ v, HasVelocityWithinAt S c J t v then Classical.choose h else 0

theorem hasVelocityWithinAt_coordinates {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    {v : TangentSpace S (c t)} (hv : HasVelocityWithinAt S c J t v) (ht : t ∈ J)
    (d : ModelChart n kind M) (hd : d ∈ S.smoothStructure.val)
    (hpd : c t ∈ d.source) :
    HasDerivWithinAt (fun s => (d (c s)).val)
      ((tangentStructure S).fiberCoordinates.equiv d hd (c t) hpd v) J t := by
  obtain ⟨hc, e, he, hp, hder⟩ := hv
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ :=
    SmoothManifolds.chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 e he d hd) hp hpd
  have hj := SmoothManifolds.TangentBundle.transition_jacobian S
    (tangentStructure S).fiberCoordinates e d he hd (c t) hp hpd
    U F hU hpU hF hrep v
  rw [hj]
  have hcomp := ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivWithinAt t hder
  exact hcomp.congr_of_eventuallyEq_of_mem (hrep.comp_tendsto hc).symm ht

theorem CoordinateC1On.exists_withinVelocity {c : ℝ → M} {J : Set ℝ}
    (h : CoordinateC1On S c J) (hc : ContinuousOn c J) {t : ℝ} (ht : t ∈ J) :
    ∃ v, HasVelocityWithinAt S c J t v := by
  obtain ⟨e, he, hp, x, hx, _, heq⟩ := h t ht
  let E := (tangentStructure S).fiberCoordinates.equiv e he (c t) hp
  refine ⟨E.symm (deriv x t), hc t ht, e, he, hp, ?_⟩
  change HasDerivWithinAt _ (E (E.symm (deriv x t))) J t
  simpa only [LinearEquiv.apply_symm_apply] using
    (hx.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt
      |>.congr_of_eventuallyEq_of_mem heq ht

theorem withinVelocity_spec {c : ℝ → M} {J : Set ℝ}
    (h : CoordinateC1On S c J) (hc : ContinuousOn c J) {t : ℝ} (ht : t ∈ J) :
    HasVelocityWithinAt S c J t (withinVelocity S c J t) := by
  classical
  have hex := CoordinateC1On.exists_withinVelocity h hc ht
  unfold withinVelocity
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

theorem withinVelocity_coordinates {c : ℝ → M} {J : Set ℝ}
    (h : CoordinateC1On S c J) (hc : ContinuousOn c J)
    (hJ : UniqueDiffOn ℝ J) {t : ℝ} (ht : t ∈ J)
    (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (hp : c t ∈ e.source) :
    (tangentStructure S).fiberCoordinates.equiv e he (c t) hp
      (withinVelocity S c J t) = derivWithin (fun s => (e (c s)).val) J t :=
  (hasVelocityWithinAt_coordinates (withinVelocity_spec h hc ht) ht e he hp).derivWithin
    (hJ t ht) |>.symm

/-- Local coordinate C¹ regularity supplies continuous one-sided coordinate
derivatives, including at the two endpoints of a nontrivial piece. -/
theorem coordinate_derivWithin_continuousWithinAt
    {c : ℝ → M} {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) {t : ℝ} (ht : t ∈ J)
    {e : ModelChart n kind M} {x : ℝ → Euclidean n}
    (hx : ContDiffAt ℝ 1 x t)
    (heq : (fun s => (e (c s)).val) =ᶠ[𝓝[J] t] x) :
    ContinuousWithinAt (derivWithin (fun s => (e (c s)).val) J) J t := by
  have hdx : ContDiffAt ℝ 0 (deriv x) t := hx.derivWithin (by norm_num)
  refine hdx.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem ?_ ht
  filter_upwards [heq.derivWithin, (hx.eventually (by simp)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hxs hsJ
  exact hs.trans ((hxs.differentiableAt (by simp)).derivWithin (hJ s hsJ))

/-- Smooth Gram coefficients and continuous coordinate derivatives give
continuous one-sided speed on each C¹ piece. -/
theorem withinNorm_continuousOn (g : RiemannianMetric S) {c : ℝ → M} {J : Set ℝ}
    (h : CoordinateC1On S c J) (hc : ContinuousOn c J) (hJ : UniqueDiffOn ℝ J) :
    ContinuousOn (fun t => tangentNorm g (c t) (withinVelocity S c J t)) J := by
  intro t ht
  obtain ⟨e, he, hp, x, hx, _, heq⟩ := h t ht
  let B := (tangentRealization S).space.bundle
  let i : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e, he⟩
  let gram : Fin n → Fin n → M → ℝ := fun j k p =>
    g.form p ((B.trivialization i).symm p (Pi.single j 1))
      ((B.trivialization i).symm p (Pi.single k 1))
  let D := derivWithin (fun s => (e (c s)).val) J
  have hD : ContinuousWithinAt D J t :=
    coordinate_derivWithin_continuousWithinAt hJ ht hx heq
  have hi : c t ∈ B.baseSet i := by
    change c t ∈ (tangentRealization S).space.bundle.baseSet i
    rw [(tangentRealization S).baseSet]
    exact hp
  have hgram (j k : Fin n) : ContinuousWithinAt (fun s => gram j k (c s)) J t :=
    (g.smooth i j k (c t) hi).1.comp_continuousWithinAt (hc t ht)
  have hQ : ContinuousWithinAt
      (fun s => ∑ j : Fin n, ∑ k : Fin n, D s j * (D s k * gram j k (c s))) J t := by
    apply tendsto_finsetSum
    intro j _
    apply tendsto_finsetSum
    intro k _
    exact ((continuous_apply j).continuousAt.comp_continuousWithinAt hD).mul
      (((continuous_apply k).continuousAt.comp_continuousWithinAt hD).mul (hgram j k))
  refine (Real.continuous_sqrt.continuousAt.comp_continuousWithinAt hQ)
    |>.congr_of_eventuallyEq_of_mem ?_ ht
  filter_upwards [(hc t ht).eventually (e.open_source.mem_nhds hp),
    self_mem_nhdsWithin] with s hse hsJ
  have hsB : c s ∈ B.baseSet i := by
    change c s ∈ (tangentRealization S).space.bundle.baseSet i
    rw [(tangentRealization S).baseSet]
    exact hse
  have hcoord : B.fiberCoordinates i (c s) hsB (withinVelocity S c J s) = D s := by
    rw [SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_apply]
    rw [(tangentRealization S).coordinates i (c s) hse]
    exact withinVelocity_coordinates h hc hJ hsJ e he hse
  have hbil := SmoothMetrics.bilinear_coordinates (B.fiberCoordinates i (c s) hsB)
    (g.form (c s)) (withinVelocity S c J s) (withinVelocity S c J s)
  simp only [SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply,
    hcoord] at hbil
  exact congrArg Real.sqrt hbil

/-- Every chart computes the intrinsic velocity by the ordinary derivative. -/
theorem hasVelocityAt_coordinates {c : ℝ → M} {t : ℝ}
    {v : TangentSpace S (c t)} (hv : HasVelocityAt S c t v)
    (d : ModelChart n kind M) (hd : d ∈ S.smoothStructure.val)
    (hpd : c t ∈ d.source) :
    HasDerivAt (fun s => (d (c s)).val)
      ((tangentStructure S).fiberCoordinates.equiv d hd (c t) hpd v) t := by
  obtain ⟨hc, e, he, hp, hder⟩ := hv
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ :=
    SmoothManifolds.chartContDiffAt_of_compatible
      (S.smoothStructure.property.1.2 e he d hd) hp hpd
  have hFd := (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt
    (by simp)
  have hj := SmoothManifolds.TangentBundle.transition_jacobian S
    (tangentStructure S).fiberCoordinates e d he hd (c t) hp hpd
    U F hU hpU hF hrep v
  rw [hj]
  have hcomp := hFd.hasFDerivAt.comp_hasDerivAt t hder
  exact hcomp.congr_of_eventuallyEq (hrep.comp_tendsto hc).symm

theorem hasVelocityAt_unique {c : ℝ → M} {t : ℝ}
    {v w : TangentSpace S (c t)} (hv : HasVelocityAt S c t v)
    (hw : HasVelocityAt S c t w) : v = w := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (c t)
  apply ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp).injective
  exact (hasVelocityAt_coordinates hv e he hp).unique
    (hasVelocityAt_coordinates hw e he hp)

theorem velocity_eq {c : ℝ → M} {t : ℝ} {v : TangentSpace S (c t)}
    (hv : HasVelocityAt S c t v) : velocity S c t = v := by
  classical
  unfold velocity
  rw [dite_eq_left (⟨v, hv⟩ : ∃ w, HasVelocityAt S c t w)]
  exact hasVelocityAt_unique (Classical.choose_spec _) hv

theorem fiberCoordinates_cast (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (p q : M) (hp : p ∈ e.source) (hq : q ∈ e.source) (h : p = q)
    (v : TangentSpace S p) :
    (tangentStructure S).fiberCoordinates.equiv e he q hq
      (cast (congrArg (TangentSpace S) h) v) =
      (tangentStructure S).fiberCoordinates.equiv e he p hp v := by
  subst q
  rfl

/-- Velocity is local in the parameter, including its base point transport. -/
theorem HasVelocityAt.congr {c d : ℝ → M} {t : ℝ} {v : TangentSpace S (c t)}
    (hv : HasVelocityAt S c t v) (heq : c =ᶠ[𝓝 t] d) :
    HasVelocityAt S d t (cast (congrArg (TangentSpace S) heq.eq_of_nhds) v) := by
  obtain ⟨hc, e, he, hp, hder⟩ := hv
  have hp' : d t ∈ e.source := heq.eq_of_nhds ▸ hp
  refine ⟨hc.congr_of_eventuallyEq heq.symm, e, he, hp', ?_⟩
  rw [fiberCoordinates_cast e he (c t) (d t) hp hp' heq.eq_of_nhds v]
  exact hder.congr_of_eventuallyEq (heq.fun_comp (fun p => (e p).val)).symm

theorem velocity_congr {c d : ℝ → M} {t : ℝ}
    (hc : HasVelocityAt S c t (velocity S c t)) (heq : c =ᶠ[𝓝 t] d) :
    HEq (velocity S c t) (velocity S d t) := by
  have h := velocity_eq (HasVelocityAt.congr hc heq)
  exact ((heq_of_eq h).trans (cast_heq _ _)).symm

theorem tangentNorm_cast (g : RiemannianMetric S) (p q : M) (h : p = q)
    (v : TangentSpace S p) :
    tangentNorm g q (cast (congrArg (TangentSpace S) h) v) = tangentNorm g p v := by
  subst q
  rfl

theorem speed_congr_of_eventuallyEq (g : RiemannianMetric S) {c d : ℝ → M} {t : ℝ}
    (hc : HasVelocityAt S c t (velocity S c t)) (heq : c =ᶠ[𝓝 t] d) :
    speed g c t = speed g d t := by
  unfold speed
  rw [velocity_eq (HasVelocityAt.congr hc heq)]
  exact (tangentNorm_cast g (c t) (d t) heq.eq_of_nhds _).symm

theorem hasVelocityAt_const (p : M) (t : ℝ) :
    HasVelocityAt S (fun _ => p) t 0 := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  exact ⟨continuousAt_const, e, he, hp, by simpa using hasDerivAt_const t (e p).val⟩

@[simp] theorem velocity_const (p : M) (t : ℝ) :
    velocity S (fun _ => p) t = 0 := velocity_eq (hasVelocityAt_const p t)

theorem coordinateC1On_const (p : M) (J : Set ℝ) :
    CoordinateC1On S (fun _ => p) J := by
  intro t _
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  exact ⟨e, he, hp, fun _ => (e p).val, contDiffAt_const, rfl,
    Filter.EventuallyEq.rfl⟩

theorem CoordinateC1On.mono {c : ℝ → M} {J K : Set ℝ}
    (h : CoordinateC1On S c J) (hK : K ⊆ J) : CoordinateC1On S c K := by
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, hxeq⟩ := h t (hK ht)
  exact ⟨e, he, hp, x, hx, hxt, hxeq.filter_mono (nhdsWithin_mono t hK)⟩

theorem CoordinateC1On.congr {c d : ℝ → M} {J : Set ℝ}
    (h : CoordinateC1On S c J) (heq : EqOn d c J) : CoordinateC1On S d J := by
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, hxeq⟩ := h t ht
  refine ⟨e, he, by simpa only [heq ht] using hp, x, hx, ?_, ?_⟩
  · simpa only [heq ht] using hxt
  · filter_upwards [hxeq, self_mem_nhdsWithin] with s hs hsJ
    simpa only [heq hsJ] using hs

/-- Ambient coordinate extensions construct an actual velocity in the
interior. No intrinsic differentiability assumption is added. -/
theorem CoordinateC1On.exists_velocity {c : ℝ → M} {J : Set ℝ}
    (h : CoordinateC1On S c J) {t : ℝ} (hJ : J ∈ 𝓝 t)
    (hc : ContinuousAt c t) : ∃ v, HasVelocityAt S c t v := by
  obtain ⟨e, he, hp, x, hx, _, hxeq⟩ := h t (mem_of_mem_nhds hJ)
  have heq : (fun s => (e (c s)).val) =ᶠ[𝓝 t] x := by
    simpa only [nhdsWithin_eq_nhds.mpr hJ] using hxeq
  let E := (tangentStructure S).fiberCoordinates.equiv e he (c t) hp
  refine ⟨E.symm (deriv x t), hc, e, he, hp, ?_⟩
  change HasDerivAt _ (E (E.symm (deriv x t))) t
  simpa only [LinearEquiv.apply_symm_apply] using
    (hx.differentiableAt (by simp)).hasDerivAt.congr_of_eventuallyEq heq

theorem node_mem {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (i : Fin (c.pieces + 1)) : c.node i ∈ Icc a b := by
  constructor
  · simpa only [c.first_node] using c.monotone_node (Fin.zero_le i)
  · simpa only [c.last_node] using c.monotone_node (Fin.le_last i)

theorem exists_velocity_on_piece {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (i : Fin c.pieces) {t : ℝ}
    (ht : t ∈ Ioo (c.node i.castSucc) (c.node i.succ)) :
    ∃ v, HasVelocityAt S c t v := by
  have hglobal : Icc a b ∈ 𝓝 t := Icc_mem_nhds
    ((node_mem c i.castSucc).1.trans_lt ht.1)
    (ht.2.trans_le (node_mem c i.succ).2)
  exact CoordinateC1On.exists_velocity (c.regular i)
    (Icc_mem_nhds ht.1 ht.2) (c.continuousOn.continuousAt hglobal)

theorem velocity_on_piece {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (i : Fin c.pieces) {t : ℝ}
    (ht : t ∈ Ioo (c.node i.castSucc) (c.node i.succ)) :
    HasVelocityAt S c t (velocity S c t) := by
  classical
  have hex := exists_velocity_on_piece c i ht
  unfold velocity
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

theorem withinVelocity_eq_velocity {c : ℝ → M} {J : Set ℝ}
    (h : CoordinateC1On S c J) (hc : ContinuousOn c J) (hJ : UniqueDiffOn ℝ J)
    {t : ℝ} (ht : t ∈ J) (hv : HasVelocityAt S c t (velocity S c t)) :
    withinVelocity S c J t = velocity S c t := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (c t)
  apply ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp).injective
  rw [withinVelocity_coordinates h hc hJ ht e he hp]
  exact (hasVelocityAt_coordinates hv e he hp).hasDerivWithinAt.derivWithin (hJ t ht)

theorem speed_integrable_on_piece (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) (i : Fin c.pieces) :
    IntervalIntegrable (speed g c) MeasureTheory.volume
      (c.node i.castSucc) (c.node i.succ) := by
  have hle := c.monotone_node (Fin.castSucc_le_succ i)
  rcases hle.eq_or_lt with heq | hlt
  · simp [heq]
  have hc : ContinuousOn c (Icc (c.node i.castSucc) (c.node i.succ)) :=
    c.continuousOn.mono (fun _ ht =>
      ⟨(node_mem c i.castSucc).1.trans ht.1, ht.2.trans (node_mem c i.succ).2⟩)
  have hcont := withinNorm_continuousOn g (c.regular i) hc (uniqueDiffOn_Icc hlt)
  apply (hcont.intervalIntegrable_of_Icc hle).congr_uIoo
  rw [uIoo_of_le hle]
  intro t ht
  dsimp only [speed, Pi.pow_apply]
  rw [withinVelocity_eq_velocity (c.regular i) hc (uniqueDiffOn_Icc hlt)
    (Ioo_subset_Icc_self ht) (velocity_on_piece c i ht)]

theorem squared_speed_integrable_on_piece (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) (i : Fin c.pieces) :
    IntervalIntegrable (fun t => speed g c t ^ 2) MeasureTheory.volume
      (c.node i.castSucc) (c.node i.succ) := by
  have hle := c.monotone_node (Fin.castSucc_le_succ i)
  rcases hle.eq_or_lt with heq | hlt
  · simp [heq]
  have hc : ContinuousOn c (Icc (c.node i.castSucc) (c.node i.succ)) :=
    c.continuousOn.mono (fun _ ht =>
      ⟨(node_mem c i.castSucc).1.trans ht.1, ht.2.trans (node_mem c i.succ).2⟩)
  have hcont := withinNorm_continuousOn g (c.regular i) hc (uniqueDiffOn_Icc hlt)
  apply ((hcont.pow 2).intervalIntegrable_of_Icc hle).congr_uIoo
  rw [uIoo_of_le hle]
  intro t ht
  dsimp only [speed, Pi.pow_apply]
  rw [withinVelocity_eq_velocity (c.regular i) hc (uniqueDiffOn_Icc hlt)
    (Ioo_subset_Icc_self ht) (velocity_on_piece c i ht)]

theorem intervalIntegrable_of_partition {k : ℕ} (node : Fin (k + 1) → ℝ)
    {f : ℝ → ℝ}
    (h : ∀ i : Fin k, IntervalIntegrable f MeasureTheory.volume
      (node i.castSucc) (node i.succ)) :
    IntervalIntegrable f MeasureTheory.volume (node 0) (node (Fin.last k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    exact (ih (fun i => node i.castSucc)
      (fun i => by simpa only [Fin.succ_castSucc] using h i.castSucc)).trans (h (Fin.last k))

theorem speed_integrable (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) : IntervalIntegrable (speed g c) MeasureTheory.volume a b := by
  simpa only [c.first_node, c.last_node] using
    intervalIntegrable_of_partition c.node (speed_integrable_on_piece g c)

theorem squared_speed_integrable (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) :
    IntervalIntegrable (fun t => speed g c t ^ 2) MeasureTheory.volume a b := by
  simpa only [c.first_node, c.last_node] using
    intervalIntegrable_of_partition c.node (squared_speed_integrable_on_piece g c)

/-- A finite ordered partition covers its interval away from its nodes. -/
theorem exists_piece_between_nodes {k : ℕ} (u : Fin (k + 1) → ℝ)
    {t : ℝ} (hfirst : u 0 < t) (hlast : t < u (Fin.last k))
    (hne : ∀ i, t ≠ u i) :
    ∃ i : Fin k, t ∈ Ioo (u i.castSucc) (u i.succ) := by
  induction k with
  | zero =>
    have h : (0 : Fin 1) = Fin.last 0 := Subsingleton.elim _ _
    rw [← h] at hlast
    exact (not_lt_of_gt hfirst hlast).elim
  | succ k ih =>
    by_cases ht : t < u ⟨k, by omega⟩
    · obtain ⟨i, hi⟩ := ih (fun i => u i.castSucc) hfirst ht
        (fun i => hne i.castSucc)
      exact ⟨i.castSucc, by simpa only [Fin.succ_castSucc] using hi⟩
    · refine ⟨Fin.last k, ?_, hlast⟩
      exact lt_of_le_of_ne (le_of_not_gt ht) (hne _).symm

theorem exists_piece_off_breakpoints {a b : ℝ} (c : PiecewiseC1Curve S a b)
    {t : ℝ} (ht : t ∈ Icc a b) (hcorner : t ∉ breakpoints c) :
    ∃ i : Fin c.pieces, t ∈ Ioo (c.node i.castSucc) (c.node i.succ) := by
  classical
  have hne : ∀ i, t ≠ c.node i := by
    intro i hi
    exact hcorner (by simp [breakpoints, hi])
  apply exists_piece_between_nodes c.node
  · have h : a ≠ t := by simpa only [c.first_node] using (hne 0).symm
    simpa only [c.first_node] using lt_of_le_of_ne ht.1 h
  · have h : t ≠ b := by simpa only [c.last_node] using hne (Fin.last c.pieces)
    simpa only [c.last_node] using lt_of_le_of_ne ht.2 h
  · exact hne

theorem hasVelocityAt_off_breakpoints {a b : ℝ} (c : PiecewiseC1Curve S a b)
    {t : ℝ} (ht : t ∈ Icc a b) (hcorner : t ∉ breakpoints c) :
    HasVelocityAt S c t (velocity S c t) := by
  obtain ⟨i, hi⟩ := exists_piece_off_breakpoints c ht hcorner
  exact velocity_on_piece c i hi

theorem speed_eq_of_eqOn (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) {d : ℝ → M} (heq : EqOn c d (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) (hcorner : t ∉ breakpoints c) :
    speed g c t = speed g d t := by
  obtain ⟨i, hi⟩ := exists_piece_off_breakpoints c ht hcorner
  have hJ : Icc a b ∈ 𝓝 t := Icc_mem_nhds
    ((node_mem c i.castSucc).1.trans_lt hi.1)
    (hi.2.trans_le (node_mem c i.succ).2)
  exact speed_congr_of_eventuallyEq g (velocity_on_piece c i hi)
    (Filter.mem_of_superset hJ (fun _ hs => heq hs))

/-- Length is independent of the total representative outside its interval,
and of all choices of partition data for the same compact-domain map. -/
theorem length_eq_of_eqOn (g : RiemannianMetric S) {a b : ℝ}
    (c d : PiecewiseC1Curve S a b) (heq : EqOn c d (Icc a b)) : length g c = length g d := by
  unfold length
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(breakpoints c).finite_toSet.countable.ae_notMem MeasureTheory.volume]
    with t ht hI
  have hIcc : t ∈ Icc a b := by
    rw [uIoc_of_le c.ordered] at hI
    exact ⟨hI.1.le, hI.2⟩
  exact speed_eq_of_eqOn g c heq hIcc ht

theorem energy_eq_of_eqOn (g : RiemannianMetric S) {a b : ℝ}
    (c d : PiecewiseC1Curve S a b) (heq : EqOn c d (Icc a b)) : energy g c = energy g d := by
  unfold energy
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(breakpoints c).finite_toSet.countable.ae_notMem MeasureTheory.volume]
    with t ht hI
  have hIcc : t ∈ Icc a b := by
    rw [uIoc_of_le c.ordered] at hI
    exact ⟨hI.1.le, hI.2⟩
  exact congrArg (fun r : ℝ => r ^ 2) (speed_eq_of_eqOn g c heq hIcc ht)

/-- The compact-interval map has the required continuity. -/
theorem compactCurve_continuous {a b : ℝ} (c : PiecewiseC1Curve S a b) :
    Continuous (compactCurve c) :=
  c.continuousOn.domRestrict

/-- Any two scalar integrands differing at finitely many parameters have the
same integral. In particular endpoints and corners carry no integration data. -/
theorem integral_eq_of_eq_off_finite {a b : ℝ} {f h : ℝ → ℝ}
    (K : Finset ℝ) (heq : ∀ t, t ∉ K → f t = h t) :
    (∫ t in a..b, f t) = ∫ t in a..b, h t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [K.finite_toSet.countable.ae_notMem MeasureTheory.volume] with t ht _
  exact heq t ht

theorem intervalIntegrable_iff_of_eq_off_finite {a b : ℝ} {f h : ℝ → ℝ}
    (K : Finset ℝ) (heq : ∀ t, t ∉ K → f t = h t) :
    IntervalIntegrable f MeasureTheory.volume a b ↔
      IntervalIntegrable h MeasureTheory.volume a b := by
  apply intervalIntegrable_congr_ae
  filter_upwards [K.finite_toSet.countable.ae_notMem
    (MeasureTheory.volume.restrict (Set.uIoc a b))] with t ht
  exact heq t ht

theorem integral_norm_eq_of_velocity_eq_off_finite
    (g : RiemannianMetric S) {c : ℝ → M}
    (v w : ∀ t, TangentSpace S (c t)) {a b : ℝ} (K : Finset ℝ)
    (heq : ∀ t, t ∉ K → v t = w t) :
    (∫ t in a..b, tangentNorm g (c t) (v t)) =
      ∫ t in a..b, tangentNorm g (c t) (w t) :=
  integral_eq_of_eq_off_finite K
    (fun t ht => congrArg (tangentNorm g (c t)) (heq t ht))

theorem integral_sq_norm_eq_of_velocity_eq_off_finite
    (g : RiemannianMetric S) {c : ℝ → M}
    (v w : ∀ t, TangentSpace S (c t)) {a b : ℝ} (K : Finset ℝ)
    (heq : ∀ t, t ∉ K → v t = w t) :
    (∫ t in a..b, tangentNorm g (c t) (v t) ^ 2) =
      ∫ t in a..b, tangentNorm g (c t) (w t) ^ 2 :=
  integral_eq_of_eq_off_finite K
    (fun t ht => congrArg (fun v => tangentNorm g (c t) v ^ 2) (heq t ht))

/-- Smooth postcomposition acts through the actual intrinsic differential. -/
theorem HasVelocityAt.postcomp
    {m : ℕ} {targetKind : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m targetKind N} {f : M → N}
    (hf : IsSmoothMap S T f) {c : ℝ → M} {t : ℝ}
    {v : TangentSpace S (c t)} (hv : HasVelocityAt S c t v)
    (L : TangentSpace S (c t) →ₗ[ℝ] TangentSpace T (f (c t)))
    (hL : SmoothManifolds.DifferentialData.IsDifferential S T f (c t) L) :
    HasVelocityAt T (f ∘ c) t (L v) := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (c t)
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (f (c t))
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ := (hf (c t)).2 e he d hd hp hpd
  have hj := SmoothManifolds.differential_jacobian S T f hf (c t) L hL
    e d he hd hp hpd
    ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp)
    ((tangentStructure T).fiberCoordinates.equiv d hd (f (c t)) hpd)
    ((tangentStructure S).fiberCoordinates.isCoordinates e he (c t) hp)
    ((tangentStructure T).fiberCoordinates.isCoordinates d hd (f (c t)) hpd)
    U F hU hpU hF hrep v
  refine ⟨(hf (c t)).1.comp hv.1, d, hd, hpd, ?_⟩
  change HasDerivAt (fun s => (d (f (c s))).val)
    (((tangentStructure T).fiberCoordinates.equiv d hd (f (c t)) hpd) (L v)) t
  rw [hj]
  exact ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt t (hasVelocityAt_coordinates hv e he hp)
    |>.congr_of_eventuallyEq (hrep.comp_tendsto hv.1).symm

/-- The ordinary one-variable chain rule gives scalar reparametrization. -/
theorem HasVelocityAt.reparam {c : ℝ → M} {t r : ℝ} {φ : ℝ → ℝ}
    {v : TangentSpace S (c (φ t))} (hv : HasVelocityAt S c (φ t) v)
    (hφ : HasDerivAt φ r t) :
    HasVelocityAt S (c ∘ φ) t (r • v) := by
  obtain ⟨hc, e, he, hp, hd⟩ := hv
  refine ⟨hc.comp hφ.continuousAt, e, he, hp, ?_⟩
  convert hd.scomp t hφ using 1 <;> simp [Function.comp_def]

theorem CoordinateC1On.postcomp
    {m : ℕ} {targetKind : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m targetKind N} {f : M → N}
    (hf : IsSmoothMap S T f) {c : ℝ → M} {J : Set ℝ}
    (hc : ContinuousOn c J) (h : CoordinateC1On S c J) :
    CoordinateC1On T (f ∘ c) J := by
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := h t ht
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (f (c t))
  obtain ⟨U, hU, hpU, F, hF, hrep⟩ := (hf (c t)).2 e he d hd hp hpd
  have hxU : x t ∈ U := hxt.symm ▸ hpU
  have hF1 : ContDiffAt ℝ 1 F (x t) :=
    (hF.contDiffAt (hU.mem_nhds hxU)).of_le (by simp)
  refine ⟨d, hd, hpd, F ∘ x, hF1.comp t hx, ?_, ?_⟩
  · exact (congrArg F hxt).trans hrep.eq_of_nhds
  · have hcomp := hrep.comp_tendsto (hc t ht)
    filter_upwards [heq, hcomp] with s hs hsf
    change (d (f (c s))).val = F (x s)
    rw [← hs]
    exact hsf.symm

/-- Postcomposition preserves the actual C¹ piece condition and continuity. -/
def postcompose
    {m : ℕ} {targetKind : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m targetKind N} (f : M → N) (hf : IsSmoothMap S T f)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) : PiecewiseC1Curve T a b where
  ordered := c.ordered
  toFun := f ∘ c
  continuousOn := (show Continuous f from continuous_iff_continuousAt.mpr
    (fun p => (hf p).1)).comp_continuousOn c.continuousOn
  pieces := c.pieces
  node := c.node
  monotone_node := c.monotone_node
  first_node := c.first_node
  last_node := c.last_node
  regular := fun i => CoordinateC1On.postcomp hf
    (c.continuousOn.mono (fun _ ht =>
      ⟨(node_mem c i.castSucc).1.trans ht.1, ht.2.trans (node_mem c i.succ).2⟩))
    (c.regular i)

theorem velocity_postcompose
    {m : ℕ} {targetKind : ModelKind} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m targetKind N} (f : M → N) (hf : IsSmoothMap S T f)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) {t : ℝ}
    (ht : t ∈ Icc a b) (hcorner : t ∉ breakpoints c)
    (L : TangentSpace S (c t) →ₗ[ℝ] TangentSpace T (f (c t)))
    (hL : SmoothManifolds.DifferentialData.IsDifferential S T f (c t) L) :
    velocity T (postcompose f hf c) t = L (velocity S c t) :=
  velocity_eq (HasVelocityAt.postcomp hf (hasVelocityAt_off_breakpoints c ht hcorner) L hL)

/-- C¹ changes of real parameter preserve the ambient coordinate extension
condition on any subset mapped into the original piece. -/
theorem CoordinateC1On.reparam {c : ℝ → M} {J K : Set ℝ} {φ : ℝ → ℝ}
    (h : CoordinateC1On S c J) (hφ : ∀ t ∈ K, ContDiffAt ℝ 1 φ t)
    (hmaps : MapsTo φ K J) : CoordinateC1On S (c ∘ φ) K := by
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := h (φ t) (hmaps ht)
  refine ⟨e, he, hp, x ∘ φ, hx.comp t (hφ t ht), hxt, ?_⟩
  exact heq.comp_tendsto ((hφ t ht).continuousAt.continuousWithinAt.tendsto_nhdsWithin hmaps)

/-- Constant coordinate data suffices on a singleton, without restrictions on
the total function away from that singleton. -/
theorem coordinateC1On_singleton (c : ℝ → M) (t : ℝ) :
    CoordinateC1On S c {t} := by
  intro s hs
  obtain rfl := Set.mem_singleton_iff.mp hs
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (c s)
  refine ⟨e, he, hp, fun _ => (e (c s)).val, contDiffAt_const, rfl, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [Set.mem_singleton_iff.mp hz]

/-- Restriction clamps the old partition nodes to the smaller interval. Empty
pieces are singletons, so no new endpoint differentiability is required. -/
def restrict {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (l r : ℝ) (hal : a ≤ l) (hlr : l ≤ r) (hrb : r ≤ b) :
    PiecewiseC1Curve S l r where
  ordered := hlr
  toFun := c
  continuousOn := c.continuousOn.mono (fun _ ht => ⟨hal.trans ht.1, ht.2.trans hrb⟩)
  pieces := c.pieces
  node := fun i => max l (min r (c.node i))
  monotone_node := by
    intro i j hij
    exact max_le_max_left l (min_le_min_left r (c.monotone_node hij))
  first_node := by simp [c.first_node, min_eq_right (hal.trans hlr), max_eq_left hal]
  last_node := by simp [c.last_node, min_eq_left hrb, max_eq_right hlr]
  regular := by
    intro i
    by_cases heq : max l (min r (c.node i.castSucc)) = max l (min r (c.node i.succ))
    · rw [heq, Icc_self]
      exact coordinateC1On_singleton c _
    · apply CoordinateC1On.mono (c.regular i)
      have hnode := c.monotone_node (Fin.castSucc_le_succ i)
      intro t ht
      simp only [mem_Icc] at ht ⊢
      constructor <;> grind

/-- Reversal keeps the same interval and reverses the finite partition. -/
def reverse {a b : ℝ} (c : PiecewiseC1Curve S a b) : PiecewiseC1Curve S a b where
  ordered := c.ordered
  toFun := fun t => c (a + b - t)
  continuousOn := c.continuousOn.comp
    (continuousOn_const.sub continuousOn_id)
    (fun t ht => by constructor <;> linarith [ht.1, ht.2])
  pieces := c.pieces
  node := fun i => a + b - c.node i.rev
  monotone_node := by
    intro i j hij
    exact sub_le_sub_left (c.monotone_node (Fin.rev_le_rev.mpr hij)) _
  first_node := by simp only [Fin.rev_zero, c.last_node]; ring
  last_node := by simp only [Fin.rev_last, c.first_node]; ring
  regular := by
    intro i
    apply CoordinateC1On.reparam (c.regular i.rev)
      (fun _ _ => contDiffAt_const.sub contDiffAt_id)
    intro t ht
    simp only [mem_Icc, Fin.rev_castSucc, Fin.rev_succ, id_eq] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]

theorem velocity_reverse {a b : ℝ} (c : PiecewiseC1Curve S a b) {t : ℝ}
    (ht : a + b - t ∈ Icc a b)
    (hcorner : a + b - t ∉ breakpoints c) :
    velocity S (reverse c) t = -velocity S c (a + b - t) := by
  have hv := hasVelocityAt_off_breakpoints c ht hcorner
  have hφ : HasDerivAt (fun s : ℝ => a + b - s) (-1) t := by
    convert (hasDerivAt_const t (a + b)).sub (hasDerivAt_id t) using 1 <;> norm_num
    ext s
    rfl
  have h := velocity_eq (HasVelocityAt.reparam hv hφ)
  change velocity S (fun s => c (a + b - s)) t = _ at h ⊢
  refine h.trans ?_
  ext z
  change (-1 : ℝ) * ((velocity S c (a + b - t)).val z) =
    -((velocity S c (a + b - t)).val z)
  ring

/-- Transfer to the literal compact-domain representation with the same nodes. -/
noncomputable def toCompact {a b : ℝ} (c : PiecewiseC1Curve S a b) : CompactPiecewiseC1Curve S a b where
  ordered := c.ordered
  toFun := compactCurve c
  continuous := compactCurve_continuous c
  pieces := c.pieces
  node := c.node
  monotone_node := c.monotone_node
  first_node := c.first_node
  last_node := c.last_node
  regular := by
    intro i
    apply CoordinateC1On.congr (c.regular i)
    intro t ht
    have htglobal : t ∈ Icc a b :=
      ⟨(node_mem c i.castSucc).1.trans ht.1, ht.2.trans (node_mem c i.succ).2⟩
    simp only [IccExtend_of_mem c.ordered (compactCurve c) htglobal, compactCurve]

/-- Every literal compact-domain curve has a total representative. -/
noncomputable def fromCompact {a b : ℝ} (c : CompactPiecewiseC1Curve S a b) : PiecewiseC1Curve S a b where
  ordered := c.ordered
  toFun := IccExtend c.ordered c.toFun
  continuousOn := (continuous_IccExtend_iff.mpr c.continuous).continuousOn
  pieces := c.pieces
  node := c.node
  monotone_node := c.monotone_node
  first_node := c.first_node
  last_node := c.last_node
  regular := c.regular

@[simp] theorem compact_fromCompact {a b : ℝ} (c : CompactPiecewiseC1Curve S a b) :
    compactCurve (fromCompact c) = c.toFun := by
  funext t
  simp [compactCurve, fromCompact, IccExtend_of_mem c.ordered c.toFun t.property]

/-- The representative obtained by clamping agrees with the original curve
everywhere on its original compact domain. -/
theorem fromCompact_toCompact {a b : ℝ} (c : PiecewiseC1Curve S a b) :
    EqOn (fromCompact (toCompact c)) c (Icc a b) := by
  intro t ht
  simp [fromCompact, toCompact, IccExtend_of_mem c.ordered (compactCurve c) ht, compactCurve]

def concatenateNode {a b z : ℝ} (c : PiecewiseC1Curve S a b)
    (d : PiecewiseC1Curve S b z) (i : Fin (c.pieces + 1 + d.pieces + 1)) : ℝ :=
  if h : i.val < c.pieces + 1 then c.node ⟨i.val, h⟩
  else d.node ⟨i.val - (c.pieces + 1), by omega⟩

theorem concatenateNode_left {a b z : ℝ} (c : PiecewiseC1Curve S a b)
    (d : PiecewiseC1Curve S b z) (i : Fin (c.pieces + 1)) :
    concatenateNode c d ⟨i.val, by omega⟩ = c.node i := by
  unfold concatenateNode
  rw [dite_eq_left i.isLt]

theorem concatenateNode_right {a b z : ℝ} (c : PiecewiseC1Curve S a b)
    (d : PiecewiseC1Curve S b z) (i : Fin (d.pieces + 1)) :
    concatenateNode c d ⟨c.pieces + 1 + i.val, by omega⟩ = d.node i := by
  unfold concatenateNode
  rw [dite_eq_right (by dsimp; omega)]
  congr 1
  apply Fin.ext
  simp

/-- Concatenation on adjacent intervals uses their original parameters. The
partition retains both copies of the matching parameter, a zero-length piece. -/
noncomputable def concatenate {a b z : ℝ} (c : PiecewiseC1Curve S a b)
    (d : PiecewiseC1Curve S b z) (hmatch : c b = d b) : PiecewiseC1Curve S a z := by
  classical
  refine {
    ordered := c.ordered.trans d.ordered
    toFun := fun t => if t ≤ b then c t else d t
    continuousOn := ?_
    pieces := c.pieces + 1 + d.pieces
    node := concatenateNode c d
    monotone_node := ?_
    first_node := ?_
    last_node := ?_
    regular := ?_ }
  · apply ContinuousOn.if
    · intro t ht
      have htb : t = b := by
        simpa only [show {t : ℝ | t ≤ b} = Iic b from rfl, frontier_Iic,
          mem_singleton_iff] using ht.2
      simpa only [htb] using hmatch
    · change ContinuousOn c (Icc a z ∩ closure (Iic b))
      rw [closure_Iic]
      exact c.continuousOn.mono (fun _ ht => ⟨ht.1.1, ht.2⟩)
    · simp only [not_le]
      change ContinuousOn d (Icc a z ∩ closure (Ioi b))
      rw [closure_Ioi]
      exact d.continuousOn.mono (fun _ ht => ⟨ht.2, ht.1.2⟩)
  · intro i j hij
    by_cases hi : i.val < c.pieces + 1
    · rw [concatenateNode, dite_eq_left hi]
      by_cases hj : j.val < c.pieces + 1
      · rw [concatenateNode, dite_eq_left hj]
        exact c.monotone_node hij
      · rw [concatenateNode, dite_eq_right hj]
        exact (node_mem c _).2.trans (node_mem d _).1
    · have hj : ¬j.val < c.pieces + 1 := by exact fun h => hi (lt_of_le_of_lt hij h)
      rw [concatenateNode, dite_eq_right hi, concatenateNode, dite_eq_right hj]
      apply d.monotone_node
      change i.val - (c.pieces + 1) ≤ j.val - (c.pieces + 1)
      omega
  · have h := (concatenateNode_left c d 0).trans c.first_node
    convert h using 1
    congr 1
  · have h := concatenateNode_right c d (Fin.last d.pieces)
    convert h.trans d.last_node using 1
    congr 1
  · intro i
    by_cases hi : i.val < c.pieces
    · let j : Fin c.pieces := ⟨i.val, hi⟩
      have hleft : concatenateNode c d i.castSucc = c.node j.castSucc := by
        have h := concatenateNode_left c d j.castSucc
        convert h using 1 <;> rfl
      have hright : concatenateNode c d i.succ = c.node j.succ := by
        have h := concatenateNode_left c d j.succ
        convert h using 1 <;> rfl
      rw [hleft, hright]
      apply CoordinateC1On.congr (c.regular j)
      intro t ht
      exact ite_eq_left (ht.2.trans (node_mem c j.succ).2)
    · by_cases heq : i.val = c.pieces
      · have hleft : concatenateNode c d i.castSucc = b := by
          have h := concatenateNode_left c d (Fin.last c.pieces)
          apply (congrArg (concatenateNode c d) (show i.castSucc = _ from
            Fin.ext (by simpa only [Fin.val_castSucc, Fin.val_mk, Fin.val_last] using heq))).trans
            (h.trans c.last_node)
        have hright : concatenateNode c d i.succ = b := by
          have h := concatenateNode_right c d 0
          apply (congrArg (concatenateNode c d) (show i.succ = _ from
            Fin.ext (by simp only [Fin.val_succ, Fin.val_mk, Fin.val_zero]; omega))).trans
            (h.trans d.first_node)
        rw [hleft, hright, Icc_self]
        exact coordinateC1On_singleton _ _
      · let j : Fin d.pieces := ⟨i.val - (c.pieces + 1), by omega⟩
        have hleft : concatenateNode c d i.castSucc = d.node j.castSucc := by
          have h := concatenateNode_right c d j.castSucc
          apply (congrArg (concatenateNode c d) (show i.castSucc = _ from
            Fin.ext (by dsimp [j]; omega))).trans h
        have hright : concatenateNode c d i.succ = d.node j.succ := by
          have h := concatenateNode_right c d j.succ
          apply (congrArg (concatenateNode c d) (show i.succ = _ from
            Fin.ext (by dsimp [j]; omega))).trans h
        rw [hleft, hright]
        apply CoordinateC1On.congr (d.regular j)
        intro t ht
        by_cases htb : t ≤ b
        · have ht' : b ≤ t := (node_mem d j.castSucc).1.trans ht.1
          have heq : t = b := le_antisymm htb ht'
          simpa [heq] using hmatch
        · exact ite_eq_right htb

theorem concatenate_eq_left {a b z : ℝ} (c : PiecewiseC1Curve S a b)
    (d : PiecewiseC1Curve S b z) (hmatch : c b = d b) :
    EqOn (concatenate c d hmatch) c (Icc a b) := by
  intro t ht
  exact ite_eq_left ht.2

theorem concatenate_eq_right {a b z : ℝ} (c : PiecewiseC1Curve S a b)
    (d : PiecewiseC1Curve S b z) (hmatch : c b = d b) :
    EqOn (concatenate c d hmatch) d (Icc b z) := by
  intro t ht
  by_cases htb : t ≤ b
  · have h : t = b := le_antisymm htb ht.1
    simpa [concatenate, h] using hmatch
  · exact ite_eq_right htb

theorem velocity_concatenate_left {a b z : ℝ} (c : PiecewiseC1Curve S a b)
    (d : PiecewiseC1Curve S b z) (hmatch : c b = d b) {t : ℝ}
    (ht : t ∈ Icc a b) (htb : t < b) (hcorner : t ∉ breakpoints c) :
    HEq (velocity S (concatenate c d hmatch) t) (velocity S c t) := by
  apply HEq.symm
  apply velocity_congr (hasVelocityAt_off_breakpoints c ht hcorner)
  filter_upwards [Iio_mem_nhds htb] with s hs
  change c s = if s ≤ b then c s else d s
  exact (ite_eq_left hs.le).symm

theorem velocity_concatenate_right {a b z : ℝ} (c : PiecewiseC1Curve S a b)
    (d : PiecewiseC1Curve S b z) (hmatch : c b = d b) {t : ℝ}
    (ht : t ∈ Icc b z) (htb : b < t) (hcorner : t ∉ breakpoints d) :
    HEq (velocity S (concatenate c d hmatch) t) (velocity S d t) := by
  apply HEq.symm
  apply velocity_congr (hasVelocityAt_off_breakpoints d ht hcorner)
  filter_upwards [Ioi_mem_nhds htb] with s hs
  change d s = if s ≤ b then c s else d s
  exact (ite_eq_right (not_le_of_gt hs)).symm

/-- A constant curve on every ordered interval, including a=b. -/
def stationary (S : SmoothManifold n kind M) (a b : ℝ) (hab : a ≤ b) (p : M) :
    PiecewiseC1Curve S a b where
  ordered := hab
  toFun := fun _ => p
  continuousOn := continuousOn_const
  pieces := 1
  node := ![a, b]
  monotone_node := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  first_node := rfl
  last_node := rfl
  regular := fun _ => coordinateC1On_const p _

@[simp] theorem speed_stationary (g : RiemannianMetric S)
    (a b : ℝ) (hab : a ≤ b) (p : M) (t : ℝ) :
    speed g (stationary S a b hab p) t = 0 := by
  change tangentNorm g p (velocity S (fun _ => p) t) = 0
  rw [velocity_const, SmoothMetrics.tangentNorm_zero]

@[simp] theorem length_stationary (g : RiemannianMetric S)
    (a b : ℝ) (hab : a ≤ b) (p : M) :
    length g (stationary S a b hab p) = 0 := by
  simp [length]

@[simp] theorem energy_stationary (g : RiemannianMetric S)
    (a b : ℝ) (hab : a ≤ b) (p : M) :
    energy g (stationary S a b hab p) = 0 := by
  simp [energy]

@[simp] theorem length_degenerate (g : RiemannianMetric S) (a : ℝ)
    (c : PiecewiseC1Curve S a a) : length g c = 0 := by simp [length]

@[simp] theorem energy_degenerate (g : RiemannianMetric S) (a : ℝ)
    (c : PiecewiseC1Curve S a a) : energy g c = 0 := by simp [energy]

/-- Every finite family on consecutive intervals with matching endpoint values
has a genuine piecewise C¹ concatenation. The empty family is stationary. -/
theorem finiteConcatenation_exists {k : ℕ} (node : Fin (k + 1) → ℝ)
    (p : Fin (k + 1) → M)
    (curves : (i : Fin k) → PiecewiseC1Curve S (node i.castSucc) (node i.succ))
    (hstart : ∀ i, curves i (node i.castSucc) = p i.castSucc)
    (hend : ∀ i, curves i (node i.succ) = p i.succ) :
    ∃ c : PiecewiseC1Curve S (node 0) (node (Fin.last k)),
      c (node 0) = p 0 ∧ c (node (Fin.last k)) = p (Fin.last k) ∧
      ∀ (i : Fin k) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) → c t = curves i t := by
  induction k with
  | zero =>
    refine ⟨stationary S _ _ (by simp) (p 0), rfl, ?_, ?_⟩
    · rfl
    · intro i
      exact Fin.elim0 i
  | succ k ih =>
    obtain ⟨c, hc0, hck, hcpieces⟩ := ih
      (fun i => node i.castSucc) (fun i => p i.castSucc)
      (fun i => curves i.castSucc) (fun i => hstart i.castSucc) (fun i => hend i.castSucc)
    let d := curves (Fin.last k)
    have hm : c (node (Fin.last k).castSucc) = d (node (Fin.last k).castSucc) :=
      hck.trans (hstart (Fin.last k)).symm
    refine ⟨concatenate c d hm, ?_, ?_, ?_⟩
    · exact (concatenate_eq_left c d hm (left_mem_Icc.mpr c.ordered)).trans hc0
    · exact (concatenate_eq_right c d hm (right_mem_Icc.mpr d.ordered)).trans (hend (Fin.last k))
    · intro i t ht
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have hnode : Monotone node := Fin.monotone_iff_le_succ.mpr (fun i => (curves i).ordered)
        have hct : t ∈ Icc (node 0) (node (Fin.last k).castSucc) := by
          constructor
          · exact (hnode (Fin.zero_le _)).trans ht.1
          · exact ht.2.trans (hnode (show j.castSucc.succ ≤ (Fin.last k).castSucc from by
              change j.val + 1 ≤ k
              omega))
        exact (concatenate_eq_left c d hm hct).trans (hcpieces j t ht)
      · exact concatenate_eq_right c d hm ht

/-- The velocity of a restriction is literally the same intrinsic vector,
since the total representative has not changed. -/
theorem velocity_restrict {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (l r : ℝ) (hal : a ≤ l) (hlr : l ≤ r) (hrb : r ≤ b) (t : ℝ) :
    velocity S (restrict c l r hal hlr hrb) t = velocity S c t := rfl

/-- Agreement on the compact interval determines the interior velocity, with
its necessary transport between the two equal tangent base points. -/
theorem velocity_eq_of_eqOn {a b : ℝ} (c : PiecewiseC1Curve S a b)
    {d : ℝ → M} (heq : EqOn c d (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) (hcorner : t ∉ breakpoints c) :
    HEq (velocity S c t) (velocity S d t) := by
  obtain ⟨i, hi⟩ := exists_piece_off_breakpoints c ht hcorner
  have hJ : Icc a b ∈ 𝓝 t := Icc_mem_nhds
    ((node_mem c i.castSucc).1.trans_lt hi.1)
    (hi.2.trans_le (node_mem c i.succ).2)
  exact velocity_congr (velocity_on_piece c i hi)
    (Filter.mem_of_superset hJ (fun _ hs => heq hs))

/-- The faithful finite concatenation also retains every original interior
velocity, away from the original finite corner sets. -/
theorem finiteConcatenation_velocity {k : ℕ} (node : Fin (k + 1) → ℝ)
    (p : Fin (k + 1) → M)
    (curves : (i : Fin k) → PiecewiseC1Curve S (node i.castSucc) (node i.succ))
    (hstart : ∀ i, curves i (node i.castSucc) = p i.castSucc)
    (hend : ∀ i, curves i (node i.succ) = p i.succ) :
    ∃ c : PiecewiseC1Curve S (node 0) (node (Fin.last k)),
      c (node 0) = p 0 ∧ c (node (Fin.last k)) = p (Fin.last k) ∧
      (∀ (i : Fin k) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) → c t = curves i t) ∧
      ∀ (i : Fin k) (t : ℝ), t ∈ Icc (node i.castSucc) (node i.succ) →
        t ∉ breakpoints (curves i) → HEq (velocity S c t) (velocity S (curves i) t) := by
  obtain ⟨c, hc0, hclast, hceq⟩ := finiteConcatenation_exists node p curves hstart hend
  refine ⟨c, hc0, hclast, hceq, ?_⟩
  intro i t ht hcorner
  exact (velocity_eq_of_eqOn (curves i) (fun s hs => (hceq i s hs).symm) ht hcorner).symm

theorem velocity_eq_coordinateExtension {c : ℝ → M} {J : Set ℝ} {t : ℝ}
    (hc : ContinuousAt c t) (hJ : J ∈ 𝓝 t)
    (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (hp : c t ∈ e.source) {x : ℝ → Euclidean n}
    (hx : ContDiffAt ℝ 1 x t)
    (heq : (fun s => (e (c s)).val) =ᶠ[𝓝[J] t] x) :
    velocity S c t = ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp).symm
      (deriv x t) := by
  apply velocity_eq
  let E := (tangentStructure S).fiberCoordinates.equiv e he (c t) hp
  refine ⟨hc, e, he, hp, ?_⟩
  change HasDerivAt _ (E (E.symm (deriv x t))) t
  have heq' : (fun s => (e (c s)).val) =ᶠ[𝓝 t] x := by
    simpa only [nhdsWithin_eq_nhds.mpr hJ] using heq
  simpa only [LinearEquiv.apply_symm_apply] using
    (hx.differentiableAt (by simp)).hasDerivAt.congr_of_eventuallyEq heq'

 theorem coordinateExtension_independent {c : ℝ → M} {J K : Set ℝ} {t : ℝ}
    (hc : ContinuousAt c t) (hJ : J ∈ 𝓝 t) (hK : K ∈ 𝓝 t)
    (e d : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (hp : c t ∈ e.source) (hq : c t ∈ d.source)
    {x y : ℝ → Euclidean n} (hx : ContDiffAt ℝ 1 x t) (hy : ContDiffAt ℝ 1 y t)
    (hxeq : (fun s => (e (c s)).val) =ᶠ[𝓝[J] t] x)
    (hyeq : (fun s => (d (c s)).val) =ᶠ[𝓝[K] t] y) :
    ((tangentStructure S).fiberCoordinates.equiv e he (c t) hp).symm (deriv x t) =
      ((tangentStructure S).fiberCoordinates.equiv d hd (c t) hq).symm (deriv y t) := by
  exact (velocity_eq_coordinateExtension hc hJ e he hp hx hxeq).symm.trans
    (velocity_eq_coordinateExtension hc hK d hd hq hy hyeq)

/-- Independent construction contract for restriction. -/
theorem restriction_exists : P202Specs.Geometry.PiecewiseCurves.restriction_existsType.{u} := by
  intro n kind M _ S a b c l r hal hlr hrb
  exact ⟨restrict c l r hal hlr hrb, fun _ => rfl, fun _ => HEq.rfl⟩

/-- Independent construction contract for reversal. -/
theorem reversal_exists : P202Specs.Geometry.PiecewiseCurves.reversal_existsType.{u} := by
  intro n kind M _ S a b c
  exact ⟨reverse c, fun _ => rfl, fun t ht hcorner => heq_of_eq (velocity_reverse c ht hcorner)⟩

/-- Independent construction contract for smooth postcomposition. -/
theorem postcomposition_exists : P202Specs.Geometry.PiecewiseCurves.postcomposition_existsType.{u} := by
  intro n kind M _ S m targetKind N _ T f hf a b c
  exact ⟨postcompose f hf c, fun _ => rfl,
    fun t ht hcorner L hL => heq_of_eq (velocity_postcompose f hf c ht hcorner L hL)⟩

/-- Independent construction contract for matching adjacent curves. -/
theorem concatenation_exists : P202Specs.Geometry.PiecewiseCurves.concatenation_existsType.{u} := by
  intro n kind M _ S a b z c d hmatch
  exact ⟨concatenate c d hmatch, concatenate_eq_left c d hmatch,
    concatenate_eq_right c d hmatch, fun _ => velocity_concatenate_left c d hmatch,
    fun _ => velocity_concatenate_right c d hmatch⟩

/-- Independent construction contract for stationary curves. -/
theorem stationary_exists : P202Specs.Geometry.PiecewiseCurves.stationary_existsType.{u} := by
  intro n kind M _ S a b hab p
  exact ⟨stationary S a b hab p, fun _ => rfl,
    fun g => ⟨length_stationary g a b hab p, energy_stationary g a b hab p⟩⟩

/-- Independent faithful compact-domain representation contract. -/
theorem compact_representation : P202Specs.Geometry.PiecewiseCurves.compact_representationType.{u} := by
  intro n kind M _ S a b
  exact ⟨fun c => ⟨toCompact c, rfl⟩, fun d => ⟨fromCompact d, compact_fromCompact d⟩⟩

/-- Public names for the independent shared curve and parameter objects. -/
abbrev Curve := @P202.CurveData.PiecewiseC1Curve
abbrev CompactCurve := @P202.CurveData.CompactPiecewiseC1Curve
abbrev IncreasingParameter := P202.CurveData.PiecewiseRegularIncreasing


/-- Every ordinary strictly increasing onto piecewise regular scalar map
has the canonical compact order-isomorphism representation. -/
theorem parameter_representation {a b l r : ℝ} (hab : a ≤ b) (hlr : l ≤ r)
    (f : ℝ → ℝ) (hmaps : MapsTo f (Icc l r) (Icc a b))
    (hincr : StrictMonoOn f (Icc l r)) (honto : SurjOn f (Icc l r) (Icc a b))
    (k : ℕ) (node : Fin (k + 1) → ℝ) (hnode : Monotone node)
    (hfirst : node 0 = l) (hlast : node (Fin.last k) = r)
    (hregular : ∀ i : Fin k, RegularRealC1On f (Icc (node i.castSucc) (node i.succ))) :
    ∃ φ : PiecewiseRegularIncreasing a b l r, EqOn φ f (Icc l r) := by
  let emb : Icc l r ↪o Icc a b := OrderEmbedding.ofStrictMono
    (fun t => ⟨f t, hmaps t.property⟩) (fun x y hxy => hincr x.property y.property hxy)
  have hemb : Function.Surjective emb := by
    intro y
    obtain ⟨x, hx, hxy⟩ := honto y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e := OrderIso.ofSurjective emb hemb
  have heq : EqOn (IccExtend hlr (fun t => (e t).val)) f (Icc l r) := by
    intro t ht
    rw [IccExtend_of_mem hlr _ ht]
    rfl
  refine ⟨{
    source_ordered := hlr
    target_ordered := hab
    map := e
    pieces := k
    node := node
    monotone_node := hnode
    first_node := hfirst
    last_node := hlast
    regular := ?_ }, heq⟩
  intro i t ht
  have htglobal : t ∈ Icc l r := by
    constructor
    · have h := hnode (Fin.zero_le i.castSucc)
      rw [hfirst] at h
      exact h.trans ht.1
    · have h := hnode (Fin.le_last i.succ)
      rw [hlast] at h
      exact ht.2.trans h
  obtain ⟨ψ, hψ, hψt, hψeq, hψpos⟩ := hregular i t ht
  refine ⟨ψ, hψ, (heq htglobal).trans hψt, ?_, hψpos⟩
  filter_upwards [hψeq, self_mem_nhdsWithin] with s hs hsI
  have hsGlobal : s ∈ Icc l r := by
    constructor
    · have h := hnode (Fin.zero_le i.castSucc)
      rw [hfirst] at h
      exact h.trans hsI.1
    · have h := hnode (Fin.le_last i.succ)
      rw [hlast] at h
      exact hsI.2.trans h
  exact (heq hsGlobal).trans hs


@[simp] theorem parameter_apply_mem {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) {t : ℝ} (ht : t ∈ Icc l r) :
    φ t = (φ.map ⟨t, ht⟩).val :=
  IccExtend_of_mem φ.source_ordered _ ht

theorem parameter_continuous {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) : Continuous φ := by
  apply continuous_IccExtend_iff.mpr
  exact continuous_subtype_val.comp φ.map.continuous

theorem parameter_mapsTo {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) : MapsTo φ (Icc l r) (Icc a b) := by
  intro t ht
  rw [parameter_apply_mem φ ht]
  exact (φ.map ⟨t, ht⟩).property

theorem parameter_strictMonoOn {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) : StrictMonoOn φ (Icc l r) := by
  intro x hx y hy hxy
  rw [parameter_apply_mem φ hx, parameter_apply_mem φ hy]
  exact φ.map.strictMono hxy

@[simp] theorem parameter_first {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) : φ l = a := by
  rw [parameter_apply_mem φ (left_mem_Icc.mpr φ.source_ordered)]
  have h : φ.map ⟨l, left_mem_Icc.mpr φ.source_ordered⟩ =
      ⟨a, left_mem_Icc.mpr φ.target_ordered⟩ := by
    apply le_antisymm
    · calc
        _ ≤ φ.map (φ.map.symm ⟨a, left_mem_Icc.mpr φ.target_ordered⟩) :=
          φ.map.monotone (φ.map.symm ⟨a, left_mem_Icc.mpr φ.target_ordered⟩).property.1
        _ = _ := φ.map.apply_symm_apply _
    · exact (φ.map ⟨l, left_mem_Icc.mpr φ.source_ordered⟩).property.1
  exact congrArg Subtype.val h

@[simp] theorem parameter_last {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) : φ r = b := by
  rw [parameter_apply_mem φ (right_mem_Icc.mpr φ.source_ordered)]
  have h : φ.map ⟨r, right_mem_Icc.mpr φ.source_ordered⟩ =
      ⟨b, right_mem_Icc.mpr φ.target_ordered⟩ := by
    apply le_antisymm
    · exact (φ.map ⟨r, right_mem_Icc.mpr φ.source_ordered⟩).property.2
    · calc
        _ = φ.map (φ.map.symm ⟨b, right_mem_Icc.mpr φ.target_ordered⟩) :=
          (φ.map.apply_symm_apply _).symm
        _ ≤ _ := φ.map.monotone
          (φ.map.symm ⟨b, right_mem_Icc.mpr φ.target_ordered⟩).property.2
  exact congrArg Subtype.val h

theorem parameter_surjOn {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) : SurjOn φ (Icc l r) (Icc a b) := by
  intro t ht
  refine ⟨(φ.map.symm ⟨t, ht⟩).val, (φ.map.symm ⟨t, ht⟩).property, ?_⟩
  rw [parameter_apply_mem]
  exact congrArg Subtype.val (φ.map.apply_symm_apply ⟨t, ht⟩)

 theorem RegularRealC1On.mono {φ : ℝ → ℝ} {J K : Set ℝ}
    (h : RegularRealC1On φ J) (hK : K ⊆ J) : RegularRealC1On φ K := by
  intro t ht
  obtain ⟨ψ, hψ, heq, heq', hpos⟩ := h t (hK ht)
  exact ⟨ψ, hψ, heq, heq'.filter_mono (nhdsWithin_mono t hK), hpos⟩

/-- Local scalar extensions suffice; the total scalar function may have corners
at the endpoints of the piece. -/
theorem CoordinateC1On.reparam_regular {c : ℝ → M} {J K : Set ℝ} {φ : ℝ → ℝ}
    (h : CoordinateC1On S c J) (hφ : RegularRealC1On φ K)
    (hcont : ContinuousOn φ K) (hmaps : MapsTo φ K J) :
    CoordinateC1On S (c ∘ φ) K := by
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := h (φ t) (hmaps ht)
  obtain ⟨ψ, hψ, hψt, hψeq, _⟩ := hφ t ht
  refine ⟨e, he, hp, x ∘ ψ, ?_, ?_, ?_⟩
  · rw [hψt] at hx
    exact hx.comp t hψ
  · simpa only [Function.comp_apply, ← hψt] using hxt
  · exact (heq.comp_tendsto ((hcont t ht).tendsto_nhdsWithin hmaps)).trans
      (hψeq.fun_comp x)


theorem parameter_node_mem {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) (i : Fin (φ.pieces + 1)) :
    φ.node i ∈ Icc l r := by
  constructor
  · simpa only [φ.first_node] using φ.monotone_node (Fin.zero_le i)
  · simpa only [φ.last_node] using φ.monotone_node (Fin.le_last i)

noncomputable def pullbackNode {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) (c : PiecewiseC1Curve S a b)
    (i : Fin (c.pieces + 1)) : ℝ :=
  (φ.map.symm ⟨c.node i, node_mem c i⟩).val

theorem pullbackNode_mem {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) (c : PiecewiseC1Curve S a b)
    (i : Fin (c.pieces + 1)) : pullbackNode φ c i ∈ Icc l r :=
  (φ.map.symm ⟨c.node i, node_mem c i⟩).property

@[simp] theorem parameter_pullbackNode {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) (c : PiecewiseC1Curve S a b)
    (i : Fin (c.pieces + 1)) : φ (pullbackNode φ c i) = c.node i := by
  rw [parameter_apply_mem φ (pullbackNode_mem φ c i)]
  exact congrArg Subtype.val (φ.map.apply_symm_apply ⟨c.node i, node_mem c i⟩)

theorem pullbackNode_monotone {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) (c : PiecewiseC1Curve S a b) :
    Monotone (pullbackNode φ c) := by
  intro i j hij
  exact φ.map.symm.monotone (c.monotone_node hij)

@[simp] theorem pullbackNode_first {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) (c : PiecewiseC1Curve S a b) :
    pullbackNode φ c 0 = l := by
  apply (parameter_strictMonoOn φ).injOn (pullbackNode_mem φ c 0)
    (left_mem_Icc.mpr φ.source_ordered)
  simp [c.first_node]

@[simp] theorem pullbackNode_last {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) (c : PiecewiseC1Curve S a b) :
    pullbackNode φ c (Fin.last c.pieces) = r := by
  apply (parameter_strictMonoOn φ).injOn (pullbackNode_mem φ c _)
    (right_mem_Icc.mpr φ.source_ordered)
  simp [c.last_node]

/-- On one scalar piece, clamp the pulled-back old partition to that piece.
This forms a finite common refinement without excluding repeated nodes. -/
noncomputable def reparametrizePiece {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r)
    (j : Fin φ.pieces) :
    PiecewiseC1Curve S (φ.node j.castSucc) (φ.node j.succ) where
  ordered := φ.monotone_node (Fin.castSucc_le_succ j)
  toFun := c ∘ φ
  continuousOn := c.continuousOn.comp (parameter_continuous φ).continuousOn
    (fun t ht => parameter_mapsTo φ
      ⟨(parameter_node_mem φ j.castSucc).1.trans ht.1,
        ht.2.trans (parameter_node_mem φ j.succ).2⟩)
  pieces := c.pieces
  node := fun i => max (φ.node j.castSucc) (min (φ.node j.succ) (pullbackNode φ c i))
  monotone_node := by
    intro i k hik
    exact max_le_max_left _ (min_le_min_left _ (pullbackNode_monotone φ c hik))
  first_node := by
    rw [pullbackNode_first]
    simp [min_eq_right ((parameter_node_mem φ j.succ).1),
      max_eq_left (parameter_node_mem φ j.castSucc).1]
  last_node := by
    rw [pullbackNode_last]
    simp [min_eq_left (parameter_node_mem φ j.succ).2,
      max_eq_right (φ.monotone_node (Fin.castSucc_le_succ j))]
  regular := by
    intro i
    by_cases heq :
        max (φ.node j.castSucc) (min (φ.node j.succ) (pullbackNode φ c i.castSucc)) =
        max (φ.node j.castSucc) (min (φ.node j.succ) (pullbackNode φ c i.succ))
    · rw [heq, Icc_self]
      exact coordinateC1On_singleton (c ∘ φ) _
    · have horder := φ.monotone_node (Fin.castSucc_le_succ j)
      have hsmall := pullbackNode_monotone φ c (Fin.castSucc_le_succ i)
      have hsub :
          Icc
            (max (φ.node j.castSucc) (min (φ.node j.succ) (pullbackNode φ c i.castSucc)))
            (max (φ.node j.castSucc) (min (φ.node j.succ) (pullbackNode φ c i.succ))) ⊆
          Icc (φ.node j.castSucc) (φ.node j.succ) := by
        intro t ht
        simp only [mem_Icc] at ht ⊢
        constructor <;> grind
      apply CoordinateC1On.reparam_regular (c.regular i)
        (RegularRealC1On.mono (φ.regular j) hsub)
        ((parameter_continuous φ).continuousOn)
      intro t ht
      have hglobal : t ∈ Icc l r :=
        ⟨(parameter_node_mem φ j.castSucc).1.trans (hsub ht).1,
          (hsub ht).2.trans (parameter_node_mem φ j.succ).2⟩
      have hbounds : pullbackNode φ c i.castSucc ≤ t ∧
          t ≤ pullbackNode φ c i.succ := by
        simp only [mem_Icc] at ht
        constructor <;> grind
      constructor
      · rw [← parameter_pullbackNode φ c i.castSucc]
        exact (parameter_strictMonoOn φ).monotoneOn
          (pullbackNode_mem φ c i.castSucc) hglobal hbounds.1
      · rw [← parameter_pullbackNode φ c i.succ]
        exact (parameter_strictMonoOn φ).monotoneOn
          hglobal (pullbackNode_mem φ c i.succ) hbounds.2


/-- Agreement on all closed pieces gives agreement on the compact interval;
the initial value handles a partition with no pieces. -/
theorem eqOn_of_eqOn_partition {k : ℕ} (node : Fin (k + 1) → ℝ)
    {f g : ℝ → M} (hfirst : f (node 0) = g (node 0))
    (hpieces : ∀ i : Fin k, EqOn f g (Icc (node i.castSucc) (node i.succ))) :
    EqOn f g (Icc (node 0) (node (Fin.last k))) := by
  induction k with
  | zero =>
    intro t ht
    have heq : t = node 0 := le_antisymm ht.2 ht.1
    simpa only [heq] using hfirst
  | succ k ih =>
    intro t ht
    by_cases htk : t ≤ node ⟨k, by omega⟩
    · exact ih (fun i => node i.castSucc) hfirst
        (fun i => hpieces i.castSucc) ⟨ht.1, htk⟩
    · exact hpieces (Fin.last k) ⟨(lt_of_not_ge htk).le, ht.2⟩

/-- Existence follows by concatenating the finitely many scalar pieces, each
already refined by all old curve nodes. -/
theorem reparametrize_exists {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r) :
    ∃ q : PiecewiseC1Curve S l r, EqOn q (c ∘ φ) (Icc l r) := by
  obtain ⟨q, hfirst, _, hpieces⟩ := finiteConcatenation_exists φ.node
    (fun i => c (φ (φ.node i))) (reparametrizePiece c φ)
    (fun _ => rfl) (fun _ => rfl)
  have heq : EqOn q (c ∘ φ) (Icc (φ.node 0) (φ.node (Fin.last φ.pieces))) :=
    eqOn_of_eqOn_partition φ.node hfirst hpieces
  refine ⟨{
    ordered := φ.source_ordered
    toFun := q
    continuousOn := ?_
    pieces := q.pieces
    node := q.node
    monotone_node := q.monotone_node
    first_node := q.first_node.trans φ.first_node
    last_node := q.last_node.trans φ.last_node
    regular := q.regular }, ?_⟩
  · simpa only [φ.first_node, φ.last_node] using q.continuousOn
  · simpa only [φ.first_node, φ.last_node] using heq

/-- The composition itself is a continuous piecewise C1 curve on the new
compact parameter interval. Only scalar C1 regularity and increasingness are
part of the input. -/
noncomputable def reparametrize {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r) :
    PiecewiseC1Curve S l r := by
  classical
  let q := Classical.choose (reparametrize_exists c φ)
  have hq := Classical.choose_spec (reparametrize_exists c φ)
  exact {
    ordered := φ.source_ordered
    toFun := c ∘ φ
    continuousOn := c.continuousOn.comp (parameter_continuous φ).continuousOn
      (parameter_mapsTo φ)
    pieces := q.pieces
    node := q.node
    monotone_node := q.monotone_node
    first_node := q.first_node
    last_node := q.last_node
    regular := fun i => CoordinateC1On.congr (q.regular i) (fun t ht =>
      (hq ⟨(node_mem q i.castSucc).1.trans ht.1,
        ht.2.trans (node_mem q i.succ).2⟩).symm) }

@[simp] theorem reparametrize_apply {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r) (t : ℝ) :
    reparametrize c φ t = c (φ t) := rfl

theorem parameter_contDiffAt_pos_deriv {a b l r : ℝ}
    (φ : PiecewiseRegularIncreasing a b l r) {t : ℝ}
    (ht : t ∈ Icc l r) (hcorner : t ∉ parameterBreakpoints φ) :
    ContDiffAt ℝ 1 φ t ∧ 0 < deriv φ t := by
  classical
  have hne : ∀ i, t ≠ φ.node i := by
    intro i hi
    exact hcorner (by simp [parameterBreakpoints, hi])
  have hfirst : φ.node 0 < t := by
    have h : l ≠ t := by simpa only [φ.first_node] using (hne 0).symm
    simpa only [φ.first_node] using lt_of_le_of_ne ht.1 h
  have hlast : t < φ.node (Fin.last φ.pieces) := by
    have h : t ≠ r := by simpa only [φ.last_node] using hne (Fin.last φ.pieces)
    simpa only [φ.last_node] using lt_of_le_of_ne ht.2 h
  obtain ⟨i, hi⟩ := exists_piece_between_nodes φ.node hfirst hlast hne
  obtain ⟨ψ, hψ, _, heq, hpos⟩ := φ.regular i t (Ioo_subset_Icc_self hi)
  have heq' : (φ : ℝ → ℝ) =ᶠ[𝓝 t] ψ := by
    simpa only [PiecewiseRegularIncreasing.toFun,
      nhdsWithin_eq_nhds.mpr (Icc_mem_nhds hi.1 hi.2)] using heq
  exact ⟨hψ.congr_of_eventuallyEq heq', heq'.deriv_eq.symm ▸ hpos⟩

theorem velocity_reparam_off_breakpoints {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r) {t : ℝ}
    (ht : t ∈ Icc l r) (hparam : t ∉ parameterBreakpoints φ)
    (hcorner : φ t ∉ breakpoints c) :
    velocity S (c ∘ φ) t = deriv φ t • velocity S c (φ t) := by
  have hφt : φ t ∈ Icc a b := by
    rw [show φ t = (φ.map ⟨t, ht⟩).val from IccExtend_of_mem φ.source_ordered _ ht]
    exact (φ.map ⟨t, ht⟩).property
  exact velocity_eq (HasVelocityAt.reparam (hasVelocityAt_off_breakpoints c hφt hcorner)
    ((parameter_contDiffAt_pos_deriv φ ht hparam).1.differentiableAt (by simp)).hasDerivAt)

/-- All parameter nodes and preimages of the original curve nodes. -/
noncomputable def reparametrizationExceptions {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r) : Finset ℝ := by
  classical
  exact parameterBreakpoints φ ∪ Finset.univ.image
    (fun i : Fin (c.pieces + 1) => (φ.map.symm ⟨c.node i, node_mem c i⟩).val)

theorem reparametrizationExceptions_exclusions {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r) {t : ℝ}
    (ht : t ∈ Icc l r) (hbad : t ∉ reparametrizationExceptions c φ) :
    t ∉ parameterBreakpoints φ ∧ φ t ∉ breakpoints c := by
  classical
  constructor
  · intro h
    exact hbad (Finset.mem_union_left _ h)
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    have hmap : (φ.map ⟨t, ht⟩).val = c.node i :=
      (show φ t = (φ.map ⟨t, ht⟩).val from IccExtend_of_mem φ.source_ordered _ ht).symm.trans hi.symm
    have hmapeq : φ.map ⟨t, ht⟩ = ⟨c.node i, node_mem c i⟩ := Subtype.ext hmap
    have hinv : (φ.map.symm ⟨c.node i, node_mem c i⟩).val = t := by
      have h := congrArg (fun z : Icc a b => (φ.map.symm z).val) hmapeq
      simpa only [OrderIso.symm_apply_apply] using h.symm
    apply hbad
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hinv⟩)

theorem velocity_reparam_off_exceptions {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r) {t : ℝ}
    (ht : t ∈ Icc l r) (hbad : t ∉ reparametrizationExceptions c φ) :
    velocity S (c ∘ φ) t = deriv φ t • velocity S c (φ t) := by
  obtain ⟨hparam, hcorner⟩ := reparametrizationExceptions_exclusions c φ ht hbad
  exact velocity_reparam_off_breakpoints c φ ht hparam hcorner

theorem reparametrization_velocity_finite_exceptions {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r) :
    ∃ K : Finset ℝ, ∀ t ∈ Icc l r, t ∉ K →
      ContDiffAt ℝ 1 φ t ∧ 0 < deriv φ t ∧
        velocity S (c ∘ φ) t = deriv φ t • velocity S c (φ t) := by
  refine ⟨reparametrizationExceptions c φ, fun t ht hbad => ?_⟩
  obtain ⟨hparam, _⟩ := reparametrizationExceptions_exclusions c φ ht hbad
  obtain ⟨hC, hD⟩ := parameter_contDiffAt_pos_deriv φ ht hparam
  exact ⟨hC, hD, velocity_reparam_off_exceptions c φ ht hbad⟩

/-- Every piecewise regular increasing parameter change has a piecewise C1
composite, and the intrinsic chain rule follows from the scalar regularity. -/
theorem reparametrization_exists_off_breakpoints {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r) :
    ∃ q : PiecewiseC1Curve S l r, (∀ t, q t = c (φ t)) ∧
      ∀ t ∈ Icc l r, t ∉ parameterBreakpoints φ → φ t ∉ breakpoints c →
        HEq (velocity S q t) (deriv φ t • velocity S c (φ t)) := by
  refine ⟨reparametrize c φ, fun _ => rfl, fun t ht hparam hcorner => ?_⟩
  exact heq_of_eq (velocity_reparam_off_breakpoints c φ ht hparam hcorner)

/-- The construction and chain rule also expose a single finite exceptional
set on the new compact interval, including all endpoint and corner choices. -/
theorem reparametrization_exists {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (φ : PiecewiseRegularIncreasing a b l r) :
    ∃ q : PiecewiseC1Curve S l r, (∀ t, q t = c (φ t)) ∧
      ∃ K : Finset ℝ, ∀ t ∈ Icc l r, t ∉ K →
        ContDiffAt ℝ 1 φ t ∧ 0 < deriv φ t ∧
          HEq (velocity S q t) (deriv φ t • velocity S c (φ t)) := by
  obtain ⟨K, hK⟩ := reparametrization_velocity_finite_exceptions c φ
  refine ⟨reparametrize c φ, fun _ => rfl, K, fun t ht hbad => ?_⟩
  obtain ⟨hC, hpos, hvel⟩ := hK t ht hbad
  exact ⟨hC, hpos, heq_of_eq hvel⟩


/-- Finite changes inside the interval are irrelevant, with no assumptions
on the integrands outside their compact integration domain. -/
theorem integral_eq_of_eqOn_off_finite {a b : ℝ} {f h : ℝ → ℝ}
    (K : Finset ℝ) (heq : ∀ t, t ∈ uIoc a b → t ∉ K → f t = h t) :
    (∫ t in a..b, f t) = ∫ t in a..b, h t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [K.finite_toSet.countable.ae_notMem MeasureTheory.volume] with t ht hI
  exact heq t hI ht

theorem intervalIntegrable_iff_of_eqOn_off_finite {a b : ℝ} {f h : ℝ → ℝ}
    (K : Finset ℝ) (heq : ∀ t, t ∈ uIoc a b → t ∉ K → f t = h t) :
    IntervalIntegrable f MeasureTheory.volume a b ↔
      IntervalIntegrable h MeasureTheory.volume a b := by
  apply intervalIntegrable_congr_ae
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [K.finite_toSet.countable.ae_notMem MeasureTheory.volume] with t ht hI
  exact heq t hI ht

theorem integral_norm_eq_of_velocity_eqOn_off_finite
    (g : RiemannianMetric S) {c : ℝ → M}
    (v w : ∀ t, TangentSpace S (c t)) {a b : ℝ} (K : Finset ℝ)
    (heq : ∀ t, t ∈ uIoc a b → t ∉ K → v t = w t) :
    (∫ t in a..b, tangentNorm g (c t) (v t)) =
      ∫ t in a..b, tangentNorm g (c t) (w t) :=
  integral_eq_of_eqOn_off_finite K
    (fun t hI ht => congrArg (tangentNorm g (c t)) (heq t hI ht))

theorem integral_sq_norm_eq_of_velocity_eqOn_off_finite
    (g : RiemannianMetric S) {c : ℝ → M}
    (v w : ∀ t, TangentSpace S (c t)) {a b : ℝ} (K : Finset ℝ)
    (heq : ∀ t, t ∈ uIoc a b → t ∉ K → v t = w t) :
    (∫ t in a..b, tangentNorm g (c t) (v t) ^ 2) =
      ∫ t in a..b, tangentNorm g (c t) (w t) ^ 2 :=
  integral_eq_of_eqOn_off_finite K
    (fun t hI ht => congrArg (fun v => tangentNorm g (c t) v ^ 2) (heq t hI ht))

/-- Public implementation aliases retain the canonical independent definitions.
The aliases are declared here so submitted definition targets belong to this
implementation module, while every theorem uses the same shared objects. -/
abbrev CoordinateC1On := @P202.CurveData.CoordinateC1On

noncomputable abbrev breakpoints := @P202.CurveData.breakpoints

abbrev compactCurve := @P202.CurveData.compactCurve

abbrev HasVelocityAt := @P202.CurveData.HasVelocityAt

noncomputable abbrev velocity := @P202.CurveData.velocity

noncomputable abbrev speed := @P202.CurveData.speed

noncomputable abbrev length := @P202.CurveData.length

noncomputable abbrev energy := @P202.CurveData.energy

abbrev RegularRealC1On := P202.CurveData.RegularRealC1On

noncomputable abbrev parameterToFun := @P202.CurveData.PiecewiseRegularIncreasing.toFun

noncomputable abbrev parameterBreakpoints := @P202.CurveData.parameterBreakpoints

end P202.Geometry.PiecewiseCurves
