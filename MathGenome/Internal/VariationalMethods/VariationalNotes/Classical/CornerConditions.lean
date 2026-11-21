import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.CornerConditions
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.BoundaryTransversality

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace VariationalNotes.Classical.Corner

theorem clampedState_continuous {I : Interval} {m : ℕ} (u : C1Curve I m) :
    Continuous (clampedState u) :=
  u.state.continuous.comp continuous_projIcc

@[simp] theorem clampedState_on_interval {I : Interval} {m : ℕ}
    (u : C1Curve I m) (t : I.Points) : clampedState u t = u.state t := by
  simp [clampedState]

theorem referenceState_continuous {K : Domain} {m : ℕ}
    (u : C1Curve K.left m) (v : C1Curve K.right m)
    (hj : u.state K.left.right = v.state K.right.left) :
    Continuous (referenceState u v) := by
  apply (clampedState_continuous u).if_le (clampedState_continuous v)
    continuous_id continuous_const
  intro t ht
  change t = K.c at ht
  subst t
  simpa [clampedState, Domain.left, Domain.right, Interval.left, Interval.right] using hj

@[simp] theorem referenceState_left {K : Domain} {m : ℕ}
    (u : C1Curve K.left m) (v : C1Curve K.right m) (t : K.left.Points) :
    referenceState u v t = u.state t := by
  rw [referenceState, ite_eq_left (show (t : ℝ) ≤ K.c from t.property.2)]
  exact clampedState_on_interval u t

@[simp] theorem referenceState_right {K : Domain} {m : ℕ}
    (u : C1Curve K.left m) (v : C1Curve K.right m)
    (hj : u.state K.left.right = v.state K.right.left) (t : K.right.Points) :
    referenceState u v t = v.state t := by
  by_cases ht : (t : ℝ) ≤ K.c
  · have he : (t : ℝ) = K.c := le_antisymm ht t.property.1
    have he' : t = K.right.left := Subtype.ext he
    subst t
    simpa [referenceState, clampedState, Domain.left, Domain.right,
      Interval.left, Interval.right] using hj
  · rw [referenceState, ite_eq_right ht]
    exact clampedState_on_interval v t

/-- Physical uniform neighborhoods contain a neighborhood in the product C¹
configuration space, even when the corner time moves. Compactness of each closed
piece makes the joint continuity estimate uniform over all its points. -/
theorem eventually_uniformClose {K : Domain} {m : ℕ}
    (u : C1Curve K.left m) (v : C1Curve K.right m)
    (hj : u.state K.left.right = v.state K.right.left) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 (reference u v), UniformClose u v x ε := by
  have hf := referenceState_continuous u v hj
  have hs : Continuous (fun x : Configuration K m => x.2.1.state) :=
    continuous_fst.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have ht : Continuous (fun x : Configuration K m => x.2.2.state) :=
    continuous_fst.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  have hl : ∀ᶠ x in 𝓝 (reference u v), ∀ t : K.left.Points,
      ‖x.2.1.state t - referenceState u v (affineTime K.left K.a x.1 t)‖ < ε := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (X := Configuration K m) (Y := K.left.Points) (x₀ := reference u v)
      (P := fun x t => ‖x.2.1.state t -
        referenceState u v (affineTime K.left K.a x.1 t)‖ < ε) ?_
    · simpa only [mem_univ, forall_const] using h
    intro t _
    have hc : Continuous (fun p : Configuration K m × K.left.Points =>
        ‖p.1.2.1.state p.2 - referenceState u v
          (affineTime K.left K.a p.1.1 p.2)‖) := by
      apply Continuous.norm
      apply ((hs.comp continuous_fst).eval continuous_snd).sub
      apply hf.comp
      unfold affineTime
      fun_prop
    apply (isOpen_lt hc continuous_const).mem_nhds
    have ha : affineTime K.left K.a K.c t = t := Boundary.affineTime_self K.left t
    simpa [reference, ha] using hε
  have hr : ∀ᶠ x in 𝓝 (reference u v), ∀ t : K.right.Points,
      ‖x.2.2.state t - referenceState u v (affineTime K.right x.1 K.b t)‖ < ε := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (X := Configuration K m) (Y := K.right.Points) (x₀ := reference u v)
      (P := fun x t => ‖x.2.2.state t -
        referenceState u v (affineTime K.right x.1 K.b t)‖ < ε) ?_
    · simpa only [mem_univ, forall_const] using h
    intro t _
    have hc : Continuous (fun p : Configuration K m × K.right.Points =>
        ‖p.1.2.2.state p.2 - referenceState u v
          (affineTime K.right p.1.1 K.b p.2)‖) := by
      apply Continuous.norm
      apply ((ht.comp continuous_fst).eval continuous_snd).sub
      apply hf.comp
      unfold affineTime
      fun_prop
    apply (isOpen_lt hc continuous_const).mem_nhds
    have ha : affineTime K.right K.c K.b t = t := Boundary.affineTime_self K.right t
    simpa [reference, ha, referenceState_right u v hj] using hε
  exact hl.and hr

@[simp] theorem totalAction_reference {K : Domain} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve K.left m) (v : C1Curve K.right m) :
    totalAction L (reference u v) = action L u + action L v := by
  exact congrArg₂ (· + ·) (Boundary.referenceAction_referenceConfiguration L u)
    (Boundary.referenceAction_referenceConfiguration L v)

private theorem weakMinimum_of_localMin {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hu : graphAdmissible L u)
    (hm : IsLocalMinOn (action L)
      (fixedEndpointClass L (u.state I.left) (u.state I.right)) u) :
    weakLocalMinimum L (u.state I.left) (u.state I.right) u := by
  change ∀ᶠ z in 𝓝[fixedEndpointClass L (u.state I.left) (u.state I.right)] u,
    action L u ≤ action L z at hm
  rw [eventually_nhdsWithin_iff] at hm
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp hm
  refine ⟨⟨hu, rfl, rfl⟩, ε, hε, ?_⟩
  intro z hz hzu
  exact hb (by change dist z.val u.val < ε; rw [dist_eq_norm]; exact hzu) hz

def WeakMinimum {K : Domain} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve K.left m) (v : C1Curve K.right m) (freeTime : Bool) : Prop :=
  reference u v ∈ feasible L u v freeTime ∧
    IsLocalMinOn (totalAction L) (feasible L u v freeTime) (reference u v)

/-- Fixing the entire other piece shows that each piece is a fixed-endpoint
weak local minimum. This also derives the stationarity hypotheses, rather than
requiring a separate certificate for them. -/
theorem WeakMinimum.piecewiseWeak {K : Domain} {m : ℕ} {L : Lagrangian m}
    {u : C1Curve K.left m} {v : C1Curve K.right m} {freeTime : Bool}
    (hm : WeakMinimum L u v freeTime) :
    weakLocalMinimum L (u.state K.left.left) (u.state K.left.right) u ∧
    weakLocalMinimum L (v.state K.right.left) (v.state K.right.right) v := by
  have hu : graphAdmissible L u :=
    (Boundary.referenceAdmissible_referenceConfiguration L u).mp hm.1.1
  have hv : graphAdmissible L v :=
    (Boundary.referenceAdmissible_referenceConfiguration L v).mp hm.1.2.1
  have hj : u.state K.left.right = v.state K.right.left := hm.1.2.2.2.2.1
  constructor
  · apply weakMinimum_of_localMin L u hu
    have hc : Continuous (fun z : C1Curve K.left m => reference z v) := by
      unfold reference
      fun_prop
    have hmap : fixedEndpointClass L (u.state K.left.left) (u.state K.left.right) ⊆
        (fun z => reference z v) ⁻¹' feasible L u v freeTime := by
      intro z hz
      refine ⟨(Boundary.referenceAdmissible_referenceConfiguration L z).mpr hz.1,
        hm.1.2.1, hz.2.1, rfl, hz.2.2.trans hj, fun _ => rfl⟩
    have h := hm.2.comp_continuousOn (g := fun z : C1Curve K.left m => reference z v) (b := u) hmap hc.continuousOn ⟨hu, rfl, rfl⟩
    change ∀ᶠ z in 𝓝[fixedEndpointClass L (u.state K.left.left) (u.state K.left.right)] u,
      totalAction L (reference u v) ≤ totalAction L (reference z v) at h
    simpa only [IsLocalMinOn, IsMinFilter, totalAction_reference, add_le_add_iff_right] using h
  · apply weakMinimum_of_localMin L v hv
    have hc : Continuous (fun z : C1Curve K.right m => reference u z) := by
      unfold reference
      fun_prop
    have hmap : fixedEndpointClass L (v.state K.right.left) (v.state K.right.right) ⊆
        (fun z => reference u z) ⁻¹' feasible L u v freeTime := by
      intro z hz
      refine ⟨hm.1.1,
        (Boundary.referenceAdmissible_referenceConfiguration L z).mpr hz.1,
        rfl, hz.2.2, hj.trans hz.2.1.symm, fun _ => rfl⟩
    have h := hm.2.comp_continuousOn hmap hc.continuousOn ⟨hv, rfl, rfl⟩
    change ∀ᶠ z in 𝓝[fixedEndpointClass L (v.state K.right.left) (v.state K.right.right)] v,
      totalAction L (reference u v) ≤ totalAction L (reference u z) at h
    simpa only [IsLocalMinOn, IsMinFilter, totalAction_reference, add_le_add_iff_left] using h

/-- The endpoint data at the join are total displacements. Both lifted pieces
use exactly the same corner curve, while the two exterior endpoint curves are
constant. The lifts are actual moving physical curves with affine pullbacks. -/
theorem joinedLifts {K : Domain} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve K.left m) (v : C1Curve K.right m)
    (hu : graphAdmissible L u) (hv : graphAdmissible L v)
    (hj : u.state K.left.right = v.state K.right.left) (τ : ℝ) (z : State m) :
    ∃ (l : MovingEndpointVariation u) (r : MovingEndpointVariation v),
      (∀ s, l.leftTime s = K.a ∧ l.rightTime s = K.c + s * τ ∧
        r.leftTime s = K.c + s * τ ∧ r.rightTime s = K.b ∧
        (l.rescaled s).state K.left.left = u.state K.left.left ∧
        (r.rescaled s).state K.right.right = v.state K.right.right ∧
        (l.rescaled s).state K.left.right = u.state K.left.right + s • z ∧
        (r.rescaled s).state K.right.left = u.state K.left.right + s • z) ∧
      endpointTimeDisplacements u l = (0, τ) ∧
      endpointTimeDisplacements v r = (τ, 0) ∧
      endpointDisplacements u l = (0, z) ∧
      endpointDisplacements v r = (z, 0) ∧
      (∀ᶠ s in 𝓝 (0 : ℝ),
        Boundary.referenceAdmissible L (Boundary.variationConfiguration l s) ∧
        Boundary.referenceAdmissible L (Boundary.variationConfiguration r s)) := by
  let γ : ℝ → ℝ × State m := fun s => (K.c + s * τ, u.state K.left.right + s • z)
  have hγ : HasDerivAt γ (τ, z) 0 := by
    simpa [γ] using (((hasDerivAt_id (0 : ℝ)).mul_const τ).const_add K.c).prodMk
      (((hasDerivAt_id (0 : ℝ)).smul_const z).const_add (u.state K.left.right))
  obtain ⟨l, hl, hlt, hlz, hla⟩ := Boundary.endpointLiftConstruction K.left m L u hu
    (fun _ => (K.a, u.state K.left.left)) γ (0, 0) (τ, z) rfl
    (by simp [γ, Domain.left])
    ((hasDerivAt_const (0 : ℝ) K.a).prodMk (hasDerivAt_const (0 : ℝ) (u.state K.left.left))) hγ
  obtain ⟨r, hr, hrt, hrz, hra⟩ := Boundary.endpointLiftConstruction K.right m L v hv
    γ (fun _ => (K.b, v.state K.right.right)) (τ, z) (0, 0)
    (by simp [γ, hj, Domain.right]) rfl hγ
    ((hasDerivAt_const (0 : ℝ) K.b).prodMk (hasDerivAt_const (0 : ℝ) (v.state K.right.right)))
  refine ⟨l, r, ?_, hlt, hrt, hlz, hrz, ?_⟩
  · intro s
    exact ⟨(hl s).1, (hl s).2.1, (hr s).1, (hr s).2.1,
      (hl s).2.2.1, (hr s).2.2.2, (hl s).2.2.2, (hr s).2.2.1⟩
  · filter_upwards [l.increasing_near, r.increasing_near, hla, hra] with s hli hri hlg hrg
    exact ⟨⟨hli, hlg⟩, ⟨hri, hrg⟩⟩

/-- The common endpoint curve yields a feasible joined competitor for both
signs of s. Fixing τ = 0 is exactly the fixed-corner-time case. -/
theorem cornerCovector {K : Domain} {m : ℕ} {L : Lagrangian m}
    {u : C1Curve K.left m} {v : C1Curve K.right m} {freeTime : Bool}
    (hregu : regularNearGraph L u 1) (hregv : regularNearGraph L v 1)
    (hm : WeakMinimum L u v freeTime) (τ : ℝ) (z : State m)
    (hτ : freeTime = false → τ = 0) :
    Boundary.endpointCovector L u K.left.right (τ, z) -
      Boundary.endpointCovector L v K.right.left (τ, z) = 0 := by
  have hu : graphAdmissible L u :=
    (Boundary.referenceAdmissible_referenceConfiguration L u).mp hm.1.1
  have hv : graphAdmissible L v :=
    (Boundary.referenceAdmissible_referenceConfiguration L v).mp hm.1.2.1
  have hj : u.state K.left.right = v.state K.right.left := hm.1.2.2.2.2.1
  obtain ⟨l, r, he, hlt, hrt, hlz, hrz, hadm⟩ := joinedLifts L u v hu hv hj τ z
  let x : ℝ → Configuration K m := fun s =>
    (l.rightTime s, l.rescaled s, r.rescaled s)
  have hx0 : x 0 = reference u v := by
    simp [x, reference, l.right_zero, l.rescaled_zero, r.rescaled_zero, Domain.left]
  have hxc : ContinuousAt x 0 :=
    l.right_differentiable.continuousAt.prodMk
      (l.rescaled_differentiable.continuousAt.prodMk r.rescaled_differentiable.continuousAt)
  have hxl : ∀ s, leftConfiguration (x s) = Boundary.variationConfiguration l s := by
    intro s
    simp [leftConfiguration, x, Boundary.variationConfiguration, (he s).1]
  have hxr : ∀ s, rightConfiguration (x s) = Boundary.variationConfiguration r s := by
    intro s
    simp [rightConfiguration, x, Boundary.variationConfiguration,
      (he s).2.1, (he s).2.2.1, (he s).2.2.2.1]
  have hxf : ∀ᶠ s in 𝓝 (0 : ℝ), x s ∈ feasible L u v freeTime := by
    filter_upwards [hadm] with s hs
    refine ⟨?_, ?_, (he s).2.2.2.2.1, (he s).2.2.2.2.2.1, ?_, ?_⟩
    · rw [hxl]; exact hs.1
    · rw [hxr]; exact hs.2
    · change (l.rescaled s).state K.left.right = (r.rescaled s).state K.right.left
      exact (he s).2.2.2.2.2.2.1.trans (he s).2.2.2.2.2.2.2.symm
    · intro hf
      change l.rightTime s = K.c
      rw [(he s).2.1, hτ hf]
      simp
  have hmin : IsLocalMin (fun s => totalAction L (x s)) 0 := by
    have hct : Tendsto x (𝓝 (0 : ℝ)) (𝓝[feasible L u v freeTime] (reference u v)) :=
      tendsto_nhdsWithin_iff.mpr ⟨by simpa only [hx0] using hxc.tendsto, hxf⟩
    have hh := hm.2
    rw [← hx0] at hh
    exact hh.comp_of_tendsto (by simpa only [hx0] using hct)
  obtain ⟨hwu, hwv⟩ := hm.piecewiseWeak
  have hpu := (classicalEulerLagrange K.left m L _ _ u (Or.inl hwu) hregu).2.2
  have hpv := (classicalEulerLagrange K.right m L _ _ v (Or.inl hwv) hregv).2.2
  have hsu := InnerTime.minimaStationary K.left m L u _ _ hregu (Or.inl hwu)
  have hsv := InnerTime.minimaStationary K.right m L v _ _ hregv (Or.inl hwv)
  have hdl := (Boundary.movingBoundaryDerivative K.left m L u hregu hpu hsu l).1
  have hdr := (Boundary.movingBoundaryDerivative K.right m L v hregv hpv hsv r).1
  have hd : HasDerivAt (fun s => totalAction L (x s))
      (Boundary.boundaryValue L u l + Boundary.boundaryValue L v r) 0 := by
    convert hdl.add hdr using 1
    funext s
    simp only [totalAction, hxl, hxr, Pi.add_apply]
  have hz := hmin.hasDerivAt_eq_zero hd
  have hb : Boundary.boundaryValue L u l + Boundary.boundaryValue L v r =
      Boundary.endpointCovector L u K.left.right (τ, z) -
        Boundary.endpointCovector L v K.right.left (τ, z) := by
    simp [Boundary.boundaryValue, hlt, hrt, hlz, hrz, Boundary.endpointCovector]
    ring
  rw [hb] at hz
  exact hz

/-- A C¹ jet transported to another closed interval by increasing affine time.
This is an actual physical C¹ curve, including its one-sided endpoint velocities. -/
def rescaleCurve {I : Interval} {m : ℕ} (u : C1Curve I m) (J : Interval) : C1Curve J m := by
  let e : J.Points → I.Points := fun t => ⟨Boundary.inverseAffine I J.a J.b t,
    Boundary.inverseAffine_mapsTo I J.a J.b J.increasing t.property⟩
  have he : Continuous e := by
    apply Continuous.subtype_mk
    unfold Boundary.inverseAffine
    fun_prop
  refine ⟨(u.state.comp ⟨e, he⟩,
    (Boundary.timeScale I J.a J.b)⁻¹ • (u.velocity.comp ⟨e, he⟩)), ?_⟩
  intro t
  have hd := (u.property (e t)).scomp (t : ℝ)
    (Boundary.inverseAffine_hasDerivAt I J.a J.b t).hasDerivWithinAt
    (Boundary.inverseAffine_mapsTo I J.a J.b J.increasing)
  apply hd.congr_of_mem _ t.property
  intro r hr
  have hm := Boundary.inverseAffine_mapsTo I J.a J.b J.increasing hr
  simp [extendState, hr, e, hm, C1Curve.state]

@[simp] theorem rescaleCurve_state_forward {I : Interval} {m : ℕ}
    (u : C1Curve I m) (J : Interval) (t : I.Points) :
    (rescaleCurve u J).state ⟨affineTime I J.a J.b t,
      Boundary.affineTime_mapsTo I J.a J.b J.increasing t.property⟩ = u.state t := by
  change u.state ⟨Boundary.inverseAffine I J.a J.b (affineTime I J.a J.b t), _⟩ = _
  congr 1
  exact Subtype.ext (Boundary.inverseAffine_forward I J.a J.b t J.increasing)

@[simp] theorem rescaleCurve_left {I : Interval} {m : ℕ}
    (u : C1Curve I m) (J : Interval) : (rescaleCurve u J).state J.left = u.state I.left := by
  convert rescaleCurve_state_forward u J I.left using 2
  apply Subtype.ext
  exact (VariationSpaces.affineTime_endpoints I J.a J.b).1.symm

@[simp] theorem rescaleCurve_right {I : Interval} {m : ℕ}
    (u : C1Curve I m) (J : Interval) : (rescaleCurve u J).state J.right = u.state I.right := by
  convert rescaleCurve_state_forward u J I.right using 2
  apply Subtype.ext
  exact (VariationSpaces.affineTime_endpoints I J.a J.b).2.symm

theorem rescaleCurve_graph {I : Interval} {m : ℕ} (u : C1Curve I m)
    (J : Interval) (t : J.Points) :
    graphPoint (rescaleCurve u J) t =
      (affineTime I J.a J.b (Boundary.inverseAffine I J.a J.b t),
        u.state ⟨Boundary.inverseAffine I J.a J.b t,
          Boundary.inverseAffine_mapsTo I J.a J.b J.increasing t.property⟩,
        (Boundary.timeScale I J.a J.b)⁻¹ •
          u.velocity ⟨Boundary.inverseAffine I J.a J.b t,
            Boundary.inverseAffine_mapsTo I J.a J.b J.increasing t.property⟩) := by
  rw [Boundary.forward_inverseAffine I J.a J.b t J.increasing]
  rfl

theorem rescaleCurve_regular {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (J : Interval)
    {U : Set (ℝ × State m × State m)} (hU : IsOpen U) (hUd : U ⊆ L.domain)
    (hL : ContDiffOn ℝ 1 L.value U)
    (hg : ∀ t : I.Points, (affineTime I J.a J.b t, u.state t,
      (Boundary.timeScale I J.a J.b)⁻¹ • u.velocity t) ∈ U) :
    regularNearGraph L (rescaleCurve u J) 1 := by
  refine ⟨U, hU, ?_, hUd, hL⟩
  intro t
  rw [rescaleCurve_graph]
  exact hg ⟨Boundary.inverseAffine I J.a J.b t,
    Boundary.inverseAffine_mapsTo I J.a J.b J.increasing t.property⟩

/-- Affine change of variables identifies the sum-action representation with
ordinary physical actions, not just their first derivatives. -/
theorem rescaleCurve_action {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (J : Interval) :
    action L (rescaleCurve u J) = Boundary.referenceAction L (J.a, J.b, u) := by
  let k := Boundary.timeScale I J.a J.b
  let g : ℝ → ℝ := fun r => L.value
    (r, stateField J m (rescaleCurve u J) r, velocityField J m (rescaleCurve u J) r)
  have haf : ∀ t : ℝ, affineTime I J.a J.b t = k * t + (J.a - k * I.a) := by
    intro t
    dsimp [k, Boundary.timeScale, affineTime]
    ring
  have hend := VariationSpaces.affineTime_endpoints I J.a J.b
  have he := intervalIntegral.smul_integral_comp_mul_add (f := g) (a := I.a) (b := I.b)
    k (J.a - k * I.a)
  simp only [← haf, hend.1, hend.2, smul_eq_mul] at he
  change (∫ r in J.a..J.b, g r) = _
  rw [← he, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le I.increasing.le] at ht
  have hm := Boundary.affineTime_mapsTo I J.a J.b J.increasing ht
  change k * g (affineTime I J.a J.b t) =
    L.value (affineTime I J.a J.b t, stateField I m u t, k⁻¹ • velocityField I m u t) * k
  rw [mul_comm k]
  congr 1
  dsimp [g]
  simp only [stateField, velocityField, extendState, dite_eq_left hm, dite_eq_left ht]
  have hforward := Boundary.inverseAffine_forward I J.a J.b t J.increasing
  change L.value (affineTime I J.a J.b t,
    u.state ⟨Boundary.inverseAffine I J.a J.b (affineTime I J.a J.b t), _⟩,
    k⁻¹ • u.velocity ⟨Boundary.inverseAffine I J.a J.b (affineTime I J.a J.b t), _⟩) = _
  simp only [hforward]

/-- Glue the two physical pieces. Equality of their joined states certifies
continuity; it imposes no equality on their velocities. -/
def gluedCurve {K : Domain} {m : ℕ} (u : C1Curve K.left m)
    (v : C1Curve K.right m) (hj : u.state K.left.right = v.state K.right.left) :
    C(K.whole.Points, State m) :=
  ⟨fun t => referenceState u v t,
    (referenceState_continuous u v hj).comp continuous_subtype_val⟩

theorem gluedCurve_left {K : Domain} {m : ℕ} (u : C1Curve K.left m)
    (v : C1Curve K.right m) (hj : u.state K.left.right = v.state K.right.left)
    (t : ℝ) (ht : t ∈ Icc K.a K.c) :
    extendState K.whole m (gluedCurve u v hj) t = stateField K.left m u t := by
  have hm : t ∈ Icc K.a K.b := ⟨ht.1, ht.2.trans K.right_lt.le⟩
  simp only [extendState, Domain.whole, hm, dite_true, gluedCurve,
    ContinuousMap.coe_mk, stateField]
  rw [referenceState_left u v ⟨t, ht⟩]
  simp [Domain.left, ht]

theorem gluedCurve_right {K : Domain} {m : ℕ} (u : C1Curve K.left m)
    (v : C1Curve K.right m) (hj : u.state K.left.right = v.state K.right.left)
    (t : ℝ) (ht : t ∈ Icc K.c K.b) :
    extendState K.whole m (gluedCurve u v hj) t = stateField K.right m v t := by
  have hm : t ∈ Icc K.a K.b := ⟨K.left_lt.le.trans ht.1, ht.2⟩
  simp only [extendState, Domain.whole, hm, dite_true, gluedCurve,
    ContinuousMap.coe_mk, stateField]
  rw [referenceState_right u v hj ⟨t, ht⟩]
  simp [Domain.right, ht]

/-- The glued physical curve has the original one-sided jets, on the whole
closed pieces. In particular both limiting velocities at the corner remain in
the admissibility test. -/
theorem gluedCurve_jets {K : Domain} {m : ℕ} (u : C1Curve K.left m)
    (v : C1Curve K.right m) (hj : u.state K.left.right = v.state K.right.left) :
    (ContDiffOn ℝ 1 (extendState K.whole m (gluedCurve u v hj)) (Icc K.a K.c) ∧
      ∀ t : K.left.Points, HasDerivWithinAt (extendState K.whole m (gluedCurve u v hj))
        (u.velocity t) (Icc K.a K.c) t) ∧
    (ContDiffOn ℝ 1 (extendState K.whole m (gluedCurve u v hj)) (Icc K.c K.b) ∧
      ∀ t : K.right.Points, HasDerivWithinAt (extendState K.whole m (gluedCurve u v hj))
        (v.velocity t) (Icc K.c K.b) t) := by
  constructor
  · constructor
    · apply (VariationSpaces.c1_contDiffOn K.left m u).congr
      exact fun t ht => gluedCurve_left u v hj t ht
    · intro t
      exact (u.property t).congr_of_mem
        (fun r hr => gluedCurve_left u v hj r hr) t.property
  · constructor
    · apply (VariationSpaces.c1_contDiffOn K.right m v).congr
      exact fun t ht => gluedCurve_right u v hj t ht
    · intro t
      exact (v.property t).congr_of_mem
        (fun r hr => gluedCurve_right u v hj r hr) t.property

theorem gluedCurve_admissible {K : Domain} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve K.left m) (v : C1Curve K.right m)
    (hj : u.state K.left.right = v.state K.right.left)
    (hu : graphAdmissible L u) (hv : graphAdmissible L v) :
    piecewiseAdmissible L (gluedCurve u v hj) := by
  have hjets := gluedCurve_jets u v hj
  have hl : ContDiffOn ℝ 1 (extendState K.whole m (gluedCurve u v hj)) (Icc K.a K.c) ∧
      ∀ t ∈ Icc K.a K.c, (t, extendState K.whole m (gluedCurve u v hj) t,
        derivWithin (extendState K.whole m (gluedCurve u v hj)) (Icc K.a K.c) t) ∈ L.domain := by
    refine ⟨hjets.1.1, ?_⟩
    intro t ht
    rw [(hjets.1.2 ⟨t, ht⟩).derivWithin (uniqueDiffOn_Icc K.left_lt t ht),
      gluedCurve_left u v hj t ht]
    simpa [graphPoint, stateField, extendState, Domain.left, ht] using hu ⟨t, ht⟩
  have hr : ContDiffOn ℝ 1 (extendState K.whole m (gluedCurve u v hj)) (Icc K.c K.b) ∧
      ∀ t ∈ Icc K.c K.b, (t, extendState K.whole m (gluedCurve u v hj) t,
        derivWithin (extendState K.whole m (gluedCurve u v hj)) (Icc K.c K.b) t) ∈ L.domain := by
    refine ⟨hjets.2.1, ?_⟩
    intro t ht
    rw [(hjets.2.2 ⟨t, ht⟩).derivWithin (uniqueDiffOn_Icc K.right_lt t ht),
      gluedCurve_right u v hj t ht]
    simpa [graphPoint, stateField, extendState, Domain.right, ht] using hv ⟨t, ht⟩
  refine ⟨{K.a, K.c, K.b}, by simp [Domain.whole], by simp [Domain.whole], ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨le_rfl, (K.left_lt.trans K.right_lt).le⟩
    · exact ⟨K.left_lt.le, K.right_lt.le⟩
    · exact ⟨(K.left_lt.trans K.right_lt).le, le_rfl⟩
  · intro s hs t ht hst hnone
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl
    all_goals try exact (lt_irrefl _ hst).elim
    all_goals try exact (not_lt_of_ge K.left_lt.le hst).elim
    all_goals try exact (not_lt_of_ge K.right_lt.le hst).elim
    all_goals try exact (not_lt_of_ge (K.left_lt.trans K.right_lt).le hst).elim
    · exact hl
    · exact (hnone K.c (by simp) ⟨K.left_lt, K.right_lt⟩).elim
    · exact hr

theorem actionDensity_continuousOn {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 1) :
    ContinuousOn (fun t => L.value (t, stateField I m u t, velocityField I m u t))
      (Icc I.a I.b) := by
  obtain ⟨U, _, hg, _, hL⟩ := hreg
  apply hL.continuousOn.comp (graphField_continuousOn I m u)
  intro t ht
  simpa [graphPoint, stateField, velocityField, extendState, ht] using hg ⟨t, ht⟩

/-- The action of the continuous glued curve is exactly the sum of the two
one-sided actions. Its undefined classical derivative at the corner affects
only a null set and is never identified with either limiting velocity. -/
theorem gluedCurve_action {K : Domain} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve K.left m) (v : C1Curve K.right m)
    (hj : u.state K.left.right = v.state K.right.left)
    (hregu : regularNearGraph L u 1) (hregv : regularNearGraph L v 1) :
    piecewiseAction L (gluedCurve u v hj) = action L u + action L v := by
  let F : ℝ → ℝ := fun t => L.value (t, extendState K.whole m (gluedCurve u v hj) t,
    derivWithin (extendState K.whole m (gluedCurve u v hj)) (Icc K.a K.b) t)
  let G : ℝ → ℝ := fun t => L.value (t, stateField K.left m u t, velocityField K.left m u t)
  let H : ℝ → ℝ := fun t => L.value (t, stateField K.right m v t, velocityField K.right m v t)
  have hjets := gluedCurve_jets u v hj
  have hl : EqOn F G (Ioo K.a K.c) := by
    intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have htall : t ∈ Icc K.a K.b := ⟨ht.1.le, (ht.2.trans K.right_lt).le⟩
    have hd := ((hjets.1.2 ⟨t, ht'⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt (s := Icc K.a K.b)
    have he := hd.derivWithin (uniqueDiffOn_Icc K.whole.increasing t htall)
    dsimp [F, G]
    rw [he, gluedCurve_left u v hj t ht']
    simp [velocityField, extendState, Domain.left, ht']
  have hr : EqOn F H (Ioo K.c K.b) := by
    intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have htall : t ∈ Icc K.a K.b := ⟨(K.left_lt.trans ht.1).le, ht.2.le⟩
    have hd := ((hjets.2.2 ⟨t, ht'⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt (s := Icc K.a K.b)
    have he := hd.derivWithin (uniqueDiffOn_Icc K.whole.increasing t htall)
    dsimp [F, H]
    rw [he, gluedCurve_right u v hj t ht']
    simp [velocityField, extendState, Domain.right, ht']
  have hG : IntervalIntegrable G volume K.a K.c := by
    exact (actionDensity_continuousOn L u hregu).intervalIntegrable_of_Icc K.left_lt.le
  have hH : IntervalIntegrable H volume K.c K.b := by
    exact (actionDensity_continuousOn L v hregv).intervalIntegrable_of_Icc K.right_lt.le
  have hFl : IntervalIntegrable F volume K.a K.c :=
    hG.congr_uIoo (by simpa only [uIoo_of_le K.left_lt.le] using hl.symm)
  have hFr : IntervalIntegrable F volume K.c K.b :=
    hH.congr_uIoo (by simpa only [uIoo_of_le K.right_lt.le] using hr.symm)
  change (∫ t in K.a..K.b, F t) = (∫ t in K.a..K.c, G t) + (∫ t in K.c..K.b, H t)
  rw [← intervalIntegral.integral_add_adjacent_intervals hFl hFr,
    intervalIntegral.integral_congr_Ioo_of_le K.left_lt.le hl,
    intervalIntegral.integral_congr_Ioo_of_le K.right_lt.le hr]

theorem Represents.join {K : Domain} {m : ℕ} {w : C(K.whole.Points, State m)}
    {u : C1Curve K.left m} {v : C1Curve K.right m} (hw : Represents w u v) :
    u.state K.left.right = v.state K.right.left := by
  rw [← hw.1 K.left.right, ← hw.2 K.right.left]
  rfl

theorem Represents.eq_gluedCurve {K : Domain} {m : ℕ} {w : C(K.whole.Points, State m)}
    {u : C1Curve K.left m} {v : C1Curve K.right m} (hw : Represents w u v) :
    w = gluedCurve u v hw.join := by
  apply ContinuousMap.ext
  intro t
  by_cases ht : (t : ℝ) ≤ K.c
  · exact (hw.1 ⟨t, t.property.1, ht⟩).trans
      (referenceState_left u v ⟨t, t.property.1, ht⟩).symm
  · exact (hw.2 ⟨t, (not_le.mp ht).le, t.property.2⟩).trans
      (referenceState_right u v hw.join ⟨t, (not_le.mp ht).le, t.property.2⟩).symm

/-- In the free-time case the physical minimum is exactly the shared strong
minimum, with no extra variation or stationarity assumption. -/
theorem piecewiseMinimum_iff {K : Domain} {m : ℕ} (L : Lagrangian m)
    (w : C(K.whole.Points, State m)) :
    PiecewiseMinimum L w true ↔
      piecewiseStrongLocalMinimum L (w K.whole.left) (w K.whole.right) w := by
  constructor
  · rintro ⟨hw, ε, hε, hm⟩
    exact ⟨hw, ε, hε, fun f hf hd => hm f hf (by simp) hd⟩
  · rintro ⟨hw, ε, hε, hm⟩
    exact ⟨hw, ε, hε, fun f hf _ hd => hm f hf hd⟩

/-- The physical strong minimum implies the coordinate weak minimum. This
bridge constructs the joined competitor and verifies its physical action and
uniform distance, rather than assuming admissible endpoint tests. -/
theorem PiecewiseMinimum.weak {K : Domain} {m : ℕ} {L : Lagrangian m}
    {w : C(K.whole.Points, State m)} {u : C1Curve K.left m} {v : C1Curve K.right m}
    {freeTime : Bool} (hw : Represents w u v)
    (hregu : regularNearGraph L u 1) (hregv : regularNearGraph L v 1)
    (hm : PiecewiseMinimum L w freeTime) : WeakMinimum L u v freeTime := by
  have hj := hw.join
  have hu : graphAdmissible L u := by
    obtain ⟨_, _, hg, hd, _⟩ := hregu
    exact fun t => hd (hg t)
  have hv : graphAdmissible L v := by
    obtain ⟨_, _, hg, hd, _⟩ := hregv
    exact fun t => hd (hg t)
  refine ⟨⟨(Boundary.referenceAdmissible_referenceConfiguration L u).mpr hu,
    (Boundary.referenceAdmissible_referenceConfiguration L v).mpr hv,
    rfl, rfl, hj, fun _ => rfl⟩, ?_⟩
  obtain ⟨hwb, ε, hε, hmin⟩ := hm
  obtain ⟨U, hU, hgu, hUd, hLU⟩ := hregu
  obtain ⟨V, hV, hgv, hVd, hLV⟩ := hregv
  have hcL : Continuous (@leftConfiguration K m) := by
    unfold leftConfiguration
    fun_prop
  have hcR : Continuous (@rightConfiguration K m) := by
    unfold rightConfiguration
    fun_prop
  have hcLt : Tendsto (@leftConfiguration K m) (𝓝 (reference u v))
      (𝓝 (Boundary.referenceConfiguration u)) := hcL.continuousAt.tendsto
  have hcRt : Tendsto (@rightConfiguration K m) (𝓝 (reference u v))
      (𝓝 (Boundary.referenceConfiguration v)) := hcR.continuousAt.tendsto
  have hUL := hcLt.eventually (Boundary.eventually_transformedGraph_mem u hU hgu)
  have hVR := hcRt.eventually (Boundary.eventually_transformedGraph_mem v hV hgv)
  change ∀ᶠ x in 𝓝[feasible L u v freeTime] (reference u v),
    totalAction L (reference u v) ≤ totalAction L x
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hUL, hVR, eventually_uniformClose u v hj (half_pos hε)] with x hxU hxV hxclose hxf
  have hleft : K.a < x.1 := hxf.1.1
  have hright : x.1 < K.b := hxf.2.1.1
  let Kx : Domain := ⟨K.a, x.1, K.b, hleft, hright⟩
  let u' := rescaleCurve x.2.1 Kx.left
  let v' := rescaleCurve x.2.2 Kx.right
  have hregu' : regularNearGraph L u' 1 :=
    rescaleCurve_regular L x.2.1 Kx.left hU hUd hLU hxU
  have hregv' : regularNearGraph L v' 1 :=
    rescaleCurve_regular L x.2.2 Kx.right hV hVd hLV hxV
  have hj' : u'.state Kx.left.right = v'.state Kx.right.left := by
    dsimp only [u', v']
    rw [rescaleCurve_right, rescaleCurve_left]
    exact hxf.2.2.2.2.1
  let w' : C(K.whole.Points, State m) := gluedCurve (K := Kx) u' v' hj'
  have hwa : piecewiseAdmissible L w' := by
    apply gluedCurve_admissible L u' v' hj'
    · obtain ⟨_, _, hg, hd, _⟩ := hregu'
      exact fun t => hd (hg t)
    · obtain ⟨_, _, hg, hd, _⟩ := hregv'
      exact fun t => hd (hg t)
  have hwleft : w' K.whole.left = w K.whole.left := by
    have he := referenceState_left u' v' Kx.left.left
    change w' K.whole.left = u'.state Kx.left.left at he
    rw [he, show u'.state Kx.left.left = x.2.1.state K.left.left from rescaleCurve_left _ _,
      hxf.2.2.1, ← hw.1 K.left.left]
    rfl
  have hwright : w' K.whole.right = w K.whole.right := by
    have he := referenceState_right u' v' hj' Kx.right.right
    change w' K.whole.right = v'.state Kx.right.right at he
    rw [he, show v'.state Kx.right.right = x.2.2.state K.right.right from rescaleCurve_right _ _,
      hxf.2.2.2.1, ← hw.2 K.right.right]
    rfl
  have hfixed : freeTime = false →
      ContDiffOn ℝ 1 (extendState K.whole m w') (Icc K.a K.c) ∧
      ContDiffOn ℝ 1 (extendState K.whole m w') (Icc K.c K.b) := by
    intro ht
    have he := hxf.2.2.2.2.2 ht
    have hjet := gluedCurve_jets u' v' hj'
    have hl : ContDiffOn ℝ 1 (extendState K.whole m w') (Icc K.a x.1) := hjet.1.1
    have hr : ContDiffOn ℝ 1 (extendState K.whole m w') (Icc x.1 K.b) := hjet.2.1
    exact ⟨by simpa only [he] using hl, by simpa only [he] using hr⟩
  have hnorm : ‖w' - w‖ ≤ ε / 2 := by
    apply (ContinuousMap.norm_le (w' - w) (half_pos hε).le).mpr
    intro t
    rw [hw.eq_gluedCurve]
    change ‖referenceState u' v' t - referenceState u v t‖ ≤ ε / 2
    by_cases ht : (t : ℝ) ≤ x.1
    · let r : K.left.Points := ⟨Boundary.inverseAffine K.left K.a x.1 t,
        Boundary.inverseAffine_mapsTo K.left K.a x.1 hleft ⟨t.property.1, ht⟩⟩
      have hclose := (hxclose.1 r).le
      rw [Boundary.forward_inverseAffine K.left K.a x.1 t hleft] at hclose
      have he := referenceState_left u' v' ⟨t, t.property.1, ht⟩
      rw [he]
      exact hclose
    · let r : K.right.Points := ⟨Boundary.inverseAffine K.right x.1 K.b t,
        Boundary.inverseAffine_mapsTo K.right x.1 K.b hright ⟨(not_le.mp ht).le, t.property.2⟩⟩
      have hclose := (hxclose.2 r).le
      rw [Boundary.forward_inverseAffine K.right x.1 K.b t hright] at hclose
      have he := referenceState_right u' v' hj' ⟨t, (not_le.mp ht).le, t.property.2⟩
      rw [he]
      exact hclose
  have hcompare := hmin w' ⟨hwa, hwleft, hwright⟩ hfixed (hnorm.trans_lt (half_lt_self hε))
  have hbase : piecewiseAction L w = totalAction L (reference u v) := by
    rw [hw.eq_gluedCurve, gluedCurve_action L u v hj ⟨U, hU, hgu, hUd, hLU⟩
      ⟨V, hV, hgv, hVd, hLV⟩, totalAction_reference]
  have htest : piecewiseAction L w' = totalAction L x := by
    rw [gluedCurve_action L u' v' hj' hregu' hregv', rescaleCurve_action, rescaleCurve_action]
    rfl
  rwa [hbase, htest] at hcompare

/-- The physical fixed-time result. No time freedom, C² assumption, or
separate Euler--Lagrange hypothesis is needed for this stronger version. -/
theorem fixedTimeMomentum : Specs.VariationalNotes.Classical.Corner.fixedTimeMomentum := by
  intro K m L w u v hw hregu hregv hm
  have hm' := hm.weak hw hregu hregv
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have h := cornerCovector hregu hregv hm' 0
    (momentum L u K.left.right - momentum L v K.right.left) (fun _ => rfl)
  simpa only [Boundary.endpointCovector, mul_zero, add_zero, inner_sub_left] using h

theorem freeTimeConditions : Specs.VariationalNotes.Classical.Corner.freeTimeConditions := by
  intro K m L w u v hw hregu hregv hm
  have hm' := hm.weak hw hregu hregv
  constructor
  · apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have h := cornerCovector hregu hregv hm' 0
      (momentum L u K.left.right - momentum L v K.right.left) (by simp)
    simpa only [Boundary.endpointCovector, mul_zero, add_zero, inner_sub_left] using h
  · have h := cornerCovector hregu hregv hm' 1 0 (by simp)
    simp only [Boundary.endpointCovector, inner_zero_right, zero_add, mul_one] at h
    rw [InnerTime.energyPairing, InnerTime.energyPairing] at h
    exact sub_eq_zero.mp h

theorem strongMinimumConditions :
    Specs.VariationalNotes.Classical.Corner.strongMinimumConditions := by
  intro K m L w u v hw hregu hregv hm
  exact freeTimeConditions K m L w u v hw hregu hregv ((piecewiseMinimum_iff L w).mpr hm)

end VariationalNotes.Classical.Corner
