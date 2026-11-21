import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.InnerTimeVariation
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.VariationSpaces
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.DistributionalPrimitive
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace VariationalNotes.Classical.InnerTime

theorem energyPairing : Specs.VariationalNotes.Classical.InnerTime.energyPairing := by
  intro I m L u t
  simpa [energy, stateField, velocityField, extendState, t.property, graphPoint] using
    congrArg (fun z : ℝ => L.value (graphPoint u t) - z)
      (VariationSpaces.momentum_pairing I m L u t (u.velocity t)).symm

theorem timePartial_eq_full {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t : ℝ)
    (hL : DifferentiableAt ℝ L.value (t, stateField I m u t, velocityField I m u t)) :
    timePartial L u t =
      fderiv ℝ L.value (t, stateField I m u t, velocityField I m u t) (1, 0, 0) := by
  exact (hL.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk
      ((hasDerivAt_const t (stateField I m u t)).prodMk
        (hasDerivAt_const t (velocityField I m u t))))).deriv

theorem velocityPartial_eq_full {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (t : ℝ)
    (hL : DifferentiableAt ℝ L.value (t, stateField I m u t, velocityField I m u t)) :
    fderiv ℝ (fun v => L.value (t, stateField I m u t, v))
      (velocityField I m u t) (velocityField I m u t) =
    fderiv ℝ L.value (t, stateField I m u t, velocityField I m u t)
      (0, 0, velocityField I m u t) := by
  have h := (hL.hasFDerivAt.comp (velocityField I m u t)
    ((hasFDerivAt_const (𝕜 := ℝ) t (velocityField I m u t)).prodMk
      ((hasFDerivAt_const (stateField I m u t) (velocityField I m u t)).prodMk
        (hasFDerivAt_id (velocityField I m u t))))).fderiv
  exact congrArg (fun D => D (velocityField I m u t)) h

theorem fieldsContinuous : Specs.VariationalNotes.Classical.InnerTime.fieldsContinuous := by
  intro I m L u hreg
  obtain ⟨U, hU, hgU, _, hL⟩ := hreg
  have hg : Continuous (graphPoint u) :=
    continuous_subtype_val.prodMk (u.state.continuous.prodMk u.velocity.continuous)
  have hdf : Continuous (fun t : I.Points => fderiv ℝ L.value (graphPoint u t)) :=
    (hL.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp_continuous hg hgU
  have hval : Continuous (fun t : I.Points => L.value (graphPoint u t)) :=
    hL.continuousOn.comp_continuous hg hgU
  have hd (t : I.Points) : DifferentiableAt ℝ L.value (graphPoint u t) :=
    (hL.differentiableOn_one (graphPoint u t) (hgU t)).differentiableAt (hU.mem_nhds (hgU t))
  have henergy : Continuous (fun t : I.Points => energy L u t) := by
    have hc : Continuous (fun t : I.Points =>
        L.value (graphPoint u t) - fderiv ℝ L.value (graphPoint u t)
          (0, 0, u.velocity t)) :=
      hval.sub (hdf.clm_apply (continuous_const.prodMk
        (continuous_const.prodMk u.velocity.continuous)))
    convert hc using 1
    funext t
    rw [energy, velocityPartial_eq_full L u t]
    · simp [stateField, velocityField, extendState, t.property, graphPoint]
    · simpa [graphPoint, stateField, velocityField, extendState, t.property] using hd t
  have htime : Continuous (fun t : I.Points => timePartial L u t) := by
    have hc : Continuous (fun t : I.Points =>
        fderiv ℝ L.value (graphPoint u t) (1, 0, 0)) := hdf.clm_apply continuous_const
    convert hc using 1
    funext t
    rw [timePartial_eq_full L u t]
    · simp [stateField, velocityField, extendState, t.property, graphPoint]
    · simpa [graphPoint, stateField, velocityField, extendState, t.property] using hd t
  exact ⟨continuousOn_iff_continuous_domRestrict.mpr henergy,
    continuousOn_iff_continuous_domRestrict.mpr htime⟩

theorem integrandDerivative :
    Specs.VariationalNotes.Classical.InnerTime.integrandDerivative := by
  intro I m L u hreg ζ t ht
  obtain ⟨U, hU, hgU, _, hL⟩ := hreg
  have hdiff : DifferentiableAt ℝ L.value
      (t, stateField I m u t, velocityField I m u t) := by
    have hg := hgU ⟨t, ht⟩
    have h := (hL.differentiableOn_one _ hg).differentiableAt (hU.mem_nhds hg)
    simpa [graphPoint, stateField, velocityField, extendState, ht] using h
  let v := velocityField I m u t
  let d := deriv ζ t
  let r := ζ t
  have hj : HasDerivAt (fun s : ℝ => 1 + s * d) d 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add ((hasDerivAt_id 0).mul_const d) using 1 <;> (first | rfl | simp)
  have hinv : HasDerivAt (fun s : ℝ => (1 + s * d)⁻¹) (-d) 0 := by
    convert hj.inv (by simp) using 1
    simp
  have htime : HasDerivAt (fun s : ℝ => t + s * r) r 0 := by
    convert (hasDerivAt_const (0 : ℝ) t).add ((hasDerivAt_id 0).mul_const r) using 1 <;> (first | rfl | simp)
  have hx : HasDerivAt (fun s : ℝ =>
      (t + s * r, stateField I m u t, (1 + s * d)⁻¹ • v))
      (r, 0, (-d) • v) 0 :=
    htime.prodMk ((hasDerivAt_const (0 : ℝ) (stateField I m u t)).prodMk
      (hinv.smul_const v))
  have hL0 : DifferentiableAt ℝ L.value
      (t + 0 * r, stateField I m u t, (1 + 0 * d)⁻¹ • v) := by
    simpa only [zero_mul, add_zero, inv_one, one_smul] using hdiff
  have hcomp := (hL0.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hx).mul hj
  simp only [Function.comp_apply, zero_mul, add_zero, inv_one, one_smul, mul_one] at hcomp
  convert hcomp using 1
  · rfl
  let D := fderiv ℝ L.value (t, stateField I m u t, v)
  have hvec : (r, (0 : State m), (-d) • v) =
      r • (1, (0 : State m), (0 : State m)) - d • (0, (0 : State m), v) := by
    ext <;> simp [neg_smul]
  change timePartial L u t * r + energy L u t * d =
    D (r, 0, (-d) • v) + L.value (t, stateField I m u t, v) * d
  rw [timePartial_eq_full L u t hdiff, energy, velocityPartial_eq_full L u t hdiff]
  change D (1, 0, 0) * r + (L.value (t, stateField I m u t, v) - D (0, 0, v)) * d = _
  rw [hvec, map_sub, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

/-- A convenient compact-rectangle version of differentiation under an integral.
Only continuity in the integration variable is needed. -/
theorem integralDerivativeOnRectangle {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (F G : ℝ × ℝ → ℝ)
    (hF : ContinuousOn F (Icc (-δ) δ ×ˢ Icc a b))
    (hG : ContinuousOn G (Icc (-δ) δ ×ˢ Icc a b))
    (hd : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc a b,
      HasDerivAt (fun s => F (s, t)) (G (s, t)) s) :
    HasDerivAt (fun s => ∫ t in a..b, F (s, t)) (∫ t in a..b, G (0, t)) 0 := by
  have hzero : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hFc (s : ℝ) (hs : s ∈ Icc (-δ) δ) :
      ContinuousOn (fun t => F (s, t)) (Icc a b) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hs, ht⟩)
  have hGc : ContinuousOn (fun t => G (0, t)) (Icc a b) :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hzero, ht⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG
  have hnhds : Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s t => F (s, t)) (F' := fun s t => G (s, t))
    (bound := fun _ => C) hnhds ?_ ?_ ?_ ?_
      (intervalIntegrable_const) ?_).2
  · filter_upwards [hnhds] with s hs
    exact (intervalIntegrable_iff.mp
      ((hFc s (Ioo_subset_Icc_self hs)).intervalIntegrable_of_Icc hab)).aestronglyMeasurable
  · exact (hFc 0 hzero).intervalIntegrable_of_Icc hab
  · exact (intervalIntegrable_iff.mp (hGc.intervalIntegrable_of_Icc hab)).aestronglyMeasurable
  · exact Eventually.of_forall (fun t ht s hs =>
      hC (s, t) ⟨Ioo_subset_Icc_self hs,
        Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using ht)⟩)
  · exact Eventually.of_forall (fun t ht s hs =>
      hd s hs t (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using ht)))

theorem actionDerivative : Specs.VariationalNotes.Classical.InnerTime.actionDerivative := by
  intro I m L u hreg ζ hζ
  obtain ⟨U, hU, hgU, hUd, hL⟩ := hreg
  let z : ℝ → State m := fun t => u.state (projIcc I.a I.b I.increasing.le t)
  let v : ℝ → State m := fun t => u.velocity (projIcc I.a I.b I.increasing.le t)
  have hz : Continuous z := u.state.continuous.comp continuous_projIcc
  have hv : Continuous v := u.velocity.continuous.comp continuous_projIcc
  have hez (t : ℝ) (ht : t ∈ Icc I.a I.b) : z t = stateField I m u t := by
    simp [z, projIcc_of_mem I.increasing.le ht, stateField, extendState, ht]
  have hev (t : ℝ) (ht : t ∈ Icc I.a I.b) : v t = velocityField I m u t := by
    simp [v, projIcc_of_mem I.increasing.le ht, velocityField, extendState, ht]
  let j : ℝ × ℝ → ℝ := fun p => 1 + p.1 * deriv ζ p.2
  have hjc : Continuous j := continuous_const.add
    (continuous_fst.mul (((contDiff_infty_iff_deriv.mp hζ.1).2).continuous.comp continuous_snd))
  let A : ℝ × ℝ → ℝ × State m × State m :=
    fun p => (p.2 + p.1 * ζ p.2, z p.2, (j p)⁻¹ • v p.2)
  have hAc_at (t : ℝ) : ContinuousAt A (0, t) := by
    apply ContinuousAt.prodMk
      ((continuous_snd.add (continuous_fst.mul (hζ.1.continuous.comp continuous_snd))).continuousAt)
    exact (hz.comp continuous_snd).continuousAt.prodMk
      ((hjc.continuousAt.inv₀ (by simp [j])).smul (hv.comp continuous_snd).continuousAt)
  have hA0 (t : ℝ) (ht : t ∈ Icc I.a I.b) : A (0, t) = graphPoint u ⟨t, ht⟩ := by
    simp [A, j, z, v, graphPoint, projIcc_of_mem I.increasing.le ht]
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ Icc I.a I.b,
      j (s, t) ≠ 0 ∧ A (s, t) ∈ U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hn : ∀ᶠ p in 𝓝 (0, t), j p ≠ 0 :=
      hjc.continuousAt.eventually (eventually_ne_nhds (by simp [j]))
    have hu : ∀ᶠ p in 𝓝 (0, t), A p ∈ U :=
      (hAc_at t).eventually (hU.mem_nhds (by rw [hA0 t ht]; exact hgU ⟨t, ht⟩))
    exact hn.and hu
  obtain ⟨δ, hδ, hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  let K : Set (ℝ × ℝ) := Icc (-δ) δ ×ˢ Icc I.a I.b
  have hK (p : ℝ × ℝ) (hp : p ∈ K) : j p ≠ 0 ∧ A p ∈ U := by
    apply hδsub ?_ p.2 hp.2
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le, mem_Icc] using hp.1
  have hAc : ContinuousOn A K := by
    apply ContinuousOn.prodMk
      ((continuous_snd.add (continuous_fst.mul (hζ.1.continuous.comp continuous_snd))).continuousOn)
    exact (hz.comp continuous_snd).continuousOn.prodMk
      ((hjc.continuousOn.inv₀ (fun p hp => (hK p hp).1)).smul
        (hv.comp continuous_snd).continuousOn)
  have hval : ContinuousOn (fun p => L.value (A p)) K :=
    hL.continuousOn.comp hAc (fun p hp => (hK p hp).2)
  have hdf : ContinuousOn (fun p => fderiv ℝ L.value (A p)) K :=
    (hL.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp hAc
      (fun p hp => (hK p hp).2)
  let F : ℝ × ℝ → ℝ := fun p => L.value (A p) * j p
  let G : ℝ × ℝ → ℝ := fun p =>
    fderiv ℝ L.value (A p)
      (ζ p.2, 0, (-deriv ζ p.2 / (j p)^2) • v p.2) * j p +
      L.value (A p) * deriv ζ p.2
  have hF : ContinuousOn F K := hval.mul hjc.continuousOn
  have hG : ContinuousOn G K := by
    have hdζ : Continuous (fun p : ℝ × ℝ => deriv ζ p.2) :=
      ((contDiff_infty_iff_deriv.mp hζ.1).2).continuous.comp continuous_snd
    exact ((hdf.clm_apply
      ((hζ.1.continuous.comp continuous_snd).continuousOn.prodMk
        (continuousOn_const.prodMk
          ((hdζ.neg.continuousOn.div (hjc.pow 2).continuousOn
            (fun p hp => pow_ne_zero 2 (hK p hp).1)).smul
              (hv.comp continuous_snd).continuousOn)))).mul hjc.continuousOn).add
                (hval.mul hdζ.continuousOn)
  have hder : ∀ s ∈ Ioo (-δ) δ, ∀ t ∈ Icc I.a I.b,
      HasDerivAt (fun s => F (s, t)) (G (s, t)) s := by
    intro s hs t ht
    have hst : (s, t) ∈ K := ⟨Ioo_subset_Icc_self hs, ht⟩
    have hj : HasDerivAt (fun r : ℝ => j (r, t)) (deriv ζ t) s := by
      convert (hasDerivAt_const s (1 : ℝ)).add
        ((hasDerivAt_id s).mul_const (deriv ζ t)) using 1 <;> (first | rfl | simp)
    have hx : HasDerivAt (fun r : ℝ => A (r, t))
        (ζ t, 0, (-deriv ζ t / (j (s, t))^2) • v t) s := by
      have htime : HasDerivAt (fun r : ℝ => t + r * ζ t) (ζ t) s := by
        convert (hasDerivAt_const s t).add ((hasDerivAt_id s).mul_const (ζ t))
          using 1 <;> (first | rfl | simp)
      exact htime.prodMk ((hasDerivAt_const s (z t)).prodMk
        ((hj.inv (hK (s, t) hst).1).smul_const (v t)))
    have hdiff : DifferentiableAt ℝ L.value (A (s, t)) :=
      (hL.differentiableOn_one _ (hK (s, t) hst).2).differentiableAt
        (hU.mem_nhds (hK (s, t) hst).2)
    exact (hdiff.hasFDerivAt.comp_hasDerivAt s hx).mul hj
  have hi := integralDerivativeOnRectangle I.increasing.le hδ F G hF hG hder
  have hFeq (s : ℝ) : (∫ t in I.a..I.b, F (s, t)) = innerTimeAction L u ζ s := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le I.increasing.le] at ht
    simp only [F, A, j, hez t ht, hev t ht]
  have hGeq (t : ℝ) (ht : t ∈ Icc I.a I.b) :
      G (0, t) = timePartial L u t * ζ t + energy L u t * deriv ζ t := by
    have hd := hder 0 ⟨by linarith, hδ⟩ t ht
    have hp := integrandDerivative I m L u ⟨U, hU, hgU, hUd, hL⟩ ζ t ht
    have hf : (fun s => F (s, t)) = (fun s : ℝ =>
        L.value (t + s * ζ t, stateField I m u t,
          (1 + s * deriv ζ t)⁻¹ • velocityField I m u t) * (1 + s * deriv ζ t)) := by
      funext s
      simp only [F, A, j, hez t ht, hev t ht]
    rw [hf] at hd
    exact hd.unique hp
  have hGint : (∫ t in I.a..I.b, G (0, t)) =
      ∫ t in I.a..I.b, timePartial L u t * ζ t + energy L u t * deriv ζ t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hGeq t (by simpa only [uIcc_of_le I.increasing.le] using ht)
  rw [hGint] at hi
  exact hi.congr_of_eventuallyEq (Eventually.of_forall (fun s => (hFeq s).symm))

/-- A continuous derivative on a closed interval gives the one-sided derivatives
at the endpoints as well. We extend q by clamping, rather than differentiating
the arbitrary ambient extension of p outside the interval. -/
theorem closedIntervalRegularity {a b : ℝ} (hab : a < b) (p q : ℝ → ℝ)
    (hp : ContinuousOn p (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt p (q t) t) :
    ContDiffOn ℝ 1 p (Icc a b) ∧
    (∀ t ∈ Icc a b, HasDerivWithinAt p (q t) (Icc a b) t) ∧
    (∀ t ∈ Ioo a b, HasDerivAt p (q t) t) := by
  let qₑ : ℝ → ℝ := fun t => q (projIcc a b hab.le t)
  have hqe : Continuous qₑ :=
    (continuousOn_iff_continuous_domRestrict.mp hq).comp continuous_projIcc
  have heq : EqOn qₑ q (Icc a b) := by
    intro t ht
    simp [qₑ, projIcc_of_mem hab.le ht]
  let Q : ℝ → ℝ := fun t => ∫ r in a..t, qₑ r
  have hQ (t : ℝ) : HasDerivAt Q (qₑ t) t :=
    intervalIntegral.integral_hasDerivAt_right (hqe.intervalIntegrable a t)
      (hqe.stronglyMeasurableAtFilter volume (𝓝 t)) hqe.continuousAt
  have hpd : DifferentiableOn ℝ p (Ioo a b) :=
    fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  have hQd : DifferentiableOn ℝ Q (Ioo a b) :=
    fun t _ => (hQ t).differentiableAt.differentiableWithinAt
  have hder : EqOn (deriv p) (deriv Q) (Ioo a b) := by
    intro t ht
    rw [(hd t ht).deriv, (hQ t).deriv, heq (Ioo_subset_Icc_self ht)]
  obtain ⟨k, hk⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq
    (convex_Ioo a b).isPreconnected hpd hQd hder
  have hkc : ContinuousOn (fun t => Q t + k) (Icc a b) :=
    (continuous_iff_continuousAt.mpr (fun t => (hQ t).continuousAt)).continuousOn.add
      continuousOn_const
  have hclosed : EqOn p (fun t => Q t + k) (Icc a b) := by
    apply hk.of_subset_closure hp hkc Ioo_subset_Icc_self
    rw [closure_Ioo hab.ne]
  have hwithin : ∀ t ∈ Icc a b, HasDerivWithinAt p (q t) (Icc a b) t := by
    intro t ht
    rw [← heq ht]
    exact ((hQ t).add_const k).hasDerivWithinAt.congr
      (fun x hx => hclosed hx) (hclosed ht)
  refine ⟨(contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mpr ⟨?_, ?_⟩,
    hwithin, hd⟩
  · exact fun t ht => (hwithin t ht).differentiableWithinAt
  · exact hq.congr (fun t ht =>
      (hwithin t ht).derivWithin (uniqueDiffOn_Icc hab t ht))

theorem regularityFromWeakIdentity :
    Specs.VariationalNotes.Classical.InnerTime.regularityFromWeakIdentity := by
  intro a b hab p q hp hq hw
  have hpc := hp.mono Ioo_subset_Icc_self
  have hqc := hq.mono Ioo_subset_Icc_self
  obtain ⟨_, hd⟩ := distributionalPrimitiveScalarContinuous a b hab p q
    (hpc.locallyIntegrableOn measurableSet_Ioo)
    (hqc.locallyIntegrableOn measurableSet_Ioo) hw hpc hqc
  exact closedIntervalRegularity hab p q hp hq hd

theorem energyRegularityOfWeakIdentity :
    Specs.VariationalNotes.Classical.InnerTime.energyRegularityOfWeakIdentity := by
  intro I m L u hreg hw
  obtain ⟨hp, hq⟩ := fieldsContinuous I m L u hreg
  apply regularityFromWeakIdentity I.a I.b I.increasing (energy L u) (timePartial L u) hp hq
  intro φ hφ hk hs
  have h := hw φ ⟨hφ, hk, hs⟩
  rw [intervalIntegral.integral_of_le I.increasing.le, integral_Ioc_eq_integral_Ioo] at h
  simpa only [add_comm] using h

theorem stationaryWeakIdentity :
    Specs.VariationalNotes.Classical.InnerTime.stationaryWeakIdentity := by
  intro I m L u hreg hstat ζ hζ
  exact (actionDerivative I m L u hreg ζ hζ).unique (hstat ζ hζ)

theorem energyRegularity : Specs.VariationalNotes.Classical.InnerTime.energyRegularity := by
  intro I m L u hreg hstat
  exact energyRegularityOfWeakIdentity I m L u hreg
    (stationaryWeakIdentity I m L u hreg hstat)

theorem strongMinimum_is_weak {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (xₐ xᵦ : State m)
    (hu : strongLocalMinimum L xₐ xᵦ u) : weakLocalMinimum L xₐ xᵦ u := by
  obtain ⟨hu, ε, hε, hmin⟩ := hu
  refine ⟨hu, ε, hε, ?_⟩
  intro v hv hd
  apply hmin v hv (lt_of_le_of_lt ?_ hd)
  change ‖(v - u).val.1‖ ≤ max ‖(v - u).val.1‖ ‖(v - u).val.2‖
  exact le_max_left _ _

/-- Fermat’s theorem applied to the physical transported competitors. -/
theorem minimaStationaryOfTransportedCurves
    (transport : Specs.VariationalNotes.Classical.InnerTime.transportedCurves) :
    Specs.VariationalNotes.Classical.InnerTime.minimaStationary := by
  intro I m L u xₐ xᵦ hreg hmin ζ hζ
  have hu : weakLocalMinimum L xₐ xᵦ u :=
    hmin.elim id (strongMinimum_is_weak L u xₐ xᵦ)
  obtain ⟨hu, ε, hε, hmin⟩ := hu
  obtain ⟨v, hv0, hvlim, δ, hδ, hv⟩ := transport I m L u hreg ζ hζ
  have hder := actionDerivative I m L u hreg ζ hζ
  have hlocal : IsLocalMin (innerTimeAction L u ζ) 0 := by
    have hs : ∀ᶠ s in 𝓝 (0 : ℝ), |s| < δ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with s hs
      have h := Metric.mem_ball.mp hs
      rwa [Real.dist_eq, sub_zero] at h
    have hc : ∀ᶠ s in 𝓝 (0 : ℝ), ‖v s - u‖ < ε := by
      filter_upwards [hvlim.eventually (Metric.ball_mem_nhds u hε)] with s hs
      have h := Metric.mem_ball.mp hs
      exact (_root_.dist_eq_norm (v s) u) ▸ h
    have hzero : innerTimeAction L u ζ 0 = action L u := by
      simpa only [hv0] using (hv 0 (by simpa using hδ)).2.2.2.2.symm
    change ∀ᶠ s in 𝓝 (0 : ℝ), innerTimeAction L u ζ 0 ≤ innerTimeAction L u ζ s
    filter_upwards [hs, hc] with s hs hc
    obtain ⟨had, hleft, hright, _, haction⟩ := hv s hs
    rw [hzero, ← haction]
    exact hmin (v s) ⟨had, hleft.trans hu.2.1, hright.trans hu.2.2⟩ hc
  rw [hlocal.hasDerivAt_eq_zero hder] at hder
  exact hder

theorem timeMap_hasDerivAt {ζ : ℝ → ℝ} (hζ : ContDiff ℝ ∞ ζ) (s t : ℝ) :
    HasDerivAt (timeMap ζ s) (1 + s * deriv ζ t) t :=
  (hasDerivAt_id t).add (((hζ.differentiable (by simp) t).hasDerivAt).const_mul s)

theorem timeMapsIncreasing :
    Specs.VariationalNotes.Classical.InnerTime.timeMapsIncreasing := by
  intro I ζ hζ
  obtain ⟨hsmooth, hcompact, hsupport⟩ := hζ
  have hdercont : Continuous (deriv ζ) :=
    ((contDiff_infty_iff_deriv.mp hsmooth).2).continuous
  obtain ⟨C, hC⟩ := hcompact.deriv.exists_bound_of_continuous hdercont
  let B : ℝ := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (t : ℝ) : |deriv ζ t| < B := by
    have := hC t
    rw [Real.norm_eq_abs] at this
    dsimp [B]
    linarith [le_max_left C 0]
  refine ⟨B⁻¹, inv_pos.mpr hB, ?_⟩
  intro s hs
  have hpos (t : ℝ) : 0 < 1 + s * deriv ζ t := by
    have hsm : |s| * B < 1 := (lt_div_iff₀ hB).mp (by simpa only [one_div] using hs)
    have hm : |s * deriv ζ t| < 1 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hbound t).le (abs_nonneg s)).trans_lt hsm
    linarith [(neg_abs_le (s * deriv ζ t))]
  have hmono : StrictMono (timeMap ζ s) :=
    strictMono_of_hasDerivAt_pos (timeMap_hasDerivAt hsmooth s) hpos
  have ha : ζ I.a = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hsupport h).1.false)
  have hb : ζ I.b = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hsupport h).2.false)
  exact ⟨hpos, hmono, by simp [timeMap, ha], by simp [timeMap, hb]⟩

theorem timeDiffeomorphisms :
    Specs.VariationalNotes.Classical.InnerTime.timeDiffeomorphisms := by
  intro I ζ hζ
  obtain ⟨ε, hε, hsmall⟩ := timeMapsIncreasing I ζ hζ
  refine ⟨ε, hε, ?_⟩
  intro s hs
  obtain ⟨hpos, hmono, ha, hb⟩ := hsmall s hs
  have hc : ContDiff ℝ ∞ (timeMap ζ s) :=
    contDiff_id.add (contDiff_const.mul hζ.1)
  have hsurjI : SurjOn (timeMap ζ s) (Icc I.a I.b) (Icc I.a I.b) := by
    have h := intermediate_value_Icc I.increasing.le hc.continuous.continuousOn
    intro y hy
    exact h (by simpa only [ha, hb] using hy)
  have hsurj : Function.Surjective (timeMap ζ s) := by
    intro y
    by_cases hy : y ∈ Icc I.a I.b
    · obtain ⟨x, _, hxy⟩ := hsurjI hy
      exact ⟨x, hxy⟩
    · have hzero : ζ y = 0 := image_eq_zero_of_notMem_tsupport
        (fun hm => hy (Ioo_subset_Icc_self (hζ.2.2 hm)))
      exact ⟨y, by simp [timeMap, hzero]⟩
  let e : ℝ ≃o ℝ := hmono.orderIsoOfSurjective (timeMap ζ s) hsurj
  have he (t : ℝ) : e t = timeMap ζ s t := rfl
  have hinv : ContDiff ℝ ∞ (e.symm : ℝ → ℝ) :=
    e.toHomeomorph.contDiff_symm_deriv (fun t => ne_of_gt (hpos t))
      (timeMap_hasDerivAt hζ.1 s) hc
  refine ⟨hpos, ha, hb, e, he, hc, hinv, ?_, hmono.injective.injOn, hsurjI⟩
  intro t ht
  constructor
  · simpa only [ha] using hmono.monotone ht.1
  · simpa only [hb] using hmono.monotone ht.2

/-- Restriction of the inverse of an endpoint-fixing order isomorphism. -/
def inverseInterval {I : Interval} (e : ℝ ≃o ℝ)
    (ha : e I.a = I.a) (hb : e I.b = I.b) : C(I.Points, I.Points) where
  toFun t := ⟨e.symm t, by
    constructor
    · have hia : e.symm I.a = I.a := (congrArg e.symm ha.symm).trans (e.symm_apply_apply _)
      simpa only [hia] using e.symm.monotone t.property.1
    · have hib : e.symm I.b = I.b := (congrArg e.symm hb.symm).trans (e.symm_apply_apply _)
      simpa only [hib] using e.symm.monotone t.property.2⟩
  continuous_toFun := (e.symm.toHomeomorph.continuous.comp continuous_subtype_val).subtype_mk _

/-- Pullback of a C¹ jet by a smooth change of the independent variable.
The jet certificate is proved by the within chain rule, including endpoints. -/
def transportCurve {I : Interval} {m : ℕ} (u : C1Curve I m) (e : ℝ ≃o ℝ)
    (d : ℝ → ℝ) (hd : ∀ t, HasDerivAt (e : ℝ → ℝ) (d t) t)
    (hc : Continuous d) (hn : ∀ t, d t ≠ 0)
    (ha : e I.a = I.a) (hb : e I.b = I.b) : C1Curve I m := by
  let h := inverseInterval e ha hb
  let z : C(I.Points, State m) := u.state.comp h
  let w : C(I.Points, State m) := ⟨fun t => (d (e.symm t))⁻¹ • u.velocity (h t),
    ((hc.comp (e.symm.toHomeomorph.continuous.comp continuous_subtype_val)).inv₀
      (fun t => hn (e.symm (t : I.Points)))).smul (u.velocity.continuous.comp h.continuous)⟩
  refine ⟨(z, w), ?_⟩
  intro t
  have hi : HasDerivAt (e.symm : ℝ → ℝ) (d (e.symm t))⁻¹ t :=
    (hd (e.symm t)).of_local_left_inverse e.symm.toHomeomorph.continuous.continuousAt
      (hn _) (Eventually.of_forall e.apply_symm_apply)
  have hm : MapsTo (e.symm : ℝ → ℝ) (Icc I.a I.b) (Icc I.a I.b) :=
    fun r hr => (h ⟨r, hr⟩).property
  have hj := (u.property (h t)).scomp (t : ℝ) hi.hasDerivWithinAt hm
  exact hj.congr (fun r hr => by
    simp [z, h, inverseInterval, extendState, hr, hm hr]; rfl)
    (by simp [z, h, inverseInterval, extendState, t.property, hm t.property]; rfl)

@[simp] theorem transportCurve_state {I : Interval} {m : ℕ} (u : C1Curve I m)
    (e : ℝ ≃o ℝ) (d : ℝ → ℝ) (hd) (hc) (hn) (ha) (hb) (t : I.Points) :
    (transportCurve u e d hd hc hn ha hb).state t =
      u.state (inverseInterval e ha hb t) := rfl

@[simp] theorem transportCurve_velocity {I : Interval} {m : ℕ} (u : C1Curve I m)
    (e : ℝ ≃o ℝ) (d : ℝ → ℝ) (hd) (hc) (hn) (ha) (hb) (t : I.Points) :
    (transportCurve u e d hd hc hn ha hb).velocity t =
      (d (e.symm t))⁻¹ • u.velocity (inverseInterval e ha hb t) := rfl

/-- The transported jet evaluated in the original coordinates. -/
theorem transportCurve_fields {I : Interval} {m : ℕ} (u : C1Curve I m)
    (e : ℝ ≃o ℝ) (d : ℝ → ℝ) (hd) (hc) (hn) (ha) (hb)
    (t : ℝ) (ht : t ∈ Icc I.a I.b) :
    stateField I m (transportCurve u e d hd hc hn ha hb) (e t) = stateField I m u t ∧
    velocityField I m (transportCurve u e d hd hc hn ha hb) (e t) =
      (d t)⁻¹ • velocityField I m u t := by
  have het : e t ∈ Icc I.a I.b :=
    ⟨by simpa only [ha] using e.monotone ht.1,
     by simpa only [hb] using e.monotone ht.2⟩
  simp only [stateField, velocityField, extendState, dite_eq_left ht, dite_eq_left het]
  constructor
  · change u.state ⟨e.symm (e t), _⟩ = u.state ⟨t, ht⟩
    congr 1
    exact Subtype.ext (e.symm_apply_apply t)
  · change (d (e.symm (e t)))⁻¹ • u.velocity ⟨e.symm (e t), _⟩ =
      (d t)⁻¹ • u.velocity ⟨t, ht⟩
    simp only [e.symm_apply_apply]

/-- Change of variables for a physical transported curve. Continuity is needed
only on the reference interval, so zero extensions at the endpoints cause no issue. -/
theorem transportAction {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u v : C1Curve I m) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ ∞ ζ) (s : ℝ)
    (ha : timeMap ζ s I.a = I.a) (hb : timeMap ζ s I.b = I.b)
    (hm : MapsTo (timeMap ζ s) (Icc I.a I.b) (Icc I.a I.b))
    (hz : ∀ t ∈ Icc I.a I.b,
      stateField I m v (timeMap ζ s t) = stateField I m u t)
    (hv : ∀ t ∈ Icc I.a I.b,
      velocityField I m v (timeMap ζ s t) =
        (1 + s * deriv ζ t)⁻¹ • velocityField I m u t)
    (hc : Continuous (fun t : I.Points => L.value (graphPoint v t))) :
    action L v = innerTimeAction L u ζ s := by
  let g : ℝ → ℝ := fun t => L.value (t, stateField I m v t, velocityField I m v t)
  have hgc : ContinuousOn g (Icc I.a I.b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert hc using 1
    funext t
    simp [g, graphPoint, stateField, velocityField, extendState, t.property.1, t.property.2]
  have him : timeMap ζ s '' uIcc I.a I.b ⊆ Icc I.a I.b := by
    rw [uIcc_of_le I.increasing.le]
    exact image_subset_iff.mpr hm
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := I.a) (b := I.b) (g := g)
    (fun t _ => timeMap_hasDerivAt hζ s t)
    ((continuous_const.add (continuous_const.mul
      ((contDiff_infty_iff_deriv.mp hζ).2).continuous)).continuousOn)
    (hgc.mono him)
  rw [ha, hb] at hsub
  change (∫ t in I.a..I.b, g t) = _
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le I.increasing.le] at ht
  simp only [Function.comp_apply, g]
  rw [hz t ht, hv t ht]
  rfl

/-- The inverse time maps depend continuously on the parameter at zero, jointly
with their evaluation point. No differentiability of u' is involved. -/
theorem inverseFamily_tendsto {I : Interval} (ζ : ℝ → ℝ)
    (hζ : HasCompactSupport ζ) (hc : Continuous ζ)
    (r : ℝ → ℝ) (hr : Tendsto r (𝓝 0) (𝓝 0))
    (e : ℝ → ℝ ≃o ℝ) (he : ∀ s t, e s t = timeMap ζ (r s) t)
    (ha : ∀ s, e s I.a = I.a) (hb : ∀ s, e s I.b = I.b)
    (t : I.Points) :
    Tendsto (fun p : ℝ × I.Points => inverseInterval (e p.1) (ha p.1) (hb p.1) p.2)
      (𝓝 (0, t)) (𝓝 t) := by
  obtain ⟨C, hC⟩ := hζ.exists_bound_of_continuous hc
  have hdist (p : ℝ × I.Points) :
      dist p.2 (inverseInterval (e p.1) (ha p.1) (hb p.1) p.2) ≤ |r p.1| * C := by
    change dist (p.2 : ℝ) ((e p.1).symm p.2) ≤ _
    have hrel := he p.1 ((e p.1).symm p.2)
    rw [(e p.1).apply_symm_apply] at hrel
    have heq : (p.2 : ℝ) - (e p.1).symm p.2 =
        r p.1 * ζ ((e p.1).symm p.2) := by
      dsimp [timeMap] at hrel
      linarith
    rw [Real.dist_eq, heq, abs_mul]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using
      (hC ((e p.1).symm p.2))) (abs_nonneg _)
  have hlim : Tendsto (fun p : ℝ × I.Points => |r p.1| * C) (𝓝 (0, t)) (𝓝 0) := by
    simpa using ((hr.comp (continuous_fst.tendsto (0, t))).abs.mul_const C)
  exact continuous_snd.continuousAt.congr_dist
    (squeeze_zero (fun _ => dist_nonneg) hdist hlim)

/-- Joint convergence of both components of a jet on a compact interval
implies convergence in the shared C¹ norm. -/
theorem curveFamily_tendsto {I : Interval} {m : ℕ} (u : C1Curve I m)
    (v : ℝ → C1Curve I m)
    (hz : ∀ t : I.Points, Tendsto (fun p : ℝ × I.Points => (v p.1).state p.2)
      (𝓝 (0, t)) (𝓝 (u.state t)))
    (hw : ∀ t : I.Points, Tendsto (fun p : ℝ × I.Points => (v p.1).velocity p.2)
      (𝓝 (0, t)) (𝓝 (u.velocity t))) : Tendsto v (𝓝 0) (𝓝 u) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hzu : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t : I.Points,
      ‖(v s).state t - u.state t‖ < ε := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (X := ℝ) (Y := I.Points) (x₀ := 0) (P := fun s t => ‖(v s).state t - u.state t‖ < ε) ?_
    · simpa only [mem_univ, forall_const] using h
    intro t _
    have ht := ((hz t).sub (u.state.continuous.continuousAt.comp
      continuous_snd.continuousAt)).norm
    have ht' : Tendsto (fun p : ℝ × I.Points => ‖(v p.1).state p.2 - u.state p.2‖)
        (𝓝 (0, t)) (𝓝 0) := by simpa using ht
    exact ht'.eventually (Iio_mem_nhds hε)
  have hwu : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t : I.Points,
      ‖(v s).velocity t - u.velocity t‖ < ε := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (X := ℝ) (Y := I.Points) (x₀ := 0) (P := fun s t => ‖(v s).velocity t - u.velocity t‖ < ε) ?_
    · simpa only [mem_univ, forall_const] using h
    intro t _
    have ht := ((hw t).sub (u.velocity.continuous.continuousAt.comp
      continuous_snd.continuousAt)).norm
    have ht' : Tendsto (fun p : ℝ × I.Points => ‖(v p.1).velocity p.2 - u.velocity p.2‖)
        (𝓝 (0, t)) (𝓝 0) := by simpa using ht
    exact ht'.eventually (Iio_mem_nhds hε)
  filter_upwards [hzu, hwu] with s hs hw
  rw [_root_.dist_eq_norm (v s) u]
  change max ‖(v s).state - u.state‖ ‖(v s).velocity - u.velocity‖ < ε
  exact max_lt ((ContinuousMap.norm_lt_iff _ hε).mpr hs)
    ((ContinuousMap.norm_lt_iff _ hε).mpr hw)

theorem continuous_graphPoint_joint {I : Interval} {m : ℕ} :
    Continuous (fun p : C1Curve I m × I.Points => graphPoint p.1 p.2) := by
  have hs : Continuous (fun u : C1Curve I m => u.state) :=
    continuous_fst.comp continuous_subtype_val
  have hv : Continuous (fun u : C1Curve I m => u.velocity) :=
    continuous_snd.comp continuous_subtype_val
  exact (continuous_subtype_val.comp continuous_snd).prodMk
    (((hs.comp continuous_fst).eval continuous_snd).prodMk
      ((hv.comp continuous_fst).eval continuous_snd))

theorem eventually_graphPoint_mem {I : Interval} {m : ℕ}
    (u : C1Curve I m) {U : Set (ℝ × State m × State m)}
    (hU : IsOpen U) (hu : ∀ t : I.Points, graphPoint u t ∈ U) :
    ∀ᶠ v in 𝓝 u, ∀ t : I.Points, graphPoint v t ∈ U := by
  have h := isCompact_univ.eventually_forall_of_forall_eventually
    (X := C1Curve I m) (Y := I.Points) (x₀ := u)
    (P := fun v t => graphPoint v t ∈ U) ?_
  · simpa only [mem_univ, forall_const] using h
  intro t _
  exact continuous_graphPoint_joint.continuousAt (hU.mem_nhds (hu t))

theorem eventually_graphAdmissible {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m) (hu : graphAdmissible L u) :
    ∀ᶠ v in 𝓝 u, graphAdmissible L v :=
  eventually_graphPoint_mem u L.isOpen_domain hu

theorem eventually_regularGraph {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m) (hreg : regularNearGraph L u 1) :
    ∀ᶠ v in 𝓝 u, graphAdmissible L v ∧
      Continuous (fun t : I.Points => L.value (graphPoint v t)) := by
  obtain ⟨U, hU, hu, hsub, hL⟩ := hreg
  filter_upwards [eventually_graphPoint_mem u hU hu] with v hv
  refine ⟨fun t => hsub (hv t), ?_⟩
  have hg : Continuous (graphPoint v) :=
    continuous_subtype_val.prodMk (v.state.continuous.prodMk v.velocity.continuous)
  exact hL.continuousOn.comp_continuous hg hv

@[simp] theorem inverseInterval_left {I : Interval} (e : ℝ ≃o ℝ)
    (ha : e I.a = I.a) (hb : e I.b = I.b) :
    inverseInterval e ha hb I.left = I.left := by
  apply Subtype.ext
  change e.symm I.a = I.a
  exact (congrArg e.symm ha.symm).trans (e.symm_apply_apply _)

@[simp] theorem inverseInterval_right {I : Interval} (e : ℝ ≃o ℝ)
    (ha : e I.a = I.a) (hb : e I.b = I.b) :
    inverseInterval e ha hb I.right = I.right := by
  apply Subtype.ext
  change e.symm I.b = I.b
  exact (congrArg e.symm hb.symm).trans (e.symm_apply_apply _)

@[simp] theorem transportCurve_state_left {I : Interval} {m : ℕ}
    (u : C1Curve I m) (e : ℝ ≃o ℝ) (d : ℝ → ℝ)
    (hd) (hc) (hn) (ha) (hb) :
    (transportCurve u e d hd hc hn ha hb).state I.left = u.state I.left := by
  rw [transportCurve_state, inverseInterval_left]

@[simp] theorem transportCurve_state_right {I : Interval} {m : ℕ}
    (u : C1Curve I m) (e : ℝ ≃o ℝ) (d : ℝ → ℝ)
    (hd) (hc) (hn) (ha) (hb) :
    (transportCurve u e d hd hc hn ha hb).state I.right = u.state I.right := by
  rw [transportCurve_state, inverseInterval_right]

theorem transportCurve_eq_self {I : Interval} {m : ℕ}
    (u : C1Curve I m) (e : ℝ ≃o ℝ) (d : ℝ → ℝ)
    (hd) (hc) (hn) (ha) (hb)
    (he : ∀ t, e t = t) (hdu : ∀ t, d t = 1) :
    transportCurve u e d hd hc hn ha hb = u := by
  have hei (t : ℝ) : e.symm t = t := by
    exact (congrArg e.symm (he t).symm).trans (e.symm_apply_apply _)
  have hi (t : I.Points) : inverseInterval e ha hb t = t :=
    Subtype.ext (hei t)
  apply Subtype.ext
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    change (transportCurve u e d hd hc hn ha hb).state t = u.state t
    rw [transportCurve_state, hi]
  · apply ContinuousMap.ext
    intro t
    change (transportCurve u e d hd hc hn ha hb).velocity t = u.velocity t
    rw [transportCurve_velocity, hdu, inv_one, one_smul, hi]

/-- A family of transported jets converges in C¹ without requiring a second
 derivative of the original curve. -/
theorem transportFamily {I : Interval} {m : ℕ} (u : C1Curve I m)
    (ζ : ℝ → ℝ) (hζ : smoothInteriorTest I ζ) :
    ∃ v : ℝ → C1Curve I m, v 0 = u ∧ Tendsto v (𝓝 0) (𝓝 u) ∧
      ∃ ε > 0, ∀ s : ℝ, |s| < ε →
        (v s).state I.left = u.state I.left ∧
        (v s).state I.right = u.state I.right ∧
        (∀ t ∈ Icc I.a I.b,
          stateField I m (v s) (timeMap ζ s t) = stateField I m u t ∧
          velocityField I m (v s) (timeMap ζ s t) =
            (1 + s * deriv ζ t)⁻¹ • velocityField I m u t) := by
  obtain ⟨ε, hε, hgeo⟩ := timeDiffeomorphisms I ζ hζ
  let r : ℝ → ℝ := fun s => if |s| < ε then s else 0
  have hr0 : r 0 = 0 := by simp [r]
  have hrs (s : ℝ) : |r s| < ε := by
    dsimp [r]
    split_ifs with hs
    · exact hs
    · simpa using hε
  have hreq : r =ᶠ[𝓝 (0 : ℝ)] id := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with s hs
    have hs' : |s| < ε := by simpa [Real.dist_eq] using hs
    simp [r, hs']
  have hr : Tendsto r (𝓝 0) (𝓝 0) := tendsto_id.congr' hreq.symm
  choose e he using fun s => (hgeo (r s) (hrs s)).2.2.2
  have hea (s : ℝ) : e s I.a = I.a := (he s).1 I.a |>.trans (hgeo (r s) (hrs s)).2.1
  have heb (s : ℝ) : e s I.b = I.b := (he s).1 I.b |>.trans (hgeo (r s) (hrs s)).2.2.1
  let d : ℝ → ℝ → ℝ := fun s t => 1 + r s * deriv ζ t
  have hd (s t : ℝ) : HasDerivAt (e s : ℝ → ℝ) (d s t) t := by
    convert timeMap_hasDerivAt hζ.1 (r s) t using 1
    exact funext (he s).1
  have hdc (s : ℝ) : Continuous (d s) := continuous_const.add
    (continuous_const.mul ((contDiff_infty_iff_deriv.mp hζ.1).2).continuous)
  have hdn (s t : ℝ) : d s t ≠ 0 := ne_of_gt ((hgeo (r s) (hrs s)).1 t)
  let v : ℝ → C1Curve I m := fun s => transportCurve u (e s) (d s) (hd s) (hdc s)
    (hdn s) (hea s) (heb s)
  have hi (t : I.Points) := inverseFamily_tendsto ζ hζ.2.1 hζ.1.continuous r hr e
    (fun s => (he s).1) hea heb t
  have hvlim : Tendsto v (𝓝 0) (𝓝 u) := by
    apply curveFamily_tendsto u v
    · intro t
      exact u.state.continuous.continuousAt.tendsto.comp (hi t)
    · intro t
      have ht : Tendsto (fun p : ℝ × I.Points => (e p.1).symm p.2)
          (𝓝 (0, t)) (𝓝 (t : ℝ)) := continuous_subtype_val.continuousAt.tendsto.comp (hi t)
      have hrr := hr.comp (continuous_fst.tendsto (0, t))
      have hj : Tendsto (fun p : ℝ × I.Points => d p.1 ((e p.1).symm p.2))
          (𝓝 (0, t)) (𝓝 (1 : ℝ)) := by
        have hj := (tendsto_const_nhds (x := (1 : ℝ))).add
          (hrr.mul (((contDiff_infty_iff_deriv.mp hζ.1).2).continuous.continuousAt.tendsto.comp ht))
        simpa [d] using hj
      have hv := (hj.inv₀ one_ne_zero).smul
        (u.velocity.continuous.continuousAt.tendsto.comp (hi t))
      simpa only [v, transportCurve_velocity, Function.comp_apply, one_smul, inv_one] using hv
  have hv0 : v 0 = u := by
    apply transportCurve_eq_self
    · intro t
      simpa only [hr0, timeMap, zero_mul, add_zero] using (he 0).1 t
    · intro t
      simp only [d, hr0, zero_mul, add_zero]
  refine ⟨v, hv0, hvlim, ε, hε, ?_⟩
  intro s hs
  refine ⟨transportCurve_state_left _ _ _ _ _ _ _ _,
    transportCurve_state_right _ _ _ _ _ _ _ _, ?_⟩
  intro t ht
  have hrs' : r s = s := by simp [r, hs]
  have hf := transportCurve_fields u (e s) (d s) (hd s) (hdc s) (hdn s) (hea s) (heb s) t ht
  simpa only [v, (he s).1 t, d, hrs'] using hf

/-- Actual two-sided physical competitors, with their action expressed on the
fixed reference interval. -/
theorem transportedCurves : Specs.VariationalNotes.Classical.InnerTime.transportedCurves := by
  intro I m L u hreg ζ hζ
  obtain ⟨v, hv0, hvlim, ε, hε, hv⟩ := transportFamily u ζ hζ
  have hnear := hvlim.eventually (eventually_regularGraph L u hreg)
  obtain ⟨δ, hδ, hδnear⟩ := Metric.nhds_basis_ball.mem_iff.mp hnear
  obtain ⟨ρ, hρ, hmono⟩ := timeMapsIncreasing I ζ hζ
  refine ⟨v, hv0, hvlim, min ε (min δ ρ), lt_min hε (lt_min hδ hρ), ?_⟩
  intro s hs
  have hsε : |s| < ε := hs.trans_le (min_le_left _ _)
  have hsδ : |s| < δ := hs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsρ : |s| < ρ := hs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hl, hr, hfields⟩ := hv s hsε
  obtain ⟨had, hc⟩ := hδnear (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hsδ)
  obtain ⟨_, hm, ha, hb⟩ := hmono s hsρ
  have hmaps : MapsTo (timeMap ζ s) (Icc I.a I.b) (Icc I.a I.b) := by
    intro t ht
    exact ⟨by simpa only [ha] using hm.monotone ht.1,
      by simpa only [hb] using hm.monotone ht.2⟩
  refine ⟨had, hl, hr, fun t ht => (hfields t ht).1, ?_⟩
  exact transportAction L u (v s) ζ hζ.1 s ha hb hmaps
    (fun t ht => (hfields t ht).1) (fun t ht => (hfields t ht).2) hc

/-- A weak or strong C¹ local minimum is stationary under the inner time
variations of the manuscript. -/
theorem minimaStationary : Specs.VariationalNotes.Classical.InnerTime.minimaStationary :=
  minimaStationaryOfTransportedCurves transportedCurves

end VariationalNotes.Classical.InnerTime
