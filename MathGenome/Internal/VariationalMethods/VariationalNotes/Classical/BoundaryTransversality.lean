import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.BoundaryTransversality
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.FirstVariation
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.InnerTimeVariation
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace VariationalNotes.Classical.Boundary

theorem affineTime_self (I : Interval) (t : ℝ) : affineTime I I.a I.b t = t := by
  have hn : I.b - I.a ≠ 0 := sub_ne_zero.mpr I.increasing.ne'
  simp [affineTime, div_mul_cancel₀ _ hn]

theorem referenceAdmissible_referenceConfiguration {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m) :
    referenceAdmissible L (referenceConfiguration u) ↔ graphAdmissible L u := by
  have hn : I.b - I.a ≠ 0 := sub_ne_zero.mpr I.increasing.ne'
  simp [referenceAdmissible, referenceConfiguration, timeScale, hn, affineTime_self,
    I.increasing, graphAdmissible, graphPoint]

theorem referenceAction_referenceConfiguration {I : Interval} {m : ℕ}
    (L : Lagrangian m) (u : C1Curve I m) :
    referenceAction L (referenceConfiguration u) = action L u := by
  have hn : I.b - I.a ≠ 0 := sub_ne_zero.mpr I.increasing.ne'
  simp [referenceAction, referenceConfiguration, timeScale, hn, affineTime_self, action]

/-- A minimum with variable constrained endpoints remains a weak local minimum
when both endpoint values and times are fixed at their reference values. -/
theorem constrainedLocalMinimum_weak {I : Interval} {m : ℕ} (L : Lagrangian m)
    (Sₐ Sᵦ : Set (ℝ × State m)) (u : C1Curve I m)
    (hm : constrainedLocalMinimum L Sₐ Sᵦ u) :
    weakLocalMinimum L (u.state I.left) (u.state I.right) u := by
  have hadm : graphAdmissible L u :=
    (referenceAdmissible_referenceConfiguration L u).mp hm.1.1
  have hu : u ∈ fixedEndpointClass L (u.state I.left) (u.state I.right) := ⟨hadm, rfl, rfl⟩
  have hc : Continuous (fun z : C1Curve I m => referenceConfiguration z) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have hmap : fixedEndpointClass L (u.state I.left) (u.state I.right) ⊆
      (fun z : C1Curve I m => referenceConfiguration z) ⁻¹' constrainedConfigurations L Sₐ Sᵦ := by
    intro z hz
    refine ⟨(referenceAdmissible_referenceConfiguration L z).mpr hz.1, ?_, ?_⟩
    · change (I.a, z.state I.left) ∈ Sₐ
      rw [hz.2.1]
      exact hm.1.2.1
    · change (I.b, z.state I.right) ∈ Sᵦ
      rw [hz.2.2]
      exact hm.1.2.2
  have hmin := hm.2.comp_continuousOn hmap hc.continuousOn hu
  have he : (referenceAction L ∘ fun z : C1Curve I m => referenceConfiguration z) = action L := by
    funext z
    exact referenceAction_referenceConfiguration L z
  rw [he] at hmin
  change ∀ᶠ z in 𝓝[fixedEndpointClass L (u.state I.left) (u.state I.right)] u,
    action L u ≤ action L z at hmin
  rw [eventually_nhdsWithin_iff] at hmin
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hmin
  refine ⟨hu, ε, hε, ?_⟩
  intro z hz hnorm
  have hdist : dist z.val u.val < ε := by
    rw [dist_eq_norm]
    exact hnorm
  exact hball hdist hz

/-- Consequently the interior extremal and inner-time hypotheses needed for
integration by parts follow at the constrained local minimum itself. -/
theorem constrainedLocalMinimum_extremal {I : Interval} {m : ℕ} (L : Lagrangian m)
    (Sₐ Sᵦ : Set (ℝ × State m)) (u : C1Curve I m)
    (hreg : regularNearGraph L u 1) (hm : constrainedLocalMinimum L Sₐ Sᵦ u) :
    momentumEquation L u ∧ innerTimeStationary L u := by
  have hw := constrainedLocalMinimum_weak L Sₐ Sᵦ u hm
  exact ⟨(classicalEulerLagrange I m L _ _ u (Or.inl hw) hreg).2.2,
    InnerTime.minimaStationary I m L u _ _ hreg (Or.inl hw)⟩

/-- The bulk first variation is a total derivative even for C¹ extremals.
Continuity up to both endpoints and derivatives on the open interval suffice. -/
theorem boundaryIntegral : Specs.VariationalNotes.Classical.Boundary.boundaryIntegral := by
  intro I m L u hreg hp hstat w h dh hhc hdc hhd
  obtain ⟨hpc, hqc⟩ := gradientFields_continuousOn L u hreg
  obtain ⟨hHc, hLc⟩ := InnerTime.fieldsContinuous I m L u hreg
  have hH := (InnerTime.energyRegularity I m L u hreg hstat).2.2
  have hwc := stateField_continuousOn I m w
  have hwvc := velocityField_continuousOn I m w
  let F : ℝ → ℝ := fun t => inner ℝ (momentumField L u t) (stateField I m w t) +
    InnerTime.energy L u t * h t
  let G : ℝ → ℝ := fun t => InnerTime.timePartial L u t * h t +
    variationDensity (momentumField L u) (stateGradientField L u)
      (stateField I m w) (velocityField I m w) t +
    InnerTime.energy L u t * dh t
  have hFc : ContinuousOn F (Icc I.a I.b) := (hpc.inner hwc).add (hHc.mul hhc)
  have hGc : ContinuousOn G (Icc I.a I.b) :=
    ((hLc.mul hhc).add ((hqc.inner hwc).add (hpc.inner hwvc))).add (hHc.mul hdc)
  have hd : ∀ t ∈ Ioo I.a I.b, HasDerivAt F (G t) t := by
    intro t ht
    have hw := (VariationSpaces.curve_derivative I m w ⟨t, Ioo_subset_Icc_self ht⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
    have hw' : HasDerivAt (stateField I m w) (velocityField I m w t) t := by
      simpa [velocityField, extendState, Ioo_subset_Icc_self ht] using hw
    convert ((hp t ht).inner ℝ hw').add ((hH t ht).mul (hhd t ht)) using 1
    simp only [G, variationDensity]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le I.increasing.le
    hFc hd (hGc.intervalIntegrable_of_Icc I.increasing.le)
  change (∫ t in I.a..I.b, G t) = _
  rw [hi]
  simp only [F, endpointCovector]
  congr 1 <;> simp [momentumField, stateField, extendState, Interval.left, Interval.right,
    I.increasing.le]

/-- The affine infinitesimal time field has its prescribed endpoint values. -/
theorem variationTimeField_hasDerivAt {I : Interval} {m : ℕ} {u : C1Curve I m}
    (v : MovingEndpointVariation u) (t : ℝ) :
    HasDerivAt (variationTimeField v) (variationTimeSlope v) t := by
  unfold variationTimeField affineTime variationTimeSlope timeScale
  convert (hasDerivAt_const t (deriv v.leftTime 0)).add
    ((((hasDerivAt_id t).sub_const I.a).div_const (I.b - I.a)).mul_const
      (deriv v.rightTime 0 - deriv v.leftTime 0)) using 1
  · rfl
  · ring

theorem movingIntegralBoundaryValue :
    Specs.VariationalNotes.Classical.Boundary.movingIntegralBoundaryValue := by
  intro I m L u hreg hp hs v
  have hc : Continuous (variationTimeField v) :=
    continuous_iff_continuousAt.mpr (fun t => (variationTimeField_hasDerivAt v t).continuousAt)
  have hi := boundaryIntegral I m L u hreg hp hs (deriv v.rescaled 0)
    (variationTimeField v) (fun _ => variationTimeSlope v) hc.continuousOn
    continuousOn_const (fun t _ => variationTimeField_hasDerivAt v t)
  simpa only [movingVariationIntegral, boundaryValue, endpointDisplacements,
    endpointTimeDisplacements, variationTimeField,
    (VariationSpaces.affineTime_endpoints I (deriv v.leftTime 0) (deriv v.rightTime 0)).1,
    (VariationSpaces.affineTime_endpoints I (deriv v.leftTime 0) (deriv v.rightTime 0)).2] using hi

/-- Assembly of the analytic differentiation/change-of-variable obligations
with the already established integration by parts. No new regularity is used. -/
theorem movingBoundaryDerivative_of_actionDerivative
    (hd : Specs.VariationalNotes.Classical.Boundary.movingActionDerivative)
    (hc : Specs.VariationalNotes.Classical.Boundary.movingActionChangeOfVariables) :
    Specs.VariationalNotes.Classical.Boundary.movingBoundaryDerivative := by
  intro I m L u hreg hp hs v
  have h := hd I m L u hreg v
  rw [movingIntegralBoundaryValue I m L u hreg hp hs v] at h
  exact ⟨h, h.congr_of_eventuallyEq (hc I m L u hreg v)⟩

/-- The local-minimum test along any admissible moving family is a two-sided
test, since continuity is in the C¹ topology of the rescaled curves. -/
theorem variation_localMinimum {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (Sₐ Sᵦ : Set (ℝ × State m))
    (hm : constrainedLocalMinimum L Sₐ Sᵦ u) (v : MovingEndpointVariation u)
    (hv : ∀ᶠ s in 𝓝 (0 : ℝ),
      variationConfiguration v s ∈ constrainedConfigurations L Sₐ Sᵦ) :
    IsLocalMin (fun s => referenceAction L (variationConfiguration v s)) 0 := by
  have hc : ContinuousAt (variationConfiguration v) 0 :=
    v.left_differentiable.continuousAt.prodMk
      (v.right_differentiable.continuousAt.prodMk v.rescaled_differentiable.continuousAt)
  have hz : variationConfiguration v 0 = referenceConfiguration u := by
    simp [variationConfiguration, referenceConfiguration, v.left_zero, v.right_zero, v.rescaled_zero]
  have hct : Tendsto (variationConfiguration v) (𝓝 0)
      (𝓝[constrainedConfigurations L Sₐ Sᵦ] (referenceConfiguration u)) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa only [hz] using hc.tendsto, hv⟩
  have hmin := hm.2
  rw [← hz] at hmin
  apply hmin.comp_of_tendsto
  rw [hz]
  exact hct

/-- Independent endpoint lifts and the analytic bulk derivative imply both
annihilator conditions. The lifts are geometric constructions, not assumptions
of the final transversality statement. -/
theorem transversality_of_endpointLifts
    (hlift : Specs.VariationalNotes.Classical.Boundary.endpointLiftConstruction)
    (hd : Specs.VariationalNotes.Classical.Boundary.movingActionDerivative) :
    Specs.VariationalNotes.Classical.Boundary.transversality := by
  intro I m L u Sₐ Sᵦ hreg hm
  have hadm := (referenceAdmissible_referenceConfiguration L u).mp hm.1.1
  obtain ⟨hp, hs⟩ := constrainedLocalMinimum_extremal L Sₐ Sᵦ u hreg hm
  have hpair (α β : ℝ → ℝ × State m) (da db : ℝ × State m)
      (ha0 : α 0 = (I.a, u.state I.left)) (hb0 : β 0 = (I.b, u.state I.right))
      (ha : HasDerivAt α da 0) (hb : HasDerivAt β db 0)
      (hα : ∀ᶠ s in 𝓝 (0 : ℝ), α s ∈ Sₐ)
      (hβ : ∀ᶠ s in 𝓝 (0 : ℝ), β s ∈ Sᵦ) :
      endpointCovector L u I.right db - endpointCovector L u I.left da = 0 := by
    obtain ⟨v, he, hdt, hdz, hg⟩ := hlift I m L u hadm α β da db ha0 hb0 ha hb
    have hv : ∀ᶠ s in 𝓝 (0 : ℝ),
        variationConfiguration v s ∈ constrainedConfigurations L Sₐ Sᵦ := by
      filter_upwards [v.increasing_near, hg, hα, hβ] with s hi hg hα hβ
      refine ⟨⟨hi, hg⟩, ?_, ?_⟩
      · change (v.leftTime s, (v.rescaled s).state I.left) ∈ Sₐ
        rw [(he s).1, (he s).2.2.1]
        exact hα
      · change (v.rightTime s, (v.rescaled s).state I.right) ∈ Sᵦ
        rw [(he s).2.1, (he s).2.2.2]
        exact hβ
    have hmin := variation_localMinimum L u Sₐ Sᵦ hm v hv
    have hdv := hd I m L u hreg v
    rw [movingIntegralBoundaryValue I m L u hreg hp hs v] at hdv
    have heq := hmin.hasDerivAt_eq_zero hdv
    simpa only [boundaryValue, hdt, hdz] using heq
  constructor
  · intro da hda
    obtain ⟨α, ha0, ha, hα⟩ := hda
    have heq := hpair α (fun _ => (I.b, u.state I.right)) da 0 ha0 rfl ha
      (hasDerivAt_const 0 _) hα (Eventually.of_forall (fun _ => hm.1.2.2))
    have hz : endpointCovector L u I.right 0 = 0 := by simp [endpointCovector]
    rw [hz, zero_sub, neg_eq_zero] at heq
    exact heq
  · intro db hdb
    obtain ⟨β, hb0, hb, hβ⟩ := hdb
    have heq := hpair (fun _ => (I.a, u.state I.left)) β 0 db rfl hb0
      (hasDerivAt_const 0 _) hb (Eventually.of_forall (fun _ => hm.1.2.1)) hβ
    simpa [endpointCovector] using heq

/-- A local chart tangent is a two-sided curve tangent. This supplies the
explicit parametrization bridge needed for smooth endpoint submanifolds. -/
theorem endpointTangent_of_parametrization {m d : ℕ} {S : Set (ℝ × State m)}
    (e : State d → ℝ × State m) (x v : State d)
    (D : State d →L[ℝ] ℝ × State m) (he : HasFDerivAt e D x)
    (hS : ∀ᶠ y in 𝓝 x, e y ∈ S) : endpointTangent S (e x) (D v) := by
  let γ : ℝ → State d := fun s => x + s • v
  have hd : HasDerivAt γ v 0 := by
    convert (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    · rfl
    · simp
  have he' : HasFDerivAt e D (γ 0) := by simpa [γ] using he
  refine ⟨e ∘ γ, by simp [γ], he'.comp_hasDerivAt (0 : ℝ) hd, ?_⟩
  have hc : Tendsto γ (𝓝 0) (𝓝 x) := by
    simpa only [γ, zero_smul, add_zero] using hd.continuousAt.tendsto
  exact hc.eventually hS

theorem covectorSpecialCases : Specs.VariationalNotes.Classical.Boundary.covectorSpecialCases := by
  intro I m L u t
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      have hz := h (momentum L u t)
      simpa only [endpointCovector, mul_zero, add_zero, inner_self_eq_zero] using hz
    · intro hp z
      simp [endpointCovector, hp]
  · rw [← InnerTime.energyPairing I m L u t]
    constructor
    · intro h
      simpa [endpointCovector] using h 1
    · intro h r
      simp [endpointCovector, h]
  · intro T
    simp only [endpointCovector, mul_zero, add_zero]

/-- The chart statement follows directly from annihilation of curve tangents. -/
theorem chartTransversality_of_transversality
    (ht : Specs.VariationalNotes.Classical.Boundary.transversality) :
    Specs.VariationalNotes.Classical.Boundary.chartTransversality := by
  intro I m L u Sₐ Sᵦ hreg hmin d e x D he
  obtain ⟨ha, hb⟩ := ht I m L u Sₐ Sᵦ hreg hmin
  constructor
  · rintro ⟨hx, hS⟩ v
    apply ha
    rw [← hx]
    exact endpointTangent_of_parametrization e x v D he hS
  · rintro ⟨hx, hS⟩ v
    apply hb
    rw [← hx]
    exact endpointTangent_of_parametrization e x v D he hS

/-- Fixed-time free-state tangents are realized by affine endpoint curves. -/
theorem fixedTime_tangent {m : ℕ} (a : ℝ) (z v : State m) :
    endpointTangent ({a} ×ˢ (univ : Set (State m))) (a, z) (0, v) := by
  refine ⟨fun s => (a, z + s • v), by simp, ?_, ?_⟩
  · simpa using (hasDerivAt_const (0 : ℝ) a).prodMk
      ((hasDerivAt_const (0 : ℝ) z).add ((hasDerivAt_id 0).smul_const v))
  · exact Eventually.of_forall (fun s => ⟨rfl, mem_univ _⟩)

/-- Fixed-state free-time tangents are realized by affine endpoint curves. -/
theorem fixedState_tangent {m : ℕ} (a r : ℝ) (z : State m) :
    endpointTangent ((univ : Set ℝ) ×ˢ {z}) (a, z) (r, 0) := by
  refine ⟨fun s => (a + s * r, z), by simp, ?_, ?_⟩
  · simpa using ((hasDerivAt_const (0 : ℝ) a).add
      ((hasDerivAt_id 0).mul_const r)).prodMk (hasDerivAt_const (0 : ℝ) z)
  · exact Eventually.of_forall (fun s => ⟨mem_univ _, rfl⟩)

theorem fixedTimeFreeState_of_transversality
    (ht : Specs.VariationalNotes.Classical.Boundary.transversality) :
    Specs.VariationalNotes.Classical.Boundary.fixedTimeFreeState := by
  intro I m L u S hreg
  constructor
  · intro hm
    apply (covectorSpecialCases I m L u I.left).1.mp
    intro z
    exact (ht I m L u _ _ hreg hm).1 _ (fixedTime_tangent I.a (u.state I.left) z)
  · intro hm
    apply (covectorSpecialCases I m L u I.right).1.mp
    intro z
    exact (ht I m L u _ _ hreg hm).2 _ (fixedTime_tangent I.b (u.state I.right) z)

theorem freeTerminalTimeFixedState_of_transversality
    (ht : Specs.VariationalNotes.Classical.Boundary.transversality) :
    Specs.VariationalNotes.Classical.Boundary.freeTerminalTimeFixedState := by
  intro I m L u S z hreg hm
  have hz : u.state I.right = z := hm.1.2.2.2
  apply (covectorSpecialCases I m L u I.right).2.1.mp
  intro r
  apply (ht I m L u _ _ hreg hm).2
  rw [hz]
  exact fixedState_tangent I.b r z

theorem fixedTimeConstrainedState_of_transversality
    (ht : Specs.VariationalNotes.Classical.Boundary.transversality) :
    Specs.VariationalNotes.Classical.Boundary.fixedTimeConstrainedState := by
  intro I m L u S N hreg hm γ v hγ hd hN
  have htan : endpointTangent ({I.b} ×ˢ N) (I.b, u.state I.right) (0, v) := by
    refine ⟨fun s => (I.b, γ s), by simp [hγ], ?_, ?_⟩
    · exact (hasDerivAt_const (0 : ℝ) I.b).prodMk hd
    · exact hN.mono fun s hs => ⟨rfl, hs⟩
  simpa [endpointCovector] using (ht I m L u _ _ hreg hm).2 _ htan

/-- The affine curve joining two prescribed states, as a linear map into C¹. -/
def endpointInterpolationLinear (I : Interval) (m : ℕ) :
    State m × State m →ₗ[ℝ] C1Curve I m where
  toFun z := ⟨(
    ⟨fun t => (1 - ((t : ℝ) - I.a) / (I.b - I.a)) • z.1 +
      (((t : ℝ) - I.a) / (I.b - I.a)) • z.2,
      by fun_prop⟩,
    ⟨fun _ => (I.b - I.a)⁻¹ • (z.2 - z.1), continuous_const⟩), by
      intro t
      have hd := (((hasDerivAt_const (t : ℝ) (1 : ℝ)).sub
        (((hasDerivAt_id (t : ℝ)).sub_const I.a).div_const (I.b - I.a))).smul_const z.1).add
        (((((hasDerivAt_id (t : ℝ)).sub_const I.a).div_const (I.b - I.a))).smul_const z.2)
      have he : (-(I.b - I.a)⁻¹) • z.1 + (I.b - I.a)⁻¹ • z.2 =
          (I.b - I.a)⁻¹ • (z.2 - z.1) := by simp [sub_eq_add_neg, add_comm]
      have hd' : HasDerivAt
          (fun r : ℝ => (1 - (r - I.a) / (I.b - I.a)) • z.1 +
            ((r - I.a) / (I.b - I.a)) • z.2)
          ((I.b - I.a)⁻¹ • (z.2 - z.1)) t := by
        convert hd using 1
        · rfl
        · simp only [one_div, zero_sub, he]
      exact hd'.hasDerivWithinAt.congr_of_mem
        (fun r hr => by simp [extendState, hr]) t.property⟩
  map_add' z w := by
    apply Subtype.ext
    apply Prod.ext <;> apply ContinuousMap.ext <;> intro t
    · change (1 - ((t : ℝ) - I.a) / (I.b - I.a)) • (z.1 + w.1) +
          (((t : ℝ) - I.a) / (I.b - I.a)) • (z.2 + w.2) = _
      change _ = ((1 - ((t : ℝ) - I.a) / (I.b - I.a)) • z.1 +
          (((t : ℝ) - I.a) / (I.b - I.a)) • z.2) +
          ((1 - ((t : ℝ) - I.a) / (I.b - I.a)) • w.1 +
          (((t : ℝ) - I.a) / (I.b - I.a)) • w.2)
      module
    · change (I.b - I.a)⁻¹ • ((z.2 + w.2) - (z.1 + w.1)) =
          (I.b - I.a)⁻¹ • (z.2 - z.1) + (I.b - I.a)⁻¹ • (w.2 - w.1)
      module
  map_smul' c z := by
    apply Subtype.ext
    apply Prod.ext <;> apply ContinuousMap.ext <;> intro t
    · change (1 - ((t : ℝ) - I.a) / (I.b - I.a)) • (c • z.1) +
          (((t : ℝ) - I.a) / (I.b - I.a)) • (c • z.2) =
          c • ((1 - ((t : ℝ) - I.a) / (I.b - I.a)) • z.1 +
          (((t : ℝ) - I.a) / (I.b - I.a)) • z.2)
      module
    · change (I.b - I.a)⁻¹ • (c • z.2 - c • z.1) =
          c • ((I.b - I.a)⁻¹ • (z.2 - z.1))
      module

/-- The domain is finite dimensional, so the interpolation operator is bounded. -/
def endpointInterpolation (I : Interval) (m : ℕ) :
    State m × State m →L[ℝ] C1Curve I m :=
  ⟨endpointInterpolationLinear I m,
    by
      convert LinearMap.continuous_of_finiteDimensional (𝕜 := ℝ)
        (E := State m × State m) (F' := C1Curve I m) (endpointInterpolationLinear I m) using 1⟩

@[simp] theorem endpointInterpolation_left (I : Interval) (m : ℕ)
    (z : State m × State m) : (endpointInterpolation I m z).state I.left = z.1 := by
  simp [endpointInterpolation, endpointInterpolationLinear, C1Curve.state, Interval.left]

@[simp] theorem endpointInterpolation_right (I : Interval) (m : ℕ)
    (z : State m × State m) : (endpointInterpolation I m z).state I.right = z.2 := by
  have hn : I.b - I.a ≠ 0 := sub_ne_zero.mpr I.increasing.ne'
  simp [endpointInterpolation, endpointInterpolationLinear, C1Curve.state, Interval.right, hn]

/-- The transformed state–velocity graph depends continuously on a configuration
with distinct endpoint times, jointly with the reference point. -/
theorem transformedGraph_continuousAt {I : Interval} {m : ℕ}
    (c : Configuration I m) (t : I.Points) (hne : c.2.1 ≠ c.1) :
    ContinuousAt (fun p : Configuration I m × I.Points =>
      (affineTime I p.1.1 p.1.2.1 p.2, p.1.2.2.state p.2,
        (timeScale I p.1.1 p.1.2.1)⁻¹ • p.1.2.2.velocity p.2)) (c, t) := by
  have hs : Continuous (fun c : Configuration I m => c.2.2.state) :=
    continuous_fst.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  have hv : Continuous (fun c : Configuration I m => c.2.2.velocity) :=
    continuous_snd.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  have hn : timeScale I c.1 c.2.1 ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hne) (sub_ne_zero.mpr I.increasing.ne')
  have ht : Continuous (fun p : Configuration I m × I.Points =>
      affineTime I p.1.1 p.1.2.1 p.2) := by unfold affineTime; fun_prop
  have hk : Continuous (fun p : Configuration I m × I.Points =>
      timeScale I p.1.1 p.1.2.1) := by unfold timeScale; fun_prop
  exact ht.continuousAt.prodMk (((hs.comp continuous_fst).eval continuous_snd).continuousAt.prodMk
    ((hk.continuousAt.inv₀ hn).smul
      ((hv.comp continuous_fst).eval continuous_snd).continuousAt))

/-- Compactness makes openness uniform over the entire closed graph. -/
theorem eventually_transformedGraph_mem {I : Interval} {m : ℕ}
    (u : C1Curve I m) {U : Set (ℝ × State m × State m)}
    (hU : IsOpen U) (hu : ∀ t : I.Points, graphPoint u t ∈ U) :
    ∀ᶠ c : Configuration I m in 𝓝 (referenceConfiguration u),
      ∀ t : I.Points, (affineTime I c.1 c.2.1 t, c.2.2.state t,
        (timeScale I c.1 c.2.1)⁻¹ • c.2.2.velocity t) ∈ U := by
  have h := isCompact_univ.eventually_forall_of_forall_eventually
    (X := Configuration I m) (Y := I.Points) (x₀ := referenceConfiguration u)
    (P := fun c t => (affineTime I c.1 c.2.1 t, c.2.2.state t,
      (timeScale I c.1 c.2.1)⁻¹ • c.2.2.velocity t) ∈ U) ?_
  · simpa only [mem_univ, forall_const] using h
  intro t _
  have hn : I.b - I.a ≠ 0 := sub_ne_zero.mpr I.increasing.ne'
  apply (transformedGraph_continuousAt (referenceConfiguration u) t I.increasing.ne').eventually
  simpa [referenceConfiguration, affineTime_self, timeScale, hn, graphPoint] using hU.mem_nhds (hu t)

/-- The endpoint curves can be lifted by affine interpolation of their state
increments, with the physical curve defined by inverse affine time. -/
theorem endpointLiftConstruction :
    Specs.VariationalNotes.Classical.Boundary.endpointLiftConstruction := by
  intro I m L u hu α β da db ha0 hb0 ha hb
  have hat : HasDerivAt (fun s => (α s).1) da.1 0 :=
    (ContinuousLinearMap.fst ℝ ℝ (State m)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ha
  have haz : HasDerivAt (fun s => (α s).2) da.2 0 :=
    (ContinuousLinearMap.snd ℝ ℝ (State m)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ha
  have hbt : HasDerivAt (fun s => (β s).1) db.1 0 :=
    (ContinuousLinearMap.fst ℝ ℝ (State m)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hb
  have hbz : HasDerivAt (fun s => (β s).2) db.2 0 :=
    (ContinuousLinearMap.snd ℝ ℝ (State m)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hb
  let z : ℝ → C1Curve I m := fun s => u + endpointInterpolation I m
    ((α s).2 - u.state I.left, (β s).2 - u.state I.right)
  have hz0 : z 0 = u := by simp only [z, ha0, hb0, sub_self]; change u + endpointInterpolation I m 0 = u; simp
  have hzd : HasDerivAt z (endpointInterpolation I m (da.2, db.2)) 0 := by
    exact ((endpointInterpolation I m).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      ((haz.sub_const _).prodMk (hbz.sub_const _))).const_add u
  have hz : DifferentiableAt ℝ z 0 :=
    HasDerivAt.differentiableAt (𝕜 := ℝ) (F := C1Curve I m) hzd
  have hinc : ∀ᶠ s in 𝓝 (0 : ℝ), (α s).1 < (β s).1 := by
    have hopen : ∀ᶠ q : ℝ × ℝ in 𝓝 ((α 0).1, (β 0).1), q.1 < q.2 := by
      rw [ha0, hb0]
      exact (isOpen_lt continuous_fst continuous_snd).mem_nhds I.increasing
    exact (hat.continuousAt.prodMk hbt.continuousAt).eventually hopen
  have hn : I.b - I.a ≠ 0 := sub_ne_zero.mpr I.increasing.ne'
  let v : MovingEndpointVariation u := {
    leftTime := fun s => (α s).1
    rightTime := fun s => (β s).1
    rescaled := z
    physicalCurve := fun s r => stateField I m (z s)
      (I.a + ((r - (α s).1) / ((β s).1 - (α s).1)) * (I.b - I.a))
    left_zero := congrArg Prod.fst ha0
    right_zero := congrArg Prod.fst hb0
    rescaled_zero := hz0
    increasing_near := hinc
    rescaling_near := by
      filter_upwards [hinc] with s hs
      intro t
      have hn' : (β s).1 - (α s).1 ≠ 0 := sub_ne_zero.mpr hs.ne'
      have he : I.a + ((affineTime I (α s).1 (β s).1 t - (α s).1) /
          ((β s).1 - (α s).1)) * (I.b - I.a) = t := by
        unfold affineTime
        field_simp [hn, hn']
        ring
      simp only [he, stateField, extendState, dite_eq_left t.property]
    left_differentiable := hat.differentiableAt
    right_differentiable := hbt.differentiableAt
    rescaled_differentiable := hz }
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro s
    refine ⟨rfl, rfl, ?_, ?_⟩
    · change u.state I.left + (endpointInterpolation I m _).state I.left = _
      rw [endpointInterpolation_left]
      simp
    · change u.state I.right + (endpointInterpolation I m _).state I.right = _
      rw [endpointInterpolation_right]
      simp
  · exact Prod.ext hat.deriv hbt.deriv
  · apply Prod.ext
    · have he : (fun s => (v.rescaled s).state I.left) = fun s => (α s).2 := by
        funext s
        change u.state I.left + (endpointInterpolation I m _).state I.left = _
        simp
      exact ((VariationSpaces.rescaled_state_derivative I m u v I.left).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => congrFun he.symm s)).unique haz
    · have he : (fun s => (v.rescaled s).state I.right) = fun s => (β s).2 := by
        funext s
        change u.state I.right + (endpointInterpolation I m _).state I.right = _
        simp
      exact ((VariationSpaces.rescaled_state_derivative I m u v I.right).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => congrFun he.symm s)).unique hbz
  · have hc : Tendsto (variationConfiguration v) (𝓝 (0 : ℝ))
        (𝓝 (referenceConfiguration u)) := by
      have ht := hat.continuousAt.prodMk (hbt.continuousAt.prodMk hz.continuousAt)
      convert ht.tendsto using 1
      · rfl
      · simp only [referenceConfiguration, ha0, hb0, hz0]
    exact hc.eventually (eventually_transformedGraph_mem u L.isOpen_domain hu)

/-- Inverse affine time, defined on the ambient real line. -/
def inverseAffine (I : Interval) (A B r : ℝ) : ℝ :=
  I.a + ((r - A) / (B - A)) * (I.b - I.a)

theorem inverseAffine_forward (I : Interval) (A B t : ℝ) (h : A < B) :
    inverseAffine I A B (affineTime I A B t) = t := by
  have hn := sub_ne_zero.mpr h.ne'
  have hi := sub_ne_zero.mpr I.increasing.ne'
  unfold inverseAffine affineTime
  field_simp [hn, hi]
  ring

theorem forward_inverseAffine (I : Interval) (A B r : ℝ) (h : A < B) :
    affineTime I A B (inverseAffine I A B r) = r := by
  have hn := sub_ne_zero.mpr h.ne'
  have hi := sub_ne_zero.mpr I.increasing.ne'
  unfold inverseAffine affineTime
  field_simp [hn, hi]
  ring

theorem inverseAffine_mapsTo (I : Interval) (A B : ℝ) (h : A < B) :
    MapsTo (inverseAffine I A B) (Icc A B) (Icc I.a I.b) := by
  intro r hr
  have h₀ : 0 ≤ (r - A) / (B - A) := div_nonneg (sub_nonneg.mpr hr.1) (sub_pos.mpr h).le
  have h₁ : (r - A) / (B - A) ≤ 1 :=
    (div_le_one (sub_pos.mpr h)).mpr (sub_le_sub_right hr.2 A)
  change I.a ≤ I.a + _ ∧ I.a + _ ≤ I.b
  constructor <;> nlinarith [I.increasing]

theorem affineTime_mapsTo (I : Interval) (A B : ℝ) (h : A < B) :
    MapsTo (affineTime I A B) (Icc I.a I.b) (Icc A B) := by
  intro t ht
  have hm := (VariationSpaces.affineTime_increasing I A B h).monotone
  have he := VariationSpaces.affineTime_endpoints I A B
  exact ⟨by simpa only [he.1] using hm ht.1,
    by simpa only [he.2] using hm ht.2⟩

theorem inverseAffine_hasDerivAt (I : Interval) (A B r : ℝ) :
    HasDerivAt (inverseAffine I A B) (timeScale I A B)⁻¹ r := by
  convert (hasDerivAt_const r I.a).add
    ((((hasDerivAt_id r).sub_const A).div_const (B - A)).mul_const (I.b - I.a)) using 1
  · rfl
  · simp [timeScale, div_eq_mul_inv, mul_comm]

/-- Rescaling determines the actual within derivative of the physical curve,
including one-sided derivatives at both endpoints. -/
theorem physicalCurve_derivWithin {I : Interval} {m : ℕ} {u : C1Curve I m}
    (v : MovingEndpointVariation u) (s : ℝ)
    (hi : v.leftTime s < v.rightTime s)
    (hr : ∀ t : I.Points, (v.rescaled s).state t =
      v.physicalCurve s (affineTime I (v.leftTime s) (v.rightTime s) t))
    (t : I.Points) :
    derivWithin (v.physicalCurve s) (Icc (v.leftTime s) (v.rightTime s))
        (affineTime I (v.leftTime s) (v.rightTime s) t) =
      (timeScale I (v.leftTime s) (v.rightTime s))⁻¹ • (v.rescaled s).velocity t := by
  let A := v.leftTime s
  let B := v.rightTime s
  let r := affineTime I A B t
  have hm := inverseAffine_mapsTo I A B hi
  have ht : r ∈ Icc A B := affineTime_mapsTo I A B hi t.property
  have he : inverseAffine I A B r = t := inverseAffine_forward I A B t hi
  have hj₀ : HasDerivWithinAt (stateField I m (v.rescaled s))
      ((v.rescaled s).velocity t) (Icc I.a I.b) (inverseAffine I A B r) := by
    rw [he]
    exact (v.rescaled s).property t
  have hj := hj₀.scomp r
    (inverseAffine_hasDerivAt I A B r).hasDerivWithinAt hm
  have hd : HasDerivWithinAt (v.physicalCurve s)
      ((timeScale I A B)⁻¹ • (v.rescaled s).velocity t) (Icc A B) r := by
    apply hj.congr_of_mem _ ht
    intro y hy
    have hy' := hr ⟨inverseAffine I A B y, hm hy⟩
    change (v.rescaled s).state ⟨inverseAffine I A B y, hm hy⟩ =
      v.physicalCurve s (affineTime I A B (inverseAffine I A B y)) at hy'
    rw [forward_inverseAffine I A B y hi] at hy'
    simpa [stateField, extendState, hm hy] using hy'.symm
  exact hd.derivWithin (uniqueDiffOn_Icc hi r ht)

/-- Affine substitution for the physical action. The statement needs no
regularity of L: the C¹ jet and the rescaling identity already suffice. -/
theorem movingActionChangeOfVariables :
    Specs.VariationalNotes.Classical.Boundary.movingActionChangeOfVariables := by
  intro I m L u _ v
  filter_upwards [v.increasing_near, v.rescaling_near] with s hi hr
  let A := v.leftTime s
  let B := v.rightTime s
  let k := timeScale I A B
  let g : ℝ → ℝ := fun r => L.value (r, v.physicalCurve s r,
    derivWithin (v.physicalCurve s) (Icc A B) r)
  have haf : ∀ t : ℝ, affineTime I A B t = k * t + (A - k * I.a) := by
    intro t
    dsimp [k, timeScale, affineTime]
    ring
  have hend := VariationSpaces.affineTime_endpoints I A B
  have he := intervalIntegral.smul_integral_comp_mul_add (f := g) (a := I.a) (b := I.b)
    k (A - k * I.a)
  simp only [← haf, hend.1, hend.2, smul_eq_mul] at he
  change (∫ r in A..B, g r) = _
  rw [← he, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le I.increasing.le] at ht
  change k * g (affineTime I A B t) =
    L.value (affineTime I A B t, stateField I m (v.rescaled s) t,
      k⁻¹ • velocityField I m (v.rescaled s) t) * k
  rw [mul_comm k]
  congr 1
  dsimp only [g]
  rw [physicalCurve_derivWithin v s hi hr ⟨t, ht⟩, ← hr ⟨t, ht⟩]
  simp [stateField, velocityField, extendState, ht, k, A, B]

/-- Pairing two continuous fields is bounded linear in their pair. -/
def pairContinuousFields {K E F : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    C(K, E) × C(K, F) →L[ℝ] C(K, E × F) :=
  LinearMap.mkContinuous {
    toFun := fun p => p.1.prodMk p.2
    map_add' := fun _ _ => by ext t <;> rfl
    map_smul' := fun _ _ => by ext t <;> rfl } 1 (by
      intro p
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg p)).mpr
      intro t
      exact max_le (le_trans (p.1.norm_coe_le_norm t) (norm_fst_le p))
        (le_trans (p.2.norm_coe_le_norm t) (norm_snd_le p)))

/-- A differentiable curve of continuous fields can be passed through a C¹
integrand and a compact-interval integral. Differentiability of the curve is
required only at zero. Local Lipschitz bounds provide domination. -/
theorem compactField_integral_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (I : Interval)
    (j : ℝ → C(I.Points, E)) (j' : C(I.Points, E)) (hj : HasDerivAt j j' 0)
    (f : E → ℝ) (hf : ∀ t, ContDiffAt ℝ 1 f (j 0 t)) :
    HasDerivAt (fun s => ∫ t in I.a..I.b,
      f (j s (projIcc I.a I.b I.increasing.le t)))
      (∫ t in I.a..I.b, fderiv ℝ f (j 0 (projIcc I.a I.b I.increasing.le t))
        (j' (projIcc I.a I.b I.increasing.le t))) 0 := by
  let U := {x : E | ContDiffAt ℝ 1 f x}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun x hx => by
    change ContDiffAt ℝ 1 f x at hx
    exact hx.eventually (by simp)
  have hfc : ContDiffOn ℝ 1 f U := fun x hx => by
    change ContDiffAt ℝ 1 f x at hx
    exact hx.contDiffWithinAt
  let K := range (j 0)
  have hK : IsCompact K := isCompact_range (j 0).continuous
  have hKU : K ⊆ U := by rintro _ ⟨t, rfl⟩; exact hf t
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hloc : LocallyLipschitzOn (Metric.cthickening δ K) f := by
    intro x hx
    obtain ⟨C, V, hV, hC⟩ := (hδU hx).exists_lipschitzOnWith
    exact ⟨C, V, mem_nhdsWithin_of_mem_nhds hV, hC⟩
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK.cthickening hloc
  obtain ⟨B, hB⟩ := hj.isBigO_sub.bound
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t, j s t ∈ Metric.cthickening δ K := by
    have hb : ∀ᶠ s in 𝓝 (0 : ℝ), dist (j s) (j 0) < δ :=
      hj.continuousAt.eventually (Metric.ball_mem_nhds _ hδ)
    filter_upwards [hb] with s hs t
    exact Metric.mem_cthickening_of_dist_le _ (j 0 t) δ K ⟨t, rfl⟩
      ((ContinuousMap.dist_apply_le_dist t).trans hs.le)
  let S := {s | (∀ t, j s t ∈ Metric.cthickening δ K) ∧ ‖j s - j 0‖ ≤ B * ‖s‖}
  have hS : S ∈ 𝓝 (0 : ℝ) := by
    filter_upwards [hnear, hB] with s hs hb
    exact ⟨hs, by simpa only [sub_zero] using hb⟩
  let π := projIcc I.a I.b I.increasing.le
  have hπ : Continuous π := continuous_projIcc
  let F : ℝ → ℝ → ℝ := fun s t => f (j s (π t))
  let D : ℝ → ℝ := fun t => fderiv ℝ f (j 0 (π t)) (j' (π t))
  have hF (s : ℝ) (hs : s ∈ S) : Continuous (F s) :=
    hfc.continuousOn.comp_continuous ((j s).continuous.comp hπ)
      (fun t => hδU (hs.1 (π t)))
  have hzero : (0 : ℝ) ∈ S := mem_of_mem_nhds hS
  have hD : Continuous D := by
    apply Continuous.clm_apply
    · exact (hfc.continuousOn_fderiv_of_isOpen hU (by simp)).comp_continuous
        ((j 0).continuous.comp hπ) (fun t => hf (π t))
    · exact j'.continuous.comp hπ
  let T : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1
  have hD' : Integrable (T ∘ D) (volume.restrict (Ioc I.a I.b)) :=
    ((T.continuous.comp hD).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hdiff : ∀ t, HasDerivAt (fun s => F s t) (D t) 0 := by
    intro t
    have he := (ContinuousMap.evalCLM ℝ (π t)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hj
    exact (hf (π t)).differentiableAt_one.hasFDerivAt.comp_hasDerivAt (0 : ℝ) he
  have hh := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (μ := volume.restrict (Ioc I.a I.b)) (F := F) (F' := T ∘ D)
    (bound := fun _ => (C : ℝ) * B) hS
    (fun s hs => (hF s hs).aestronglyMeasurable)
    ((hF 0 hzero).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (T.continuous.comp hD).aestronglyMeasurable
    (Eventually.of_forall fun t s hs => by
      calc
        ‖F s t - F 0 t‖ ≤ (C : ℝ) * ‖j s (π t) - j 0 (π t)‖ :=
          hC.norm_sub_le (hs.1 _) (Metric.self_subset_cthickening K ⟨π t, rfl⟩)
        _ ≤ (C : ℝ) * (B * ‖s - 0‖) :=
          mul_le_mul_of_nonneg_left
            (by simpa only [sub_zero, ContinuousMap.sub_apply] using
              (ContinuousMap.norm_coe_le_norm (j s - j 0) (π t)).trans hs.2) C.coe_nonneg
        _ = _ := by ring)
    (integrable_const _) (Eventually.of_forall fun t => (hdiff t).hasFDerivAt)
  have hd := hh.2.hasDerivAt
  have he : (∫ t in Ioc I.a I.b, (T ∘ D) t) 1 = ∫ t in Ioc I.a I.b, D t := by
    rw [ContinuousLinearMap.integral_apply hD' 1]
    congr 1
    funext t
    simp [T]
  have hde : HasDerivAt (fun s => ∫ t in Ioc I.a I.b, F s t)
      (∫ t in Ioc I.a I.b, D t) 0 := by simpa only [he] using hd
  simpa only [intervalIntegral.integral_of_le I.increasing.le] using hde

/-- Reference time barycentric coordinate as a continuous scalar field. -/
def timeCoordinate (I : Interval) : C(I.Points, ℝ) :=
  ⟨fun t => ((t : ℝ) - I.a) / (I.b - I.a), by fun_prop⟩

/-- The raw pulled-back graph and its time Jacobian, as a continuous field.
Velocity division is performed by the finite-dimensional integrand below. -/
def movingJet {I : Interval} {m : ℕ} {u : C1Curve I m}
    (v : MovingEndpointVariation u) (s : ℝ) :
    C(I.Points, (ℝ × State m × State m) × ℝ) :=
  pairContinuousFields
    (pairContinuousFields
      (v.leftTime s • (1 - timeCoordinate I) + v.rightTime s • timeCoordinate I,
        pairContinuousFields ((v.rescaled s).state, (v.rescaled s).velocity)),
      ContinuousMap.const I.Points (timeScale I (v.leftTime s) (v.rightTime s)))

def movingJetDirection {I : Interval} {m : ℕ} {u : C1Curve I m}
    (v : MovingEndpointVariation u) : C(I.Points, (ℝ × State m × State m) × ℝ) :=
  pairContinuousFields
    (pairContinuousFields
      (deriv v.leftTime 0 • (1 - timeCoordinate I) +
        deriv v.rightTime 0 • timeCoordinate I,
        pairContinuousFields ((deriv v.rescaled 0).state, (deriv v.rescaled 0).velocity)),
      ContinuousMap.const I.Points (variationTimeSlope v))

theorem movingJet_hasDerivAt {I : Interval} {m : ℕ} {u : C1Curve I m}
    (v : MovingEndpointVariation u) : HasDerivAt (movingJet v) (movingJetDirection v) 0 := by
  have hA := v.left_differentiable.hasDerivAt
  have hB := v.right_differentiable.hasDerivAt
  have hz := DifferentiableAt.hasDerivAt (𝕜 := ℝ) (F := C1Curve I m)
    v.rescaled_differentiable
  have he : HasFDerivAt (fun z : C1Curve I m => z.val) (curveJets I m).subtypeL
      (v.rescaled 0) := by
    convert ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := C1Curve I m)
      (F := C(I.Points, State m) × C(I.Points, State m))
      (curveJets I m).subtypeL (x := v.rescaled 0) using 1
    rfl
  have hj : HasDerivAt (fun s => (v.rescaled s).val) (deriv v.rescaled 0).val 0 := by
    convert HasFDerivAt.comp_hasDerivAt (F := C1Curve I m)
      (E := C(I.Points, State m) × C(I.Points, State m)) (0 : ℝ) he hz using 1
    all_goals rfl
  have hj' := pairContinuousFields.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hj
  have ht := (hA.smul_const (1 - timeCoordinate I)).add (hB.smul_const (timeCoordinate I))
  have hg := pairContinuousFields.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (ht.prodMk hj')
  have hk : HasDerivAt (fun s => timeScale I (v.leftTime s) (v.rightTime s))
      (variationTimeSlope v) 0 := (hB.sub hA).div_const (I.b - I.a)
  have hkc := (ContinuousLinearMap.const I.Points (R := ℝ) (M := ℝ)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hk
  exact pairContinuousFields.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hg.prodMk hkc)

theorem movingJet_apply {I : Interval} {m : ℕ} {u : C1Curve I m}
    (v : MovingEndpointVariation u) (s : ℝ) (t : I.Points) :
    movingJet v s t =
      ((affineTime I (v.leftTime s) (v.rightTime s) t,
        (v.rescaled s).state t, (v.rescaled s).velocity t),
        timeScale I (v.leftTime s) (v.rightTime s)) := by
  apply Prod.ext
  · apply Prod.ext
    · change v.leftTime s * (1 - (((t : ℝ) - I.a) / (I.b - I.a))) +
        v.rightTime s * (((t : ℝ) - I.a) / (I.b - I.a)) = _
      unfold affineTime
      ring
    · rfl
  · rfl

theorem movingJet_zero {I : Interval} {m : ℕ} {u : C1Curve I m}
    (v : MovingEndpointVariation u) (t : I.Points) :
    movingJet v 0 t = (graphPoint u t, 1) := by
  have hn : I.b - I.a ≠ 0 := sub_ne_zero.mpr I.increasing.ne'
  simp [movingJet_apply, v.left_zero, v.right_zero, v.rescaled_zero, affineTime_self,
    timeScale, hn, graphPoint]

theorem movingJetDirection_apply {I : Interval} {m : ℕ} {u : C1Curve I m}
    (v : MovingEndpointVariation u) (t : I.Points) :
    movingJetDirection v t =
      ((variationTimeField v t, (deriv v.rescaled 0).state t,
        (deriv v.rescaled 0).velocity t), variationTimeSlope v) := by
  apply Prod.ext
  · apply Prod.ext
    · change deriv v.leftTime 0 * (1 - (((t : ℝ) - I.a) / (I.b - I.a))) +
        deriv v.rightTime 0 * (((t : ℝ) - I.a) / (I.b - I.a)) = _
      unfold variationTimeField affineTime
      ring
    · rfl
  · rfl

/-- Finite-dimensional action density with its positive affine Jacobian. -/
def scaledLagrangian {m : ℕ} (L : Lagrangian m)
    (x : (ℝ × State m × State m) × ℝ) : ℝ :=
  L.value (x.1.1, x.1.2.1, x.2⁻¹ • x.1.2.2) * x.2

theorem scaledLagrangian_regular {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 1) (t : I.Points) :
    ContDiffAt ℝ 1 (scaledLagrangian L) (graphPoint u t, 1) := by
  obtain ⟨U, hU, hu, _, hL⟩ := hreg
  have hLc : ContDiffAt ℝ 1 L.value (graphPoint u t) :=
    (hL (graphPoint u t) (hu t)).contDiffAt (hU.mem_nhds (hu t))
  have hmap : ContDiffAt ℝ 1 (fun x : (ℝ × State m × State m) × ℝ =>
      (x.1.1, x.1.2.1, x.2⁻¹ • x.1.2.2)) (graphPoint u t, 1) := by
    apply ContDiffAt.prodMk
    · fun_prop
    · apply ContDiffAt.prodMk
      · fun_prop
      · have hi : ContDiffAt ℝ 1
            (fun x : (ℝ × State m × State m) × ℝ => x.2⁻¹) (graphPoint u t, 1) :=
          contDiffAt_snd.inv (by simp)
        have hv : ContDiffAt ℝ 1
            (fun x : (ℝ × State m × State m) × ℝ => x.1.2.2) (graphPoint u t, 1) := by fun_prop
        convert hi.smul hv using 1
  have he : (fun x : (ℝ × State m × State m) × ℝ =>
      (x.1.1, x.1.2.1, x.2⁻¹ • x.1.2.2)) (graphPoint u t, 1) = graphPoint u t := by simp
  have hLc' : ContDiffAt ℝ 1 L.value
      ((fun x : (ℝ × State m × State m) × ℝ =>
        (x.1.1, x.1.2.1, x.2⁻¹ • x.1.2.2)) (graphPoint u t, 1)) := by
    rw [he]
    exact hLc
  exact (ContDiffAt.comp (graphPoint u t, 1)
    (f := fun x : (ℝ × State m × State m) × ℝ =>
      (x.1.1, x.1.2.1, x.2⁻¹ • x.1.2.2)) (g := L.value) hLc' hmap).mul contDiffAt_snd

/-- Differential of the scaled integrand at unit time Jacobian. -/
theorem scaledLagrangian_fderiv {m : ℕ} (L : Lagrangian m)
    (g : ℝ × State m × State m) (hL : DifferentiableAt ℝ L.value g)
    (d : (ℝ × State m × State m) × ℝ) :
    fderiv ℝ (scaledLagrangian L) (g, 1) d =
      fderiv ℝ L.value g (d.1.1, d.1.2.1, d.1.2.2 - d.2 • g.2.2) +
        L.value g * d.2 := by
  have hx := hasFDerivAt_id (𝕜 := ℝ) (g, (1 : ℝ))
  have hi := (hasFDerivAt_inv (𝕜 := ℝ) (x := (1 : ℝ)) (by norm_num)).comp (g, (1 : ℝ)) hx.snd
  have hn := hx.fst.fst.prodMk (hx.fst.snd.fst.prodMk (hi.smul hx.fst.snd.snd))
  have hL' : HasFDerivAt L.value (fderiv ℝ L.value g)
      ((fun x : (ℝ × State m × State m) × ℝ =>
        (x.1.1, x.1.2.1, x.2⁻¹ • x.1.2.2)) (g, 1)) := by
    simpa using hL.hasFDerivAt
  have hc := HasFDerivAt.comp (g, (1 : ℝ))
    (f := fun x : (ℝ × State m × State m) × ℝ =>
      (x.1.1, x.1.2.1, x.2⁻¹ • x.1.2.2)) hL' hn
  have he := congrArg (fun D => D d) (hc.mul hx.snd).fderiv
  change fderiv ℝ (scaledLagrangian L) (g, 1) d = _ at he
  simpa [ContinuousLinearMap.comp_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_comm] using he

/-- Identify the differential with the classical bulk density. -/
theorem movingJet_density {I : Interval} {m : ℕ} (L : Lagrangian m)
    (u : C1Curve I m) (hreg : regularNearGraph L u 1)
    (v : MovingEndpointVariation u) (t : I.Points) :
    fderiv ℝ (scaledLagrangian L) (movingJet v 0 t) (movingJetDirection v t) =
      InnerTime.timePartial L u t * variationTimeField v t +
      variationDensity (momentumField L u) (stateGradientField L u)
        (stateField I m (deriv v.rescaled 0)) (velocityField I m (deriv v.rescaled 0)) t +
      InnerTime.energy L u t * variationTimeSlope v := by
  obtain ⟨U, hU, hu, _, hL⟩ := hreg
  have hd : DifferentiableAt ℝ L.value (graphPoint u t) :=
    (hL.differentiableOn_one _ (hu t)).differentiableAt (hU.mem_nhds (hu t))
  rw [movingJet_zero, movingJetDirection_apply, scaledLagrangian_fderiv L _ hd]
  let D := fderiv ℝ L.value (graphPoint u t)
  have htime : InnerTime.timePartial L u t = D (1, 0, 0) := by
    have hd' : DifferentiableAt ℝ L.value (t, stateField I m u t, velocityField I m u t) := by
      convert hd using 1
      simp [graphPoint, stateField, velocityField, extendState, t.property]
    simpa [D, graphPoint, stateField, velocityField, extendState, t.property] using
      InnerTime.timePartial_eq_full L u t hd'
  have hz (z : State m) : inner ℝ (stateGradient L u t) z = D (0, z, 0) := by
    rw [stateGradient_eq_total L u t hd]
    exact InnerProductSpace.toDual_symm_apply
  have hp (z : State m) : inner ℝ (momentum L u t) z = D (0, 0, z) := by
    rw [momentum_eq_total L u t hd]
    exact InnerProductSpace.toDual_symm_apply
  have hvec : (variationTimeField v t, (deriv v.rescaled 0).state t,
      (deriv v.rescaled 0).velocity t - variationTimeSlope v • u.velocity t) =
      variationTimeField v t • (1, (0 : State m), (0 : State m)) +
        (0, (deriv v.rescaled 0).state t, 0) +
        (0, 0, (deriv v.rescaled 0).velocity t) -
        variationTimeSlope v • (0, 0, u.velocity t) := by
    ext <;> simp
  change D (variationTimeField v t, (deriv v.rescaled 0).state t,
    (deriv v.rescaled 0).velocity t - variationTimeSlope v • u.velocity t) +
    L.value (graphPoint u t) * variationTimeSlope v = _
  rw [hvec, map_sub, map_add, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  rw [htime, InnerTime.energyPairing I m L u t]
  simp only [variationDensity, momentumField, stateGradientField, stateField, velocityField,
    extendState, dite_eq_left t.property]
  rw [hz, hp, hp]
  ring

/-- Full differentiation of an arbitrary C¹-differentiable moving family. -/
theorem movingActionDerivative :
    Specs.VariationalNotes.Classical.Boundary.movingActionDerivative := by
  intro I m L u hreg v
  have hreg' : ∀ t, ContDiffAt ℝ 1 (scaledLagrangian L) (movingJet v 0 t) := by
    intro t
    rw [movingJet_zero]
    exact scaledLagrangian_regular L u hreg t
  have hd := compactField_integral_hasDerivAt I (movingJet v) (movingJetDirection v)
    (movingJet_hasDerivAt v) (scaledLagrangian L) hreg'
  have hfun : (fun s => ∫ t in I.a..I.b,
      scaledLagrangian L (movingJet v s (projIcc I.a I.b I.increasing.le t))) =
      fun s => referenceAction L (variationConfiguration v s) := by
    funext s
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le I.increasing.le] at ht
    dsimp only
    rw [projIcc_of_mem _ ht, movingJet_apply]
    simp [scaledLagrangian, variationConfiguration,
      stateField, velocityField, extendState, ht]
  have hint : (∫ t in I.a..I.b,
      fderiv ℝ (scaledLagrangian L) (movingJet v 0 (projIcc I.a I.b I.increasing.le t))
        (movingJetDirection v (projIcc I.a I.b I.increasing.le t))) =
      movingVariationIntegral L u v := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le I.increasing.le] at ht
    dsimp only
    rw [projIcc_of_mem _ ht]
    exact movingJet_density L u hreg v ⟨t, ht⟩
  rw [hfun, hint] at hd
  exact hd

/-- Boundary formula, for both the reference and the physical action. -/
theorem movingBoundaryDerivative :
    Specs.VariationalNotes.Classical.Boundary.movingBoundaryDerivative :=
  movingBoundaryDerivative_of_actionDerivative movingActionDerivative movingActionChangeOfVariables

theorem transversality : Specs.VariationalNotes.Classical.Boundary.transversality :=
  transversality_of_endpointLifts endpointLiftConstruction movingActionDerivative

theorem chartTransversality : Specs.VariationalNotes.Classical.Boundary.chartTransversality :=
  chartTransversality_of_transversality transversality

theorem fixedTimeFreeState : Specs.VariationalNotes.Classical.Boundary.fixedTimeFreeState :=
  fixedTimeFreeState_of_transversality transversality

theorem freeTerminalTimeFixedState :
    Specs.VariationalNotes.Classical.Boundary.freeTerminalTimeFixedState :=
  freeTerminalTimeFixedState_of_transversality transversality

theorem fixedTimeConstrainedState :
    Specs.VariationalNotes.Classical.Boundary.fixedTimeConstrainedState :=
  fixedTimeConstrainedState_of_transversality transversality

end VariationalNotes.Classical.Boundary
